module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoBase
public import CFSG.LieType.SeitzGeneration.UnitaryTwoWeights

public section

namespace CFSG.LieType.SeitzGeneration.UnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ} {ω : K} {𝔈 : Set (SUid σ n)}
  (F : EigenFrame σ n 𝔈)

@[expose] def EigenFrame.spanOf (S : Finset (Fin n)) : Submodule K (Fin n → K) :=
  Submodule.span K (F.u '' (S : Set (Fin n)))

theorem EigenFrame.spanOf_hasON (hσ : ∀ c, σ (σ c) = c) {S : Finset (Fin n)} (hS : 4 ≤ S.card) :
    HasONBasis σ (F.spanOf S) := by
  refine ⟨S.card, fun i => F.u (S.equivFin.symm i : Fin n), fun i j => ?_, ?_, Or.inl hS⟩
  · rw [F.herm_u]
    simp [Subtype.ext_iff]
  · rw [EigenFrame.spanOf]
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (S.equivFin.symm i).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩

theorem EigenFrame.herm_spanOf_of_notMem {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    {w : Fin n → K} (hw : w ∈ F.spanOf S) : herm σ w (F.u j) = 0 := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    exact F.herm_u_of_ne (fun h => hj (h ▸ hi))
  | zero => simp
  | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [herm_smul_left, ha, mul_zero]

theorem EigenFrame.allCenters_spanOf_union (hK : Field4 σ ω)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {S₀ : Finset (Fin n)} (h4 : 4 ≤ S₀.card)
    (hA : AllCenters (centSub 𝔈) (F.spanOf S₀)) (T : Finset (Fin n)) :
    AllCenters (centSub 𝔈) (F.spanOf (S₀ ∪ T)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hA
  | insert j T hj ih =>
    rw [Finset.union_insert]
    by_cases hjS : j ∈ S₀ ∪ T
    · rwa [Finset.insert_eq_of_mem hjS]
    · set S := S₀ ∪ T with hSdef
      have hS4 : 4 ≤ S.card := h4.trans (Finset.card_le_card Finset.subset_union_left)
      obtain ⟨a, haS⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      have haj : a ≠ j := fun h => hjS (h ▸ haS)
      have hua : F.u a ∈ F.spanOf S := Submodule.subset_span ⟨a, haS, rfl⟩
      have hstep := allCenters_step hK.invol hK.norm_one hK.two (F.spanOf_hasON hK.invol.invol hS4)
        ih hua (F.herm_u_self a) (F.herm_u_self j) (fun w hw => F.herm_spanOf_of_notMem hjS hw)
        (F.isCenter_pair_one hK hpair haj)
      have hspan : F.spanOf (insert j S) = F.spanOf S ⊔ Submodule.span K {F.u j} := by
        rw [EigenFrame.spanOf, Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert,
          sup_comm]
        rfl
      rw [hspan]
      exact hstep

theorem EigenFrame.centSub_eq_top (hK : Field4 σ ω) (hne : 𝔈.Nonempty) (hn : 5 ≤ n)
    (hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b)
    {τ : Fin 5 → Fin n} (hτ : Function.Injective τ)
    (htri : ∃ e ∈ 𝔈, ∃ t : K, e • F.u (τ 0) = t • F.u (τ 0) ∧ e • F.u (τ 1) = t • F.u (τ 1) ∧
      e • F.u (τ 2) = t • F.u (τ 2)) : centSub 𝔈 = ⊤ := by
  classical
  have hinj : Function.Injective (fun s : Fin 4 => τ s.castSucc) := fun a b h =>
    Fin.castSucc_injective 4 (hτ h)
  set S₀ : Finset (Fin n) := Finset.univ.image (fun s : Fin 4 => τ s.castSucc) with hS₀
  have hS₀card : S₀.card = 4 := by
    rw [hS₀, Finset.card_image_of_injective _ hinj]
    simp
  have hspan₀ : F.spanOf S₀ = Submodule.span K (Set.range (F.blk τ)) := by
    rw [EigenFrame.spanOf]
    congr 1
    ext v
    simp only [hS₀, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image,
      Set.mem_range, EigenFrame.blk]
    constructor
    · rintro ⟨a, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, rfl⟩
  have hA₀ : AllCenters (centSub 𝔈) (F.spanOf S₀) := by
    rw [hspan₀]
    exact F.allCenters_blk hK hne hpair hτ htri
  have hall := F.allCenters_spanOf_union hK hpair (by omega) hA₀ Finset.univ
  rw [Finset.union_eq_right.2 (Finset.subset_univ _)] at hall
  have htop : F.spanOf (Finset.univ : Finset (Fin n)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, rfl⟩ := F.spans v
    refine Submodule.span_mono ?_ (orthoEmb_mem_span F.u c)
    rintro _ ⟨i, rfl⟩
    exact ⟨i, Finset.mem_coe.2 (Finset.mem_univ i), rfl⟩
  rw [htop] at hall
  exact eq_top_of_forall_isCenter hK.invol (by omega) (fun h => by omega)
    fun a ha => hall a Submodule.mem_top ha

theorem injective_five {α : Type*} {i j k l m : α} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m)
    (hlm : l ≠ m) : Function.Injective (![i, j, k, l, m] : Fin 5 → α) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

end CFSG.LieType.SeitzGeneration.UnitaryTwo

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt
  CFSG.LieType.SeitzGeneration.UnitaryTwo CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem closure_centralizers_unitarySU_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn : 5 ≤ n) (E : Subgroup (unitarySU ℓ f K n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hcard4 : Nat.card K = 4 := by
    rw [h.card_eq_sq, hq]
    norm_num
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
    (hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega))
  have h2 : (1 : K) + 1 = 0 := by
    have h := CharP.cast_eq_zero K ℓ
    rw [hℓ2] at h
    rw [one_add_one_eq_two]
    exact_mod_cast h
  have hqn : ∀ c : K, c ≠ 0 → σ c * c = 1 := fun c hc => by
    have hc3 : c ^ 3 = 1 := by
      have := Fintype.ofFinite K
      have h := FiniteField.pow_card_sub_one_eq_one c hc
      rwa [← Nat.card_eq_fintype_card, hcard4] at h
    rw [hσdef, unitaryInvolution_apply, hq]
    linear_combination hc3
  have hKunits : Nat.card Kˣ = 3 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard4]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω', hω'⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hKunits])
  have hω3 : (ω' : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω'
    rw [hω'] at this
    simpa using congrArg Units.val this
  have hω1 : (ω' : K) ≠ 1 := fun h => by
    have : ω' = 1 := Units.ext h
    rw [this, orderOf_one] at hω'
    omega
  have hK : Field4 σ (ω' : K) := ⟨hσ, hqn, h2, hω3, hω1⟩
  have hcardE : Nat.card E = 9 := by rw [hcard]; norm_num
  let φ : unitarySU ℓ f K n ≃* SUid σ n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n).symm
  have hsm : ∀ (x : unitarySU ℓ f K n) (v : Fin n → K),
      φ x • v = ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := fun x v => rfl
  obtain ⟨u, huON₀, hspan, heig⟩ := exists_eigenframe h (by rw [hq]) E hcomm hexp
  have huON : IsON σ u := huON₀
  let ev : E → Fin n → K := fun y i => herm σ (u i) (φ y.1 • u i)
  have hev : ∀ (y : E) (i : Fin n), φ y.1 • u i = ev y i • u i := by
    intro y i
    obtain ⟨d, hd⟩ := heig y.1 y.2
    have h1 : φ y.1 • u i = d i • u i := (hsm y.1 (u i)).trans (hd i)
    have h2 : ev y i = d i := by
      simp only [ev, h1, herm_smul_right, huON i i]
      simp
    rw [h2]
    exact h1
  have hev_mul : ∀ (y y' : E) (i : Fin n), ev (y * y') i = ev y i * ev y' i := by
    intro y y' i
    have h1 : φ (y * y').1 • u i = (ev y i * ev y' i) • u i := by
      rw [Subgroup.coe_mul, map_mul, mul_smul, hev y' i, smul_comm, hev y i, smul_smul,
        mul_comm]
    show herm σ (u i) (φ (y * y').1 • u i) = _
    rw [h1, herm_smul_right, huON i i]
    simp
  have hev_one : ∀ i : Fin n, ev 1 i = 1 := fun i => by
    simp [ev, huON i i]
  have hev_ne : ∀ (y : E) (i : Fin n), ev y i ≠ 0 := fun y i h0 => by
    have := hev_mul y y⁻¹ i
    rw [mul_inv_cancel, hev_one, h0, zero_mul] at this
    exact one_ne_zero this
  let χ : Fin n → E →* Kˣ := fun i =>
    MonoidHom.mk' (fun y => Units.mk0 (ev y i) (hev_ne y i))
      (fun y y' => Units.ext (hev_mul y y' i))
  let X : Set (unitarySU ℓ f K n) := {x | x ∈ E ∧ x ≠ 1}
  let 𝔈 : Set (SUid σ n) := φ '' X
  have hmemE : ∀ y : E, y ≠ 1 → φ y.1 ∈ 𝔈 := fun y hy =>
    ⟨y.1, ⟨y.2, fun h1 => hy (Subtype.ext h1)⟩, rfl⟩
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨y₀, hy₀⟩ := exists_ne (1 : E)
  have hne : 𝔈.Nonempty := ⟨_, hmemE y₀ hy₀⟩
  let F : EigenFrame σ n 𝔈 := ⟨u, huON, hspan, fun e he => by
    obtain ⟨x, ⟨hxE, _⟩, rfl⟩ := he
    obtain ⟨d, hd⟩ := heig x hxE
    exact ⟨d, fun i => (hsm x (u i)).trans (hd i)⟩⟩
  have hpair : ∀ a b : Fin n, a ≠ b →
      ∃ e ∈ 𝔈, ∃ t : K, e • F.u a = t • F.u a ∧ e • F.u b = t • F.u b := by
    intro a b hab
    obtain ⟨y, hy1, hyab⟩ := exists_ne_one_eq (E := E) hcardE hKunits (χ a) (χ b)
    refine ⟨φ y.1, hmemE y hy1, ev y a, hev y a, ?_⟩
    show φ y.1 • u b = ev y a • u b
    rw [hev y b, show ev y a = ev y b from congrArg Units.val hyab]
  obtain ⟨y, hy1, i, j, k, hij, hik, hjk, hc1, hc2⟩ :=
    exists_eq_triple (E := E) hcardE hKunits (fun s : Fin 5 => χ (Fin.castLE hn s))
  obtain ⟨l, m, hli, hlj, hlk, hmi, hmj, hmk, hlm⟩ := exists_two_complement i j k hij hik hjk
  let ρ : Fin 5 → Fin 5 := ![i, j, k, l, m]
  have hρ : Function.Injective ρ :=
    injective_five hij hik (Ne.symm hli) (Ne.symm hmi) hjk (Ne.symm hlj) (Ne.symm hmj)
      (Ne.symm hlk) (Ne.symm hmk) hlm
  let τ : Fin 5 → Fin n := fun s => Fin.castLE hn (ρ s)
  have hτ : Function.Injective τ := fun a b hab => hρ (Fin.castLE_injective hn hab)
  have hc1' : ev y (Fin.castLE hn i) = ev y (Fin.castLE hn j) := congrArg Units.val hc1
  have hc2' : ev y (Fin.castLE hn i) = ev y (Fin.castLE hn k) := congrArg Units.val hc2
  have htri : ∃ e ∈ 𝔈, ∃ t : K, e • F.u (τ 0) = t • F.u (τ 0) ∧ e • F.u (τ 1) = t • F.u (τ 1) ∧
      e • F.u (τ 2) = t • F.u (τ 2) := by
    refine ⟨φ y.1, hmemE y hy1, ev y (Fin.castLE hn i), hev y _, ?_, ?_⟩
    · show φ y.1 • u (Fin.castLE hn j) = _
      rw [hev y _, ← hc1']
      rfl
    · show φ y.1 • u (Fin.castLE hn k) = _
      rw [hev y _, ← hc2']
      rfl
  have hgen : centSub 𝔈 = ⊤ := F.centSub_eq_top hK hne hn hpair hτ htri
  have hX : {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} =
      {g | ∃ x ∈ X, g * x = x * g} := by
    ext g
    constructor
    · rintro ⟨x, hx, hx1, hg⟩
      exact ⟨x, ⟨hx, hx1⟩, hg⟩
    · rintro ⟨x, ⟨hx, hx1⟩, hg⟩
      exact ⟨x, hx, hx1, hg⟩
  rw [hX]
  exact closure_centralizers_of_equiv φ X hgen

end CFSG.LieType.SeitzGeneration
