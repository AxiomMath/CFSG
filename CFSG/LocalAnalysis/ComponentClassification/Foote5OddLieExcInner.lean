module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToralRigid
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcE6

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank

variable {τ : Tag}

theorem outerCoreAt_innerDiag_of_toral
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K))
    (htor : ∀ c : Fin τ.rank → Kˣ, (∀ i, c i = 1 ∨ c i = -1) →
      ∀ i₀ : MulAut (adjointGroup τ K), (∀ h : adjointGroup τ K,
        (i₀ h : ModGL τ K) = rootDiagUnit τ c * h * (rootDiagUnit τ c)⁻¹) → OuterCoreAt i₀)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set ι := algebraMap K L with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  have hL2 : ringChar L ≠ 2 := by
    rw [ringChar.eq L p]
    exact hp2
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin τ.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL τ K) * rootDiagUnit τ b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness τ K hK L ι
  have hgG : baseChangeGL ι (g : ModGL τ K) ∈ adjointGroup τ L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ L b).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ b := baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ K,
      x * baseChangeGL ι (h : ModGL τ K) * x⁻¹ = baseChangeGL ι (α h : ModGL τ K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) = rootDiagUnit τ b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  obtain ⟨h, hhR, b', hb', hhx, hmapH, -, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K L hτ hK Fr hFr hxR hx2
  try rw [← hι] at hmapH
  have hhG : h ∈ adjointGroup τ L := (Subgroup.mem_inf.1 hhR).1
  have hhN : h ∈ Subgroup.normalizer
      (((adjointGroup τ K).map (baseChangeGL ι) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hmapH]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hmapH] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      have hyy' : y' = y := by
        have h1 : h * y' * h⁻¹ = h * y * h⁻¹ := hyy
        simpa using h1
      rw [← hyy']
      exact hy'
  have hne : (-1 : Lˣ) ≠ 1 := fun h1 =>
    Ring.neg_one_ne_one_of_char_ne_two hL2 (by simpa using congrArg Units.val h1)
  obtain ⟨c, hcdef⟩ : ∃ c : Fin τ.rank → Kˣ, c = fun i => if b' i = 1 then 1 else -1 :=
    ⟨_, rfl⟩
  have hc : ∀ i, c i = 1 ∨ c i = -1 := fun i => by
    rw [hcdef]
    by_cases hi : b' i = 1
    · exact Or.inl (ite_eq_left hi)
    · exact Or.inr (ite_eq_right hi)
  have hcb : (fun i => Units.map ι.toMonoidHom (c i)) = b' := by
    funext i
    rcases hb' i with hi | hi
    · have hci : c i = 1 := by
        rw [hcdef]
        exact ite_eq_left hi
      rw [hci, hi, map_one]
    · have hi' : b' i ≠ 1 := by
        rw [hi]
        exact hne
      have hci : c i = -1 := by
        rw [hcdef]
        exact ite_eq_right hi'
      rw [hci, hi]
      ext
      simp
  have hdc : rootDiagUnit τ b' = baseChangeGL ι (rootDiagUnit τ c) := by
    rw [baseChangeGL_rootDiagUnit, hcb]
  let e : adjointGroup τ K ≃* (adjointGroup τ K).map (baseChangeGL ι) :=
    (adjointGroup τ K).equivMapOfInjective (baseChangeGL ι) hinj
  let ψH : MulAut ((adjointGroup τ K).map (baseChangeGL ι)) :=
    conjNormalizerHom (adjointGroup τ L) ((adjointGroup τ K).map (baseChangeGL ι))
      ⟨h, Subgroup.mem_inf.2 ⟨hhG, hhN⟩⟩
  let ψ : MulAut (adjointGroup τ K) := (e.trans ψH).trans e.symm
  have hψι : ∀ u : adjointGroup τ K, baseChangeGL ι (ψ u : ModGL τ K) =
      h * baseChangeGL ι (u : ModGL τ K) * h⁻¹ := by
    intro u
    have h1 : baseChangeGL ι (ψ u : ModGL τ K) =
        ((e (ψ u) : (adjointGroup τ K).map (baseChangeGL ι)) : ModGL τ L) := rfl
    rw [h1, show e (ψ u) = ψH (e u) from e.apply_symm_apply _]
    rfl
  have hi₀ : ∀ u : adjointGroup τ K, ((ψ * α * ψ⁻¹) u : ModGL τ K) =
      rootDiagUnit τ c * u * (rootDiagUnit τ c)⁻¹ := by
    intro u
    apply hinj
    have hu : baseChangeGL ι ((ψ⁻¹ u : adjointGroup τ K) : ModGL τ K) =
        h⁻¹ * baseChangeGL ι (u : ModGL τ K) * h := by
      have h1 := hψι (ψ⁻¹ u)
      rw [show ψ (ψ⁻¹ u) = u from ψ.apply_symm_apply u] at h1
      rw [h1]
      group
    rw [MulAut.mul_apply, MulAut.mul_apply, hψι, ← hxconj, hu, map_mul, map_mul, map_inv, ← hdc,
      ← hhx]
    group
  exact outerCoreAt_of_conj (ψ := ψ) rfl (htor c hc (ψ * α * ψ⁻¹) hi₀)

theorem exists_normalForm_of_odd
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (hG2 : τ = .G2 → ringChar K ≠ 3) (r : MulAut (adjointGroup τ K))
    (hr : Odd (orderOf r)) :
    ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (φ : K ≃+* K), ∀ h : adjointGroup τ K,
      (r h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
          (g : ModGL τ K)⁻¹ := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  rcases hτ with rfl | rfl | rfl | rfl
  ·
    obtain ⟨hU, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hcard
      .G2 (Or.inr ⟨rfl, fun h3 => hG2 rfl (hchar.trans h3)⟩)
    obtain ⟨gφ, hgφ, -⟩ := hU r
    refine ⟨gφ.1, 1, gφ.2, fun h => ?_⟩
    rw [hgφ h, rootDiagUnit_one, mul_one, inv_one, mul_one]
  ·
    obtain ⟨hU, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hcard
      .F4 (Or.inl rfl)
    obtain ⟨gφ, hgφ, -⟩ := hU r
    refine ⟨gφ.1, 1, gφ.2, fun h => ?_⟩
    rw [hgφ h, rootDiagUnit_one, mul_one, inv_one, mul_one]
  ·
    obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
    obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
      ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
    obtain ⟨g, a, φ, ε, hgaφ⟩ := hNF r
    have hε : (ε : ℕ) = 0 := by
      have h1 : Θ r ^ orderOf r = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [hΘ r g a φ ε hgaφ] at h1
      have h2 := congrArg Prod.snd h1
      rw [Prod.pow_snd, Prod.snd_one, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
      have hε2 : (ε : ℕ) < 2 := ε.isLt
      by_contra hne
      have hε1 : (ε : ℕ) = 1 := by omega
      rw [hε1, Nat.cast_one, mul_one] at h2
      have h3 : ((orderOf r : ℕ) : ZMod 2) = 0 := h2
      exact (Nat.not_even_iff_odd.2 hr) (ZMod.natCast_eq_zero_iff_even.1 h3)
    refine ⟨g, a, φ, fun h => ?_⟩
    rw [hgaφ h, hε, show exactQ Tag.E6 K 0 = 1 from pow_zero _, mul_one, inv_one, mul_one]
  ·
    obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K
    obtain ⟨g, a, φ, ε, hgaφ⟩ := hNF r
    refine ⟨g, a, φ, fun h => ?_⟩
    rw [hgaφ h, show exactQ Tag.E8 K (ε : ℕ) = 1 from rfl, mul_one, inv_one, mul_one]

theorem entryDegreeBound_lt {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (hG2 : τ = .G2 → p ≠ 3) :
    entryDegreeBound τ < p := by
  have h2 := hp.two_le
  unfold entryDegreeBound
  split_ifs with h
  · have h3 := hG2 h
    have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
    omega
  · omega

theorem exists_cartan_eq_neg_one (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) :
    ∃ i k : Fin τ.rank, τ.cartan i k = -1 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

theorem outerCoreAt_innerDiag_of_five_le
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (hK5 : 5 ≤ Nat.card K) (hG2 : τ = .G2 → ringChar K ≠ 3)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hD : entryDegreeBound τ < ringChar K := by
    rw [hchar]
    exact entryDegreeBound_lt hp2 hp fun h h3 => hG2 h (hchar.trans h3)
  refine outerCoreAt_innerDiag_of_toral hτ hK (fun c hc i₀ hi₀ => ?_) hαg hα
  exact outerCoreAt_toral hτ hK2 hK5 hD (exists_cartan_eq_neg_one hτ) hc hi₀
    fun r hr => exists_normalForm_of_odd hτ hK hG2 r hr

@[expose] def InnerDiagThreeCoreInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 → α ≠ 1 →
      ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), (∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ *
          (g : ModGL τ K)⁻¹) →
      OuterCoreAt α

@[expose] def G2ThreeInnerCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 3 →
    ∀ α : MulAut (adjointGroup Tag.G2 K), α ^ 2 = 1 → α ≠ 1 →
      ∀ (g : adjointGroup Tag.G2 K) (a : Fin Tag.G2.rank → Kˣ), (∀ h : adjointGroup Tag.G2 K,
        (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) * rootDiagUnit Tag.G2 a * h *
          (rootDiagUnit Tag.G2 a)⁻¹ * (g : ModGL Tag.G2 K)⁻¹) →
      OuterCoreAt α

theorem five_le_of_odd {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) (hne : m ≠ 3) : 5 ≤ m := by
  obtain ⟨k, rfl⟩ := hm
  omega

theorem innerDiagCoreInput_of_three
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (h3 : InnerDiagThreeCoreInput τ) :
    InnerDiagCoreInput τ := by
  intro K _ _ hK α hα hα1 g a hαg
  by_cases h3K : Nat.card K = 3
  · exact h3 K h3K α hα hα1 g a hαg
  · have hK3 : 3 ≤ Nat.card K := by
      obtain ⟨p, f, hp, hp2, hf, -, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
      rw [hcard]
      have : 3 ≤ p := by
        have := hp.two_le
        omega
      exact this.trans (Nat.le_self_pow (by omega) p)
    have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := Or.inr hτ
    have hG2 : τ = .G2 → ringChar K ≠ 3 := fun h => by
      rcases hτ with h' | h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
    exact outerCoreAt_innerDiag_of_five_le hτ' hK (five_le_of_odd hK hK3 h3K) hG2 hαg hα

theorem innerDiagCoreInput_G2_of_three
    (h3 : G2ThreeInnerCoreInput) : InnerDiagCoreInput .G2 := by
  intro K _ _ hK α hα hα1 g a hαg
  by_cases h3K : ringChar K = 3
  · exact h3 K h3K α hα hα1 g a hαg
  · obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h3 : p ≠ 3 := fun h => h3K (hchar.trans h)
      have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
      omega
    have hK5 : 5 ≤ Nat.card K := by
      rw [hcard]
      exact hp5.trans (Nat.le_self_pow (by omega) p)
    exact outerCoreAt_innerDiag_of_five_le (Or.inl rfl) hK hK5 (fun _ => h3K) hαg hα

theorem oddLieCoreFamilyInput_F4_of_three
    (h3 : InnerDiagThreeCoreInput .F4) : OddLieCoreFamilyInput .F4 :=
  oddLieCoreFamilyInput_F4 (innerDiagCoreInput_of_three (Or.inl rfl) h3)

theorem oddLieCoreFamilyInput_E8_of_three
    (h3 : InnerDiagThreeCoreInput .E8) : OddLieCoreFamilyInput .E8 :=
  oddLieCoreFamilyInput_E8 (innerDiagCoreInput_of_three (Or.inr (Or.inr rfl)) h3)

theorem oddLieCoreFamilyInput_E6_of_three
    (h3 : InnerDiagThreeCoreInput .E6) (hgr : E6GraphCoreInput) : OddLieCoreFamilyInput .E6 :=
  oddLieCoreFamilyInput_E6 (innerDiagCoreInput_of_three (Or.inr (Or.inl rfl)) h3) hgr

theorem oddLieCoreFamilyInput_G2_of_three
    (h3i : G2ThreeInnerCoreInput) (h3 : G2ThreeOuterCoreInput) : OddLieCoreFamilyInput .G2 :=
  oddLieCoreFamilyInput_G2 (innerDiagCoreInput_G2_of_three h3i) h3

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
