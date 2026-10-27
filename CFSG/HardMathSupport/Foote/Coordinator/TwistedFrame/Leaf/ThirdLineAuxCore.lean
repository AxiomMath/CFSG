module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false

section Arith

variable {p : ℕ} [Fact p.Prime]

theorem phi6_of_orderOf {x : ZMod p} (h : orderOf x = 6) : x ^ 2 - x + 1 = 0 := by
  have h6 : x ^ 6 = 1 := h ▸ pow_orderOf_eq_one x
  have hne : ∀ k : ℕ, ¬ 6 ∣ k → x ^ k ≠ 1 := fun k hk hx =>
    hk (h ▸ orderOf_dvd_of_pow_eq_one hx)
  have h1 : x - 1 ≠ 0 := fun hx => hne 1 (by norm_num) (by rw [pow_one]; exact sub_eq_zero.1 hx)
  have h2 : x + 1 ≠ 0 := fun hx => hne 2 (by norm_num) (by linear_combination (x - 1) * hx)
  have h3 : x ^ 2 + x + 1 ≠ 0 := fun hx => hne 3 (by norm_num) (by
    linear_combination (x - 1) * hx)
  have hprod : (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1) = 0 := by
    linear_combination h6
  rcases mul_eq_zero.1 hprod with ha | ha
  · rcases mul_eq_zero.1 ha with hb | hb
    · rcases mul_eq_zero.1 hb with hc | hc
      · exact absurd hc h1
      · exact absurd hc h2
    · exact absurd hb h3
  · exact ha

theorem phi10_of_orderOf {x : ZMod p} (h : orderOf x = 10) :
    (-x) ^ 4 + (-x) ^ 3 + (-x) ^ 2 + (-x) + 1 = 0 := by
  have h10 : x ^ 10 = 1 := h ▸ pow_orderOf_eq_one x
  have hne : ∀ k : ℕ, ¬ 10 ∣ k → x ^ k ≠ 1 := fun k hk hx =>
    hk (h ▸ orderOf_dvd_of_pow_eq_one hx)
  have h5 : x ^ 5 - 1 ≠ 0 := fun hx => hne 5 (by norm_num) (sub_eq_zero.1 hx)
  have h5' : x ^ 5 + 1 = 0 := by
    have : (x ^ 5 - 1) * (x ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 this with ha | ha
    · exact absurd ha h5
    · exact ha
  obtain ⟨y, hy⟩ : ∃ y : ZMod p, -x = y := ⟨-x, rfl⟩
  rw [hy]
  have hxy : x + y = 0 := by rw [← hy]; exact add_neg_cancel x
  have hy1 : y - 1 ≠ 0 := fun hy' => hne 2 (by norm_num) (by
    have hx1 : x + 1 = 0 := by linear_combination hxy - hy'
    linear_combination (x - 1) * hx1)
  have h' : (y - 1) * (y ^ 4 + y ^ 3 + y ^ 2 + y + 1) = 0 := by
    linear_combination (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) * hxy - h5'
  rcases mul_eq_zero.1 h' with ha | ha
  · exact absurd ha hy1
  · exact ha

theorem phi12_of_orderOf {x : ZMod p} (h : orderOf x = 12) : x ^ 4 - x ^ 2 + 1 = 0 := by
  have h12 : x ^ 12 = 1 := h ▸ pow_orderOf_eq_one x
  have hne : ∀ k : ℕ, ¬ 12 ∣ k → x ^ k ≠ 1 := fun k hk hx =>
    hk (h ▸ orderOf_dvd_of_pow_eq_one hx)
  have h6 : x ^ 6 + 1 = 0 := by
    have : (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by linear_combination h12
    rcases mul_eq_zero.1 this with ha | ha
    · exact absurd (sub_eq_zero.1 ha) (hne 6 (by norm_num))
    · exact ha
  have h2 : x ^ 2 + 1 ≠ 0 := fun hx => hne 4 (by norm_num) (by
    linear_combination (x ^ 2 - 1) * hx)
  have : (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.1 this with ha | ha
  · exact absurd ha h2
  · exact ha

end Arith


theorem card_rootFinset_F4 : (rootFinset .F4).card = 48 := by
  rw [card_rootFinset]
  rfl

theorem card_rootFinset_E6 : (rootFinset .E6).card = 72 := by
  rw [card_rootFinset]
  rfl

theorem card_rootFinset_E8 : (rootFinset .E8).card = 240 := by
  rw [card_rootFinset]
  rfl

theorem exists_ne_one_ker {A : Type*} [Group A] [Finite A] {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ 2) (χ : A →* Lˣ) (hχ : ∀ a, χ a ^ p = 1) :
    ∃ a : A, a ≠ 1 ∧ χ a = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective χ := (injective_iff_map_eq_one χ).2 fun a ha => by
    by_contra hne
    exact hcon a hne ha
  have hle : Nat.card A ≤ Nat.card (rootsOfUnity p L) :=
    Nat.card_le_card_of_injective (fun a => (⟨χ a, (mem_rootsOfUnity p (χ a)).2 (hχ a)⟩ :
      rootsOfUnity p L)) fun a b hab => hinj (congrArg Subtype.val hab)
  have h2 := card_rootsOfUnity L p
  have hp2 := hp.two_le
  rw [hA] at hle
  nlinarith

theorem not_isSolvable_of_quasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  obtain ⟨hperf, -, a, b, hab⟩ := h
  have : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hs : ∀ u v : G ⧸ Subgroup.center G, u = v := fun u v => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      rw [Subsingleton.elim x y]
    exact hab (hs _ _)
  exact Group.IsPerfect.not_isSolvable G

theorem not_isSolvable_of_embedding {D G : Type*} [Group D] [Group G] (ψ : D →* G)
    (hψ : Function.Injective ψ) {P : Subgroup G} (hP : CFSG.IsQuasisimple ↥P)
    (hle : P ≤ ψ.range) : ¬ Group.IsSolvable D := by
  intro hD
  have hr : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_surjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hP' : Group.IsSolvable ↥P :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact not_isSolvable_of_quasisimple hP hP'

theorem twThirdLine_of_kernel {τ : Tag} {K : Type} [Field K] [Finite K] {L : Type} [Field L]
    [Algebra K L] (Φ : ModGL τ L →* ModGL τ L) (n g0 : ModGL τ L) {p : ℕ} (hp : p.Prime)
    (hconj : ∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q →
      ∃ c : adjointGroup τ K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb τ K L (c * y * c⁻¹) * g0 ∈ twistedTorusOf n Φ)
    (B : ℕ) (hB : 2 * B < (rootFinset τ).card)
    (hbound : ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ twistedTorusOf n Φ →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (rootCharKernel b).ncard ≤ B)
    (hperx : ∀ (x c : adjointGroup τ K) (b : Fin τ.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ →
      rootDiagUnit τ b = g0⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)))) :
    TwThirdLine τ K p := by
  classical
  intro E hEc hEp a b haE hbE ha1 hb1
  have : Fact p.Prime := ⟨hp⟩
  have hinj0 : Function.Injective (rootDiagUnitHom τ L) := rootDiagUnit_injective
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact (pow_pos hp.pos 2).ne')
  obtain ⟨c, hc⟩ := hconj E (IsPGroup.of_card hEc)
  let φ : E →* ModGL τ L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb τ K L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ x : E, φ x =
      g0⁻¹ * adjEmb τ K L (c * (x : adjointGroup τ K) * c⁻¹) * g0 := fun x => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ :=
    (MulAut.conj g0⁻¹).injective.comp (adjEmb_injective.comp
      ((MulAut.conj c).injective.comp E.subtype_injective))
  have hφT : ∀ x : E, φ x ∈ twistedTorusOf n Φ := fun x => by
    rw [hφ]
    exact hc x x.2
  choose β hβ using fun x : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT x)).1 :
      ∃ b : Fin τ.rank → Lˣ, φ x = rootDiagUnit τ b)
  have hβmul : ∀ x y : E, β (x * y) = β x * β y := fun x y => by
    apply rootDiagUnit_injective (τ := τ) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := τ) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  let βh : E →* (Fin τ.rank → Lˣ) :=
    { toFun := β, map_one' := hβone, map_mul' := hβmul }
  have hβinj : Function.Injective β := fun x y h => hφinj (by rw [hβ, hβ, h])
  have hβT : ∀ x : E, rootDiagUnit τ (β x) ∈ twistedTorusOf n Φ := fun x => by
    rw [← hβ]
    exact hφT x
  have hxp : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hEp x x.2)
  have hβp : ∀ x : E, ∀ i, β x i ^ p = 1 := fun x i => by
    have h : β x ^ p = 1 := by
      have h0 : βh (x ^ p) = βh x ^ p := map_pow βh x p
      rw [hxp, map_one] at h0
      exact h0.symm
    simpa using congrFun h i
  let χ : (Fin τ.rank → ℤ) → (E →* Lˣ) := fun α =>
    { toFun := fun x => rootChar (β x) α
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α
      map_mul' := fun x y => by rw [hβmul, CTTorus.rootChar_mul] }
  have hχ : ∀ α (x : E), χ α x = rootChar (β x) α := fun _ _ => rfl
  have hχp : ∀ α (x : E), χ α x ^ p = 1 := fun α x => CTTorus.rootChar_pow_eq_one (hβp x) α
  have hker : ∀ α, ∃ x : E, x ≠ 1 ∧ χ α x = 1 := fun α =>
    exists_ne_one_ker hp hEc (χ α) (hχp α)
  have hpow : ∀ (g x : E), x ≠ 1 → x ∈ Subgroup.zpowers g → ∀ α, χ α x = 1 → χ α g = 1 := by
    intro g x hx1 hxg α hα
    obtain ⟨k, rfl⟩ := hxg
    by_contra hne
    have hord' : orderOf (χ α g) = p := orderOf_eq_prime (hχp α g) hne
    have hk : χ α g ^ k = 1 := by rw [← map_zpow]; exact hα
    have hpk : (p : ℤ) ∣ k := by
      rw [← hord']
      exact orderOf_dvd_iff_zpow_eq_one.2 hk
    obtain ⟨m, hm⟩ := hpk
    apply hx1
    show g ^ k = 1
    rw [hm, _root_.zpow_mul, zpow_natCast, hxp, _root_.one_zpow]
  have hsmall : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).ncard ≤ B := by
    intro x hx1
    have hβ1 : β x ≠ 1 := fun h => hx1 (hβinj (by rw [h, hβone]))
    exact hbound (β x) (hβT x) (hβp x) hβ1
  have hfinK : ∀ x : E, (rootCharKernel (β x)).Finite := by
    intro x
    have hsub : rootCharKernel (β x) ⊆ ↑(rootFinset τ) := fun α hα => mem_rootFinset.2 hα.1
    exact (rootFinset τ).finite_toSet.subset hsub
  set a' : E := ⟨a, haE⟩ with ha'
  set b' : E := ⟨b, hbE⟩ with hb'
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hoff : ∃ α, IsRoot τ α ∧ ∃ x : E, x ≠ 1 ∧ χ α x = 1 ∧ x ∉ Subgroup.zpowers a' ∧
      x ∉ Subgroup.zpowers b' := by
    by_contra hcon
    push Not at hcon
    have hcover : (↑(rootFinset τ) : Set (Fin τ.rank → ℤ)) ⊆
        rootCharKernel (β a') ∪ rootCharKernel (β b') := by
      intro α hα
      have hα' : IsRoot τ α := mem_rootFinset.1 hα
      obtain ⟨x, hx1, hxα⟩ := hker α
      by_cases hxa : x ∈ Subgroup.zpowers a'
      · exact Or.inl ⟨hα', hpow a' x hx1 hxa α hxα⟩
      · exact Or.inr ⟨hα', hpow b' x hx1 (hcon α hα' x hx1 hxα hxa) α hxα⟩
    have hle := Set.ncard_le_ncard hcover ((hfinK a').union (hfinK b'))
    have hun := Set.ncard_union_le (rootCharKernel (β a')) (rootCharKernel (β b'))
    have h1 := hsmall a' ha'1
    have h2 := hsmall b' hb'1
    rw [Set.ncard_coe_finset] at hle
    omega
  obtain ⟨α, hαr, x, hx1, hxα, hxa, hxb⟩ := hoff
  set e : adjointGroup τ K := (x : adjointGroup τ K) with hedef
  have he1 : e ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hep : e ^ p = 1 := hEp e x.2
  have he : orderOf e = p := orderOf_eq_prime hep he1
  have hh : g0⁻¹ * adjEmb τ K L (c * e * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ x]
    exact hφT x
  have hb : rootDiagUnit τ (β x) = g0⁻¹ * adjEmb τ K L (c * e * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  refine ⟨e, x.2, fun h => hxa ?_, fun h => hxb ?_,
    Subgroup.centralizer ({e} : Set (adjointGroup τ K)), le_rfl, ?_⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · exact hperx e c (β x) he hh hb ⟨α, hαr, hxα⟩

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_char_pow (K : Type) [Field K] [Finite K] :
    ∃ (ℓ f : ℕ) (_ : Fact ℓ.Prime) (_ : CharP K ℓ), 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hprime : ℓ.Prime := CharP.char_is_prime K ℓ
  haveI : Fact ℓ.Prime := ⟨hprime⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  refine ⟨ℓ, (n : ℕ), inferInstance, hℓ, n.pos, ?_⟩
  rw [Nat.card_eq_fintype_card, hn]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
