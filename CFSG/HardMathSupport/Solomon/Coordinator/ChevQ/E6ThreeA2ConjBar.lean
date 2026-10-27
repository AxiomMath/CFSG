module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFusion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

theorem ne_three_of_cube_root {K : Type} [Field K] {p : ℕ} [CharP K p] {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : p ≠ 3 := by
  rintro rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : ((ω : K) - 1) ^ 3 = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hω3, Units.val_one, one_pow, sub_self]
  exact hω1 (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)))

section Bar


variable {K : Type} [Field K] [Finite K]

open scoped Classical in
theorem exists_conj_e6Line_bar {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {sL : ModGL .E6 (AlgebraicClosure K)} (hsL : sL ∈ adjointGroup .E6 (AlgebraicClosure K))
    (hsL3 : sL ^ 3 = 1)
    (hdim : Module.finrank (AlgebraicClosure K) (LinearMap.ker ((sL : Module.End
      (AlgebraicClosure K) (RootModule .E6 (AlgebraicClosure K))) - 1)) = 24) :
    ∃ y ∈ adjointGroup .E6 (AlgebraicClosure K), sL = y *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootDiagUnit .E6 (e6LineChar ω)) *
        y⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpn, -⟩ := FiniteField.card K (ringChar K)
  obtain ⟨p, hp⟩ : ∃ p, p = ringChar K := ⟨_, rfl⟩
  rw [← hp] at hpn
  haveI : Fact p.Prime := ⟨hpn⟩
  haveI : CharP K p := hp ▸ ringChar.charP K
  have hp3 : p ≠ 3 := ne_three_of_cube_root hω3 hω1
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hL3 : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) p]
    exact hp3
  have hfin : ((Subgroup.zpowers sL : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
      Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hsL3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers sL, x ^ 3 = 1 := by
    rintro _ ⟨n, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsL3, one_zpow]
  have hzle : Subgroup.zpowers sL ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [Subgroup.zpowers_le]
    exact hsL
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := p) (p := 3) hp3
    (isAlgebraic_zmod_algebraicClosure_of_finite K p) hzle hfin hexp
  have hn := hc₁m sL (Subgroup.mem_zpowers sL)
  have hn3 : (c₁ * sL * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hsL3, mul_one, mul_inv_cancel]
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial
    monomialToralAt_E6_three hL3 hn hn3
  obtain ⟨t, ht⟩ : ∃ t, t = (c₂ * c₁) * sL * (c₂ * c₁)⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * sL * c₁⁻¹) * c₂⁻¹ := by rw [ht]; group
  have htT : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit Tag.E6 a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hsL3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom Tag.E6 (AlgebraicClosure K) (a ^ 3) =
        rootDiagUnitHom Tag.E6 (AlgebraicClosure K) 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit Tag.E6 a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := Tag.E6)
      (K := AlgebraicClosure K) h1
    intro i
    have := congrFun h2 i
    simpa using this
  choose m hm using fun i => exists_eq_map_pow_of_pow_three
    (algebraMap K (AlgebraicClosure K)) hω (ha3 i)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin Tag.E6.rank → ZMod 3, x₀ = fun i => (m i : ZMod 3) := ⟨_, rfl⟩
  have hax : (fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
      (torV ω x₀ i)) = a := by
    funext i
    rw [hm i, torV, hx₀, ZMod.val_natCast]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (m i) 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  have hdimt : Module.finrank (AlgebraicClosure K)
      (LinearMap.ker ((rootDiag a : Module.End (AlgebraicClosure K) (RootModule Tag.E6
        (AlgebraicClosure K))) - 1)) = 24 := by
    have h := finrank_ker_conj_sub_one (c₂ * c₁) sL
    rw [← ht] at h
    rw [← hdim, ← h, hta]
    rfl
  have hcardL : ((rootFinset .E6).filter fun α => rootChar a α = 1).card = 18 := by
    have h := finrank_ker_rootDiag_sub_one_card a
    rw [hdimt] at h
    change 24 = 6 + _ at h
    omega
  have hx18 : ((rootFinset .E6).filter fun α => rootChar (torV ω x₀) α = 1).card = 18 := by
    rw [← hcardL]
    refine congrArg Finset.card (Finset.filter_congr fun α _ => ?_)
    rw [← hax, rootChar_map_tuple]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact Units.map_injective (f := (algebraMap K (AlgebraicClosure K)).toMonoidHom)
        (algebraMap K (AlgebraicClosure K)).injective (h.trans (map_one _).symm)
  obtain ⟨w, hw⟩ := exists_weylTuple_eq_e6LineChar hω3 hω1 x₀ hx18
  obtain ⟨nw, hnw⟩ : ∃ nw, nw = canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w :=
    ⟨_, rfl⟩
  have hnwG : nw ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    hnw ▸ canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) _ w
  have hwa : weylTuple w a = fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
      (e6LineChar ω i) := by
    funext i
    rw [← hax, ← hw]
    simp only [weylTuple]
    rw [rootChar_map_tuple]
  have hnt : nw * t * nw⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      (rootDiagUnit Tag.E6 (e6LineChar ω)) := by
    rw [baseChangeGL_rootDiagUnit, hnw, hta, canonicalRep_conj_rootDiagUnit, hwa]
  obtain ⟨y, hy⟩ : ∃ y, y = (nw * (c₂ * c₁))⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    hy ▸ inv_mem (mul_mem hnwG (mul_mem hc₂ hc₁))
  refine ⟨y, hyG, ?_⟩
  rw [← hnt, hy, ht]
  group

end Bar

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
