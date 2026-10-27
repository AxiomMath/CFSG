module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedUnipotent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

theorem two_eq_zero_of_card_four (hK : Nat.card K = 4) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h4 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h4
  have h22 : (2 : K) * 2 = 0 := by
    have : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [← this]
    exact h4
  exact mul_self_eq_zero.1 h22

theorem charP_two_of_card_four (hK : Nat.card K = 4) : CharP K 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast two_eq_zero_of_card_four hK)

theorem exists_eq_map_pow_of_pow_three {L : Type} [Field L] (ι : K →+* L)
    {ω : Kˣ} (hω : orderOf ω = 3) {v : Lˣ} (hv : v ^ 3 = 1) :
    ∃ m : ℕ, v = Units.map ι.toMonoidHom (ω ^ m) := by
  set w : L := ι (ω : K) with hw
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow, ← Units.val_pow_eq_pow_val, hω3, Units.val_one, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply hω1
    apply Units.ext
    apply ι.injective
    rw [← hw, h, Units.val_one, map_one]
  have hsum : w ^ 2 + w + 1 = 0 := by
    have h1 : (w - 1) * (w ^ 2 + w + 1) = 0 := by
      have : (w - 1) * (w ^ 2 + w + 1) = w ^ 3 - 1 := by ring
      rw [this, hw3, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hw1)
  have hv3 : (v : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hv, Units.val_one]
  have hprod : ((v : L) - 1) * ((v : L) - w) * ((v : L) - w ^ 2) = 0 := by
    have : ((v : L) - 1) * ((v : L) - w) * ((v : L) - w ^ 2) =
        (v : L) ^ 3 - (w ^ 2 + w + 1) * (v : L) ^ 2 + (w ^ 2 + w + 1) * w * (v : L) -
          w ^ 3 := by ring
    rw [this, hsum, hw3, hv3]
    ring
  have key : ∀ m : ℕ, (Units.map ι.toMonoidHom (ω ^ m) : L) = w ^ m := by
    intro m
    simp [hw]
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · refine ⟨0, Units.ext ?_⟩
      rw [key, pow_zero]
      exact sub_eq_zero.1 h
    · refine ⟨1, Units.ext ?_⟩
      rw [key, pow_one]
      exact sub_eq_zero.1 h
  · refine ⟨2, Units.ext ?_⟩
    rw [key]
    exact sub_eq_zero.1 h

section Fusion

variable {τ : Tag}

theorem exists_conj_dV_of_pow_three (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    (hmon : MonomialToralAt τ 3)
    (hLang : ∀ [CharP (AlgebraicClosure K) 2] (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      (∀ i, a i ^ 3 = 1) → ∀ c ∈ toralCentralizer τ (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer τ (AlgebraicClosure K) a,
          z⁻¹ * entrywiseFrobGL τ (AlgebraicClosure K) 2 2 z = c)
    (hdesc : ∀ [CharP (AlgebraicClosure K) 2] (y : ModGL τ (AlgebraicClosure K)),
      y ∈ adjointGroup τ (AlgebraicClosure K) →
      entrywiseFrobGL τ (AlgebraicClosure K) 2 2 y = y →
        y ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {s : ModGL τ K} (hs : s ∈ adjointGroup τ K) (hs3 : s ^ 3 = 1) :
    ∃ c ∈ adjointGroup τ K, ∃ x : Fin τ.rank → ZMod 3, c * s * c⁻¹ = dV ω x := by
  have : CharP K 2 := charP_two_of_card_four hK
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι := algebraMap K L
  set sL := baseChangeGL ι s with hsL
  have hsLG : sL ∈ adjointGroup τ L := CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι hs
  have hsL3 : sL ^ 3 = 1 := by rw [hsL, ← map_pow, hs3, map_one]
  have hfin : ((Subgroup.zpowers sL : Subgroup (ModGL τ L)) : Set (ModGL τ L)).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hsL3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers sL, x ^ 3 = 1 := by
    rintro _ ⟨n, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsL3, one_zpow]
  have hzle : Subgroup.zpowers sL ≤ adjointGroup τ L := by
    rw [Subgroup.zpowers_le]
    exact hsLG
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := 2) (p := 3)
    (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hzle hfin hexp
  have hn := hc₁m sL (Subgroup.mem_zpowers sL)
  have hn3 : (c₁ * sL * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hsL3, mul_one, mul_inv_cancel]
  have hL3 : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hL3 hn hn3
  set h := c₂ * c₁ with hh
  set t := h * sL * h⁻¹ with ht
  have ht' : t = c₂ * (c₁ * sL * c₁⁻¹) * c₂⁻¹ := by rw [ht, hh]; group
  have htT : t ∈ torusGroup τ L := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit τ a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hsL3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom τ L (a ^ 3) = rootDiagUnitHom τ L 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit τ a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := rootDiagUnit_injective (τ := τ) (K := L) h1
    intro i
    have := congrFun h2 i
    simpa using this
  set F := entrywiseFrobGL τ L 2 2 with hF
  have hFr : ∀ c : L, iterateFrobenius L 2 2 c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
    norm_num
  have hFs : F sL = sL := units_map_entrywiseHom_baseChangeGL_algebraMap _ hFr s
  have hFt : F t = t := by
    rw [hta, hF, entrywiseFrobGL_rootDiagUnit_pow 2 2 a, ← hta]
    have : t ^ 2 ^ 2 = t ^ 3 * t := by rw [← pow_succ]; norm_num
    rw [this, ht3, one_mul]
  obtain ⟨y, hy⟩ : ∃ y, y = h⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ adjointGroup τ L := hy ▸ inv_mem (mul_mem hc₂ hc₁)
  have hsy : sL = y * t * y⁻¹ := by rw [ht, hy]; group
  have hFsy : F y * t * (F y)⁻¹ = sL := by
    have := congrArg F hsy
    rw [map_mul, map_mul, map_inv, hFt, hFs] at this
    exact this.symm
  have h1 : F y * t * (F y)⁻¹ = y * t * y⁻¹ := hFsy.trans hsy
  have hcc : y⁻¹ * F y ∈ toralCentralizer τ L a := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem hyG) (entrywiseFrobGL_mem 2 2 hyG), ?_⟩
    have h2 : (y⁻¹ * F y) * t = t * (y⁻¹ * F y) := by
      calc (y⁻¹ * F y) * t = y⁻¹ * (F y * t * (F y)⁻¹) * y * (y⁻¹ * F y) := by group
        _ = y⁻¹ * (y * t * y⁻¹) * y * (y⁻¹ * F y) := by rw [h1]
        _ = t * (y⁻¹ * F y) := by group
    rw [← hta]
    calc t * (y⁻¹ * F y) * t⁻¹ = (y⁻¹ * F y) * t * t⁻¹ := by rw [h2]
      _ = y⁻¹ * F y := by group
  obtain ⟨z, hz, hzc⟩ := hLang a ha3 _ hcc
  have hzc' : z⁻¹ * F z = y⁻¹ * F y := hzc
  obtain ⟨hzG, hzt⟩ := mem_toralCentralizer.1 hz
  obtain ⟨u, hu⟩ : ∃ u, u = y * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (y⁻¹ * F y) := by rw [← hzc']; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem hyG (inv_mem hzG)
  have hut : u * t * u⁻¹ = sL := by
    have hzt' : z * t = t * z := by
      have h3 : t * z * t⁻¹ = z := by rw [hta]; exact hzt
      calc z * t = (t * z * t⁻¹) * t := by rw [h3]
        _ = t * z := by group
    rw [hsy, hu]
    calc y * z⁻¹ * t * (y * z⁻¹)⁻¹ = y * (z⁻¹ * (t * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * t)) * y⁻¹ := by rw [hzt']
      _ = y * t * y⁻¹ := by group
  obtain ⟨u', hu'G, hu'⟩ := hdesc u huG hFu
  choose m hm using fun i => exists_eq_map_pow_of_pow_three ι hω (ha3 i)
  set x : Fin τ.rank → ZMod 3 := fun i => (m i : ZMod 3) with hx
  have hax : (fun i => Units.map ι.toMonoidHom (torV ω x i)) = a := by
    funext i
    rw [hm i, torV, hx, ZMod.val_natCast]
    have h3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (m i) 3]
    rw [pow_add, pow_mul, h3, one_pow, mul_one]
  have htx : t = baseChangeGL ι (dV ω x) := by
    rw [dV, baseChangeGL_rootDiagUnit, hax, hta]
  refine ⟨u'⁻¹, inv_mem hu'G, x, baseChangeGL_injective (τ := τ) ι ?_⟩
  rw [map_mul, map_mul, map_inv, inv_inv, hu', ← hsL, ← htx, ← hut]
  group

theorem exists_conj_dV_F4 (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {s : ModGL Tag.F4 K} (hs : s ∈ adjointGroup Tag.F4 K) (hs3 : s ^ 3 = 1) :
    ∃ c ∈ adjointGroup Tag.F4 K, ∃ x : Fin Tag.F4.rank → ZMod 3, c * s * c⁻¹ = dV ω x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_conj_dV_of_pow_three hK hω (monomialToralAt_three_of_block a2BlockToral_F4)
    (fun a ha3 c hc => ?_) (fun y hy hFy => ?_) hs hs3
  · obtain ⟨z, hz, hzc⟩ := toral_centralizer_Lang_F4_three 2 (AlgebraicClosure K) (by norm_num) a
      ha3 2 (by norm_num) (one_mem _) (s := 1) (by norm_num) (by simp) c hc
    refine ⟨z, hz, ?_⟩
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc
    exact hzc
  · have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 2 c =
        c ^ Nat.card K := fun c => by
      rw [iterateFrobenius_def, hK]
      norm_num
    have h := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4
      (Or.inr rfl) K (AlgebraicClosure K) _ hFr).1
    rw [← h]
    exact ⟨hy, hFy⟩

theorem exists_conj_dV_E8
    (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {s : ModGL Tag.E8 K} (hs : s ∈ adjointGroup Tag.E8 K) (hs3 : s ^ 3 = 1) :
    ∃ c ∈ adjointGroup Tag.E8 K, ∃ x : Fin Tag.E8.rank → ZMod 3, c * s * c⁻¹ = dV ω x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_conj_dV_of_pow_three hK hω (monomialToralAt_three_of_block a2BlockToral_E8)
    (fun a ha3 c hc => ?_) (fun y hy hFy => ?_) hs hs3
  · obtain ⟨z, hz, hzc⟩ := toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K) (by norm_num) a
      ha3 2 (by norm_num) (one_mem _) (s := 1) (by norm_num) (by simp) c hc
    refine ⟨z, hz, ?_⟩
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc
    exact hzc
  · have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 2 c =
        c ^ Nat.card K := fun c => by
      rw [iterateFrobenius_def, hK]
      norm_num
    have hfinF := CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum.finite_entrywise_fixed
      (τ := Tag.E8) (k := AlgebraicClosure K) (p₀ := 2) (N := 2) (by norm_num)
    have hsub : ((Subgroup.zpowers y : Subgroup (ModGL Tag.E8 (AlgebraicClosure K))) :
        Set (ModGL Tag.E8 (AlgebraicClosure K))) ⊆
        {g : ModGL Tag.E8 (AlgebraicClosure K) |
          Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 2)) g = g} := by
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [map_zpow]
      exact congrArg (· ^ n) hFy
    have : Finite (Subgroup.zpowers y) := (hfinF.subset hsub).to_subtype
    have hdesc := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (K := K) 1
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) _ hFr (Subgroup.zpowers y)
      (by rw [Subgroup.zpowers_le]; exact hy) (by
        rintro _ ⟨n, rfl⟩
        simp only
        rw [map_zpow]
        exact congrArg (· ^ n) hFy)).1
    have hle := Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 hdesc)
    exact hle (Subgroup.mem_zpowers y)

end Fusion

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
