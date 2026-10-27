module

public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl2

public section

namespace CFSG.KC.F4Inv

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.SeitzReduction.F4Pilot
  CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41


noncomputable abbrev cenGL (x : F42C) : Subgroup (ModGL ReeTag.F4.tag (ZMod 2)) :=
  (Subgroup.centralizer ({x} : Set F42C)).map (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype

theorem coe_mem_cenGL {x g : F42C} : (g : ModGL ReeTag.F4.tag (ZMod 2)) ∈ cenGL x ↔
    g * x = x * g := by
  rw [← Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, he⟩
    rwa [← Subtype.ext he]
  · exact fun h => ⟨g, h, rfl⟩

theorem card_cenGL (x : F42C) :
    Nat.card (cenGL x) = Nat.card (Subgroup.centralizer ({x} : Set F42C)) :=
  Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem cen_eq_parabolic {x : F42C} (hx : ∀ q ∈ Q₀, q * x = x * q) :
    cenGL x = parabolicSubgroup ReeTag.F4.tag (ZMod 2)
      {i | weylElement ReeTag.F4.tag (ZMod 2) i * x = x * weylElement ReeTag.F4.tag (ZMod 2) i} := by
  have hB : borelGroup ReeTag.F4.tag (ZMod 2) ≤ cenGL x := by
    have hT : torusGroup ReeTag.F4.tag (ZMod 2) = ⊥ :=
      CFSG.StandardType.TableBF4TwoInputs.torusGroup_F4_eq_bot (by simp)
    rw [borelGroup, hT, bot_sup_eq]
    intro p hp
    have hpG := posUnipotent_le_adjointGroup hp
    exact (coe_mem_cenGL (g := ⟨p, hpG⟩)).2 (hx _ hp)
  have h := eq_parabolicSubgroup_of_borelGroup_le hB (Subgroup.map_subtype_le _)
  rw [h]
  congr 1
  ext i
  exact coe_mem_cenGL (g := weylElement ReeTag.F4.tag (ZMod 2) i)

theorem parabolicRadicalRoots_123 :
    parabolicRadicalRoots ReeTag.F4.tag {i | i ≠ 0} =
      {α | IsRoot ReeTag.F4.tag α ∧ (0 < height α ∧ α 0 ≠ 0)} := by
  ext α
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_inter_iff, not_and, not_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun h0 => h3 ⟨h1, fun i hi => by rwa [show i = 0 by simpa using hi]⟩ h1 h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun hh _ _ => h3 (hh.2 0 (by simp))⟩

theorem card_parabolicRadical_123 :
    Nat.card (parabolicRadical ReeTag.F4.tag (ZMod 2) {i | i ≠ 0}) = 2 ^ 15 := by
  rw [card_parabolicRadical, Nat.card_zmod, parabolicRadicalRoots_123,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  decide +kernel

theorem parabolicLevi_123 :
    parabolicLevi ReeTag.F4.tag (ZMod 2) {i | i ≠ 0} = rootSpan .F4 (ZMod 2) c3LeviRoots := by
  refine le_antisymm (CFSG.StandardType.TableBF4TwoInputs.parabolicLevi_le_rootSpan (by simp)
    fun j hj => CFSG.StandardType.F4Rest.single_mem_c3LeviRoots hj) ?_
  refine iSup₂_le fun α hα => ?_
  refine CFSG.ClassicalInvolution.ModelFacts.Levi.rootSubgroup_le_parabolicLevi'
    ⟨hα.1, fun i hi => ?_⟩
  have hi0 : i = 0 := by_contra fun h => hi h
  rw [hi0]
  exact hα.2

theorem card_rootSpan_c3 : Nat.card (rootSpan .F4 (ZMod 2) c3LeviRoots) = 1451520 := by
  have hle : rootSpan .F4 (ZMod 2) c3LeviRoots ≤ adjointGroup .F4 (ZMod 2) :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have e1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have e2 := Nat.card_congr (c3LeviEquiv (ZMod 2)).toEquiv
  rw [← e1]
  change Nat.card (C3Levi (ZMod 2)) = _
  rw [← e2, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem card_parabolic_123 :
    Nat.card (parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0}) = 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  rw [card_parabolicSubgroup_eq_mul, card_parabolicRadical_123, parabolicLevi_123]
  exact (congrArg (fun n => 2 ^ 15 * n) card_rootSpan_c3).trans (by norm_num)

theorem card_parabolic_12_lt :
    Nat.card (parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0 ∧ i ≠ 3}) <
      Nat.card (parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0}) := by
  have hfin : Finite (parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0}) := by
    have : Finite F42C := finite_adjF
    refine Finite.of_injective (fun g => (⟨g.1, parabolicSubgroup_le_adjointGroup _ _ _ g.2⟩ :
      F42C)) ?_
    intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  have hle : parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0 ∧ i ≠ 3} ≤
      parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0} :=
    parabolicSubgroup_le_parabolicSubgroup_iff.2 fun i hi => hi.1
  have hne : ¬ parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0} ≤
      parabolicSubgroup ReeTag.F4.tag (ZMod 2) {i | i ≠ 0 ∧ i ≠ 3} := by
    rw [parabolicSubgroup_le_parabolicSubgroup_iff]
    intro h
    exact (h (show (3 : Fin 4) ≠ 0 by decide)).2 rfl
  exact Subgroup.card_lt_of_lt (lt_of_le_not_ge hle hne)

theorem mem_sylow_of_commute {X : Type*} [Group X] {z : X}
    (hz : ∀ g : X, Commute g z) (hzo : orderOf z = 2) (T : Sylow 2 X) : z ∈ T := by
  have : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hz g).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z k⟩
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, hzo]
  exact hP.le_sylow_of_normal T (Subgroup.mem_zpowers z)

theorem eq_of_card_four {G : Type*} [Finite G] (hG : Nat.card G = 4) {x y z w : G} (h1 : x ≠ y)
    (h2 : x ≠ z) (h3 : x ≠ w) (h4 : y ≠ z) (h5 : y ≠ w) (h6 : z ≠ w) (a : G) :
    a = x ∨ a = y ∨ a = z ∨ a = w := by
  by_contra! h
  obtain ⟨ha1, ha2, ha3, ha4⟩ := h
  have hinj : Function.Injective (![x, y, z, w, a] : Fin 5 → G) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [hG, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem factorization_cen : (2 ^ 24 * 3 ^ 4 * 5 * 7).factorization 2 = 24 := by
  have h : (2 ^ 24 * 3 ^ 4 * 5 * 7 : ℕ) = 2 ^ 24 * 2835 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

set_option maxRecDepth 100000 in
theorem center_Q₀_cases (a : ↥(Subgroup.center ↥Q₀)) :
    (a : ↥Q₀).1 = 1 ∨ (a : ↥Q₀).1 = zA ∨ (a : ↥Q₀).1 = zB' ∨ (a : ↥Q₀).1 = zA * zB' := by
  have : Finite F42C := finite_adjF
  have hval : ∀ x y : ↥(Subgroup.center ↥Q₀), x = y → (x : ↥Q₀).1 = (y : ↥Q₀).1 :=
    fun x y h => by rw [h]
  have hsq : zB' * zB' = 1 := zB'_sq
  have ca : (⟨zA, zA_mem⟩ : ↥Q₀) ∈ Subgroup.center ↥Q₀ :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (by
      change y.1 * zA = zA * y.1
      exact zA_central y.2)
  have cb : (⟨zB', zB'_mem⟩ : ↥Q₀) ∈ Subgroup.center ↥Q₀ :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (by
      change y.1 * zB' = zB' * y.1
      exact zB'_central y.2)
  have h := eq_of_card_four card_center_Q₀ (x := (1 : ↥(Subgroup.center ↥Q₀)))
    (y := ⟨_, ca⟩) (z := ⟨_, cb⟩) (w := ⟨_, mul_mem ca cb⟩) ?_ ?_ ?_ ?_ ?_ ?_ a
  · rcases h with h | h | h | h
    · exact Or.inl (hval _ _ h)
    · exact Or.inr (Or.inl (hval _ _ h))
    · exact Or.inr (Or.inr (Or.inl (hval _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (hval _ _ h)))
  · intro h
    have h1 := hval _ _ h
    exact zA_ne_one h1.symm
  · intro h
    have h1 := hval _ _ h
    exact zB'_ne_one h1.symm
  · intro h
    have h1 := hval _ _ h
    have h'' : (1 : F42C) = zA * zB' := h1
    apply zA_ne_zB'
    calc zA = zA * (zB' * zB') := by rw [hsq, mul_one]
      _ = (zA * zB') * zB' := by rw [mul_assoc]
      _ = 1 * zB' := by rw [← h'']
      _ = zB' := one_mul _
  · intro h
    have h1 := hval _ _ h
    exact zA_ne_zB' h1
  · intro h
    have h1 := hval _ _ h
    have h' : zA = zA * zB' := h1
    exact zB'_ne_one (by simpa using h')
  · intro h
    have h1 := hval _ _ h
    have h' : zB' = zA * zB' := h1
    exact zA_ne_one (by simpa using h'.symm)

theorem conj_center_of_card_cen {v : F42C} (hv : orderOf v = 2)
    (hc : Nat.card (Subgroup.centralizer ({v} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7) :
    IsConj zA v ∨ IsConj zB' v ∨ IsConj (zA * zB') v := by
  have : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({v} : Set F42C)
  obtain ⟨T⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hvT : (⟨v, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ T :=
    mem_sylow_of_commute (fun g => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2))
      ((Subgroup.orderOf_coe _).symm.trans hv) T
  set S := (T : Subgroup C).map C.subtype
  have hS : Nat.card S = 2 ^ 24 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), T.card_eq_multiplicity, hc,
      factorization_cen]
  have hSyl : IsSylowOf 2 S (⊤ : Subgroup F42C) := isSylowOf_of_card_p le_top
    (by rw [hS, Subgroup.card_top, card_F42C, factorization_two_card])
  obtain ⟨k, -, hk⟩ := exists_conjBy_eq_sylowOf hSyl isSylowOf_Q₀
  have hvS : v ∈ S := ⟨_, hvT, rfl⟩
  rw [← hk] at hvS
  obtain ⟨q, hq, hqv⟩ := hvS
  have hqv' : k * q * k⁻¹ = v := hqv
  have hcen : (⟨q, hq⟩ : Q₀) ∈ Subgroup.center Q₀ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hyS : k * y.1 * k⁻¹ ∈ S := by
      rw [← hk]
      exact ⟨y.1, y.2, rfl⟩
    obtain ⟨y', hy', hy'e⟩ := hyS
    have hyC : k * y.1 * k⁻¹ ∈ C := by
      rw [← hy'e]
      exact y'.2
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [← hqv'] at h1
    apply Subtype.ext
    change y.1 * q = q * y.1
    have h2 : k * (y.1 * q) * k⁻¹ = k * (q * y.1) * k⁻¹ := by
      calc k * (y.1 * q) * k⁻¹ = (k * y.1 * k⁻¹) * (k * q * k⁻¹) := by group
        _ = (k * q * k⁻¹) * (k * y.1 * k⁻¹) := h1
        _ = k * (q * y.1) * k⁻¹ := by group
    simpa using h2
  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at hqv'
    rw [← hqv', orderOf_one] at hv
    omega
  rcases center_Q₀_cases ⟨⟨q, hq⟩, hcen⟩ with h | h | h | h
  · exact absurd h hq1
  · exact Or.inl (isConj_iff.2 ⟨k, by rw [← h, hqv']⟩)
  · exact Or.inr (Or.inl (isConj_iff.2 ⟨k, by rw [← h, hqv']⟩))
  · exact Or.inr (Or.inr (isConj_iff.2 ⟨k, by rw [← h, hqv']⟩))

end CFSG.KC.F4Inv

end
