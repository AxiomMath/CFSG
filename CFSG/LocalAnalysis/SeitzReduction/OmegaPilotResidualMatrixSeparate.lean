module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixRecentre
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)

section CharP

theorem false_of_isCharacteristicP_of_normal_simple {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hH : IsCharacteristicP p H) {N : Subgroup H} (hN : N.Normal)
    (hs : IsSimpleGroup ↥N) (hperf : ⁅N, N⁆ = N) : False := by
  have hNbot : N ≠ ⊥ := (N.nontrivial_iff_ne_bot).mp hs.toNontrivial
  have hPn : (CFSG.pCore p H).Normal := CFSG.pCore_normal
  have hPp : IsPGroup p (CFSG.pCore p H) := CFSG.pCore_isPGroup
  have hnorm : ((CFSG.pCore p H).subgroupOf N).Normal := hPn.subgroupOf N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore p H).subgroupOf N) with h | h
  ·
    have hdisj : N ⊓ CFSG.pCore p H = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : N) ∈ (CFSG.pCore p H).subgroupOf N := hx.2
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
    have hcomm : ⁅N, CFSG.pCore p H⁆ = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.commutator_le_inf N (CFSG.pCore p H)).trans hdisj.le)
    have hNC : N ≤ centralizer (CFSG.pCore p H : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hNP : N ≤ CFSG.pCore p H := hNC.trans hH
    apply hNbot
    rw [eq_bot_iff, ← hdisj]
    exact le_inf le_rfl hNP
  ·
    have hNP : N ≤ CFSG.pCore p H := by
      intro x hx
      have hx' : (⟨x, hx⟩ : N) ∈ (CFSG.pCore p H).subgroupOf N := by rw [h]; exact mem_top _
      exact hx'
    have hNp : IsPGroup p N := hPp.to_le hNP
    have : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr hperf
    have : Nontrivial ↥N := (N.nontrivial_iff_ne_bot).mpr hNbot
    exact Group.IsPerfect.not_isNilpotent (G := ↥N) hNp.isNilpotent

end CharP


section FieldOrder

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [CharP K 2] in
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem card_pairDescentDerived (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : (polarBilin Q).Nondegenerate)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hσσ : S.val.right * S.val.right = 1) (hσ1 : S.val.right ≠ 1)
    (hTT : ∀ v, coordinateSemilinearMap S.val (coordinateSemilinearMap S.val v) = v) :
    ∃ τ : CFSG.Assembly.LowTwoRank.StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      Nat.card ↥(pairDescentDerived hS) = F4Pilot.evenLieOrder τ n (f / 2) := by
  obtain ⟨hfeven, hk, -⟩ := card_descentField hf hK hσσ hσ1
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField S.val.right) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hk2 hk
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨τ, Y, _, hτ, -, hlie, ⟨eY⟩⟩ :=
    LinearPilot.exists_lieModel_derivedOrthogonal_tag hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  refine ⟨τ, hτ, ?_⟩
  rw [Nat.card_congr eY.toEquiv]
  exact F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags
    (by rcases hτ with rfl | rfl <;> decide) hlie

end FieldOrder


section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem fieldCore_simple_card_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα2 : α ^ 2 = 1)
    (hfp : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn α ≠ 1) :
    Even f ∧ IsSimpleGroup ↥(perfectCore (autFixSubgroup α)) ∧
      ⁅perfectCore (autFixSubgroup α), perfectCore (autFixSubgroup α)⁆ =
        perfectCore (autFixSubgroup α) ∧
      ∃ τ : CFSG.Assembly.LowTwoRank.StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
        Nat.card ↥(perfectCore (autFixSubgroup α)) = F4Pilot.evenLieOrder τ n (f / 2) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  obtain ⟨S, hS, rfl, hσσ, hσ1, hTT⟩ := exists_fieldPair_plus hK hn hα2 hfp
  have hreg := regular_coordinateQuadPlus n K (by omega)
  obtain ⟨⟨F⟩, hsimple, -, -⟩ := fieldCore_spec hf hK (by omega) hreg.1 hreg.2 hS hσσ hσ1 hTT
  obtain ⟨τ, hτ, hcard⟩ := card_pairDescentDerived hf hK (by omega) hreg.1 hS hσσ hσ1 hTT
  exact ⟨(card_descentField hf hK hσσ hσ1).1, @MulEquiv.isSimpleGroup _ _ _ _ hsimple F,
    perfectCore_perfect _, τ, hτ, (Nat.card_congr F.toEquiv).trans hcard⟩

theorem autFixSubgroup_eq_fixedSubgroup' {P : Type*} [Group P] (β : MulAut P) :
    autFixSubgroup β = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β :=
  Subgroup.ext fun _ => Iff.rfl

theorem commutator_perfectCore_subgroupOf {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ⁅(perfectCore H).subgroupOf H, (perfectCore H).subgroupOf H⁆ =
      (perfectCore H).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (perfectCore_le H), perfectCore_perfect]


open CFSG.Assembly.LowTwoRank (StatedProj StatedSp) in
theorem symmetryCore_spec (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {v : Fin (2 * n) → K} (hv : coordinateQuadPlus n K v = 1) :
    IsSimpleGroup ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) ∧
      ⁅perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)),
        perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))⁆ =
        perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ∧
      Nat.card ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) =
        Nat.card K ^ ((n - 1) ^ 2) * ∏ j ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * j) - 1) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hout : symmetryAut (coordinateQuadPlus n K) v ∉
      inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective _ y
    rw [← kappa_derived_eq_conj] at hy
    have h1 := CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
      hreg.1 hreg.2 hE (a₁ := Subgroup.inclusion (matrixDerived_le_isometries _) g)
      (a₂ := symmetryIsometry _ v) hy
    apply CFSG.ComponentClassification.EvenOrthSelector.symmetryGL_not_mem_matrixDerived
      hreg.1 hreg.2 hE hv
    have h2 : ((Subgroup.inclusion (matrixDerived_le_isometries _) g : matrixIsometries _) :
        GL (Fin (2 * n)) K) = symmetryGL _ v := congrArg Subtype.val h1
    rw [← h2]
    exact g.2
  obtain ⟨ε⟩ := F4Pilot.omega_symmetry_fixed hf hK (by omega) hreg.1 hreg.2 hE hv hout
  obtain ⟨hSs, hSp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (r := n - 1)
    (k := K) (by omega) (by omega)
  have e : ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ≃*
      StatedProj (StatedSp (n - 1) K) :=
    (MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup' _)).trans (ε.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot
          (n - 1))).trans QuotientGroup.quotientBot).symm)
  have hFperf : Group.IsPerfect ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hXβ : perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) =
      autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v) :=
    CFSG.Quasithin.perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hFperf)
  rw [hXβ]
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hSs e, Subgroup.isPerfect_iff.mp hFperf,
    (Nat.card_congr e.toEquiv).trans
      (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (n - 1))⟩

theorem not_isSimpleGroup_core_of_two_le_rank (hn : 5 ≤ n)
    (s : matrixIsometries (coordinateQuadPlus n K))
    (hs2 : orderOf (isometryConjugationHom _ s) = 2)
    (hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank) :
    ¬ IsSimpleGroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  intro hsimple
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hchar :=
    CFSG.ComponentClassification.CatLeafProof.isCharacteristicP_inner_centralizer_of_two_le_rank
      hreg.1 hreg.2 hE s hs2 hr
  have hcj :=
    CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
      hreg.1 hreg.2 hE
  have hchar' := CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (CFSG.ComponentClassification.CatLeafProof.fixedInnerEquiv hcj _).symm hchar
  rw [← autFixSubgroup_eq_fixedSubgroup'] at hchar'
  have hN : ((perfectCore (autFixSubgroup (isometryConjugationHom _ s))).subgroupOf
      (autFixSubgroup (isometryConjugationHom _ s))).Normal :=
    CFSG.Quasithin.perfectCore_normal _
  have hNs : IsSimpleGroup ↥((perfectCore (autFixSubgroup (isometryConjugationHom _ s))).subgroupOf
      (autFixSubgroup (isometryConjugationHom _ s))) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hsimple (Subgroup.subgroupOfEquivOfLe (perfectCore_le _))
  exact false_of_isCharacteristicP_of_normal_simple (p := 2) hchar' hN hNs
    (commutator_perfectCore_subgroupOf _)

theorem nonField_cases (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (hfp : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn α = 1) :
    (∃ v : Fin (2 * n) → K, coordinateQuadPlus n K v = 1 ∧
        α = symmetryAut (coordinateQuadPlus n K) v) ∨
      ∃ s : matrixIsometries (coordinateQuadPlus n K), α = isometryConjugationHom _ s ∧
        orderOf (isometryConjugationHom _ s) = 2 ∧
        2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  obtain ⟨s, rfl⟩ := (orthAutFieldPart_eq_one_iff _ _ α).mp hfp
  have hs2 : orderOf (isometryConjugationHom _ s) = 2 := orderOf_eq_prime hα2 hα1
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · exact Or.inr ⟨s, rfl, hs2, hr⟩
  · left
    have hss : s * s = 1 := by
      apply CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
        hreg.1 hreg.2 hE
      rw [map_mul, map_one]
      change isometryConjugationHom _ s * isometryConjugationHom _ s = 1
      rw [← pow_two]
      exact hα2
    have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
      intro h
      apply hα1
      have : s = 1 := Subtype.ext h
      rw [this, map_one]
    obtain ⟨v, hv, hsv⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.exists_symmetry_of_rank_le_one
        hreg.1 s.2 (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry _ v := Subtype.ext hsv
    subst hincl
    exact ⟨v, hv, rfl⟩

theorem fieldCoresSeparated_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    FieldCoresSeparated (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn) := by
  intro α β hα2 hfpα hβ2 hβ1 hfpβ
  refine ⟨fun ψ => ?_⟩
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  obtain ⟨hfeven, hsimple, -, τ, hτ, hcard⟩ := fieldCore_simple_card_plus hK hn hα2 hfpα
  rcases nonField_cases hK hn hβ2 hβ1 hfpβ with ⟨v, hv, rfl⟩ | ⟨s, rfl, hs2, hr⟩
  · obtain ⟨-, -, hcardβ⟩ := symmetryCore_spec hK hn hv
    have hψcard := Nat.card_congr ψ.toEquiv
    have hk2 : 1 ≤ f / 2 := by
      obtain ⟨m, hm⟩ := hfeven
      omega
    obtain ⟨r, hr_odd, hr_eq⟩ : ∃ r, Odd r ∧
        F4Pilot.evenLieOrder τ n (f / 2) = 2 ^ (f / 2 * (n * (n - 1))) * r := by
      rcases hτ with rfl | rfl
      · exact (F4Pilot.profile_idxD (by omega) hk2).two
      · exact (F4Pilot.profile_idx2D (by omega) hk2).two
    have hP : Odd (∏ j ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * j) - 1)) := by
      rw [hK]
      exact CFSG.Timmesfeld.Orders.odd_prod fun j hj =>
        CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by simp at hj; omega)
    have hpow : Nat.card K ^ ((n - 1) ^ 2) = 2 ^ (f * (n - 1) ^ 2) := by rw [hK, ← pow_mul]
    have key := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr_odd hP (by
      rw [← hr_eq, ← hcard, hψcard, ← hpow]
      exact hcardβ)
    obtain ⟨g, hg⟩ := hfeven
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hg2 : f / 2 = g := by omega
    have hm1 : m + 5 - 1 = m + 4 := by omega
    rw [hg2, hm1, hg] at key
    have hg0 : (0 : ℤ) < g := by
      have : 1 ≤ g := by omega
      exact_mod_cast this
    have key' : (g : ℤ) * ((m + 5) * (m + 4)) = (g + g) * (m + 4) ^ 2 := by exact_mod_cast key
    have hpos : (0 : ℤ) < g * (m + 4) * (m + 3) :=
      mul_pos (mul_pos hg0 (by positivity)) (by positivity)
    nlinarith [key', hpos]
  · exact not_isSimpleGroup_core_of_two_le_rank hn s hs2 hr
      (@MulEquiv.isSimpleGroup _ _ _ _ hsimple ψ.symm)

theorem fieldRecentreIn_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    FieldRecentreIn (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
      (IsLongRoot (coordinateQuadPlus n K)) :=
  fieldRecentreIn_plus_of_separated hK hn (fieldCoresSeparated_plus hK hn)

end Plus

end CFSG.SeitzReduction.OmegaPilot
