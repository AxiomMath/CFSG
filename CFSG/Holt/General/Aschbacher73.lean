module

public import CFSG.Holt.General.Aschbacher73ZStar
public import CFSG.Holt.General.Basic
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Holt.General

open MulAction CFSG.Open CFSG.BenderSuzuki CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity
open CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1


variable {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] {Q : Subgroup G} {α : Ω}

theorem fusionStronglyEmbedded_stabilizer_subgroupOf_closure
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G)) {z : G} (hzQ : z ∈ Q)
    (hz : orderOf z = 2) {g : G} (hg : g • α ≠ α) :
    fusionStronglyEmbedded
      ((stabilizer G α).subgroupOf (Subgroup.closure (involutionConjugates Q))) := by
  have hN := isNormalSet_involutionConjugates Q
  have hnp := noPolar_involutionConjugates hQα hQN
  have hzα := hQα z hzQ hz
  set D := involutionConjugates Q
  set L := Subgroup.closure D
  set DL : Set L := ((↑) : L → G) ⁻¹' D
  have hNL : IsNormalSet DL := by
    intro x y hy
    change ((x * y * x⁻¹ : L) : G) ∈ D
    simpa using hN x y hy
  have hDL2 : IsInvolutionSet DL := by
    intro x hx
    rw [← Subgroup.orderOf_coe]
    exact hx.1
  have hnpL : Moufang.NoPolar DL := by
    intro x hx y hy hxy hne
    change ((x * y : L) : G) ∈ D
    exact hnp x hx y hy (hxy.map L.subtype) (fun h => hne (Subtype.ext h))
  have hzD : z ∈ D := mem_involutionConjugates_of_mem hzQ hz
  have hgzD : g * z * g⁻¹ ∈ D := hN g z hzD
  have hzL : z ∈ L := Subgroup.subset_closure hzD
  have hgzL : g * z * g⁻¹ ∈ L := Subgroup.subset_closure hgzD
  have hdiscL : Disconnected DL := ⟨⟨z, hzL⟩, hzD, ⟨_, hgzL⟩, hgzD,
    fun h => not_reach_conj hQα hzQ hz hg (reach_of_reach_preimage L h)⟩
  have hSE := asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput L DL hNL hDL2
    Subgroup.closure_closure_coe_preimage hnpL hdiscL ⟨z, hzL⟩ hzD
  refine CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded.of_le
    ((fusionStronglyEmbedded_iff _).2 hSE) ?_ ?_
  · intro x hx
    have h1 := smul_eq_iff_of_reach hQα hzα (reach_of_reach_preimage L hx)
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_iff]
    exact (h1 _).mp ((conj_smul_eq_self_iff hzα (x : G) _).mpr rfl)
  · intro htop
    have hmem : (⟨g * z * g⁻¹, hgzL⟩ : L) ∈ (stabilizer G α).subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_iff] at hmem
    exact hg ((conj_smul_eq_self_iff hzα g α).mp hmem).symm

theorem fusionStronglyEmbedded_stabilizer_subgroupOf_normalClosure
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G)) {z : G} (hzQ : z ∈ Q)
    (hz : orderOf z = 2) {g : G} (hg : g • α ≠ α) :
    fusionStronglyEmbedded ((stabilizer G α).subgroupOf (Subgroup.normalClosure {z})) := by
  rw [← closure_involutionConjugates_eq hQα hQN hzQ hz hg]
  exact fusionStronglyEmbedded_stabilizer_subgroupOf_closure hQα hQN hzQ hz hg

theorem aschbacher73_theorem2_of_commute [IsPretransitive G Ω] [FaithfulSMul G Ω]
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G)) {z : G} (hzQ : z ∈ Q)
    (hz : orderOf z = 2) {g : G} (hne : g * z * g⁻¹ ≠ z) (hcomm : Commute z (g * z * g⁻¹)) :
    fusionIsBenderGroup (Subgroup.normalClosure ({z} : Set G)) ∧
      IsPretransitive (Subgroup.normalClosure ({z} : Set G)) Ω ∧
      IsBorelSubgroup ((stabilizer G α).subgroupOf (Subgroup.normalClosure ({z} : Set G))) := by
  have : Finite Ω := Finite.of_surjective (fun h : G => h • α) fun ω => exists_smul_eq G α ω
  have hzα := hQα z hzQ hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by decide)
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, z • ω ≠ ω := by
    by_contra h
    push Not at h
    exact hz1 (eq_of_smul_eq_smul fun ω => by rw [h ω, one_smul])
  obtain ⟨k, hk⟩ := exists_smul_eq G α ω
  have hkα : k • α ≠ α := by
    rw [hk]
    intro h
    exact hω (by rw [h]; exact (hzα α).mpr rfl)
  set L := Subgroup.normalClosure ({z} : Set G)
  have hLn : L.Normal := Subgroup.normalClosure_normal
  have hzL : z ∈ L := Subgroup.subset_normalClosure rfl
  have hgzL : g * z * g⁻¹ ∈ L := hLn.conj_mem z hzL g
  have hSE := fusionStronglyEmbedded_stabilizer_subgroupOf_normalClosure hQα hQN hzQ hz hkα
  set M := (stabilizer G α).subgroupOf L
  have hrank : TwoRankAtLeastTwo L := by
    refine twoRankAtLeastTwo_of_commute (a := (⟨z, hzL⟩ : L)) (b := ⟨_, hgzL⟩)
      (Subtype.ext hzz) (Subtype.ext ?_) (Subtype.ext hcomm.eq)
      (fun h => hz1 (congrArg Subtype.val h)) (fun h => ?_)
      (fun h => hne (congrArg Subtype.val h).symm)
    · change g * z * g⁻¹ * (g * z * g⁻¹) = 1
      rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz, mul_one,
        mul_inv_cancel]
    · have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
      exact hz1 (by rw [show z = g⁻¹ * (g * z * g⁻¹) * g by group, h', mul_one, inv_mul_cancel])
  rcases theorem_SE M hSE.to_native with hlow | hB
  · exact absurd (twoRankAtLeastTwo_involutionCore_iff.mpr hrank) hlow
  obtain ⟨hBender, hOle, hBorel⟩ := hB
  have hcore : involutionCore L = ⊤ := involutionCore_normalClosure_eq_top hz
  set K := involutionCore L
  let e : K ≃* L := (MulEquiv.subgroupCongr hcore).trans Subgroup.topEquiv
  have hmap : (twoPrimeCore K).map e.toMonoidHom = twoPrimeCore L := by
    simpa only [twoPrimeCore] using CFSG.pPrimeCore_map_iso 2 e
  have hOM : twoPrimeCore L ≤ M := by
    rw [← hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_inf.mp (hOle ⟨x, hx, rfl⟩)).1
  have hO : twoPrimeCore L = ⊥ := by
    have : (twoPrimeCore L).Characteristic := by
      simpa [twoPrimeCore] using CFSG.pPrimeCore_characteristic (p := 2) (G := L)
    have hYn : ((twoPrimeCore L).map L.subtype).Normal := inferInstance
    rw [← Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
    obtain ⟨h, rfl⟩ := exists_smul_eq G α ω
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (hYn.conj_mem y hy h⁻¹)
    have hw : (h⁻¹ * y * h⁻¹⁻¹) • α = α := by
      rw [← hxy]
      exact mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp (hOM hx))
    rw [inv_inv] at hw
    calc y • h • α = h • (h⁻¹ * y * h) • α := by
          rw [smul_smul, smul_smul, show h * (h⁻¹ * y * h) = y * h by group]
      _ = (1 : G) • h • α := by rw [hw, one_smul]
  let q : (K ⧸ twoPrimeCore K) ≃* L :=
    (QuotientGroup.congr (twoPrimeCore K) (twoPrimeCore L) e hmap).trans
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  have hcomp : q.toMonoidHom.comp (QuotientGroup.mk' (twoPrimeCore K)) = K.subtype := by
    ext x
    rfl
  refine ⟨fusionIsBenderGroup_of_isSimpleBenderGroup (hBender.map_mulEquiv q), ?_, ?_⟩
  · have : IsPretransitive (⊤ : Subgroup G) Ω := ⟨fun a b => by
      obtain ⟨x, hx⟩ := exists_smul_eq G a b
      exact ⟨⟨x, trivial⟩, hx⟩⟩
    exact isPretransitive_of_le_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf hz hzL hzα
  · have hB := CFSG.ShultStronglyClosedTI.ProperPairModel.isBorelSubgroup_map_mulEquiv q hBorel
    have hBM : (((M ⊓ K).subgroupOf K).map (QuotientGroup.mk' (twoPrimeCore K))).map
        q.toMonoidHom = M := by
      rw [Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
      exact inf_eq_left.mpr (le_top.trans_eq hcore.symm)
    rwa [hBM] at hB

theorem aschbacher73_theorem2 [IsPretransitive G Ω] [FaithfulSMul G Ω]
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G)) {z : G} (hzQ : z ∈ Q)
    (hz : orderOf z = 2) :
    (Subgroup.normalClosure {z} ≤ fusionZStar G ∧
        IsPretransitive (oddCoreOf (Subgroup.normalClosure {z})) Ω) ∨
      (fusionIsBenderGroup (Subgroup.normalClosure ({z} : Set G)) ∧
        IsPretransitive (Subgroup.normalClosure ({z} : Set G)) Ω ∧
        IsBorelSubgroup ((stabilizer G α).subgroupOf (Subgroup.normalClosure ({z} : Set G)))) := by
  by_cases h : ∃ g : G, g * z * g⁻¹ ≠ z ∧ Commute z (g * z * g⁻¹)
  · obtain ⟨g, hne, hc⟩ := h
    exact Or.inr (aschbacher73_theorem2_of_commute hQα hQN hzQ hz hne hc)
  · exact Or.inl (isPretransitive_oddCoreOf_of_isolated hz (hQα z hzQ hz)
      fun g hc => by_contra fun hne => h ⟨g, hne, hc⟩)

end CFSG.Holt.General
