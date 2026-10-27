module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Classes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherAssembly
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.Foundations
public import CFSG.GH74.GLS.Classes
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.Walter.J1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup CFSG.ProperTwoGeneratedCore.Assembly
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem eq_one_or_eq_of_mem_centralizer_of_sylow {J : Subgroup X} [J.Normal] {zb : X}
    (hzc : zb ∈ center X) (hodd : CFSG.pPrimeCore 2 X = ⊥) (T : Sylow 2 X)
    (hT : ∀ k ∈ (T : Subgroup X), k ∈ centralizer (J : Set X) → k = 1 ∨ k = zb)
    {c : X} (hc : c ∈ centralizer (J : Set X)) : c = 1 ∨ c = zb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (J : Set X) with hC
  have hcen : ∀ p : C, (p : X) ∈ (T : Subgroup X) → p ∈ center C := fun p hp => by
    rcases hT p hp p.2 with h | h
    · rw [show p = 1 from Subtype.ext h]
      exact (center C).one_mem
    · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
        exact Subgroup.mem_center_iff.mp hzc g)
  let P := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T C
  have hP : (P : Subgroup C) ≤ CFSG.centerIn (Subgroup.normalizer (P : Subgroup C)) := by
    intro p hp
    refine ⟨Subgroup.le_normalizer hp, Subgroup.mem_centralizer_iff.mpr fun g _ => ?_⟩
    exact Subgroup.mem_center_iff.mp (hcen p hp) g
  obtain ⟨N, hN, hcop, hNp⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 P hP
  have hcore : CFSG.pPrimeCore 2 C = ⊥ := by
    have h := CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 2)
      (Subgroup.normal_centralizer (H := J))
    rwa [hodd, inf_bot_eq, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at h
  have hNbot : N = ⊥ := le_bot_iff.mp (hcore ▸ le_sSup ⟨hN, hcop⟩)
  subst hNbot
  have hC2 : IsPGroup 2 C := hNp.of_equiv QuotientGroup.quotientBot
  exact hT c (IsPGroup.le_sylow_of_normal hC2 T hc) hc

theorem two_le_pRank_of_mem_zbar {J D : Subgroup X} (hJ : IsTwoANine J)
    (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {x : J} (hx : proj e x = aNineEGenX)
    (hxD : (x : X) ∈ D) (hzD : (zbar J : X) ∈ D) : 2 ≤ CFSG.Open.pRank 2 D := by
  have hct : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
    rw [hx, aNineEGenX_eq_mul]
    exact cycleType_aNineSylowGenA_mul_genC
  have hx2 := hJ.orderOf_eq_two_of_cycleType_two_two_two_two e hct
  refine two_le_pRank_of_commuting_involutions hxD hzD
    (by rw [Subgroup.orderOf_coe]; exact hx2.1) (by rw [Subgroup.orderOf_coe]; exact hJ.orderOf_zbar)
    (fun h => hx2.2 ?_) ((hJ.commute_zbar x).map J.subtype)
  rw [Subtype.ext h]
  exact hJ.zbar_mem_center

theorem two_le_pRank_of_isTwoANine {J : Subgroup X} (hJ : IsTwoANine J) :
    2 ≤ CFSG.Open.pRank 2 J := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  obtain ⟨x, hx⟩ := proj_surjective e aNineEGenX
  exact two_le_pRank_of_mem_zbar hJ e hx x.2 (zbar J).2

section Stabilizer

variable {J B : Subgroup X} (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
  (hsyl : ∀ x : J, proj e x ∈ ANineSylow → (x : X) ∈ B)
  (hnorm : ∀ D : Subgroup X, D ≤ B → 2 ≤ CFSG.Open.pRank 2 D → normalizer (D : Set X) ≤ B)
include hJ hsyl hnorm

theorem normalizer_le_map_subgroupOf_of_le_aNineSylow {E : Subgroup (alternatingGroup (Fin 9))}
    (hE : E ≤ ANineSylow) (hX : aNineEGenX ∈ E) :
    normalizer (E : Set (alternatingGroup (Fin 9))) ≤ (B.subgroupOf J).map (proj e) := by
  intro n hn
  obtain ⟨m, rfl⟩ := proj_surjective e n
  set D : Subgroup X := (E.comap (proj e)).map J.subtype with hD
  have hDB : D ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsyl x (hE hx)
  obtain ⟨x, hx⟩ := proj_surjective e aNineEGenX
  have hxD : (x : X) ∈ D := ⟨x, show proj e x ∈ E by rw [hx]; exact hX, rfl⟩
  have hzD : (zbar J : X) ∈ D :=
    ⟨zbar J, show proj e (zbar J) ∈ E by rw [hJ.proj_zbar e]; exact E.one_mem, rfl⟩
  have hD2 := two_le_pRank_of_mem_zbar hJ e hx hxD hzD
  have hmN : (m : X) ∈ normalizer (D : Set X) :=
    Subgroup.le_normalizer_map J.subtype (Subgroup.mem_map_of_mem _
      (Subgroup.le_normalizer_comap (proj e) hn))
  exact ⟨m, Subgroup.mem_subgroupOf.mpr (hnorm D hDB hD2 hmN), rfl⟩

theorem map_subgroupOf_eq_stabilizer_eight (hJB : ¬ J ≤ B) :
    (B.subgroupOf J).map (proj e) = MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) := by
  refine eq_stabilizer_of_normalizer_le_of_ne_top
    (normalizer_le_map_subgroupOf_of_le_aNineSylow hJ e hsyl hnorm aNineEZero_le_aNineSylow
      (Subgroup.subset_closure (by simp)))
    (normalizer_le_map_subgroupOf_of_le_aNineSylow hJ e hsyl hnorm aNineEOne_le_aNineSylow
      (Subgroup.subset_closure (by simp))) fun htop => hJB fun x hx => ?_
  obtain ⟨b, hb, hbx⟩ : proj e ⟨x, hx⟩ ∈ (B.subgroupOf J).map (proj e) := htop ▸ mem_top _
  have hzB : (zbar J : X) ∈ B := hsyl _ (by rw [hJ.proj_zbar e]; exact ANineSylow.one_mem)
  rcases (hJ.proj_eq_proj_iff' e).mp hbx with h | h
  · rw [show x = (b : X) from congrArg Subtype.val h]
    exact hb
  · rw [show x = (b : X) * zbar J from congrArg Subtype.val h]
    exact B.mul_mem hb hzB

end Stabilizer

theorem exists_mulEquiv_proj_mem_of_sylow_le {J B : Subgroup X} [J.Normal] (hJ : IsTwoANine J)
    (U : Sylow 2 X) (hUB : (U : Subgroup X) ≤ B) :
    ∃ e : J ⧸ center J ≃* alternatingGroup (Fin 9),
      ∀ x : J, proj e x ∈ ANineSylow → (x : X) ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hJ.nonempty_mulEquiv
  let Q := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal U J
  let P := Q.mapSurjective (proj_surjective e₀)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 9)) P aNineSylowSylow
  refine ⟨e₀.trans (MulAut.conj g), fun x hx => ?_⟩
  have hx' : g * proj e₀ x * g⁻¹ ∈ MulAut.conj g • (P : Subgroup (alternatingGroup (Fin 9))) := by
    rw [← Sylow.coe_subgroup_smul, hg, coe_aNineSylowSylow]
    exact hx
  rw [← MulAut.conj_apply, ← MulAut.smul_def, Subgroup.smul_mem_pointwise_smul_iff,
    Sylow.coe_mapSurjective] at hx'
  obtain ⟨q, hq, hqx⟩ := hx'
  have hqU : (q : X) ∈ U := hq
  rcases (hJ.proj_eq_proj_iff' e₀).mp hqx with h | h
  · rw [h]
    exact hUB hqU
  · have hz : ((zbar J : J) : X) ∈ U := hJ.center_le_sylow Q hJ.zbar_mem_center
    rw [h, Subgroup.coe_mul]
    exact hUB (U.mul_mem hqU hz)

theorem mul_eq_mul_mul_of_mul_self_eq {G : Type*} [Group G] {a c z : G} (hzz : z * z = 1)
    (ha : a * a = z) (hc : c * c = z) (hac : a * c * (a * c) = z) : c * a = a * c * z := by
  have hainv : a⁻¹ = a * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha, hzz])
  have hcinv : c⁻¹ = c * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hc, hzz])
  calc c * a = a⁻¹ * (a * c * (a * c)) * c⁻¹ := by group
    _ = a * z * z * (c * z) := by rw [hac, hainv, hcinv]
    _ = a * c * z := by rw [mul_assoc a z z, hzz, mul_one, mul_assoc]

theorem mul_mul_mul_self_eq_one_of_anticomm {G : Type*} [Group G] {a b c z : G}
    (hz : z ∈ center G) (hzz : z * z = 1) (hab : a * b * (a * b) = z) (hc : c * c = z)
    (hca : c * a = a * c * z) (hcb : c * b = b * c * z) : a * b * c * (a * b * c) = 1 := by
  have hzc : ∀ g : G, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have h1 : c * (a * b) = a * b * c := by
    calc c * (a * b) = c * a * b := by group
      _ = a * c * (z * b) := by rw [hca, mul_assoc (a * c) z b]
      _ = a * (c * b) * z := by rw [← hzc b]; group
      _ = a * b * c * (z * z) := by rw [hcb]; group
      _ = a * b * c := by rw [hzz, mul_one]
  calc a * b * c * (a * b * c) = a * b * (c * (a * b)) * c := by group
    _ = a * b * (a * b) * (c * c) := by rw [h1]; group
    _ = 1 := by rw [hab, hc, hzz]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
