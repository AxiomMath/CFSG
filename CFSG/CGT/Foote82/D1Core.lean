module

public import CFSG.CGT.Foote82.EF1Bridge
import CFSG.CGT.Foote82.EF2
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem d1c_normalizer_eq {M : Subgroup G} (hM : GLBIsMaxTwoLocal M) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQ0 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨R, hR0, hR2, hMR⟩ := hM.1
    intro hbot
    apply hR0
    have hRM : R ≤ M := hMR ▸ Subgroup.le_normalizer
    have hRQ : R ≤ pCoreOf 2 M :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 R M hRM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr (hMR ▸ le_rfl)) hR2
    rw [hbot] at hRQ
    exact le_bot_iff.mp hRQ
  exact hM.2 _ ⟨pCoreOf 2 M, hQ0, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M, rfl⟩
    hMQ

private theorem d1c_blockU_le {M J : Subgroup G} (hJ : IsFooteBlock M J) :
    blockU J ≤ pCoreOf 2 M := by
  have hQJ : blockQ J ≤ J := C1.blockQ_le J
  have hn : ((blockQ J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).mpr (C1.le_normalizer_blockQ J)
  have hsub : IsSubnormal (blockQ J) M := .step hQJ hn hJ.subnormal
  exact (blockU_le_blockQ J).trans
    (CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub
      (C1.blockQ_isPGroup J))

private theorem d1c_isQuasisimple_hat {M J : Subgroup G} (hJ : IsFooteBlock M J) :
    CFSG.IsQuasisimple ↥(hatIn M J) :=
  isQuasisimple_of_block (IsFooteBlock.self hJ) (hatMap hJ.le) (hatMap_surjective hJ.le)
    (ker_hatMap_le hJ.le)
    fun k hk => (mem_ker_hatMap hJ.le k).mpr (d1c_blockU_le hJ hk)

private theorem d1c_isComponent_hat {M J : Subgroup G} (hJ : IsFooteBlock M J) :
    CFSG.IsComponent (hatIn M J) := by
  refine ⟨d1c_isQuasisimple_hat hJ, ?_⟩
  have h1 : IsSubnormal (J.subgroupOf M) (M.subgroupOf M) :=
    CFSG.Open.IsSubnormal.comap M.subtype hJ.subnormal
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) h1
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact CFSG.Open.IsSubnormal.top_iff.mp h2

private theorem d1c_not_comm {L : Type*} [Group L] (hq : CFSG.IsQuasisimple L) :
    ¬ ∀ a b : L, a * b = b * a := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a b])

private def d1cF (M : Subgroup G) : Subgroup G :=
  ((CFSG.generalizedFitting (NHat M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

private theorem mem_d1cF {M : Subgroup G} {g : G} :
    g ∈ d1cF M ↔ ∃ h : g ∈ M,
      (QuotientGroup.mk ⟨g, h⟩ : NHat M) ∈ CFSG.generalizedFitting (NHat M) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

private theorem d1cF_le (M : Subgroup G) : d1cF M ≤ M := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

private theorem pCoreOf_le_d1cF (M : Subgroup G) : pCoreOf 2 M ≤ d1cF M := by
  intro g hg
  have hgM : g ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hg
  refine mem_d1cF.mpr ⟨hgM, ?_⟩
  rw [(mk_eq_one_iff ⟨g, hgM⟩).mpr hg]
  exact Subgroup.one_mem _

private theorem le_normalizer_d1cF (M : Subgroup G) :
    M ≤ Subgroup.normalizer (d1cF M : Set G) := by
  haveI : (CFSG.generalizedFitting (NHat M)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := NHat M)).2
  have key : ∀ m ∈ M, ∀ g ∈ d1cF M, m * g * m⁻¹ ∈ d1cF M := by
    intro m hm g hg
    obtain ⟨hgM, hgF⟩ := mem_d1cF.mp hg
    have hmgM : m * g * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hgM) (M.inv_mem hm)
    refine mem_d1cF.mpr ⟨hmgM, ?_⟩
    have e : (⟨m * g * m⁻¹, hmgM⟩ : ↥M) = ⟨m, hm⟩ * ⟨g, hgM⟩ * ⟨m, hm⟩⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact (inferInstance : (CFSG.generalizedFitting (NHat M)).Normal).conj_mem _ hgF _
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key m hm g, fun hg => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hg
  simpa [mul_assoc] using this

private theorem d1c_fstar_le_normalizer {M J : Subgroup G} (hJ : IsFooteBlock M J) :
    CFSG.generalizedFitting (NHat M) ≤ Subgroup.normalizer (hatIn M J : Set (NHat M)) := by
  have hc := d1c_isComponent_hat hJ
  have hF : CFSG.fittingSubgroup (NHat M) ≤
      Subgroup.centralizer (CFSG.layer (NHat M) : Set (NHat M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := NHat M))
  show CFSG.fittingSubgroup (NHat M) ⊔ CFSG.layer (NHat M) ≤ _
  refine sup_le ?_ (CFSG.LocalCores.layer_le_normalizer hc)
  exact hF.trans ((Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (CFSG.LocalCores.component_le_layer hc))).trans
      (Subgroup.centralizer_le_normalizer _))

private theorem d1c_hat_le_hat_map {M J : Subgroup G} {f : G} (hfM : f ∈ M)
    (hf : (QuotientGroup.mk ⟨f, hfM⟩ : NHat M) ∈ Subgroup.normalizer (hatIn M J : Set (NHat M))) :
    hatIn M J ≤ hatIn M (J.map (MulAut.conj f).toMonoidHom) := by
  intro b hb
  obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_normalizer_iff.mp (inv_mem hf) b).mp hb
  refine ⟨⟨f, hfM⟩ * y * ⟨f, hfM⟩⁻¹,
    Subgroup.mem_subgroupOf.mpr ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, rfl⟩, ?_⟩
  simp only [map_mul, map_inv, QuotientGroup.mk'_apply] at hyb ⊢
  rw [hyb]
  group

private theorem d1c_hat_comm {M A B : Subgroup G} (hAB : ⁅A, B⁆ = ⊥)
    (hle : hatIn M A ≤ hatIn M B) : ∀ a b : ↥(hatIn M A), a * b = b * a := by
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨b, hb⟩
  obtain ⟨z, hz, rfl⟩ := hle hb
  have hxz : (z : G) * (x : G) = (x : G) * (z : G) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB (Subgroup.mem_subgroupOf.mp hx))
      (z : G) (Subgroup.mem_subgroupOf.mp hz)
  apply Subtype.ext
  show (QuotientGroup.mk x : NHat M) * QuotientGroup.mk z = QuotientGroup.mk z * QuotientGroup.mk x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hxz.symm

private theorem d1c_F_le_normalizer {M J : Subgroup G} (hJ : IsFooteBlock M J) :
    d1cF M ≤ Subgroup.normalizer (J : Set G) := by
  intro f hf
  obtain ⟨hfM, hfF⟩ := mem_d1cF.mp hf
  have hfN := d1c_fstar_le_normalizer hJ hfF
  have hJf := isFooteBlock_map hJ (MulAut.conj f)
  rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hfM)] at hJf
  by_cases hne : J = J.map (MulAut.conj f).toMonoidHom
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hne]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [hne] at hy
      obtain ⟨y', hy', hyy'⟩ := hy
      have : y' = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
        exact mul_left_cancel (mul_right_cancel hyy')
      exact this ▸ hy'
  · exfalso
    exact d1c_not_comm (d1c_isQuasisimple_hat hJ)
      (d1c_hat_comm (blocks_commute hJ hJf hne) (d1c_hat_le_hat_map hfM hfN))

private theorem d1c_eq_bot_of_centralizes {X : Type} [Group X] [Finite X]
    (hX : CFSG.pCore 2 X = ⊥) {T : Subgroup X} (hT : IsPGroup 2 T)
    (hTC : T ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X)) : T = ⊥ := by
  haveI : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hTF : T ≤ CFSG.generalizedFitting X := hTC.trans (CFSG.centralizer_generalizedFitting_le X)
  have hWn : (CFSG.generalizedFitting X ⊓
      Subgroup.centralizer (CFSG.generalizedFitting X : Set X)).Normal :=
    Subgroup.normal_inf_normal _ _
  have hW : ∀ x ∈ CFSG.generalizedFitting X ⊓
      Subgroup.centralizer (CFSG.generalizedFitting X : Set X),
      ∀ y ∈ CFSG.generalizedFitting X ⊓
        Subgroup.centralizer (CFSG.generalizedFitting X : Set X), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  have hle := le_pCore_of_isPGroup_of_le_commutative_normal hWn hW (le_inf hTF hTC) hT
  rw [hX] at hle
  exact le_bot_iff.mp hle

private theorem d1c_inf_le {M P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hFP : d1cF M ≤ Subgroup.normalizer (P : Set G)) :
    ∀ x ∈ P, x ∈ M → x ∈ pCoreOf 2 M := by
  intro x hxP hxM
  have hFPQ : d1cF M ⊓ P ≤ pCoreOf 2 M := by
    have hF2 : IsPGroup 2 ↥(d1cF M ⊓ P) := hP2.to_le inf_le_right
    have hn1 : ((d1cF M ⊓ P).subgroupOf (d1cF M)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hFP hg⟩
    have hn2 : ((d1cF M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (d1cF_le M)).mpr (le_normalizer_d1cF M)
    have hsub : IsSubnormal (d1cF M ⊓ P) M :=
      .step inf_le_left hn1 (.step (d1cF_le M) hn2 (.refl M))
    exact CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub hF2
  have hcomm : ∀ y ∈ P, y ∈ M → ∀ f ∈ d1cF M, y * f * y⁻¹ * f⁻¹ ∈ pCoreOf 2 M := by
    intro y hyP hyM f hf
    refine hFPQ ⟨?_, ?_⟩
    · exact (d1cF M).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_d1cF M hyM) f).mp hf)
        ((d1cF M).inv_mem hf)
    · have e : y * f * y⁻¹ * f⁻¹ = y * (f * y⁻¹ * f⁻¹) := by group
      rw [e]
      exact P.mul_mem hyP ((Subgroup.mem_normalizer_iff.mp (hFP hf) _).mp (P.inv_mem hyP))
  have hle : hatIn M P ≤ Subgroup.centralizer
      (CFSG.generalizedFitting (NHat M) : Set (NHat M)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    have hgF : (g' : G) ∈ d1cF M := mem_d1cF.mpr ⟨g'.2, hg⟩
    have hc : ((y * g' * y⁻¹ * g'⁻¹ : ↥M) : G) ∈ pCoreOf 2 M :=
      hcomm (y : G) (Subgroup.mem_subgroupOf.mp hy) y.2 (g' : G) hgF
    have h1 : (QuotientGroup.mk (y * g' * y⁻¹ * g'⁻¹) : NHat M) = 1 := (mk_eq_one_iff _).mpr hc
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    show (QuotientGroup.mk g' : NHat M) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk g'
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hbot : hatIn M P = ⊥ :=
    d1c_eq_bot_of_centralizes (pCore_quotient_pCore_eq_bot' (X := ↥M) 2)
      ((hP2.comap_of_injective M.subtype Subtype.val_injective).map _) hle
  have hx1 : (QuotientGroup.mk ⟨x, hxM⟩ : NHat M) = 1 := by
    have hx : (QuotientGroup.mk ⟨x, hxM⟩ : NHat M) ∈ hatIn M P :=
      ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    rw [hbot] at hx
    exact Subgroup.mem_bot.mp hx
  exact (mk_eq_one_iff _).mp hx1

theorem d1_core_le {M N J : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hJ : IsFooteBlock M J)
    (hJN : Subgroup.normalizer (J : Set G) ≤ N) : pCoreOf 2 N ≤ pCoreOf 2 M := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hP2 : IsPGroup 2 (pCoreOf 2 N) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  have hNP : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  have hFN : d1cF M ≤ N := (d1c_F_le_normalizer hJ).trans hJN
  have hQN : pCoreOf 2 M ≤ N := (pCoreOf_le_d1cF M).trans hFN
  have step4 := d1c_inf_le hP2 (hFN.trans hNP)
  by_contra hPQ
  have hQP2 : IsPGroup 2 ↥(pCoreOf 2 M ⊔ pCoreOf 2 N) :=
    IsPGroup.to_sup_of_normal_right' hQ2 hP2 (hQN.trans hNP)
  have hlt : pCoreOf 2 M < pCoreOf 2 M ⊔ pCoreOf 2 N :=
    lt_of_le_of_ne le_sup_left fun he => hPQ (sup_eq_left.mp he.symm)
  obtain ⟨x, ⟨hxQP, hxNQ⟩, hxQ⟩ := SetLike.exists_of_lt (lt_inf_normalizer hlt hQP2)
  have hx' : x ∈ ((pCoreOf 2 M ⊔ pCoreOf 2 N : Subgroup G) : Set G) := hxQP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (pCoreOf 2 M) (pCoreOf 2 N)
    (hQN.trans hNP)] at hx'
  obtain ⟨q, hq, p, hp, rfl⟩ := hx'
  have hpNQ : p ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    have e : p = q⁻¹ * (q * p) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hq)) hxNQ
  have hpM : p ∈ M := (d1c_normalizer_eq hM).le hpNQ
  exact hxQ ((pCoreOf 2 M).mul_mem hq (step4 p hp hpM))

end CFSG.CGT.Foote82
