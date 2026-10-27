module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem op_p'p_map_mulEquiv_s15 (p : ℕ) {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') :
    (CFSG.Op_p'p p H).map e.toMonoidHom = CFSG.Op_p'p p H' := by
  have hN : (CFSG.pPrimeCore p H).map e.toMonoidHom = CFSG.pPrimeCore p H' :=
    CFSG.pPrimeCore_map_iso p e
  let g : H ⧸ CFSG.pPrimeCore p H ≃* H' ⧸ CFSG.pPrimeCore p H' :=
    QuotientGroup.congr (CFSG.pPrimeCore p H) (CFSG.pPrimeCore p H') e hN
  have hC : (CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H)).map g.toMonoidHom =
      CFSG.pCore p (H' ⧸ CFSG.pPrimeCore p H') := CFSG.pCore_map_iso p g
  ext x'
  obtain ⟨y, rfl⟩ := e.surjective x'
  have hgy : g (QuotientGroup.mk' _ y) = QuotientGroup.mk' _ (e y) := rfl
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [CFSG.Op_p'p, Subgroup.mem_comap]
  rw [← hC, ← hgy, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem isSylowOf_map_mulEquiv_s15 (p : ℕ) {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    {P K : Subgroup H} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨Q, rfl⟩ := h
  let r : K ≃* K.map e.toMonoidHom := Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  refine ⟨{ toSubgroup := (Q : Subgroup K).map r.toMonoidHom
            isPGroup' := Q.isPGroup'.map r.toMonoidHom
            is_maximal' := ?_ }, ?_⟩
  · intro R hR hle
    have h1 : (Q : Subgroup K) ≤ R.map r.symm.toMonoidHom := by
      intro x hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      exact hle (Subgroup.mem_map_of_mem r.toMonoidHom hx)
    have hR0 : IsPGroup p (R.map r.symm.toMonoidHom : Subgroup K) :=
      hR.map r.symm.toMonoidHom
    have h2 : R.map r.symm.toMonoidHom = (Q : Subgroup K) := Q.is_maximal' hR0 h1
    have h3 := congrArg (Subgroup.map r.toMonoidHom) h2
    rw [Subgroup.map_map] at h3
    have hid : r.toMonoidHom.comp r.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact congrArg Subtype.val (r.apply_symm_apply x)
    rw [hid, Subgroup.map_id] at h3
    exact h3
  · have hφ : (K.map e.toMonoidHom).subtype.comp r.toMonoidHom =
        e.toMonoidHom.comp K.subtype := by
      ext x
      rfl
    show ((Q : Subgroup K).map r.toMonoidHom).map (K.map e.toMonoidHom).subtype =
      ((Q : Subgroup K).map K.subtype).map e.toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map, hφ]

theorem isPConstrained_of_mulEquiv_s15 (p : ℕ) {H H' : Type*} [Group H] [Group H']
    (e : H ≃* H') (h : CFSG.ABGLocalTools.IsPConstrained p H) :
    CFSG.ABGLocalTools.IsPConstrained p H' := by
  intro P' hP'
  have hOp : (CFSG.Op_p'p p H).map e.toMonoidHom = CFSG.Op_p'p p H' :=
    op_p'p_map_mulEquiv_s15 p e
  have hOp' : (CFSG.Op_p'p p H').map e.symm.toMonoidHom = CFSG.Op_p'p p H :=
    (Subgroup.map_symm_eq_iff_map_eq _).mpr hOp
  have hP : CFSG.ABGLocalTools.IsSylowOf p (P'.map e.symm.toMonoidHom) (CFSG.Op_p'p p H) := by
    have h1 := isSylowOf_map_mulEquiv_s15 p e.symm hP'
    rwa [hOp'] at h1
  have hc := h _ hP
  intro x' hx'
  rw [← hOp, Subgroup.mem_map_equiv]
  refine hc ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : k ∈ P'.map e.symm.toMonoidHom := hk
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk'
  have hyc : y * x' = x' * y := Subgroup.mem_centralizer_iff.mp hx' y hy
  show e.symm y * e.symm x' = e.symm x' * e.symm y
  rw [← map_mul, ← map_mul, hyc]

theorem isPConstrained_congr_mulEquiv_s15 (p : ℕ) {H H' : Type*} [Group H] [Group H']
    (e : H ≃* H') :
    CFSG.ABGLocalTools.IsPConstrained p H ↔ CFSG.ABGLocalTools.IsPConstrained p H' :=
  ⟨isPConstrained_of_mulEquiv_s15 p e, isPConstrained_of_mulEquiv_s15 p e.symm⟩

theorem autOn_mulEquiv_quot {M T : Subgroup G}
    (hC : gnC (T.subgroupOf M) = (Subgroup.centralizer (uCore M T : Set G)).subgroupOf M) :
    Nonempty (↥(CFSG.Quasithin.autOn M (uCore M T)) ≃* (↥M ⧸ gnC (T.subgroupOf M))) := by
  have hMU : M ≤ Subgroup.normalizer (uCore M T : Set G) := le_normalizer_uCore M T
  have hker : (CFSG.Quasithin.InternalSec.autOnHom hMU).ker = gnC (T.subgroupOf M) := by
    rw [hC]
    ext l
    rw [CFSG.Quasithin.InternalSec.mem_ker_autOnHom hMU l, Subgroup.mem_subgroupOf]
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _
      (CFSG.Quasithin.InternalSec.autOnHom_surjective hMU)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem isPConstrained_autOn_iff_quot {M T : Subgroup G} (p : ℕ)
    (hC : gnC (T.subgroupOf M) = (Subgroup.centralizer (uCore M T : Set G)).subgroupOf M) :
    CFSG.ABGLocalTools.IsPConstrained p ↥(CFSG.Quasithin.autOn M (uCore M T)) ↔
      CFSG.ABGLocalTools.IsPConstrained p (↥M ⧸ gnC (T.subgroupOf M)) := by
  obtain ⟨e⟩ := autOn_mulEquiv_quot hC
  exact isPConstrained_congr_mulEquiv_s15 p e

end CFSG.LocalAnalysis.RankThreeUC.S15
