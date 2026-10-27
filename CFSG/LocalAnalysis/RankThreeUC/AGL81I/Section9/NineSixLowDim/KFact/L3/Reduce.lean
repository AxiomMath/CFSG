module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Gen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
public import CFSG.Milestones.ASVolI.A3Lie

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix MatrixGroups CFSG.ASVolI CFSG.ASVolI.ChA

private theorem diagAut_mk_of_commute {F : Type} [Field F] {g : GL (Fin 3) F} {s : SL(3, F)}
    (h : g * Matrix.SpecialLinearGroup.toGL s = Matrix.SpecialLinearGroup.toGL s * g) :
    psl3DiagAut g (QuotientGroup.mk s : PSL(3, F)) = QuotientGroup.mk s := by
  show pslOfSL (slConj g) (QuotientGroup.mk s) = _
  rw [burnsideA315h_pslOfSL_mk]
  congr 1
  apply Subtype.ext
  show (g : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = s
  have h' := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h'
  rw [h', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private noncomputable def cHom (F : Type) [Field F] : GL (Fin 3) F →* MulAut PSL(3, F) where
  toFun := psl3DiagAut
  map_one' := burnsideA315h_diag_one F
  map_mul' := burnsideA315h_diag_mul

private theorem cHom_apply {F : Type} [Field F] (g : GL (Fin 3) F) : cHom F g = psl3DiagAut g :=
  rfl

private theorem diagAut_eq_one_iff {F : Type} [Field F] [Finite F] (g : GL (Fin 3) F) :
    psl3DiagAut g = 1 ↔ g ∈ Subgroup.center (GL (Fin 3) F) := by
  constructor
  · intro h
    have h1 : psl3DiagAut g * psl3FieldAut (1 : RingAut F) = 1 := by
      rw [burnsideA315h_field_one, mul_one, h]
    obtain ⟨-, c, hc⟩ := burnsideA315h_diagfield_eq_one h1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← hc]
    exact ⟨c, rfl⟩
  · intro h
    ext x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    rw [diagAut_mk_of_commute (Subgroup.mem_center_iff.1 h _).symm, MulAut.one_apply]

private theorem ker_diagHom {F : Type} [Field F] [Finite F] :
    (cHom F).ker = Subgroup.center (GL (Fin 3) F) := by
  ext g
  rw [MonoidHom.mem_ker, cHom_apply]
  exact diagAut_eq_one_iff g

private theorem mem_range_diagHom {q : ℕ} [Fact q.Prime] {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime)
    {α : MulAut PSL(3, ZMod q)} (hα : α ^ p = 1) :
    α ∈ (cHom (ZMod q)).range := by
  obtain ⟨g, σ, ε, hε, rfl⟩ := burnsideA315h_classification α
  rw [Subsingleton.elim σ 1, burnsideA315h_field_one, mul_one] at hα ⊢
  have hsq : (psl3DiagAut g * psl3GraphAut ^ ε) ^ 2 ∈ (cHom (ZMod q)).range := by
    interval_cases ε
    · exact ⟨g ^ 2, by rw [map_pow, cHom_apply, pow_zero, mul_one]⟩
    · refine ⟨g * Matrix.GeneralLinearGroup.inverseTranspose g, ?_⟩
      rw [cHom_apply, burnsideA315h_diag_mul, ← burnsideA315h_graph_diag]
      simp only [pow_one, pow_two, mul_assoc]
  set α := psl3DiagAut g * psl3GraphAut ^ ε
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have : α = (α ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hα, one_mul]
  rw [this]
  exact pow_mem hsq _

private theorem isElemModScalars_comap {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut PSL(3, ZMod q))} (hE : CFSG.Open.IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) :
    IsElemModScalars p (E.comap (cHom (ZMod q))) := by
  have hker := ker_diagHom (F := ZMod q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hker]
    exact Subgroup.ker_le_comap _ _
  · intro g hg
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hE.2 _ hg
  · intro g hg h hh
    rw [← hker, MonoidHom.mem_ker]
    have hcomm := hE.1.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩
    have hcomm' := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul] at hcomm'
    simp only [map_mul, map_inv, hcomm', mul_inv_cancel_right, mul_inv_cancel]
  · have hle : E ≤ (cHom (ZMod q)).range := fun α hα =>
      mem_range_diagHom hp2 hp (hE.2 α hα)
    have hri : Nat.card (E.comap (cHom (ZMod q)) ⧸
        (Subgroup.center (GL (Fin 3) (ZMod q))).subgroupOf (E.comap (cHom (ZMod q)))) =
        (Subgroup.center _).relIndex (E.comap (cHom (ZMod q))) := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
    rw [hri, ← hker, Subgroup.relIndex_ker, Subgroup.map_comap_eq, inf_eq_right.2 hle, hc]

private theorem mk_mem_fixPPrime {F : Type} [Field F] [Finite F] {p : ℕ}
    {E : Subgroup (MulAut PSL(3, F))} {s : SL(3, F)}
    (hs : Matrix.SpecialLinearGroup.toGL s ∈ fixSetThree p (E.comap (cHom F))) :
    (QuotientGroup.mk s : PSL(3, F)) ∈ fixPPrime p E := by
  obtain ⟨-, hord, g, hg, hgZ, hgs⟩ := hs
  refine ⟨fun hdvd => hord ?_, psl3DiagAut g, hg, fun h1 => hgZ ((diagAut_eq_one_iff g).1 h1),
    diagAut_mk_of_commute hgs⟩
  rw [orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective s]
  exact hdvd.trans (orderOf_map_dvd (QuotientGroup.mk' _) s)

private theorem closure_preimage_eq_top {F : Type} [Field F] {p : ℕ}
    {A : Subgroup (GL (Fin 3) F)}
    (h : Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 F) :
    Subgroup.closure {s : SL(3, F) | Matrix.SpecialLinearGroup.toGL s ∈ fixSetThree p A} = ⊤ := by
  have himg : Matrix.SpecialLinearGroup.toGL ''
      {s : SL(3, F) | Matrix.SpecialLinearGroup.toGL s ∈ fixSetThree p A} = fixSetThree p A := by
    ext x
    refine ⟨fun ⟨s, hs, hsx⟩ => hsx ▸ hs, fun hx => ⟨⟨x, hx.1⟩, ?_, Units.ext rfl⟩⟩
    have : Matrix.SpecialLinearGroup.toGL ⟨(x : Matrix (Fin 3) (Fin 3) F), hx.1⟩ = x :=
      Units.ext rfl
    show Matrix.SpecialLinearGroup.toGL (⟨(x : Matrix (Fin 3) (Fin 3) F), hx.1⟩ : SL(3, F)) ∈
      fixSetThree p A
    rw [this]
    exact hx
  have hmap := MonoidHom.map_closure Matrix.SpecialLinearGroup.toGL
    {s : SL(3, F) | Matrix.SpecialLinearGroup.toGL s ∈ fixSetThree p A}
  rw [himg, h] at hmap
  rw [eq_top_iff]
  intro s _
  have hs : Matrix.SpecialLinearGroup.toGL s ∈ CFSG.Open.StatedSL 3 F :=
    Subgroup.subset_closure s.2
  rw [← hmap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rwa [Matrix.SpecialLinearGroup.toGL_injective hts] at ht

theorem pPrimeGenAt_psl_three_of {q : ℕ} [Fact q.Prime] (_hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (_hpq : p ≠ q)
    (h : ∀ A : Subgroup (GL (Fin 3) (ZMod q)), IsElemModScalars p A →
      Subgroup.closure (fixSetThree p A) = CFSG.Open.StatedSL 3 (ZMod q)) :
    PPrimeGenAt p PSL(3, ZMod q) := by
  intro E hE hc
  have htop := closure_preimage_eq_top (h _ (isElemModScalars_comap hp hp2 hE hc))
  rw [eq_top_iff]
  intro y _
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  have hs : s ∈ Subgroup.closure
      {s : SL(3, ZMod q) | Matrix.SpecialLinearGroup.toGL s ∈
        fixSetThree p (E.comap (cHom (ZMod q)))} := htop ▸ Subgroup.mem_top s
  have hs' := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center SL(3, ZMod q))) hs
  rw [MonoidHom.map_closure] at hs'
  refine Subgroup.closure_mono ?_ hs'
  rintro _ ⟨t, ht, rfl⟩
  exact mk_mem_fixPPrime ht

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
