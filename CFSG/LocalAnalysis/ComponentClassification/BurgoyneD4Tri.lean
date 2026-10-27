module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Fam
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Cycle
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (familyTransport
  familyTransport_apply familyTransport_automorphism)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open scoped Pointwise

theorem map_oddCoreIn_equiv {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    (B : Subgroup G) (t : G) :
    (oddCoreIn B t).map φ.toMonoidHom = oddCoreIn (B.map φ.toMonoidHom) (φ t) := by
  set C := B ⊓ centralizer ({t} : Set G) with hC
  set D := B.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G') with hD
  have hCD : C.map φ.toMonoidHom = D := by
    rw [hC, hD, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective]
    congr 1
    ext y
    simp only [mem_map_equiv, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg φ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
    · intro h
      apply φ.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  let e : C ≃* D := (C.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hCD)
  have hcore := CFSG.pPrimeCore_map_iso 2 e
  rw [oddCoreIn, oddCoreIn, Subgroup.map_map, ← hC, ← hD, ← hcore, Subgroup.map_map]
  rfl

variable {K : Type} [Field K] {d : ℕ}

section Defs

variable (Q : QuadraticForm K (Fin d → K))

@[expose] def TriCyc (y : MulAut (StatedProj (matrixDerived Q))) : Prop :=
  ∃ C₁ C₂ : Set (Subgroup (StatedProj (matrixDerived Q))),
    IsCycle3 y (ptFam Q) C₁ C₂ ∧ C₁ ∪ C₂ = tsFam Q

@[expose] def D4Geom : Prop :=
  ∀ z : MulAut (StatedProj (matrixDerived Q)), Odd (orderOf z) → z • ptFam Q ≠ ptFam Q →
    TriCyc Q z

@[expose] def PtRigid : Prop :=
  ∀ L L' : Points Q, subStab Q L.val = subStab Q L'.val → L = L'

structure Sit (B : Subgroup (MulAut (StatedProj (matrixDerived Q))))
    (t y : MulAut (StatedProj (matrixDerived Q))) : Prop where
  inj : Function.Injective (MulAut.conj : StatedProj (matrixDerived Q) →*
    MulAut (StatedProj (matrixDerived Q)))
  inn : (MulAut.conj : StatedProj (matrixDerived Q) →* MulAut (StatedProj (matrixDerived Q))).range
    ≤ B
  core : y ∈ oddCoreIn B t
  move : y • ptFam Q ≠ ptFam Q
  geom : D4Geom Q
  rigid : PtRigid Q

end Defs

variable {Q : QuadraticForm K (Fin d → K)}

theorem TriCyc.exists_ts_of_pt {y : MulAut (StatedProj (matrixDerived Q))} (h : TriCyc Q y)
    {H : Subgroup (StatedProj (matrixDerived Q))} (hH : ∀ x ∈ H, y x = x) {L : Points Q}
    (hHL : H ≤ subStab Q L.val) : ∃ W, IsTS Q 4 W ∧ H ≤ subStab Q W := by
  obtain ⟨C₁, C₂, hc, hU⟩ := h
  obtain ⟨M, hM, hHM⟩ := (exists_le_of_cycle hc hH (subStab_mem_ptFam Q L) hHL).1
  have hM' : M ∈ tsFam Q := hU ▸ Or.inl hM
  obtain ⟨W, hW, rfl⟩ := hM'
  exact ⟨W, hW, hHM⟩

theorem TriCyc.exists_pt_of_ts {y : MulAut (StatedProj (matrixDerived Q))} (h : TriCyc Q y)
    {H : Subgroup (StatedProj (matrixDerived Q))} (hH : ∀ x ∈ H, y x = x)
    {W : Submodule K (Fin d → K)} (hW : IsTS Q 4 W) (hHW : H ≤ subStab Q W) :
    ∃ L : Points Q, H ≤ subStab Q L.val := by
  obtain ⟨C₁, C₂, hc, hU⟩ := h
  have hM : subStab Q W ∈ C₁ ∪ C₂ := hU ▸ subStab_mem_tsFam Q hW
  have hpt : ∀ M ∈ ptFam Q, H ≤ M → ∃ L : Points Q, H ≤ subStab Q L.val := by
    rintro _ ⟨L, rfl⟩ hHM
    exact ⟨L, hHM⟩
  rcases hM with hM | hM
  · obtain ⟨M, hM, hHM⟩ := (exists_le_of_cycle hc.rotate hH hM hHW).2
    exact hpt M hM hHM
  · obtain ⟨M, hM, hHM⟩ := (exists_le_of_cycle hc.rotate.rotate hH hM hHW).1
    exact hpt M hM hHM

theorem TriCyc.exists_pt_of_ts_map {y t : MulAut (StatedProj (matrixDerived Q))} (h : TriCyc Q y)
    (hty : t * y = y * t) {W : Submodule K (Fin d → K)} (hW : IsTS Q 4 W)
    (htW : (subStab Q W).map t.toMonoidHom = subStab Q W) :
    ∃ L : Points Q, (subStab Q L.val).map t.toMonoidHom = subStab Q L.val := by
  obtain ⟨C₁, C₂, hc, hU⟩ := h
  have hM : subStab Q W ∈ C₁ ∪ C₂ := hU ▸ subStab_mem_tsFam Q hW
  have hpt : ∀ M ∈ ptFam Q, M.map t.toMonoidHom = M →
      ∃ L : Points Q, (subStab Q L.val).map t.toMonoidHom = subStab Q L.val := by
    rintro _ ⟨L, rfl⟩ hM
    exact ⟨L, hM⟩
  rcases hM with hM | hM
  · obtain ⟨M, hM, hHM⟩ := (exists_map_eq_of_cycle hc.rotate hty hM htW).2
    exact hpt M hM hHM
  · obtain ⟨M, hM, hHM⟩ := (exists_map_eq_of_cycle hc.rotate.rotate hty hM htW).1
    exact hpt M hM hHM

section Transport

variable {Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K) (ν : Kˣ)
  (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)

theorem familyTransport_smul (α : MulAut (StatedProj (matrixDerived Q)))
    (F : Set (Subgroup (StatedProj (matrixDerived Q)))) :
    familyTransport (oTransport S ν hS) (α • F) =
      MulAut.congr (oTransport S ν hS) α • familyTransport (oTransport S ν hS) F :=
  familyTransport_automorphism _ F α

theorem smul_ptFam_ne_iff (α : MulAut (StatedProj (matrixDerived Q))) :
    MulAut.congr (oTransport S ν hS) α • ptFam Q' ≠ ptFam Q' ↔ α • ptFam Q ≠ ptFam Q := by
  rw [← familyTransport_ptFam S ν hS, ← familyTransport_smul, Ne, Ne,
    (familyTransport (oTransport S ν hS)).injective.eq_iff]

theorem TriCyc.transport {y : MulAut (StatedProj (matrixDerived Q))} (h : TriCyc Q y) :
    TriCyc Q' (MulAut.congr (oTransport S ν hS) y) := by
  obtain ⟨C₁, C₂, hc, hU⟩ := h
  set T := familyTransport (oTransport S ν hS) with hT
  have hF := familyTransport_ptFam S ν hS
  have e : ∀ F F' : Set (Subgroup (StatedProj (matrixDerived Q))), y • F = F' →
      MulAut.congr (oTransport S ν hS) y • T F = T F' := by
    intro F F' hFF'
    rw [hT, ← familyTransport_smul, hFF']
  refine ⟨T C₁, T C₂, ?_, ?_⟩
  · rw [← hF]
    rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨e _ _ h1, e _ _ h2, e _ _ h3⟩
    · exact Or.inr ⟨e _ _ h1, e _ _ h2, e _ _ h3⟩
  · rw [← familyTransport_tsFam S ν hS, ← hU, hT, familyTransport_apply, familyTransport_apply,
      familyTransport_apply, Set.image_union]

include hS in
theorem D4Geom.transport (h : D4Geom Q) : D4Geom Q' := by
  intro z hz hzF
  obtain ⟨y, rfl⟩ := (MulAut.congr (oTransport S ν hS)).surjective z
  rw [MulEquiv.orderOf_eq] at hz
  exact (h y hz ((smul_ptFam_ne_iff S ν hS y).1 hzF)).transport S ν hS

include hS in
theorem PtRigid.transport (h : PtRigid Q) : PtRigid Q' := by
  intro L L' hLL'
  set M := pointTransport S⁻¹ ν⁻¹ (inv_similarity S ν hS) L with hM
  set M' := pointTransport S⁻¹ ν⁻¹ (inv_similarity S ν hS) L' with hM'
  have hL : pointTransport S ν hS M = L := Subtype.ext (subPerm_mul_inv S L.val)
  have hL' : pointTransport S ν hS M' = L' := Subtype.ext (subPerm_mul_inv S L'.val)
  have e : (subStab Q M.val).map (oTransport S ν hS).toMonoidHom =
      (subStab Q M'.val).map (oTransport S ν hS).toMonoidHom := by
    rw [subStab_map_oTransport, subStab_map_oTransport]
    change subStab Q' (pointTransport S ν hS M).val = subStab Q' (pointTransport S ν hS M').val
    rw [hL, hL', hLL']
  rw [← hL, ← hL', h M M' (Subgroup.map_injective (oTransport S ν hS).injective e)]

theorem congr_conj (x : StatedProj (matrixDerived Q)) :
    MulAut.congr (oTransport S ν hS) (MulAut.conj x) = MulAut.conj (oTransport S ν hS x) := by
  ext z
  simp [MulAut.conj_apply]

theorem Sit.transport {B : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    {t y : MulAut (StatedProj (matrixDerived Q))} (h : Sit Q B t y) :
    Sit Q' (B.map (MulAut.congr (oTransport S ν hS)).toMonoidHom)
      (MulAut.congr (oTransport S ν hS) t) (MulAut.congr (oTransport S ν hS) y) := by
  set Θ := oTransport S ν hS with hΘ
  refine ⟨fun x x' hxx' => ?_, ?_, ?_, ?_, h.geom.transport S ν hS, h.rigid.transport S ν hS⟩
  · obtain ⟨x, rfl⟩ := Θ.surjective x
    obtain ⟨x', rfl⟩ := Θ.surjective x'
    rw [← congr_conj, ← congr_conj] at hxx'
    rw [h.inj ((MulAut.congr Θ).injective hxx')]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Θ.surjective x
    exact ⟨MulAut.conj x, h.inn ⟨x, rfl⟩, congr_conj S ν hS x⟩
  · rw [← map_oddCoreIn_equiv]
    exact ⟨y, h.core, rfl⟩
  · exact (smul_ptFam_ne_iff S ν hS y).2 h.move

end Transport

theorem conj_smul_ptFam (x : StatedProj (matrixDerived Q)) :
    MulAut.conj x • ptFam Q = ptFam Q := by
  ext M
  constructor
  · rintro ⟨_, ⟨L, rfl⟩, rfl⟩
    refine ⟨⟨subAction Q x L.val, ?_, ?_⟩, ?_⟩
    · rw [← projectivePointAction_val]
      exact (projectivePointAction Q x L).2.1
    · rw [← projectivePointAction_val]
      exact (projectivePointAction Q x L).2.2
    · exact (subStab_map_conj Q x L.val).symm
  · rintro ⟨L, rfl⟩
    refine ⟨subStab Q (subAction Q x⁻¹ L.val), ⟨⟨subAction Q x⁻¹ L.val, ?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← projectivePointAction_val]
      exact (projectivePointAction Q x⁻¹ L).2.1
    · rw [← projectivePointAction_val]
      exact (projectivePointAction Q x⁻¹ L).2.2
    · change (subStab Q (subAction Q x⁻¹ L.val)).map (MulAut.conj x).toMonoidHom = _
      rw [subStab_map_conj, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Equiv.Perm.one_apply]

theorem commutator_smul_ptFam (y : MulAut (StatedProj (matrixDerived Q)))
    (x : StatedProj (matrixDerived Q)) :
    (y⁻¹ * (MulAut.conj x * y * (MulAut.conj x)⁻¹)) • ptFam Q = ptFam Q := by
  have h1 : y⁻¹ * MulAut.conj x * y = MulAut.conj (y⁻¹ x) := by
    ext z
    simp [MulAut.conj_apply]
  have e : y⁻¹ * (MulAut.conj x * y * (MulAut.conj x)⁻¹) =
      MulAut.conj (y⁻¹ x) * (MulAut.conj x)⁻¹ := by
    rw [← h1]
    group
  rw [e, mul_smul, ← map_inv, conj_smul_ptFam, conj_smul_ptFam]

theorem Sit.exists_commute [Finite K] {B : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    {t y : MulAut (StatedProj (matrixDerived Q))} (h : Sit Q B t y)
    {x : StatedProj (matrixDerived Q)} (hx : x * x = 1)
    (hxt : MulAut.conj x * t = t * MulAut.conj x) :
    ∃ y', Sit Q B t y' ∧ MulAut.conj x * y' = y' * MulAut.conj x := by
  set e := MulAut.conj x with he
  have hee : e * e = 1 := by rw [he, ← map_mul, hx, map_one]
  have heB : e ∈ B ⊓ centralizer ({t} : Set _) :=
    ⟨h.inn ⟨x, rfl⟩, mem_centralizer_singleton_iff.2 hxt⟩
  set u := y⁻¹ * (e * y * e⁻¹) with hu
  have huO : u ∈ oddCoreIn B t :=
    mul_mem (inv_mem h.core)
      (CFSG.ComponentClassification.Burgoyne.PSL.conj_mem_oddCoreIn h.core heB)
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem_oddCoreIn huO
  have hu1 : u ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one u
  have huN : u ∈ MulAction.stabilizer (MulAut (StatedProj (matrixDerived Q))) (ptFam Q) :=
    commutator_smul_ptFam y x
  set y' := y * u ^ (j + 1) with hy'
  have hφφ : ∀ z, e * (e * z * e⁻¹) * e⁻¹ = z := fun z => by
    calc e * (e * z * e⁻¹) * e⁻¹ = (e * e) * z * (e * e)⁻¹ := by group
      _ = z := by rw [hee]; group
  have heu : e * u * e⁻¹ = u⁻¹ := by
    rw [hu]
    calc e * (y⁻¹ * (e * y * e⁻¹)) * e⁻¹ = (e * y * e⁻¹)⁻¹ * (e * (e * y * e⁻¹) * e⁻¹) := by
          group
      _ = (e * y * e⁻¹)⁻¹ * y := by rw [hφφ]
      _ = (y⁻¹ * (e * y * e⁻¹))⁻¹ := by group
  have hpow : u * (u⁻¹) ^ (j + 1) = u ^ (j + 1) := by
    rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_add]
    calc u = u ^ (2 * j + 1) * u := by rw [hu1, one_mul]
      _ = u ^ (j + 1 + (j + 1)) := by
          rw [← pow_succ]
          congr 1
          ring
  have hcomm : e * y' * e⁻¹ = y' := by
    have h1 : e * y * e⁻¹ = y * u := by rw [hu]; group
    calc e * y' * e⁻¹ = (e * y * e⁻¹) * (e * u * e⁻¹) ^ (j + 1) := by
          rw [hy', ← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
      _ = y * (u * (u⁻¹) ^ (j + 1)) := by rw [h1, heu, mul_assoc]
      _ = y' := by rw [hpow]
  refine ⟨y', ⟨h.inj, h.inn, mul_mem h.core (pow_mem huO _), fun hF => h.move ?_, h.geom,
    h.rigid⟩, ?_⟩
  · have hpF : u ^ (j + 1) • ptFam Q = ptFam Q := pow_mem huN (j + 1)
    calc y • ptFam Q = y • (u ^ (j + 1) • ptFam Q) := by rw [hpF]
      _ = y' • ptFam Q := by rw [hy', mul_smul]
      _ = ptFam Q := hF
  · calc e * y' = e * y' * e⁻¹ * e := by group
      _ = y' * e := by rw [hcomm]

end CFSG.ComponentClassification.Burgoyne.D4
