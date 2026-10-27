module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaAdapt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem ff_isPGroup_of_isElemAb2 {B : Subgroup G} {k : ℕ} (hB : IsElemAb2 B k) :
    IsPGroup 2 B := by
  intro g
  exact ⟨1, by apply Subtype.ext; simpa using hB.1.2 (g : G) g.2⟩

theorem ff_adapt_exists (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (fr : NFrame Q (Fin 6) 1) {U : Subgroup G} (hUL : U ≤ L) (hU : IsElemAb2 U 4) :
    ∃ y : ProjSim Q, ffImg (ff6mPhi (ffAdapt h2 e y)) U = ffB1 hQ fr := by
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hU2 : IsPGroup 2 U := ff_isPGroup_of_isElemAb2 hU
  have hE : IsElemAb2 (ffImg (ff6mPhi e) U) 4 :=
    (ff_cover_elemAb2_iff hφ hUL hU2 4).mp hU
  obtain ⟨y, hy⟩ := ff_star_E16_conj hQ hdim hsgn h2 fr hE
  exact ⟨y, ffImg_ffAdapt h2 e y U (ffB1 hQ fr) hy⟩

theorem ff_exists_model_B1 [Finite G] (h : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : NFrame Q (Fin 6) 1),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧ ffImg (ff6mPhi e) B = ffB1 hQ fr := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff6m_exists_model h
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  obtain ⟨y, hy⟩ := ff_adapt_exists hQ hdim hsgn h2 e (ff6m_odd_center h) fr hBL hB
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, ffAdapt h2 e y, fr, hdim, hsgn,
    hy⟩

end CFSG.OddStandard.SmallF3.Omega
