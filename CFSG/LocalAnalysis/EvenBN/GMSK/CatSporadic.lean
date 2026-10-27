module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicSmall
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicLarge
public import CFSG.LocalAnalysis.EvenBN.GMSK.SporadicONOuter
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open CFSG.Blueprint

theorem sporadicRep_fixedRoot
    {D : Type} [Group D] [Finite D] (hDs : IsSimpleGroup D)
    (hspor : NativeSporadic.SporadicRep D) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = 2 ^ n) (α : MulAut D) (hα : orderOf α = 2) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) (hr : FixedRootRankOne α S) :
    n = 2 ∧ (NativeSporadic.IsSporadic D .J1 ∨ NativeSporadic.IsSporadic D .M12) := by
  have h : IsRankOneFixedRoot n α S :=
    ⟨hn, hα, hSα, hSn, ⟨K, inferInstance, inferInstance, hK, hSK⟩, hr⟩
  obtain ⟨s, hs⟩ := hspor
  cases s with
  | J1 => exact ⟨j1_fixedRootFieldFour D hDs hs n α S h, Or.inl hs⟩
  | M12 => exact ⟨m12_fixedRootFieldFour D hDs hs n α S h, Or.inr hs⟩
  | M11 => exact (m11_fixedRootFree D hDs hs n α S h).elim
  | M22 => exact (m22_fixedRootFree D hDs hs n α S h).elim
  | M23 => exact (m23_fixedRootFree D hDs hs n α S h).elim
  | M24 => exact (m24_fixedRootFree D hDs hs n α S h).elim
  | J2 => exact (j2_fixedRootFree D hDs hs n α S h).elim
  | J3 => exact (j3_fixedRootFree D hDs hs n α S h).elim
  | J4 => exact (j4_fixedRootFree D hDs hs n α S h).elim
  | HS => exact (hs_fixedRootFree D hDs hs n α S h).elim
  | McL => exact (mcl_fixedRootFree D hDs hs n α S h).elim
  | He => exact (he_fixedRootFree D hDs hs n α S h).elim
  | Ru => exact (ru_fixedRootFree D hDs hs n α S h).elim
  | Suz => exact (suz_fixedRootFree D hDs hs n α S h).elim
  | ONan => exact (on_fixedRootFree D hDs hs n α S h).elim
  | Co1 => exact (co1_fixedRootFree D hDs hs n α S h).elim
  | Co2 => exact (co2_fixedRootFree D hDs hs n α S h).elim
  | Co3 => exact (co3_fixedRootFree D hDs hs n α S h).elim
  | Fi22 => exact (fi22_fixedRootFree D hDs hs n α S h).elim
  | Fi23 => exact (fi23_fixedRootFree D hDs hs n α S h).elim
  | Fi24Prime => exact (fi24prime_fixedRootFree D hDs hs n α S h).elim
  | HN => exact (hn_fixedRootFree D hDs hs n α S h).elim
  | Ly => exact (ly_fixedRootFree D hDs hs n α S h).elim
  | Th => exact (th_fixedRootFree D hDs hs n α S h).elim
  | B => exact (b_fixedRootFree D hDs hs n α S h).elim
  | M => exact (m_fixedRootFree D hDs hs n α S h).elim

theorem fixedRootSelector_sporadicRep :
    FixedRootSelector fun D _ => NativeSporadic.SporadicRep D := by
  intro D _ _ hD hspor n hn K _ _ hK α hα S hSα hSn hSK hr
  obtain ⟨h2, hJ | hM⟩ := sporadicRep_fixedRoot hD hspor hn K hK α hα S hSα hSn hSK hr
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, Or.inl hJ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, Or.inr (Or.inl hM)⟩)))

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
