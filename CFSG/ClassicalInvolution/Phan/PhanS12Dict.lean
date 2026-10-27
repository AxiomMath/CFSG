module

public import CFSG.ClassicalInvolution.Phan.PhanS12Plane
public import CFSG.ClassicalInvolution.Phan.PhanS11Iso
public import CFSG.ClassicalInvolution.Phan.PhanS6Dict

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan

section Dict

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))} (S : Setup M E D)
  (c₂ : GaloisField p (2 * f)) (hc : c₂ * D.τ c₂ = -1 / 4)

include S

theorem Setup.geom7_of_geomPt (gx gy gz : spinGroup (quadOdd 3 (GaloisField p f)))
    (hg : Std.GeomPt (stdModel D S.h2K) (ptIso S c₂ hc (gx : _)) (ptIso S c₂ hc (gy : _))
      (ptIso S c₂ hc (gz : _))) :
    Geom7 D (actK gx (vXi D)) (actK gy (vXi D)) (actK gz (vXi D)) := by
  obtain ⟨κx, hκx, hx⟩ := Std.FFPt.mk_rep (stdModel D S.h2K) (isFF_ptVec S c₂ hc gx)
  obtain ⟨κy, hκy, hy⟩ := Std.FFPt.mk_rep (stdModel D S.h2K) (isFF_ptVec S c₂ hc gy)
  obtain ⟨κz, hκz, hz⟩ := Std.FFPt.mk_rep (stdModel D S.h2K) (isFF_ptVec S c₂ hc gz)
  have hg' : Std.Geom (stdModel D S.h2K) (κx • ptVec S c₂ hc gx) (κy • ptVec S c₂ hc gy)
      (κz • ptVec S c₂ hc gz) := by
    rw [← hx, ← hy, ← hz]
    exact hg
  have h3 := (Std.geom_smul (stdModel D S.h2K) hκx hκy hκz).1 hg'
  have h4 := (geom_iff_geom7 D c₂ S.h2K hc _ _ _).1 h3
  rwa [Θ_ptVec, Θ_ptVec, Θ_ptVec] at h4

theorem Setup.geom_null2 (hb : PlaneBase E D) (hm : PlaneMove D) (h0 : PtStep0 E)
    (x y z : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2})
    (hxy : (ptGraph E).Adj x y) (hyz : (ptGraph E).Adj y z) (hzx : (ptGraph E).Adj z x)
    (hg : Std.GeomPt (stdModel D S.h2K) (ptIso S c₂ hc x) (ptIso S c₂ hc y)
      (ptIso S c₂ hc z)) :
    Null2 E h0 (.cons hxy (.cons hyz (.cons hzx .nil))) := by
  obtain ⟨gx, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨gy, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨gz, rfl⟩ := QuotientGroup.mk_surjective z
  have hg7 := S.geom7_of_geomPt c₂ hc gx gy gz hg
  rcases hg7.2.2.2 with hdet | hline
  · exact S.null2_plane hb hm h0 hxy hyz hzx hdet
  · exact S.null2_line h0 hxy hyz hzx (isFF7_actK D S.h2K gz (isFF7_vXi D S.h2K)) hline

noncomputable def Setup.dict (hb : PlaneBase E D) (hm : PlaneMove D) :
    PhanB3Dict (stdModel D S.h2K) E where
  step0 := ptStep0_of_model D S.good S.h2K S.h4 S.range S.n0 S.n1 S.tau
  edge := ptEdge_of_model D S.good S.h2K S.h4 S.range S.n0 S.n1 S.tau S.ord
  iso := ptIso S c₂ hc
  geom := fun x y z hxy hyz hzx hg =>
    S.geom_null2 c₂ hc hb hm _ x y z hxy hyz hzx hg

end Dict

end CFSG.ClassicalInvolution.PhanB3.S
