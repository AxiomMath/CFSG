module

public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan

section Pts

variable {K : Type} [Field K] (M : Std.Model K)

theorem ffpt_mk_eq_iff {v w : Std.Vec K} (hv : Std.IsFF M v) (hw : Std.IsFF M w) :
    Std.FFPt.mk M hv = Std.FFPt.mk M hw ↔ ∃ a : K, a ≠ 0 ∧ a • w = v := by
  obtain ⟨c₁, hc₁, h₁⟩ := Std.FFPt.mk_rep M hv
  obtain ⟨c₂, hc₂, h₂⟩ := Std.FFPt.mk_rep M hw
  constructor
  · intro h
    have h3 : (Std.FFPt.mk M hv).1.rep = (Std.FFPt.mk M hw).1.rep := by rw [h]
    rw [h₁, h₂] at h3
    refine ⟨c₂ / c₁, div_ne_zero hc₂ hc₁, ?_⟩
    calc (c₂ / c₁) • w = c₁⁻¹ • (c₂ • w) := by rw [smul_smul, div_eq_inv_mul]
      _ = c₁⁻¹ • (c₁ • v) := by rw [h3]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  · rintro ⟨a, ha, hav⟩
    apply Subtype.ext
    refine (Projectivization.mk_rep _).symm.trans (Eq.trans ?_ (Projectivization.mk_rep _))
    refine (Projectivization.mk_eq_mk_iff' K _ _ (Projectivization.rep_nonzero _)
      (Projectivization.rep_nonzero _)).2 ⟨c₁ * a / c₂, ?_⟩
    rw [h₁, h₂, ← hav]
    simp only [smul_smul]
    congr 1
    exact div_mul_cancel₀ _ hc₂

end Pts

section Iso

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))} (S : Setup M E D)
  (c₂ : GaloisField p (2 * f)) (hc : c₂ * D.τ c₂ = -1 / 4)

@[expose] noncomputable def ptVec (g : spinGroup (quadOdd 3 (GaloisField p f))) :
    Std.Vec (GaloisField p (2 * f)) :=
  (ΘEquiv D c₂ S.h2K hc).symm (actK g (vXi D))

theorem Θ_ptVec (g : spinGroup (quadOdd 3 (GaloisField p f))) :
    ΘEquiv D c₂ S.h2K hc (ptVec S c₂ hc g) = actK g (vXi D) :=
  LinearEquiv.apply_symm_apply _ _

theorem isFF_ptVec (g : spinGroup (quadOdd 3 (GaloisField p f))) :
    Std.IsFF (stdModel D S.h2K) (ptVec S c₂ hc g) := by
  rw [isFF_iff_isFF7 D c₂ S.h2K hc, Θ_ptVec]
  exact isFF7_actK D S.h2K g (isFF7_vXi D S.h2K)

@[expose] noncomputable def ptFF (g : spinGroup (quadOdd 3 (GaloisField p f))) :
    Std.FFPt (stdModel D S.h2K) :=
  Std.FFPt.mk _ (isFF_ptVec S c₂ hc g)

theorem ptFF_eq_iff (g g' : spinGroup (quadOdd 3 (GaloisField p f))) :
    ptFF S c₂ hc g = ptFF S c₂ hc g' ↔ g⁻¹ * g' ∈ parab E {1, 2} := by
  rw [ptFF, ptFF, ffpt_mk_eq_iff, S.mem_parab_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    have h' := congrArg (ΘEquiv D c₂ S.h2K hc) h
    rw [map_smul, Θ_ptVec, Θ_ptVec] at h'
    refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
    have h3 : actK g⁻¹ (actK g (vXi D)) = actK g⁻¹ (a • actK g' (vXi D)) := by rw [h']
    rw [← actK_mul, inv_mul_cancel, actK_one, map_smul, ← actK_mul] at h3
    calc actK (g⁻¹ * g') (vXi D) = a⁻¹ • (a • actK (g⁻¹ * g') (vXi D)) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • vXi D := by rw [← h3]
  · rintro ⟨c, hc0, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
    apply (ΘEquiv D c₂ S.h2K hc).injective
    rw [map_smul, Θ_ptVec, Θ_ptVec]
    have h3 : actK g' (vXi D) = c • actK g (vXi D) := by
      have := congrArg (actK g) h
      rwa [← actK_mul, mul_inv_cancel_left, map_smul] at this
    rw [h3, smul_smul, inv_mul_cancel₀ hc0, one_smul]

@[expose] noncomputable def ptEquiv : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2} ≃
    Std.FFPt (stdModel D S.h2K) :=
  Equiv.ofBijective (fun q => Quotient.liftOn' q (ptFF S c₂ hc) (fun a b hab =>
    (ptFF_eq_iff S c₂ hc a b).2 (QuotientGroup.leftRel_apply.mp hab))) (by
    constructor
    · intro x y hxy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((ptFF_eq_iff S c₂ hc g h).1 hxy)
    · intro z
      obtain ⟨v, hv, rfl⟩ := Std.FFPt.exists_vec _ z
      have hΘ : IsFF7 D (ΘEquiv D c₂ S.h2K hc v) := (isFF_iff_isFF7 D c₂ S.h2K hc v).1 hv
      obtain ⟨g, c, hcne, hg⟩ := S.exists_move_xi hΘ
      refine ⟨(g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}), ?_⟩
      show ptFF S c₂ hc g = _
      rw [ptFF, ffpt_mk_eq_iff]
      refine ⟨c, hcne, ?_⟩
      apply (ΘEquiv D c₂ S.h2K hc).injective
      rw [map_smul, Θ_ptVec, hg])

theorem ptEquiv_mk (g : spinGroup (quadOdd 3 (GaloisField p f))) :
    ptEquiv S c₂ hc (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ptFF S c₂ hc g := rfl

@[expose] noncomputable def ptIso : ptGraph E ≃g Std.ffGraph (stdModel D S.h2K) where
  toEquiv := ptEquiv S c₂ hc
  map_rel_iff' := by
    intro x y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [ptEquiv_mk, ptEquiv_mk, ptFF, ptFF, Std.ffGraph_adj_mk, S.adj_iff_col7,
      col_iff_col7 D c₂ S.h2K hc, Θ_ptVec, Θ_ptVec]

end Iso

end CFSG.ClassicalInvolution.PhanB3.S
