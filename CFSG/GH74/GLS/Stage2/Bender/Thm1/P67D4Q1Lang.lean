module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4InNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Class
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem normalizes_of_map {Y : Type*} [Group Y] {p : ℕ} (φ : Y ≃* Y) (E R : Subgroup Y)
    (hRp : IsPGroup p R) (hR1 : R ≠ ⊥)
    (h : E.map φ.toMonoidHom ≤ Subgroup.normalizer (R : Set Y)) :
    ∃ R' : Subgroup Y, IsPGroup p R' ∧ R' ≠ ⊥ ∧ E ≤ Subgroup.normalizer (R' : Set Y) := by
  have hmem : ∀ x : Y, x ∈ R.map φ.symm.toMonoidHom ↔ φ x ∈ R := fun x => by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      show φ (φ.symm r) ∈ R
      rw [MulEquiv.apply_symm_apply]
      exact hr
    · intro hx
      exact ⟨φ x, hx, MulEquiv.symm_apply_apply φ x⟩
  refine ⟨R.map φ.symm.toMonoidHom, hRp.map _, ?_, fun e he => ?_⟩
  · intro hbot
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R φ.symm.injective).1 hbot)
  · have h1 := Subgroup.mem_normalizer_iff.1 (h ⟨e, he, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    have h2 : φ x ∈ R ↔ φ e * φ x * (φ e)⁻¹ ∈ R := h1 (φ x)
    rw [map_mul, map_mul, map_inv]
    exact h2

theorem d4_toral_split_normalizes {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {y z : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hz : z ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hFy : twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f)
      y = z * y)
    (hyE : ∀ e ∈ E, y * triEmb K σ (AlgebraicClosure K) e * y⁻¹ ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K)) :
    ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R ∧ R ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hp : p.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hrange := triEmb_range (L := L) hp hf hK hσ Fr hFr
  have hM : ∀ x, weylQuotientHom TwistTag.D4.tag L
      ⟨1, one_mem (monomialSubgroup TwistTag.D4.tag L)⟩ • x =
      d4PermMat *ᵥ permLattice TwistTag.D4.perm.symm x := fun x => by
    have h1 : weylQuotientHom TwistTag.D4.tag L
        ⟨1, one_mem (monomialSubgroup TwistTag.D4.tag L)⟩ = 1 := map_one _
    rw [h1, one_smul, permLattice_symm_d4_eq, Matrix.mulVec_mulVec, d4PermMat_mul,
      Matrix.one_mulVec]
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust Fr hFr (one_mem (monomialSubgroup TwistTag.D4.tag L))
    d4PermMat hM (d4PermMat_sub_det_ne_zero hq2) (inv_mem hz)
  set F := twistHom TwistTag.D4 L Fr with hF
  have hFs : F s = s * z⁻¹ := by simpa using hs
  have hsG : s ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hsT
  have hy' : s * y ∈ adjointGroup TwistTag.D4.tag L := mul_mem hsG hy
  have hFy' : F (s * y) = s * y := by
    rw [map_mul, hFs, hFy]
    group
  have hy'r : s * y ∈ (triEmb K σ L).range := by
    rw [hrange]
    exact Subgroup.mem_inf.2 ⟨hy', hFy'⟩
  obtain ⟨y₀, hy₀⟩ := hy'r
  have hT : ∀ e₁ ∈ E.map (MulAut.conj y₀).toMonoidHom,
      (e₁ : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨e, he, rfl⟩
    have hadj : (((MulAut.conj y₀).toMonoidHom e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
        (graphFixedRootGroup_le _ _ _ ((MulAut.conj y₀).toMonoidHom e).2)).1
    refine Subgroup.mem_inf.2 ⟨?_, graphFixedRootGroup_le _ _ _ ((MulAut.conj y₀).toMonoidHom e).2⟩
    refine CFSG.RankThree.Classical2.mem_torusGroup_of_baseChangeGL_mem (algebraMap K L) hadj ?_
    have e1 : baseChangeGL (algebraMap K L)
        (((MulAut.conj y₀).toMonoidHom e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) =
        s * (y * triEmb K σ L e * y⁻¹) * s⁻¹ := by
      have h1 : triEmb K σ L ((MulAut.conj y₀).toMonoidHom e) =
          (s * y) * triEmb K σ L e * (s * y)⁻¹ := by
        rw [← hy₀]
        change triEmb K σ L (y₀ * e * y₀⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [show baseChangeGL (algebraMap K L)
        (((MulAut.conj y₀).toMonoidHom e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) = triEmb K σ L ((MulAut.conj y₀).toMonoidHom e) from rfl, h1]
      group
    rw [e1]
    exact mul_mem (mul_mem hsT (hyE e he)) (inv_mem hsT)
  obtain ⟨R, hRp, hR1, hER⟩ := d4_torus_plane_not_aniso hp hf K hK σ hσ _ hT
  exact normalizes_of_map (MulAut.conj y₀) E R hRp hR1 hER

end CFSG.GH74.GLS.Stage2.Bender.Thm1
