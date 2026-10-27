module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om12

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ}
  {Ã : Subgroup ↥(orthDerived Q)}

theorem blockEnd_sub_mem_blockSpace [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane (orthImage Ã) p) (v : V) :
    blockEnd (orthImage Ã) hp hpF hAe t ht D v - v ∈ blockSpace (orthImage Ã) D.1 := by
  obtain ⟨a, b, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker (orthImage Ã) hp hpF hAe D) v
  have hxGa : blockEnd (orthImage Ã) hp hpF hAe t ht D (a : V) = (t D : V ≃ₗ[F] V) (a : V) :=
    blockEnd_apply_mem (orthImage Ã) hp hpF hAe t ht D a.2
  have hxGb : blockEnd (orthImage Ã) hp hpF hAe t ht D (b : V) = (b : V) :=
    blockEnd_apply_of_ker (orthImage Ã) hp hpF hAe t ht D b.2
  rw [map_add, hxGa, hxGb]
  have hgoal : ((t D : V ≃ₗ[F] V) (a : V) + (b : V)) - ((a : V) + (b : V)) =
      (t D : V ≃ₗ[F] V) (a : V) - (a : V) := by abel
  rw [hgoal]
  exact Submodule.sub_mem _ (blockSpace_invariant (orthImage Ã) hp hpF hAe a.2) a.2

theorem exists_restriction_mem_supportedFixedDerived
    {xD xE xG : V ≃ₗ[F] V} {B : Submodule F V}
    (hcommEG : Commute xE xG) (hcommGD : Commute xG xD)
    (hxGquad : ∀ v : V, Q (xG v) = Q v)
    (hxGsub : ∀ v : V, xG v - v ∈ B)
    (hxEfixB : ∀ v ∈ B, xE v = v)
    {xE' : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)}
    (hxE'coe : ∀ z : ↥(fixedSpace xD), ((xE' z : ↥(fixedSpace xD)) : V) = xE (z : V))
    (hxE'odd : OddOrderIsometry (Q.comp (fixedSpace xD).subtype) p xE')
    {xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')}
    (hxGZcoe : ∀ z : ↥(fixedSpace xE'),
      ((xGZ z : ↥(fixedSpace xE')) : ↥(fixedSpace xD)) = xG (z : ↥(fixedSpace xD)))
    (hxGZmem : xGZ ∈ orthDerived ((Q.comp (fixedSpace xD).subtype).comp
      (fixedSpace xE').subtype)) :
    ∃ xGW : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD),
      (∀ w : ↥(fixedSpace xD), ((xGW w : ↥(fixedSpace xD)) : V) = xG (w : V)) ∧
      xGW ∈ supportedFixedDerived (Q.comp (fixedSpace xD).subtype) xE' := by
  classical
  have hxG_W : ∀ w ∈ fixedSpace xD, xG w ∈ fixedSpace xD := by
    intro w hw
    have hwD : xD w = w := mem_fixedSpace.mp hw
    refine mem_fixedSpace.mpr ?_
    rw [← LinearEquiv.mul_apply, ← hcommGD.eq, LinearEquiv.mul_apply, hwD]
  have hxG_Winv : ∀ w ∈ fixedSpace xD, xG⁻¹ w ∈ fixedSpace xD := by
    intro w hw
    have hwD : xD w = w := mem_fixedSpace.mp hw
    have hc : Commute xG⁻¹ xD := hcommGD.inv_left
    refine mem_fixedSpace.mpr ?_
    rw [← LinearEquiv.mul_apply, ← hc.eq, LinearEquiv.mul_apply, hwD]
  let xGW : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD) :=
    restrictEquiv (fixedSpace xD) xG hxG_W hxG_Winv
  have hxGWcoe : ∀ w : ↥(fixedSpace xD), ((xGW w : ↥(fixedSpace xD)) : V) = xG (w : V) :=
    fun w => by dsimp only [xGW]; exact coe_restrictEquiv (fixedSpace xD) xG hxG_W hxG_Winv w
  have hxGW_fix_others : ∀ r ∈ othersSpace xE'.toLinearMap (X - 1), xGW r = r := by
    intro r hr
    obtain ⟨w, hw⟩ := othersSpace_le_range hxE'odd hr
    have hrw : (r : V) = xE (w : V) - (w : V) := by
      have h := congrArg (fun z : ↥(fixedSpace xD) => (z : V)) hw
      have h1 : ((xE' w : ↥(fixedSpace xD)) : V) = xE (w : V) := hxE'coe w
      have h2 : (((xE' w - w : ↥(fixedSpace xD)) : V)) =
          ((xE' w : ↥(fixedSpace xD)) : V) - (w : V) := rfl
      have h3 : (((xE'.toLinearMap - 1) w : ↥(fixedSpace xD)) : V) =
          ((xE' w - w : ↥(fixedSpace xD)) : V) := rfl
      rw [h3, h2, h1] at h
      exact h.symm
    have hdiffG : xG (w : V) - (w : V) ∈ B := hxGsub (w : V)
    have hfixG : xE (xG (w : V) - (w : V)) = xG (w : V) - (w : V) :=
      hxEfixB _ hdiffG
    have hxG_r : xG (r : V) = (r : V) := by
      rw [hrw]
      have hcx : xG (xE (w : V)) = xE (xG (w : V)) := by
        rw [← LinearEquiv.mul_apply, ← hcommEG.eq, LinearEquiv.mul_apply]
      calc xG (xE (w : V) - (w : V))
          = xG (xE (w : V)) - xG (w : V) := by rw [map_sub]
        _ = xE (xG (w : V)) - xG (w : V) := by rw [hcx]
        _ = xE ((xG (w : V) - (w : V)) + (w : V)) - xG (w : V) := by rw [sub_add_cancel]
        _ = (xE (xG (w : V) - (w : V)) + xE (w : V)) - xG (w : V) := by rw [map_add]
        _ = ((xG (w : V) - (w : V)) + xE (w : V)) - xG (w : V) := by rw [hfixG]
        _ = xE (w : V) - (w : V) := by abel
    apply Subtype.ext
    show ((xGW r : ↥(fixedSpace xD)) : V) = (r : V)
    rw [hxGWcoe]
    exact hxG_r
  have hxGW_cent : xGW ∈ isometryCentralizer (Q.comp (fixedSpace xD).subtype) xE' := by
    refine mem_isometryCentralizer.mpr ⟨fun w => ?_, fun w => ?_⟩
    · show Q ((xGW w : ↥(fixedSpace xD)) : V) = Q (w : V)
      rw [hxGWcoe]
      exact hxGquad (w : V)
    · apply Subtype.ext
      show ((xGW (xE' w) : ↥(fixedSpace xD)) : V) =
        ((xE' (xGW w) : ↥(fixedSpace xD)) : V)
      rw [hxGWcoe, hxE'coe, hxE'coe, hxGWcoe]
      rw [← LinearEquiv.mul_apply, ← hcommEG.eq, LinearEquiv.mul_apply]
  have hxGW_supp : xGW ∈ supportedBlock (Q.comp (fixedSpace xD).subtype) xE' (X - 1) :=
    mem_supportedBlock.mpr ⟨hxGW_cent, hxGW_fix_others⟩
  have hres_xGZ : (restrictFixed (Q.comp (fixedSpace xD).subtype) xE'
      ⟨xGW, hxGW_supp⟩ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')) = xGZ := by
    apply LinearEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_restrictFixed]
    dsimp only
    rw [hxGWcoe, hxGZcoe]
  refine ⟨xGW, hxGWcoe, ?_⟩
  refine mem_supportedFixedDerived.mpr ⟨hxGW_supp, ?_⟩
  rw [hres_xGZ]
  exact hxGZmem

private theorem blockEnd_mem_fixedSpace_of_ne [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p} (hDE : D ≠ E) :
    ∀ b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D),
      blockEnd (orthImage Ã) hp hpF hAe t ht E b ∈
        fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D) := by
  intro b hb
  have hc : Commute (blockEnd (orthImage Ã) hp hpF hAe t ht E)
      (blockEnd (orthImage Ã) hp hpF hAe t ht D) :=
    blockEnd_commute_of_ne (orthImage Ã) hp hpF hAe t ht hDE.symm
  refine mem_fixedSpace.mpr ?_
  rw [← LinearEquiv.mul_apply, ← hc.eq, LinearEquiv.mul_apply, mem_fixedSpace.mp hb]

private theorem commute_blockEnd_of_fix_block_of_restrict [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p} (hDE : D ≠ E)
    {j : V ≃ₗ[F] V} (hjfix : ∀ a ∈ blockSpace (orthImage Ã) D.1, j a = a)
    (hjW : ∀ b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D),
      j b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    (hxEW : ∀ b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D),
      blockEnd (orthImage Ã) hp hpF hAe t ht E b ∈
        fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    {Φ : (↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))}
    (hjΦ : ∀ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      j (b : V) = ((Φ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V))
    (hΦcomm : ∀ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      (((Φ (xE' b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) =
        (((xE' (Φ b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V))) :
    Commute j (blockEnd (orthImage Ã) hp hpF hAe t ht E) := by
  have hj_xE : ∀ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      j (blockEnd (orthImage Ã) hp hpF hAe t ht E (b : V)) =
        (((Φ (xE' b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) := by
    intro b
    have hbW : (⟨blockEnd (orthImage Ã) hp hpF hAe t ht E (b : V),
        hxEW b b.2⟩ :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) = xE' b :=
      Subtype.ext (hxE'coe b).symm
    calc j (blockEnd (orthImage Ã) hp hpF hAe t ht E (b : V))
        = ((Φ ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E (b : V), hxEW b b.2⟩ : V)) :=
            hjΦ ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E (b : V), hxEW b b.2⟩
      _ = (((Φ (xE' b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) := by
            rw [hbW]
  have hxE_j : ∀ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      blockEnd (orthImage Ã) hp hpF hAe t ht E
          (((Φ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) =
        (((xE' (Φ b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) :=
    fun b => (hxE'coe (Φ b)).symm
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, b, hab⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker (orthImage Ã) hp hpF hAe D) v
  let bW : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) := ⟨(b : V), by
    rw [fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht D]
    exact b.2⟩
  have hbW : (bW : V) = (b : V) := rfl
  rw [← hab, ← hbW]
  calc j (blockEnd (orthImage Ã) hp hpF hAe t ht E ((a : V) + (bW : V)))
      = j ((a : V) + blockEnd (orthImage Ã) hp hpF hAe t ht E (bW : V)) := by
          rw [map_add, blockEnd_apply_of_mem_block (orthImage Ã) hp hpF hAe t ht
            (D := E) (E := D) hDE a.2]
    _ = j (a : V) + j (blockEnd (orthImage Ã) hp hpF hAe t ht E (bW : V)) := by rw [map_add]
    _ = (a : V) + (((Φ (xE' bW) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) := by
          rw [hjfix a a.2]
          exact congrArg (fun z => (a : V) + z) (hj_xE bW)
    _ = (a : V) + (((xE' (Φ bW) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) := by
          rw [hΦcomm bW]
    _ = (a : V) + blockEnd (orthImage Ã) hp hpF hAe t ht E
          (((Φ bW : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) := by
          rw [hxE_j bW]
    _ = (a : V) + blockEnd (orthImage Ã) hp hpF hAe t ht E (j (bW : V)) := by rw [← hjΦ bW]
    _ = blockEnd (orthImage Ã) hp hpF hAe t ht E ((a : V) + j (bW : V)) := by
          rw [map_add]
          exact congrArg (fun z => z + blockEnd (orthImage Ã) hp hpF hAe t ht E
            (j (bW : V)))
            (blockEnd_apply_of_mem_block (orthImage Ã) hp hpF hAe t ht (D := E) (E := D)
              hDE a.2).symm
    _ = blockEnd (orthImage Ã) hp hpF hAe t ht E (j ((a : V) + (bW : V))) := by
          have h1 : j ((a : V) + (bW : V)) = j (a : V) + j (bW : V) := map_add _ _ _
          rw [h1, hjfix a a.2]
    _ = (blockEnd (orthImage Ã) hp hpF hAe t ht E * j) ((a : V) + (bW : V)) := rfl

private theorem commute_blockEnd_of_mem_supportedFixedDerived [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (hQ : (polarBilin Q).Nondegenerate)
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p} (hDE : D ≠ E)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    {J : Subgroup ↥(orthDerived Q)}
    (hJmem : ∀ j : ↥J,
      ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
        supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {Φ : ↥J →* (↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))}
    (hΦ_apply : ∀ (j : ↥J) (w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))),
      ((Φ j w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) (w : V))
    {L'J : Subgroup ↥J}
    (hL'J_cent : ∀ j : ↥J, j ∈ L'J →
      Φ j ∈ isometryCentralizer
        (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) xE')
    {j : ↥J} (hjL'J : j ∈ L'J) :
    Commute ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (blockEnd (orthImage Ã) hp hpF hAe t ht E) := by
  have hjSF : ((j : ↥J) : ↥(orthDerived Q)).val ∈
      supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D) := hJmem j
  have hjSupp : ((j : ↥J) : ↥(orthDerived Q)).val ∈
      supportedBlock Q (blockEnd (orthImage Ã) hp hpF hAe t ht D) (X - 1) :=
    supportedFixedDerived_le_supportedBlock hjSF
  have hfixD : ∀ a ∈ blockSpace (orthImage Ã) D.1, (j : V ≃ₗ[F] V) a = a := by
    intro a ha
    have h := (mem_supportedBlock.mp hjSupp).2
    rw [othersSpace_blockEnd_eq_blockSpace (orthImage Ã) hp hpF hAe hQ hQinv hB t ht D] at h
    exact h a ha
  have hpresW : ∀ b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D),
      (j : V ≃ₗ[F] V) b ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D) := by
    intro b hb
    have hc := commute_of_mem_supportedFixedDerived hjSF
    refine mem_fixedSpace.mpr ?_
    rw [← LinearEquiv.mul_apply, ← hc.eq, LinearEquiv.mul_apply, mem_fixedSpace.mp hb]
  have hΦj_comm : ∀ b : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      (((Φ j (xE' b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) =
        (((xE' (Φ j b) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) :=
    fun b => congrArg
      (fun w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) => (w : V))
      ((mem_isometryCentralizer.mp (hL'J_cent j hjL'J)).2 b)
  exact commute_blockEnd_of_fix_block_of_restrict hp hpF hAe t ht hDE hfixD hpresW
    (blockEnd_mem_fixedSpace_of_ne hp hpF hAe t ht hDE) hxE'coe
    (fun b => (hΦ_apply j b).symm) hΦj_comm

private theorem closure_pair_le_centralizer {xDK xEK jK : ↥(orthDerived Q)}
    (hcommD : Commute jK xDK) (hcommE : Commute jK xEK) :
    Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q)) ≤
      Subgroup.centralizer ({jK} : Set ↥(orthDerived Q)) := by
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  change z ∈ Subgroup.centralizer ({jK} : Set ↥(orthDerived Q))
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rcases hz with rfl | rfl
  · exact hcommD
  · exact hcommE

theorem layer_le_centralizer [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (hQ : (polarBilin Q).Nondegenerate)
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p} (hDE : D ≠ E)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    {J : Subgroup ↥(orthDerived Q)}
    (hJmem : ∀ j : ↥J,
      ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
        supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {Φ : ↥J →* (↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))}
    (hΦ_apply : ∀ (j : ↥J) (w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))),
      ((Φ j w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) (w : V))
    {L'J : Subgroup ↥J}
    (hL'J_cent : ∀ j : ↥J, j ∈ L'J →
      Φ j ∈ isometryCentralizer
        (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) xE')
    {L : Subgroup ↥(orthDerived Q)}
    (hLdef : L = L'J.map (Subgroup.subtype J))
    {DK EK : Subgroup ↥(orthDerived Q)} {xDK xEK : ↥(orthDerived Q)}
    (hxDH : blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthDerived Q)
    (hxEH : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthDerived Q)
    (hxDKdef : xDK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht D, hxDH⟩)
    (hxEKdef : xEK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩)
    (hJcent : J ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q))) (hxDKmem : xDK ∈ DK)
    (hEKdef : EK = Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q))) :
    L ≤ Subgroup.centralizer (EK : Set ↥(orthDerived Q)) := by
  classical
  subst xDK
  subst xEK
  let xDK : ↥(orthDerived Q) := ⟨blockEnd (orthImage Ã) hp hpF hAe t ht D, hxDH⟩
  let xEK : ↥(orthDerived Q) := ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩
  intro l hl
  rw [hLdef] at hl
  obtain ⟨j, hjL'J, rfl⟩ := Subgroup.mem_map.mp hl
  let jK : ↥(orthDerived Q) := (j : ↥J)
  have hcommD : Commute jK xDK := by
    have h := Subgroup.mem_centralizer_iff.mp (hJcent j.2) xDK hxDKmem
    exact h.symm
  have hcommE : Commute jK xEK := by
    apply Subtype.ext
    exact commute_blockEnd_of_mem_supportedFixedDerived hp hpF hAe hQ hQinv hB t ht hDE
      hxE'coe hJmem hΦ_apply hL'J_cent hjL'J
  have hEKle : EK ≤ Subgroup.centralizer ({jK} : Set ↥(orthDerived Q)) := by
    rw [hEKdef]
    exact closure_pair_le_centralizer hcommD hcommE
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hEKle hy) jK (Set.mem_singleton jK)).symm

theorem layer_normal
    (hp : p.Prime)
    {W : Submodule F V} {xE' : ↥W ≃ₗ[F] ↥W}
    (hxE'odd : OddOrderIsometry (Q.comp W.subtype) p xE')
    {J EK L : Subgroup ↥(orthDerived Q)}
    {L'SFD : Subgroup (↥W ≃ₗ[F] ↥W)} {Φ : ↥J →* (↥W ≃ₗ[F] ↥W)}
    {L'J : Subgroup ↥J}
    (hL'SFDdef : L'SFD = supportedFixedDerived (Q.comp W.subtype) xE')
    (hL'Jdef : L'J = L'SFD.comap Φ)
    (hL'J_mem : ∀ j : ↥J, j ∈ L'J → Φ j ∈ L'SFD)
    (hΦ_cent : ∀ y : ↥J, (y : ↥(orthDerived Q)) ∈
      Subgroup.centralizer (EK : Set ↥(orthDerived Q)) →
        Φ y ∈ isometryCentralizer (Q.comp W.subtype) xE')
    (hLdef : L = L'J.map (Subgroup.subtype J))
    (hLqOpen : CFSG.Open.IsQuasisimple ↥L) (hpdvdL : p ∣ Nat.card ↥L)
    (hLleJ : L ≤ J)
    (hLleCent : L ≤ Subgroup.centralizer (EK : Set ↥(orthDerived Q))) :
    GLAPLayer p (J ⊓ Subgroup.centralizer (EK : Set ↥(orthDerived Q))) ≠ ⊥ := by
  classical
  let Y : Subgroup ↥(orthDerived Q) := J ⊓ Subgroup.centralizer (EK : Set ↥(orthDerived Q))
  have hLleY : L ≤ Y := le_inf hLleJ hLleCent
  have hLnorm : (L.subgroupOf Y).Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hyJ : (y : ↥(orthDerived Q)) ∈ J := (Subgroup.mem_inf.mp y.2).1
    have hyC : (y : ↥(orthDerived Q)) ∈
        Subgroup.centralizer (EK : Set ↥(orthDerived Q)) := (Subgroup.mem_inf.mp y.2).2
    rw [hLdef] at hn
    obtain ⟨jn, hjnL'J, hjn⟩ := Subgroup.mem_map.mp hn
    let yJ : ↥J := ⟨(y : ↥(orthDerived Q)), hyJ⟩
    have hconj : ((y * n * y⁻¹ : ↥Y) : ↥(orthDerived Q)) = yJ * jn * yJ⁻¹ := by
      apply Subtype.ext
      change (y : V ≃ₗ[F] V) * (n : V ≃ₗ[F] V) * (y : V ≃ₗ[F] V)⁻¹ =
        (y : V ≃ₗ[F] V) * (jn : V ≃ₗ[F] V) * (y : V ≃ₗ[F] V)⁻¹
      rw [show (n : V ≃ₗ[F] V) = (jn : V ≃ₗ[F] V) from (congrArg Subtype.val hjn).symm]
    rw [hconj, hLdef]
    refine Subgroup.mem_map.mpr ⟨yJ * jn * yJ⁻¹, ?_, rfl⟩
    have hjnSFD : Φ jn ∈ supportedFixedDerived (Q.comp W.subtype) xE' := by
      rw [← hL'SFDdef]; exact hL'J_mem jn hjnL'J
    rw [hL'Jdef, Subgroup.mem_comap, map_mul, map_mul, map_inv, hL'SFDdef]
    exact hxE'odd.conj_mem_supportedFixedDerived (hΦ_cent yJ hyC) hjnSFD
  have hcompY : GLAPComponent p Y L :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hLqOpen hpdvdL hLleY hLnorm
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711.glaPLayer_ne_bot_of_glaPComponent
    hcompY

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
