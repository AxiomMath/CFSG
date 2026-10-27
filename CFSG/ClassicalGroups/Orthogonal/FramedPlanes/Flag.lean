module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Geometry
public import CFSG.LieType.CurtisTits.TitsGeometry
import CFSG.RankThree.OrthogonalInvolutions.Witt
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.CurtisTits (IsFlag)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {ν : F} {n : ℕ}

private def frameSrc (S : Set (FrameVert Q ν n)) : S ⊕ S → V
  | Sum.inl x => x.1.u
  | Sum.inr x => x.1.w

private def frameDualSrc (S : Set (FrameVert Q ν n)) : S ⊕ S → V
  | Sum.inl x => x.1.w
  | Sum.inr x => x.1.u

private def frameTgt (ch : Fin n → FrameVert Q ν n) (S : Set (FrameVert Q ν n)) :
    S ⊕ S → V
  | Sum.inl x => (ch x.1.typ).u
  | Sum.inr x => (ch x.1.typ).w

private def frameDualTgt (ch : Fin n → FrameVert Q ν n) (S : Set (FrameVert Q ν n)) :
    S ⊕ S → V
  | Sum.inl x => (ch x.1.typ).w
  | Sum.inr x => (ch x.1.typ).u

private theorem frameTyp_ne {S : Set (FrameVert Q ν n)}
    (hS : IsFlag (frameGraph Q ν n) S) {x y : S} (hxy : x ≠ y) : x.1.typ ≠ y.1.typ := by
  have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  exact (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).1

private theorem polar_frameSrc_frameDualSrc [CharP F 2] {S : Set (FrameVert Q ν n)}
    [DecidableEq (S ⊕ S)] (hS : IsFlag (frameGraph Q ν n) S) (p q : S ⊕ S) :
    polar Q (frameSrc S p) (frameDualSrc S q) = if p = q then 1 else 0 := by
  classical
  rcases p with x | x <;> rcases q with y | y
  · by_cases hxy : x = y
    · subst hxy
      simp [frameSrc, frameDualSrc, x.1.polar_u_w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨-, h2, -, -⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      have hne : (Sum.inl x : S ⊕ S) ≠ Sum.inl y := fun h => hxy (Sum.inl_injective h)
      simp [frameSrc, frameDualSrc, h2, hne]
  · by_cases hxy : x = y
    · subst hxy
      simp [frameSrc, frameDualSrc,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x.1.u]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨h1, -, -, -⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      simp [frameSrc, frameDualSrc, h1]
  · by_cases hxy : x = y
    · subst hxy
      simp [frameSrc, frameDualSrc,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x.1.w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨-, -, -, h4⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      simp [frameSrc, frameDualSrc, h4]
  · by_cases hxy : x = y
    · subst hxy
      have hcomm : polar Q x.1.w x.1.u = 1 := by
        rw [polar_comm Q x.1.w x.1.u, x.1.polar_u_w]
      simp [frameSrc, frameDualSrc, hcomm]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨-, -, h3, -⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      have hne : (Sum.inr x : S ⊕ S) ≠ Sum.inr y := fun h => hxy (Sum.inr_injective h)
      simp [frameSrc, frameDualSrc, h3, hne]

private theorem polar_frameTgt_frameDualTgt [CharP F 2] {S : Set (FrameVert Q ν n)}
    [DecidableEq (S ⊕ S)] (hS : IsFlag (frameGraph Q ν n) S)
    {ch : Fin n → FrameVert Q ν n}
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j)) (p q : S ⊕ S) :
    polar Q (frameTgt ch S p) (frameDualTgt ch S q) = if p = q then 1 else 0 := by
  classical
  rcases p with x | x <;> rcases q with y | y
  · by_cases hxy : x = y
    · subst hxy
      simp [frameTgt, frameDualTgt, (ch x.1.typ).polar_u_w]
    · have htyp : x.1.typ ≠ y.1.typ := frameTyp_ne hS hxy
      obtain ⟨-, h2, -, -⟩ := (frameGraph_adj_iff.mp (hchadj x.1.typ y.1.typ htyp)).2
      have hne : (Sum.inl x : S ⊕ S) ≠ Sum.inl y := fun h => hxy (Sum.inl_injective h)
      simp [frameTgt, frameDualTgt, h2, hne]
  · by_cases hxy : x = y
    · subst hxy
      simp [frameTgt, frameDualTgt,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q (ch x.1.typ).u]
    · have htyp : x.1.typ ≠ y.1.typ := frameTyp_ne hS hxy
      obtain ⟨h1, -, -, -⟩ := (frameGraph_adj_iff.mp (hchadj x.1.typ y.1.typ htyp)).2
      simp [frameTgt, frameDualTgt, h1]
  · by_cases hxy : x = y
    · subst hxy
      simp [frameTgt, frameDualTgt,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q (ch x.1.typ).w]
    · have htyp : x.1.typ ≠ y.1.typ := frameTyp_ne hS hxy
      obtain ⟨-, -, -, h4⟩ := (frameGraph_adj_iff.mp (hchadj x.1.typ y.1.typ htyp)).2
      simp [frameTgt, frameDualTgt, h4]
  · by_cases hxy : x = y
    · subst hxy
      have hcomm : polar Q (ch x.1.typ).w (ch x.1.typ).u = 1 := by
        rw [polar_comm Q (ch x.1.typ).w (ch x.1.typ).u, (ch x.1.typ).polar_u_w]
      simp [frameTgt, frameDualTgt, hcomm]
    · have htyp : x.1.typ ≠ y.1.typ := frameTyp_ne hS hxy
      obtain ⟨-, -, h3, -⟩ := (frameGraph_adj_iff.mp (hchadj x.1.typ y.1.typ htyp)).2
      have hne : (Sum.inr x : S ⊕ S) ≠ Sum.inr y := fun h => hxy (Sum.inr_injective h)
      simp [frameTgt, frameDualTgt, h3, hne]

private theorem frameSrc_linearIndependent [CharP F 2] (S : Set (FrameVert Q ν n))
    (hS : IsFlag (frameGraph Q ν n) S) : LinearIndependent F (frameSrc S) := by
  classical
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (frameSrc S)
    (fun p => (polarBilin Q).flip (frameDualSrc S p)) ?_ ?_
  · intro p q hpq
    rw [LinearMap.flip_apply, polarBilin_apply_apply,
      polar_frameSrc_frameDualSrc hS q p, if_neg (Ne.symm hpq)]
  · intro p
    rw [LinearMap.flip_apply, polarBilin_apply_apply,
      polar_frameSrc_frameDualSrc hS p p, if_pos rfl]

private theorem frameTgt_linearIndependent [CharP F 2] {S : Set (FrameVert Q ν n)}
    (hS : IsFlag (frameGraph Q ν n) S) {ch : Fin n → FrameVert Q ν n}
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j)) :
    LinearIndependent F (frameTgt ch S) := by
  classical
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (frameTgt ch S)
    (fun p => (polarBilin Q).flip (frameDualTgt ch S p)) ?_ ?_
  · intro p q hpq
    rw [LinearMap.flip_apply, polarBilin_apply_apply,
      polar_frameTgt_frameDualTgt hS hchadj q p, if_neg (Ne.symm hpq)]
  · intro p
    rw [LinearMap.flip_apply, polarBilin_apply_apply,
      polar_frameTgt_frameDualTgt hS hchadj p p, if_pos rfl]

private theorem Q_frameTgt_frameSrc (ch : Fin n → FrameVert Q ν n)
    (S : Set (FrameVert Q ν n)) (p : S ⊕ S) :
    Q (frameTgt ch S p) = Q (frameSrc S p) := by
  rcases p with x | x
  · dsimp only [frameTgt, frameSrc]
    rw [(ch x.1.typ).Q_u, x.1.Q_u]
  · dsimp only [frameTgt, frameSrc]
    rw [(ch x.1.typ).Q_w, x.1.Q_w]

private theorem polar_frameTgt_frameSrc_of_adj {ch : Fin n → FrameVert Q ν n}
    {x y : FrameVert Q ν n} (hxy : (frameGraph Q ν n).Adj x y)
    (hchxy : (frameGraph Q ν n).Adj (ch x.typ) (ch y.typ)) :
    polar Q (ch x.typ).u (ch y.typ).u = polar Q x.u y.u ∧
      polar Q (ch x.typ).u (ch y.typ).w = polar Q x.u y.w ∧
      polar Q (ch x.typ).w (ch y.typ).u = polar Q x.w y.u ∧
      polar Q (ch x.typ).w (ch y.typ).w = polar Q x.w y.w := by
  obtain ⟨h1s, h2s, h3s, h4s⟩ := (frameGraph_adj_iff.mp hxy).2
  obtain ⟨h1t, h2t, h3t, h4t⟩ := (frameGraph_adj_iff.mp hchxy).2
  exact ⟨by rw [h1t, h1s], by rw [h2t, h2s], by rw [h3t, h3s], by rw [h4t, h4s]⟩

private theorem polar_frameTgt_frameSrc_of_eq [CharP F 2] (ch : Fin n → FrameVert Q ν n)
    (x : FrameVert Q ν n) :
    polar Q (ch x.typ).u (ch x.typ).u = polar Q x.u x.u ∧
      polar Q (ch x.typ).u (ch x.typ).w = polar Q x.u x.w ∧
      polar Q (ch x.typ).w (ch x.typ).u = polar Q x.w x.u ∧
      polar Q (ch x.typ).w (ch x.typ).w = polar Q x.w x.w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q (ch x.typ).u,
      CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x.u]
  · rw [(ch x.typ).polar_u_w, x.polar_u_w]
  · rw [polar_comm Q (ch x.typ).w (ch x.typ).u, polar_comm Q x.w x.u,
      (ch x.typ).polar_u_w, x.polar_u_w]
  · rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q (ch x.typ).w,
      CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x.w]

private theorem polar_frameTgt_frameSrc [CharP F 2] {S : Set (FrameVert Q ν n)}
    (hS : IsFlag (frameGraph Q ν n) S) (ch : Fin n → FrameVert Q ν n)
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j)) (p q : S ⊕ S) :
    polar Q (frameTgt ch S p) (frameTgt ch S q) =
      polar Q (frameSrc S p) (frameSrc S q) := by
  classical
  rcases p with x | x <;> rcases q with y | y
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      exact (polar_frameTgt_frameSrc_of_eq ch x).1
    · exact (polar_frameTgt_frameSrc_of_adj
        (hS.2 x.2 y.2 (fun h => hxy (Subtype.ext h)))
        (hchadj x.1.typ y.1.typ (frameTyp_ne hS hxy))).1
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      exact (polar_frameTgt_frameSrc_of_eq ch x).2.1
    · exact (polar_frameTgt_frameSrc_of_adj
        (hS.2 x.2 y.2 (fun h => hxy (Subtype.ext h)))
        (hchadj x.1.typ y.1.typ (frameTyp_ne hS hxy))).2.1
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      exact (polar_frameTgt_frameSrc_of_eq ch x).2.2.1
    · exact (polar_frameTgt_frameSrc_of_adj
        (hS.2 x.2 y.2 (fun h => hxy (Subtype.ext h)))
        (hchadj x.1.typ y.1.typ (frameTyp_ne hS hxy))).2.2.1
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      exact (polar_frameTgt_frameSrc_of_eq ch x).2.2.2
    · exact (polar_frameTgt_frameSrc_of_adj
        (hS.2 x.2 y.2 (fun h => hxy (Subtype.ext h)))
        (hchadj x.1.typ y.1.typ (frameTyp_ne hS hxy))).2.2.2

private theorem exists_mem_orthogonalGroup_frameSrc_eq_frameTgt [CharP F 2]
    [FiniteDimensional F V] {S : Set (FrameVert Q ν n)}
    (hQ : (polarBilin Q).Nondegenerate) (ch : Fin n → FrameVert Q ν n)
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j))
    (hS : IsFlag (frameGraph Q ν n) S) :
    ∃ g : V ≃ₗ[F] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ∀ p : S ⊕ S, g (frameSrc S p) = frameTgt ch S p := by
  classical
  have : Fintype S := hS.1.fintype
  let k := Fintype.card (S ⊕ S)
  let e : S ⊕ S ≃ Fin k := Fintype.equivFin (S ⊕ S)
  let src : Fin k → V := fun i => frameSrc S (e.symm i)
  let tgt : Fin k → V := fun i => frameTgt ch S (e.symm i)
  have hsrc : LinearIndependent F src :=
    (frameSrc_linearIndependent S hS).comp e.symm e.symm.injective
  have htgt : LinearIndependent F tgt :=
    (frameTgt_linearIndependent hS hchadj).comp e.symm e.symm.injective
  have hQ' : ∀ i, Q (tgt i) = Q (src i) := fun i => Q_frameTgt_frameSrc ch S (e.symm i)
  have hpol' : ∀ i j, polar Q (tgt i) (tgt j) = polar Q (src i) (src j) :=
    fun i j => polar_frameTgt_frameSrc hS ch hchadj (e.symm i) (e.symm j)
  obtain ⟨g, hgO, hgmap⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
      (Q := Q) hQ src tgt hsrc htgt hQ' hpol'
  refine ⟨g, hgO, fun p => ?_⟩
  have h := hgmap (e p)
  simpa [src, tgt, Equiv.symm_apply_apply] using h

private theorem exists_mem_orthDerived_of_mem_orthogonalGroup [Finite F] [CharP F 2]
    [FiniteDimensional F V] {S : Set (FrameVert Q ν n)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {ch : Fin n → FrameVert Q ν n} {v : V} (hv : Q v ≠ 0)
    (hvch : ∀ j, polar Q v (ch j).u = 0 ∧ polar Q v (ch j).w = 0)
    {g : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ p : S ⊕ S, g (frameSrc S p) = frameTgt ch S p) :
    ∃ g' : V ≃ₗ[F] V, g' ∈ orthDerived Q ∧
      ∀ p : S ⊕ S, g' (frameSrc S p) = frameTgt ch S p := by
  classical
  by_cases hge : Even (finrank F (commSpace g))
  · exact ⟨g, CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hgO, hge⟩), hg⟩
  · have hodd : Odd (finrank F (commSpace g)) := Nat.not_even_iff_odd.mp hge
    let _ : Invertible (Q v) := invertibleOfNonzero hv
    let r : V ≃ₗ[F] V := TauCeti.QuadraticMap.reflection Q v
    have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
    have hrgO : r * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hrO hgO
    have hre : Even (finrank F (commSpace (r * g))) := by
      rw [← ZMod.natCast_eq_zero_iff_even,
        CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul (Q := Q) hQ hrO hgO,
        CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection (Q := Q) hQ v,
        (ZMod.natCast_eq_one_iff_odd).mpr hodd, Nat.cast_one]
      rfl
    have hfix : ∀ p : S ⊕ S, r (frameTgt ch S p) = frameTgt ch S p := fun p => by
      rcases p with x | x <;> dsimp only [r, frameTgt]
      · exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q v (hvch x.1.typ).1
      · exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q v (hvch x.1.typ).2
    refine ⟨r * g, CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hrgO, hre⟩), fun p => ?_⟩
    calc
      (r * g) (frameSrc S p) = r (g (frameSrc S p)) := rfl
      _ = r (frameTgt ch S p) := by rw [hg p]
      _ = frameTgt ch S p := hfix p

private theorem exists_mem_orthDerived_frameSrc_eq_frameTgt [Finite F] [CharP F 2]
    [FiniteDimensional F V] {S : Set (FrameVert Q ν n)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ch : Fin n → FrameVert Q ν n)
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j))
    {v : V} (hv : Q v ≠ 0) (hvch : ∀ j, polar Q v (ch j).u = 0 ∧ polar Q v (ch j).w = 0)
    (hS : IsFlag (frameGraph Q ν n) S) :
    ∃ g : V ≃ₗ[F] V, g ∈ orthDerived Q ∧
      ∀ p : S ⊕ S, g (frameSrc S p) = frameTgt ch S p := by
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_frameSrc_eq_frameTgt hQ ch hchadj hS
  exact exists_mem_orthDerived_of_mem_orthogonalGroup hQ hT hv hvch hgO hg

theorem flagTransitive_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ch : Fin n → FrameVert Q ν n) (hch : ∀ j, (ch j).typ = j)
    (hchadj : ∀ i j, i ≠ j → (frameGraph Q ν n).Adj (ch i) (ch j))
    {v : V} (hv : Q v ≠ 0) (hvch : ∀ j, polar Q v (ch j).u = 0 ∧ polar Q v (ch j).w = 0) :
    CFSG.LieType.CurtisTits.FlagTransitive ↥(orthDerived Q) (frameGraph Q ν n) ch := by
  classical
  intro S hS
  have : Fintype S := hS.1.fintype
  obtain ⟨g, hgD, hg⟩ :=
    exists_mem_orthDerived_frameSrc_eq_frameTgt hQ hT ch hchadj hv hvch hS
  refine ⟨⟨g, hgD⟩, fun x hx => ?_⟩
  have hu : g x.u = (ch x.typ).u := by
    simpa [frameSrc, frameTgt] using hg (Sum.inl ⟨x, hx⟩)
  have hw : g x.w = (ch x.typ).w := by
    simpa [frameSrc, frameTgt] using hg (Sum.inr ⟨x, hx⟩)
  have hEq : (⟨g, hgD⟩ : ↥(orthDerived Q)) • x = ch x.typ :=
    FrameVert.ext (hch x.typ).symm (by simpa using hu) (by simpa using hw)
  exact ⟨x.typ, hEq.symm⟩

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
