module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameGeometry
public import CFSG.LieType.CurtisTits.TitsGeometry

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open _root_.QuadraticMap
open Module
open CFSG.LieType.CurtisTits
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup commSpace
  finrank_commSpace_reflection natCast_finrank_commSpace_mul)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def frameSrc (S : Set FrameVert) : S ⊕ S → V 6
  | Sum.inl x => x.1.u
  | Sum.inr x => x.1.w

private def frameDualSrc (S : Set FrameVert) : S ⊕ S → V 6
  | Sum.inl x => x.1.w
  | Sum.inr x => x.1.u

private def frameTgt (ι : Fin 5 → Fin 6) (S : Set FrameVert) : S ⊕ S → V 6
  | Sum.inl x => Pi.single (Sum.inl (ι x.1.typ)) 1
  | Sum.inr x => Pi.single (Sum.inr (ι x.1.typ)) 1

private def frameIdx (ι : Fin 5 → Fin 6) (S : Set FrameVert) : S ⊕ S → Fin 6 ⊕ Fin 6
  | Sum.inl x => Sum.inl (ι x.1.typ)
  | Sum.inr x => Sum.inr (ι x.1.typ)

private theorem frameTyp_injective {S : Set FrameVert} (hS : IsFlag frameGraph S) :
    Function.Injective (fun x : S => x.1.typ) := by
  intro x y hxy
  by_contra hne
  have hval : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
  exact (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).1 hxy

private theorem frameIdx_injective {S : Set FrameVert} (hS : IsFlag frameGraph S)
    {ι : Fin 5 → Fin 6} (hι : Function.Injective ι) :
    Function.Injective (frameIdx ι S) := by
  intro p q hpq
  rcases p with x | x <;> rcases q with y | y
  · exact congrArg Sum.inl (frameTyp_injective hS (hι (Sum.inl_injective hpq)))
  · exact (Sum.inl_ne_inr hpq).elim
  · exact (Sum.inr_ne_inl hpq).elim
  · exact congrArg Sum.inr (frameTyp_injective hS (hι (Sum.inr_injective hpq)))

private theorem polar_frameSrc_frameDualSrc {S : Set FrameVert} [DecidableEq (S ⊕ S)]
    (hS : IsFlag frameGraph S) (p q : S ⊕ S) :
    polar (Q 6) (frameSrc S p) (frameDualSrc S q) = if p = q then 1 else 0 := by
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
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6) x.1.u]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨h1, -, -, -⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      simp [frameSrc, frameDualSrc, h1]
  · by_cases hxy : x = y
    · subst hxy
      simp [frameSrc, frameDualSrc,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6) x.1.w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨-, -, -, h4⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      simp [frameSrc, frameDualSrc, h4]
  · by_cases hxy : x = y
    · subst hxy
      have hcomm : polar (Q 6) x.1.w x.1.u = 1 := by
        rw [polar_comm (Q 6) x.1.w x.1.u, x.1.polar_u_w]
      simp [frameSrc, frameDualSrc, hcomm]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      obtain ⟨-, -, h3, -⟩ := (frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)).2
      have hne : (Sum.inr x : S ⊕ S) ≠ Sum.inr y := fun h => hxy (Sum.inr_injective h)
      simp [frameSrc, frameDualSrc, h3, hne]

private theorem frameSrc_linearIndependent {S : Set FrameVert} [Fintype S]
    (hS : IsFlag frameGraph S) : LinearIndependent (ZMod 2) (frameSrc S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hpair : ∀ i j : S ⊕ S,
      polar (Q 6) (frameSrc S i) (frameDualSrc S j) = if i = j then 1 else 0 :=
    polar_frameSrc_frameDualSrc hS
  have h0 := congrArg (fun z => (polarBilin (Q 6)).flip (frameDualSrc S p) z) hc
  simp only [map_sum, map_smul, LinearMap.flip_apply, polarBilin_apply_apply, hpair,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, map_zero] at h0
  exact h0

private theorem frameTgt_linearIndependent {S : Set FrameVert}
    (hS : IsFlag frameGraph S) {ι : Fin 5 → Fin 6} (hι : Function.Injective ι) :
    LinearIndependent (ZMod 2) (frameTgt ι S) := by
  have h' : LinearIndependent (ZMod 2)
      (fun p : S ⊕ S => (Pi.single (frameIdx ι S p) (1 : ZMod 2) : V 6)) := by
    simpa [Pi.basisFun_apply, Function.comp_def] using
      (Pi.basisFun (ZMod 2) (Fin 6 ⊕ Fin 6)).linearIndependent.comp
        (frameIdx ι S) (frameIdx_injective hS hι)
  have hfam : (fun p : S ⊕ S => (Pi.single (frameIdx ι S p) (1 : ZMod 2) : V 6)) =
      frameTgt ι S := by
    funext p
    rcases p with x | x <;> rfl
  rwa [hfam] at h'

private theorem Q_frameTgt_frameSrc {S : Set FrameVert} {ι : Fin 5 → Fin 6}
    (p : S ⊕ S) : Q 6 (frameTgt ι S p) = Q 6 (frameSrc S p) := by
  rcases p with x | x <;> simp [frameTgt, frameSrc, Q_single, x.1.Q_u, x.1.Q_w]

private theorem polar_frameTgt_frameSrc {S : Set FrameVert} (hS : IsFlag frameGraph S)
    {ι : Fin 5 → Fin 6} (hι : Function.Injective ι) (p q : S ⊕ S) :
    polar (Q 6) (frameTgt ι S p) (frameTgt ι S q) =
      polar (Q 6) (frameSrc S p) (frameSrc S q) := by
  classical
  rcases p with x | x <;> rcases q with y | y
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6)
          (Pi.single (Sum.inl (ι x.1.typ)) 1),
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6) x.1.u]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hadj := frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)
      have hιtyp : ι x.1.typ ≠ ι y.1.typ := fun h => hadj.1 (hι h)
      obtain ⟨h1, -, -, -⟩ := hadj.2
      dsimp only [frameTgt, frameSrc]
      rw [polar_single_single_of_planeOf_ne (n := 6) (by simpa [planeOf] using hιtyp), h1]
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      rw [polar_single_inl_inr (ι x.1.typ), x.1.polar_u_w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hadj := frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)
      have hιtyp : ι x.1.typ ≠ ι y.1.typ := fun h => hadj.1 (hι h)
      obtain ⟨-, h2, -, -⟩ := hadj.2
      dsimp only [frameTgt, frameSrc]
      rw [polar_single_single_of_planeOf_ne (n := 6) (by simpa [planeOf] using hιtyp), h2]
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      rw [polar_comm (Q 6) (Pi.single (Sum.inr (ι x.1.typ)) 1)
          (Pi.single (Sum.inl (ι x.1.typ)) 1),
        polar_comm (Q 6) x.1.w x.1.u, polar_single_inl_inr (ι x.1.typ), x.1.polar_u_w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hadj := frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)
      have hιtyp : ι x.1.typ ≠ ι y.1.typ := fun h => hadj.1 (hι h)
      obtain ⟨-, -, h3, -⟩ := hadj.2
      dsimp only [frameTgt, frameSrc]
      rw [polar_single_single_of_planeOf_ne (n := 6) (by simpa [planeOf] using hιtyp), h3]
  · by_cases hxy : x = y
    · subst hxy
      dsimp only [frameTgt, frameSrc]
      rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6)
          (Pi.single (Sum.inr (ι x.1.typ)) 1),
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero (Q 6) x.1.w]
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hadj := frameGraph_adj_iff.mp (hS.2 x.2 y.2 hval)
      have hιtyp : ι x.1.typ ≠ ι y.1.typ := fun h => hadj.1 (hι h)
      obtain ⟨-, -, -, h4⟩ := hadj.2
      dsimp only [frameTgt, frameSrc]
      rw [polar_single_single_of_planeOf_ne (n := 6) (by simpa [planeOf] using hιtyp), h4]

private theorem reflection_frameTgt {S : Set FrameVert} {ι : Fin 5 → Fin 6} {m : Fin 6}
    (hm : m ∉ Set.range ι) (p : S ⊕ S) :
    TauCeti.QuadraticMap.reflection (Q 6) (Pi.single (Sum.inl m) 1)
      (frameTgt ι S p) = frameTgt ι S p := by
  rcases p with x | x
  · have hne : planeOf (Sum.inl m) ≠ planeOf (Sum.inl (ι x.1.typ)) := by
      intro h
      exact hm ⟨x.1.typ, by simpa [planeOf] using h.symm⟩
    simpa [frameTgt] using
      TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero (Q 6) (Pi.single (Sum.inl m) 1)
        (polar_single_single_of_planeOf_ne (n := 6) hne)
  · have hne : planeOf (Sum.inl m) ≠ planeOf (Sum.inr (ι x.1.typ)) := by
      intro h
      exact hm ⟨x.1.typ, by simpa [planeOf] using h.symm⟩
    simpa [frameTgt] using
      TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero (Q 6) (Pi.single (Sum.inl m) 1)
        (polar_single_single_of_planeOf_ne (n := 6) hne)

private theorem exists_mem_omegaGroup_frameSrc_eq_frameTgt {S : Set FrameVert} [Fintype S]
    (hS : IsFlag frameGraph S) {ι : Fin 5 → Fin 6} (hι : Function.Injective ι) :
    ∃ g : Om 6, ∀ p : S ⊕ S,
      (g : V 6 ≃ₗ[ZMod 2] V 6) (frameSrc S p) = frameTgt ι S p := by
  classical
  let k := Fintype.card (S ⊕ S)
  let e : S ⊕ S ≃ Fin k := Fintype.equivFin (S ⊕ S)
  let src' : Fin k → V 6 := fun i => frameSrc S (e.symm i)
  let tgt' : Fin k → V 6 := fun i => frameTgt ι S (e.symm i)
  have hsrc' : LinearIndependent (ZMod 2) src' :=
    (frameSrc_linearIndependent hS).comp e.symm e.symm.injective
  have htgt' : LinearIndependent (ZMod 2) tgt' :=
    (frameTgt_linearIndependent hS hι).comp e.symm e.symm.injective
  have hQ' : ∀ i, Q 6 (tgt' i) = Q 6 (src' i) :=
    fun i => Q_frameTgt_frameSrc (S := S) (ι := ι) (e.symm i)
  have hpol' : ∀ i j, polar (Q 6) (tgt' i) (tgt' j) =
      polar (Q 6) (src' i) (src' j) :=
    fun i j => polar_frameTgt_frameSrc hS hι (e.symm i) (e.symm j)
  obtain ⟨g, hgO, hgmap⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
      (Q := Q 6) (nondegenerate_Q 6) src' tgt' hsrc' htgt' hQ' hpol'
  have hg : ∀ p : S ⊕ S, g (frameSrc S p) = frameTgt ι S p := by
    intro p
    have h := hgmap (e p)
    simpa [src', tgt', Equiv.symm_apply_apply] using h
  obtain ⟨m, hm⟩ : ∃ m : Fin 6, m ∉ Set.range ι := by
    by_contra! h
    have hsurj : Function.Surjective ι := fun y => Set.mem_range.mp (h y)
    have hcard := Fintype.card_le_of_surjective ι hsurj
    simp only [Fintype.card_fin] at hcard
    omega
  by_cases hge : Even (finrank (ZMod 2) (commSpace g))
  · exact ⟨⟨g, mem_omegaGroup.mpr ⟨hgO, hge⟩⟩, hg⟩
  · have hodd : Odd (finrank (ZMod 2) (commSpace g)) := Nat.not_even_iff_odd.mp hge
    let r : V 6 ≃ₗ[ZMod 2] V 6 :=
      TauCeti.QuadraticMap.reflection (Q 6) (Pi.single (Sum.inl m) 1)
    have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (Q 6) :=
      TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (Q 6) (Pi.single (Sum.inl m) 1)
    have hrgO : r * g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q 6) := mul_mem hrO hgO
    have heven : Even (finrank (ZMod 2) (commSpace (r * g))) := by
      dsimp only [r]
      rw [← ZMod.natCast_eq_zero_iff_even,
        natCast_finrank_commSpace_mul (Q := Q 6) (nondegenerate_Q 6) hrO hgO,
        finrank_commSpace_reflection (Q := Q 6) (nondegenerate_Q 6)
          (Pi.single (Sum.inl m) 1),
        (ZMod.natCast_eq_one_iff_odd).mpr hodd, Nat.cast_one]
      rfl
    refine ⟨⟨r * g, mem_omegaGroup.mpr ⟨hrgO, heven⟩⟩, fun p => ?_⟩
    have hfix := reflection_frameTgt (S := S) (ι := ι) (m := m) hm p
    calc
      (r * g) (frameSrc S p) = r (g (frameSrc S p)) := rfl
      _ = r (frameTgt ι S p) := by rw [hg p]
      _ = frameTgt ι S p := hfix

theorem flagTransitive_frameGraph {ι : Fin 5 → Fin 6} (hι : Function.Injective ι) :
    CFSG.LieType.CurtisTits.FlagTransitive ↥(Om 6) frameGraph (fun j => stdVert j (ι j)) := by
  classical
  intro S hS
  have : Fintype S := hS.1.fintype
  obtain ⟨g, hg⟩ := exists_mem_omegaGroup_frameSrc_eq_frameTgt hS hι
  refine ⟨g, fun x hx => ?_⟩
  have hu : (g : V 6 ≃ₗ[ZMod 2] V 6) x.u = Pi.single (Sum.inl (ι x.typ)) 1 := by
    have h := hg (Sum.inl ⟨x, hx⟩)
    simpa [frameSrc, frameTgt] using h
  have hw : (g : V 6 ≃ₗ[ZMod 2] V 6) x.w = Pi.single (Sum.inr (ι x.typ)) 1 := by
    have h := hg (Sum.inr ⟨x, hx⟩)
    simpa [frameSrc, frameTgt] using h
  have hEq : g • x = stdVert x.typ (ι x.typ) :=
    FrameVert.ext rfl (by simpa [stdVert] using hu) (by simpa [stdVert] using hw)
  exact ⟨x.typ, hEq.symm⟩

end CFSG.ClassicalGroups.Orthogonal.SixPlane
