module

public import CFSG.ClassicalInvolution.Q3.TL4OddCover
public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Case


variable {Y : Type} [Group Y]

@[expose] def LinkE4 (R : Subgroup Y) (t : Y) : Prop :=
  (∀ L ∈ restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)),
    ∀ L' ∈ restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)),
      ∃ g : ↥(omegaGen (coreLinkFam R t)), conjSub g L = L') ∧
    (∃ L ∈ restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)),
      (omegaNbr (restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t))) L).Nonempty) ∧
    (CoverSp4 ↥(omegaGen (coreLinkFam R t)) ∨ CoverSL4 ↥(omegaGen (coreLinkFam R t)))

end Case

section Frames

variable {Y : Type} [Group Y]

structure E4FrameAt (R : Subgroup Y) (t : Y) (J K' : Subgroup Y) (u x y x' : Y) : Prop where
  memJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  invJ : IsUniqueInvolution J u
  memK : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  memKJ : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J
  invK : IsUniqueInvolution K' (t * u)
  memx : x ∈ tightCore R
  memy : y ∈ J
  memx' : x' ∈ K'
  sqx : x * x = t
  sqy : y * y = u
  sqx' : x' * x' = t * u
  cxy : x * y = y * x
  cxx' : x * x' = x' * x
  cyx' : y * x' = x' * y
  notMem : x * y * x' ∉ Subgroup.closure ({t, u} : Set Y)
  invx : ∃ a : Y, a * x * a⁻¹ = x⁻¹ ∧ a * y = y * a ∧ a * x' = x' * a
  invy : ∃ b : Y, b * y * b⁻¹ = y⁻¹ ∧ b * x = x * b ∧ b * x' = x' * b

variable {R : Subgroup Y} {t : Y} {J K' : Subgroup Y} {u x y x' : Y}

theorem E4FrameAt.commute_t (hF : E4FrameAt R t J K' u x y x') :
    Commute t x ∧ Commute t y ∧ Commute t x' := by
  have hxy : Commute x y := hF.cxy
  have hxx' : Commute x x' := hF.cxx'
  rw [← hF.sqx]
  exact ⟨(Commute.refl x).mul_left (Commute.refl x), hxy.mul_left hxy, hxx'.mul_left hxx'⟩

theorem E4FrameAt.commute_u (hF : E4FrameAt R t J K' u x y x') :
    Commute u x ∧ Commute u y ∧ Commute u x' := by
  have hxy : Commute x y := hF.cxy
  have hyx' : Commute y x' := hF.cyx'
  have h1 : Commute y x := hxy.symm
  rw [← hF.sqy]
  exact ⟨h1.mul_left h1, (Commute.refl y).mul_left (Commute.refl y), hyx'.mul_left hyx'⟩

theorem E4FrameAt.comm_tu (hF : E4FrameAt R t J K' u x y x') : t * u = u * t := by
  obtain ⟨-, h, -⟩ := hF.commute_t
  have h2 : Commute t u := by
    rw [← hF.sqy]
    exact h.mul_right h
  exact h2

theorem E4FrameAt.comm_ts (hF : E4FrameAt R t J K' u x y x') :
    t * (x * y * x') = x * y * x' * t := by
  obtain ⟨h1, h2, h3⟩ := hF.commute_t
  exact (h1.mul_right h2).mul_right h3

theorem E4FrameAt.comm_us (hF : E4FrameAt R t J K' u x y x') :
    u * (x * y * x') = x * y * x' * u := by
  obtain ⟨h1, h2, h3⟩ := hF.commute_u
  exact (h1.mul_right h2).mul_right h3

theorem E4FrameAt.sq_s (hF : E4FrameAt R t J K' u x y x') (ht : t * t = 1) (hu : u * u = 1) :
    x * y * x' * (x * y * x') = 1 := by
  have ctu := hF.comm_tu
  calc x * y * x' * (x * y * x') = x * y * (x' * x) * (y * x') := by group
    _ = x * (y * x) * (x' * y) * x' := by rw [← hF.cxx']; group
    _ = x * x * (y * y) * (x' * x') := by rw [← hF.cxy, ← hF.cyx']; group
    _ = t * (u * t) * u := by rw [hF.sqx, hF.sqy, hF.sqx']; group
    _ = 1 := by rw [← ctu, ← mul_assoc, ht, one_mul, hu]

end Frames

section E8


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem E4FrameAt.isElemAbelian (hL : TightLargeHypR r n Y R S t)
    (hF : E4FrameAt R t J K' u x y x') :
    IsElemAbelian 2 (Subgroup.closure ({t, u, x * y * x'} : Set Y)) :=
  T8T.isElemAbelian_closure_three hL.datum.isUniqueInvolution_core.sq hF.invJ.sq
    (hF.sq_s hL.datum.isUniqueInvolution_core.sq hF.invJ.sq) hF.comm_tu hF.comm_ts hF.comm_us

theorem E4FrameAt.natCard (hL : TightLargeHypR r n Y R S t) (hF : E4FrameAt R t J K' u x y x') :
    Nat.card ↥(Subgroup.closure ({t, u, x * y * x'} : Set Y)) = 8 := by
  have ht := hL.datum.isUniqueInvolution_core
  have htu : t ≠ u := fun h =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (h ▸ hF.invJ))
  have hs1 : x * y * x' ≠ 1 := fun h => hF.notMem (h ▸ Subgroup.one_mem _)
  exact T8T.natCard_closure_three ht.sq hF.invJ.sq (hF.sq_s ht.sq hF.invJ.sq) hF.comm_tu
    hF.comm_ts hF.comm_us ht.ne_one hF.invJ.ne_one htu hs1 hF.notMem

end E8

end CFSG.ClassicalInvolution.Q3.TL4
