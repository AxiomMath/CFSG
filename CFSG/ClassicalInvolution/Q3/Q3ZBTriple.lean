module

public import CFSG.ClassicalInvolution.Q3.Q3ZBGen
public import CFSG.ClassicalInvolution.Q3.Q3ZBRigid

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane IsHyperbolicPlane
  longBlock planeGroup_stdPlane longInv)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

structure TripleMem {G : Type} [Group G] (Ω : Set (Subgroup G)) (A B X : StatedSp 2 F3 →* G)
    (Kp Kh Kr : Subgroup G) : Prop where
  injA : Function.Injective A
  injB : Function.Injective B
  injX : Function.Injective X
  mem_p : Kp ∈ Ω
  mem_h : Kh ∈ Ω
  mem_r : Kr ∈ Ω
  A0 : (planeGroup (stdPlane F3 2 0)).map A = Kp
  A1 : (planeGroup (stdPlane F3 2 1)).map A = Kh
  B0 : (planeGroup (stdPlane F3 2 0)).map B = Kh
  B1 : (planeGroup (stdPlane F3 2 1)).map B = Kr
  X0 : (planeGroup (stdPlane F3 2 0)).map X = Kp
  X1 : (planeGroup (stdPlane F3 2 1)).map X = Kr
  cA : ∀ a ∈ A.range, ∀ b ∈ Kr, a * b = b * a
  cB : ∀ a ∈ B.range, ∀ b ∈ Kp, a * b = b * a
  cX : ∀ a ∈ X.range, ∀ b ∈ Kh, a * b = b * a
  hub : ∀ x, A (longBlock F3 2 1 x) = B (longBlock F3 2 0 x)
  end_p : ∀ x, X (longBlock F3 2 0 x) = A (longBlock F3 2 0 x)
  end_r : ∀ x, X (longBlock F3 2 1 x) = B (longBlock F3 2 1 x)

section Unpack

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {A B X : StatedSp 2 F3 →* G}

theorem LayerTriple.exists_tripleMem (hL : LayerTriple Ω A B X) :
    ∃ Kp Kh Kr : Subgroup G, TripleMem Ω A B X Kp Kh Kr := by
  obtain ⟨Kp, Kh, Kr, h1, h2, h3, e1, e2, e3, e4, e5, e6, c1, c2, c3⟩ := hL.members
  exact ⟨Kp, Kh, Kr, hL.injA, hL.injB, hL.injX, h1, h2, h3, e1, e2, e3, e4, e5, e6, c1, c2, c3,
    hL.hub, hL.end_p, hL.end_r⟩

variable {Kp Kh Kr : Subgroup G} (hT : TripleMem Ω A B X Kp Kh Kr)

include hT

theorem TripleMem.hubX : IsHubLayer Ω Kh X :=
  ⟨hT.injX, hT.mem_h, hT.X0 ▸ hT.mem_p, hT.cX⟩

theorem TripleMem.hubA : IsHubLayer Ω Kr A :=
  ⟨hT.injA, hT.mem_r, hT.A0 ▸ hT.mem_p, hT.cA⟩

theorem TripleMem.hubB : IsHubLayer Ω Kp B :=
  ⟨hT.injB, hT.mem_p, hT.B0 ▸ hT.mem_h, hT.cB⟩

end Unpack

section Involutions

variable {G : Type} [Group G] {Λ : StatedSp 2 F3 →* G}

theorem longInv_ne_one (k : Fin 2) : longInv F3 2 k ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg (mat 2 F3) h) (Sum.inl k)) (Sum.inl k)
  simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longInv,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.inl_mem_coords] at h1
  exact one_ne_neg_one_f3 h1.symm

theorem isCentralInvolution_longInv (hΛ : Function.Injective Λ) (k : Fin 2) :
    IsCentralInvolution ((planeGroup (stdPlane F3 2 k)).map Λ) (Λ (longInv F3 2 k)) where
  mem := ⟨longInv F3 2 k, by
    rw [planeGroup_stdPlane]
    exact ⟨-1, rfl⟩, rfl⟩
  ne_one := fun h => longInv_ne_one k (hΛ (h.trans (map_one Λ).symm))
  sq := by rw [← map_mul, longInv_mul_self, map_one]
  central := by
    rintro _ ⟨y, hy, rfl⟩
    rw [planeGroup_stdPlane] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [← map_mul, ← map_mul, longInv_comm_lb]

end Involutions

section Dependent

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {A B X : StatedSp 2 F3 →* G} {Kp Kh Kr : Subgroup G}


theorem TripleMem.dependent (hctx : Ctx G K z) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A (longInv F3 2 0) * A (longInv F3 2 1) * B (longInv F3 2 1) = 1 := by
  have hr : B (longInv F3 2 1) = X (longInv F3 2 1) := (hT.end_r (-1)).symm
  have hp : X (longInv F3 2 0) = A (longInv F3 2 0) := hT.end_p (-1)
  have hzh : A (longInv F3 2 1) ∈ Kh := hT.A1 ▸ ⟨longInv F3 2 1, by
    rw [planeGroup_stdPlane]
    exact ⟨-1, rfl⟩, rfl⟩
  have hzr : X (longInv F3 2 1) ∈ Kr := hT.X1 ▸ ⟨longInv F3 2 1, by
    rw [planeGroup_stdPlane]
    exact ⟨-1, rfl⟩, rfl⟩
  have hc : A (longInv F3 2 0) * A (longInv F3 2 1) = A (negOne 2 F3) := by
    rw [← map_mul, negOne_two_eq]
  have hc' : X (longInv F3 2 0) * X (longInv F3 2 1) = X (negOne 2 F3) := by
    rw [← map_mul, negOne_two_eq]
  have hcomm : X (longInv F3 2 1) * A (longInv F3 2 1) = A (longInv F3 2 1) * X (longInv F3 2 1) :=
    hT.cX _ ⟨_, rfl⟩ _ hzh
  have hs : A (longInv F3 2 0) * A (longInv F3 2 1) * X (longInv F3 2 1) =
      X (negOne 2 F3) * A (longInv F3 2 1) := by
    rw [← hc', ← hp, mul_assoc, ← hcomm, ← mul_assoc]
  rw [hr]
  refine eq_one_of_centralizes_layers hctx hT.hubX hT.X0 hT.A0 hT.A1 ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [hc]
    have h1 : A x * A (negOne 2 F3) = A (negOne 2 F3) * A x := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 negOne_mem_center x]
    have h2 := hT.cA (A x) ⟨x, rfl⟩ _ hzr
    calc A x * (A (negOne 2 F3) * X (longInv F3 2 1))
        = (A x * A (negOne 2 F3)) * X (longInv F3 2 1) := by rw [mul_assoc]
      _ = A (negOne 2 F3) * (A x * X (longInv F3 2 1)) := by rw [h1, mul_assoc]
      _ = A (negOne 2 F3) * (X (longInv F3 2 1) * A x) := by rw [h2]
      _ = _ := (mul_assoc _ _ _).symm
  · rintro _ ⟨x, rfl⟩
    rw [hs]
    have h1 : X x * X (negOne 2 F3) = X (negOne 2 F3) * X x := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 negOne_mem_center x]
    have h2 := hT.cX (X x) ⟨x, rfl⟩ _ hzh
    calc X x * (X (negOne 2 F3) * A (longInv F3 2 1))
        = (X x * X (negOne 2 F3)) * A (longInv F3 2 1) := by rw [mul_assoc]
      _ = X (negOne 2 F3) * (X x * A (longInv F3 2 1)) := by rw [h1, mul_assoc]
      _ = X (negOne 2 F3) * (A (longInv F3 2 1) * X x) := by rw [h2]
      _ = _ := (mul_assoc _ _ _).symm

theorem TripleMem.negOne_layers (hctx : Ctx G K z) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    X (negOne 2 F3) = A (longInv F3 2 1) ∧ A (negOne 2 F3) = B (longInv F3 2 1) ∧
      B (negOne 2 F3) = A (longInv F3 2 0) := by
  have hd := hT.dependent hctx
  have hsq : ∀ (Λ : StatedSp 2 F3 →* G) (k : Fin 2),
      (Λ (longInv F3 2 k))⁻¹ = Λ (longInv F3 2 k) := fun Λ k => by
    rw [← map_inv, longInv_inv]
  have hr : X (longInv F3 2 1) = B (longInv F3 2 1) := hT.end_r (-1)
  have hp : X (longInv F3 2 0) = A (longInv F3 2 0) := hT.end_p (-1)
  have hh : B (longInv F3 2 0) = A (longInv F3 2 1) := (hT.hub (-1)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [negOne_two_eq, map_mul, hp, hr]
    have h1 : A (longInv F3 2 1) =
        (A (longInv F3 2 0))⁻¹ * (A (longInv F3 2 0) * A (longInv F3 2 1) * B (longInv F3 2 1)) *
          (B (longInv F3 2 1))⁻¹ := by group
    rw [hd, hsq, hsq] at h1
    rw [h1]
    group
  · rw [negOne_two_eq, map_mul]
    have h1 : A (longInv F3 2 0) * A (longInv F3 2 1) = (B (longInv F3 2 1))⁻¹ :=
      eq_inv_of_mul_eq_one_left hd
    rw [h1, hsq]
  · rw [negOne_two_eq, map_mul, hh]
    have h1 : A (longInv F3 2 1) * B (longInv F3 2 1) = (A (longInv F3 2 0))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc A (longInv F3 2 1) * B (longInv F3 2 1) * A (longInv F3 2 0)
          = (A (longInv F3 2 0))⁻¹ * (A (longInv F3 2 0) * A (longInv F3 2 1) *
            B (longInv F3 2 1)) * A (longInv F3 2 0) := by group
        _ = 1 := by rw [hd]; group
    rw [h1, hsq]

end Dependent

end CFSG.ClassicalInvolution.Q3.Q3ZB
