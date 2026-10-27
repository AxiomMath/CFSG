module

public import CFSG.ClassicalInvolution.Asc77.AscC5OStmt
public import CFSG.ClassicalInvolution.Asc77.AscC25Y3
public import CFSG.ClassicalInvolution.Asc77.AscT7TInv

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Config

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure Ctx (Ω : Set (Subgroup G)) (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G)
    (z t u₁ u₂ a : G) : Prop where
  hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂
  haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haz : a ≠ z
  hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z
  hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z
  hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))
  hbad' : z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G))
  h5 : LayerOrthType p f Ω a 5 true
  h5' : LayerOrthType p f Ω (a * z) 5 true

end Config

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem hz2 (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : z * z = 1 := C.hyp.std.setting.hz.sq

theorem hz1 (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : z ≠ 1 := C.hyp.std.setting.hz.ne_one

theorem comm (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : a * z = z * a := C.hyp.hzS a C.haA.1

theorem mul_z_mul_z (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : a * z * z = a := by
  rw [mul_assoc, C.hz2, mul_one]

theorem haR (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : ∀ x ∈ R, a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp C.haA.2) x (Subgroup.mem_sup_left hx)).symm

theorem haR' (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : ∀ x ∈ R', a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp C.haA.2) x (Subgroup.mem_sup_right hx)).symm

theorem swap [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    Ctx p f Ω K K' W S R R' z t u₁ u₂ (a * z) := by
  have hzA := T7T.z_mem_centralizer_of_hyp C.hyp
  have hz2 := C.hz2
  have haz' := C.comm
  have hazz' := C.mul_z_mul_z
  refine ⟨C.hyp, Subgroup.mul_mem _ C.haA hzA, ?_, ?_, ?_, ?_, ?_, C.hbad', ?_, C.h5', ?_⟩
  · calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [haz']
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [C.ha2, hz2, one_mul]
  · intro h
    apply C.haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hz2]
  · intro h
    apply C.ha1
    calc a = (a * z) * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := by group
  · intro s hs
    have hszs : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [C.hyp.hzS s hs]
        _ = z := by group
    have hsa : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * z := by
      calc s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
        _ = (s * a * s⁻¹) * z := by rw [hszs]
    rcases C.hconj s hs with h | h
    · left; rw [hsa, h]
    · right; rw [hsa, h, hazz']
  · intro b hb
    rcases C.hA0 b hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [hazz', h])))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rw [hazz']; exact C.hbad
  · rw [hazz']; exact C.h5

theorem om5 [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    ∃ (hzY : z ∈ exactLayer Ω a) (hu₁Y : u₁ ∈ exactLayer Ω a) (hu₂Y : u₂ ∈ exactLayer Ω a),
      K ∈ tqMembers Ω a ∧ K' ∈ tqMembers Ω a ∧
      Om5Data p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
        (oddQuotientFamily (exactPair Ω a)) (T7H.exactImg Ω a K) (T7H.exactImg Ω a K')
        (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y) (T7H.toBar Ω a u₂ hu₂Y) := by
  classical
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -, -, htw⟩ :=
    C25X.layer_a_frame C.hyp C.ha2 C.ha1 C.haR C.haR'
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := C.h5
  refine ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hs.stand.odd, hs.stand.five, ⟨D, hD1, i₀, ?_⟩, htw, ?_⟩
  · rw [hDt, hDn]; exact hT
  · intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x]
    exact T7H.exactImg_mem (conjSub_mem_tqMembers hΩ.conjInvariant
      (exactLayer_le_centralizer Ω a x.2) hMtq)

end Ctx

end Basic

end CFSG.ClassicalInvolution.Asc77.C5O
