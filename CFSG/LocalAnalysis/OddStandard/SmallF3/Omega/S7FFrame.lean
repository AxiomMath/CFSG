module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

@[expose] def s7fKap (t x : G) : G := x * t * x⁻¹ * t⁻¹

@[expose] def s7fActs (φ : (Fin 5 → ZMod 2) → G) (h : G) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)

structure S7FFrame (t : G) (B E H : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) : Prop where
  t_mem : t ∈ E
  t_sq : t * t = 1
  t_not_mem : t ∉ B
  B_le : B ≤ E
  card_B : Nat.card B = 16
  comm_B : ∀ e ∈ E, ∀ b ∈ B, e * b = b * e
  sq_mem : ∀ e ∈ E, e * e ∈ B
  kap_mem : ∀ e ∈ E, s7fKap t e ∈ B
  kap_ker : ∀ e ∈ E, s7fKap t e = 1 → e ∈ B ∨ t * e ∈ B
  kap_surj : ∀ b ∈ B, ∃ e ∈ E, s7fKap t e = b
  H_E : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E
  H_t : ∀ h ∈ H, t⁻¹ * (h * t * h⁻¹) ∈ B
  perm : IsPermModuleVia IsEvenVec φ B H ⊤
  triv : ∀ h ∈ H, (∀ b ∈ B, h * b = b * h) → ∀ e ∈ E, e⁻¹ * (h * e * h⁻¹) ∈ B

end CFSG.OddStandard.SmallF3.Omega
