module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Frame

theorem fl3_center_eq_bot {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) {p0 f : ℕ} (hp02 : p0 ≠ 2)
    (hL : CFSG.Blueprint.LieModel (K ⧸ center K) .PSL 3 p0 f) : center K = ⊥ := by
  have hker : (QuotientGroup.mk' (center K)).ker = center K := QuotientGroup.ker_mk' _
  obtain ⟨-, hdvd⟩ := CFSG.LieType.Steinberg.odd_field_higher_linear_perfect_central_two_kernel_cyclic
    hp02 hq.1 (QuotientGroup.mk'_surjective (center K)) (by rw [hker]) (by rw [hker]; exact h2) hL
  rw [hker] at hdvd
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have h3 : Nat.card ↥(center K) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  rw [hn] at h3
  have hn0 : n = 0 := by
    by_contra hne
    have h2d : 2 ∣ 2 ^ n := dvd_pow_self 2 hne
    have : 2 ∣ 3 := h2d.trans h3
    omega
  rw [hn0, pow_zero] at hn
  exact (Subgroup.card_eq_one.mp hn)

variable {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}

theorem fl3_frame (hd : CellData zb p X) {p0 f : ℕ} (hp02 : p0 ≠ 2)
    (hL : CFSG.Blueprint.LieModel (↥(layer A) ⧸ center ↥(layer A)) .PSL 3 p0 f) :
    center ↥(layer A) = ⊥ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p0 ^ f ∧
      ∃ e : ↥(layer A) ≃* projectiveSL 3 F, ∃ α : MulAut (projectiveSL 3 F), α * α = 1 ∧ α ≠ 1 ∧
        ∀ k : ↥(layer A), e (layerAut zb k) = α (e k) := by
  have hZ2 : IsPGroup 2 ↥(center ↥(layer A)) := by
    rw [hd.Zcore]
    exact CFSG.pCore_isPGroup
  have hZ : center ↥(layer A) = ⊥ := fl3_center_eq_bot hd.quasi hZ2 hp02 hL
  refine ⟨hZ, ?_⟩
  obtain ⟨F, hFfield, hFfin, hcard, ⟨e0⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  obtain ⟨π, α, hπ, hker, hcomm, hαα⟩ :=
    exists_induced (layerAut zb) (layerAut_layerAut hd.z2) e0
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ center ↥(layer A) := by rw [← hker]; exact hx
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  refine ⟨F, hFfield, hFfin, hcard, MulEquiv.ofBijective π ⟨hinj, hπ⟩, α, ?_, ?_, ?_⟩
  · ext s
    rw [MulAut.mul_apply]
    exact hαα s
  · intro h1
    obtain ⟨k, hk, hne⟩ := hd.exists_not_commute
    apply hne
    have h3 := hcomm ⟨k, hk⟩
    rw [h1, MulAut.one_apply] at h3
    have h4 := hinj h3
    have h5 := congrArg Subtype.val h4
    rw [coe_layerAut] at h5
    have hzi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hd.z2
    rw [hzi] at h5
    calc zb * k = zb * k * zb * zb := by rw [mul_assoc (zb * k) zb zb, hd.z2, mul_one]
      _ = k * zb := by rw [h5]
  · intro k
    exact hcomm k

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
