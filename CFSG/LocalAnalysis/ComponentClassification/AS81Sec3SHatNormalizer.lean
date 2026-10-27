module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatLift
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatConjX
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open Sec3Theta Census
open scoped Pointwise

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem smul_N0_of_comm_X0
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (m : ↥(nSHat Q₀ Q Zs)) (hcomm : hT.hN m * X0 = X0 * hT.hN m) : hT.hN m • N0 = N0 := by
  set xn : ↥(nSHat Q₀ Q Zs) := ⟨x, H.x_mem_nSHat⟩ with hxn
  have hk1 : hT.hN (m * xn * m⁻¹ * xn⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hT.hN_x, hcomm, mul_inv_cancel_right,
      mul_inv_cancel]
  have hk : ∀ s ∈ sec3SHat (Q₀ ⊔ Q) Zs,
      ((m : G) * x * (m : G)⁻¹ * x⁻¹) * s * ((m : G) * x * (m : G)⁻¹ * x⁻¹)⁻¹ * s⁻¹ ∈ Zs :=
    fun s hs => hT.comm_mem_of_hN_eq_one _ hk1 hs
  obtain ⟨s, hs, w, hw, hsx⟩ :=
    H.exists_conj_x h17 hinner hCBz hT.hΩ hT.hQF hT.hRc hT.hZQ m.2.1 hk
  set n' : ↥(nSHat Q₀ Q Zs) := ⟨s, mem_nSHat_of_mem_SHat hs⟩ * m with hn'def
  have hn' : hT.hN n' = hT.hN m := by
    rw [hn'def, map_mul, hT.hN_eq_one_of_mem_SHat hs, one_mul]
  have hfix : ∀ c ∈ B₀ ⊓ centralizer (Zs : Set G), ∀ hc : c ∈ nSHat Q₀ Q Zs,
      hT.hN ⟨c, hc⟩ • (hT.hN n' • N0) = hT.hN n' • N0 := by
    intro c hcB hc
    have h1 : hT.hN (n'⁻¹ * ⟨c, hc⟩ * n') • N0 = N0 :=
      hT.smul_N0_of_conj _ fun u hu =>
        H.conj_mem_U h17 hinner hCBz hT.hRc n'.2.1 hw hsx hcB.1 hcB.2 hu
    calc hT.hN ⟨c, hc⟩ • (hT.hN n' • N0) = hT.hN n' • (hT.hN (n'⁻¹ * ⟨c, hc⟩ * n') • N0) := by
          rw [smul_smul, smul_smul, ← map_mul, ← map_mul]
          congr 2
          group
      _ = hT.hN n' • N0 := by rw [h1]
  obtain ⟨c₃, hc₃, hc₃S, hB3⟩ := hT.exists_B3
  obtain ⟨c₅, hc₅, hc₅S, hB5⟩ := hT.exists_B5
  have h := eq_of_fixed_b (g := hT.hN n') (by rw [← hB3]; exact hfix c₃ hc₃ hc₃S)
    (by rw [← hB5]; exact hfix c₅ hc₅ hc₅S)
  rwa [hn'] at h

end ThetaHyp

end Sec38Hyp

theorem sec3SHatNormalizer_of
    (h17 : Step17G24Odd) : Sec3SHatNormalizer := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  obtain ⟨H, hΩ, hQF, hZQ, hRc⟩ := exists_sec38Hyp_SHat h17 hQ
  obtain ⟨-, ⟨τ, hτ⟩, -⟩ := exists_sec38Hyp_omega h17 hQ
  have hS := hQ.dData.suz
  have hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G) :=
    fun w hw => Sec3.exists_mem_sec3B_of_comm hS hτ.normB hτ.inv_x hw
  have hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ,
      k = b₀ * x ^ i :=
    fun k hk => Sec3.exists_mem_B₀_of_mem_centralizer hS hk
  obtain ⟨e, b, t, hT⟩ := H.exists_thetaHyp hΩ hQF hRc hZQ
  intro n hn
  have hall : ∀ k : ↥(nSHat Q₀ Q Zs), hT.hN k • N0 = N0 := fun k =>
    census hT.hN.range hT.G1_mem_range hT.G2_mem_range
      (by
        rintro _ ⟨m, rfl⟩ hcomm
        exact hT.smul_N0_of_comm_X0 h17 hinner hCBz m hcomm) ⟨k, rfl⟩
  have hnNU : n ∈ normalizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hT.conj_mem_U_of_smul ⟨n, hn⟩ (hall ⟨n, hn⟩) hu
  have hnz : n * z = z * n := (mem_centralizer_iff.mp hn.1 z H.z_mem_Zs).symm
  exact H.mem_N_of_mem_normalizer_U h17 hinner hCBz hZQ hnNU hnz

theorem sec3CentZNormalizes_of_sec3SHatNormal
    (h17 : Step17G24Odd) (h1 : Sec3SHatNormal) : Sec3CentZNormalizes :=
  sec3CentZNormalizes_of h17 h1 (sec3SHatNormalizer_of h17)

end CFSG.ComponentClassification.AS81
