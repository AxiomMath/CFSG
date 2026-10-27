module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RD
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelMain
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RC

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

theorem card_eq_of_isDihedralTwoGroup {G : Type} [Group G] {P : Subgroup G} {n : ℕ}
    (h : IsDihedralTwoGroup ↥P n) : Nat.card ↥P = 2 ^ n := by
  obtain ⟨-, k, hk, -, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  omega

theorem thm1_L39core_of_rel (hP31a : Thm1P31a_rel) (h33c : B_thm1_L33c'_rel)
    (h33d : B_thm1_L33d_rel) (h34a : B_thm1_L34a_rel) (hL32 : B_thm1_L32'_rel)
    (hP31c : B_thm1_P31c_rel) (h37 : B_thm1_L37_rel) (h38 : B_thm1_L38_rel)
    (h3rd : B_thm1_L39_third_rel) : B_thm1_L39core_rel := by
  intro G _ _ hG hN x y K T V W f z cfg hsp hVW hnotA7 hle h5
  obtain ⟨hnc, hKnorm, hPT⟩ := hP31a G hG hN x y K cfg.hu2 h5
  obtain ⟨hdih, z', hz'P, -, -, hz'u⟩ := hPT T cfg.setup
  have hzP : z ∈ T ⊓ K := cfg.z_mem.1
  have hzz' : z = z' := by
    rcases hz'u z hzP (fun p hp => (cfg.z_mem.2.2 p hp.1).symm) with h | h
    · exfalso
      have h2 := cfg.z_mem.2.1
      rw [h, orderOf_one] at h2
      omega
    · exact h
  have hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
    intro w hw hc
    rw [hzz']
    exact hz'u w hw hc
  obtain ⟨⟨h37a, h37b⟩, h37c, h37d⟩ := h37 G hG hN x y K T V W f z cfg hsp hVW h5
  obtain ⟨S, a, P₀, f₁, hS, hTS, hTne, haS, haN, haT, ha2, hP₀, haP₀, hax, haz, hf₁, haf₁⟩ :=
    exists_frame cfg hnc hdih hzu h37b h37c h37d (fun S a hS hTS haS haN haT ha2 =>
      h38 G hG hN x y K T V W f z cfg hVW S a hS hTS haS haN haT ha2 h5)
  obtain ⟨⟨-, hcard⟩, ⟨hPgen, -⟩, -⟩ :=
    h38 G hG hN x y K T V W f z cfg hVW S a hS hTS haS haN haT ha2 h5
  have F : Frame39 x y K T V W f z S a P₀ f₁ :=
    ⟨cfg, hle, h37a, h37b, h37c, h37d, hcard, hPgen, hS, hTS, hTne, haS, haN, haT, ha2, hP₀, haP₀,
      hax, haz, hf₁, haf₁⟩
  have h8 : 8 ≤ Nat.card ↥(T ⊓ K) := by
    obtain ⟨n, hn3, hdn⟩ := hdih
    rw [card_eq_of_isDihedralTwoGroup hdn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  by_cases hJeq : pumpJ K f₁ = layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁)
  · exact F.false_of_sup_eq h33c h33d hL32 hG hN h5 hJeq
  · have hlt : layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁) < pumpJ K f₁ :=
      lt_of_le_of_ne (sup_le (Thm1.layerI_le_pumpJ K f₁) (Thm1.pPrimeCoreOf_le_self _))
        (Ne.symm hJeq)
    obtain ⟨w₁, hw₁, h5J, hcard'⟩ := F.exists_third_data h34a hL32 hP31c hG hN h5 hnotA7 h8 hlt
    exact F.false_of_third h38 h3rd hL32 hG hN h5 hnotA7 hKnorm hzu hlt hw₁ h5J hcard'

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
