module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenClosed
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

namespace AltGenCore

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
include s

theorem centralizer_pi0A_le (hGA : Asc76X.GoldschmidtTheoremA) {h8 : 2 * 4 ≤ n + 4}
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) :
    centralizer ({Φ (pi0A h8)} : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := Φ (pi0A h8) with he
  set C := centralizer ({e} : Set G) with hC
  set Ye := yeOf Φ h8 with hYe
  set Yp := Φ.range ⊔ centralizer (Φ.range : Set G) with hYp
  obtain ⟨S, hS, hYeS, hSY⟩ := s.exists_sylow_ye (h8 := h8) hN hF
  have he2 : e * e = 1 := e_mul_self
  have he1 : e ≠ 1 := fun h => pi0A_ne_one (s.injective (by rw [map_one]; exact h))
  have hYe2 : IsPGroup 2 Ye := IsPGroup.of_card (n := 3) (by rw [s.card_ye]; norm_num)
  have hQz : ∃ q ∈ Ye, q ∉ zpowers e := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show Ye ≤ zpowers e from h)
    rw [s.card_ye, Nat.card_zpowers] at h1
    have h2 : orderOf e ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq, he2]))
    omega
  have hcl := s.ye_closed (h8 := h8) hN hF hSY
  have hnc := qbarNoComponent_of hGA he2 he1 hS hYeS e_mem_ye (fun _ hx => ye_mul_self hx)
    (fun _ hx _ hy => ye_comm hx hy) hQz hcl (fun _ hx _ hy hx1 hy1 => ye_trans hx hy hx1 hy1)
    (fun _ hYP hPS hΩ => s.ye_mul_mem_of_omega hS.isPGroup (hS.le) hSY hYP hPS hΩ)
  have hCN := AS81.centralizer_le_normalizer_of_goldschmidt hGA (by rw [sq]; exact he2) hS hYeS
    e_mem_ye (fun x hx y hy => by
      rw [ye_comm hx hy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _) hcl hnc
  set O := AS76b.oddCoreIn C with hO
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn C
  have hYeC : Ye ≤ C := ye_le_centralizer
  have hOY : O ≤ Yp := by
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
      Nat.prime_two (A := veOf Φ h8) (X := O) isElemAbelian_ve (by rw [s.card_ve]; norm_num)
      ((ve_le_ye.trans hYeC).trans (AS76b.le_normalizer_oddCoreIn C))
      (Nat.coprime_two_left.mpr hOodd)
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    obtain ⟨ρ, hρ, rfl⟩ := exists_root_of_mem_ve ha ha1
    exact inf_le_right.trans (s.centralizer_root_le hN hρ)
  have hNY : ∀ c : G, c ∈ normalizer (Ye : Set G) → c ∈ Yp := by
    intro c hc
    obtain ⟨q, hq, hqz⟩ := hQz
    rw [mem_zpowers_iff_of_mul_self he2, not_or] at hqz
    obtain ⟨ρ, -, hρ, rfl⟩ := exists_root_of_mem_ye hq hqz.1 hqz.2
    exact s.mem_sup_of_conj_root_mem_of hN hF hρ
      (ye_le_sup ((mem_normalizer_iff.mp hc _).mp hq))
  have hYeO : Ye ≤ normalizer (O : Set G) := hYeC.trans (AS76b.le_normalizer_oddCoreIn C)
  have hMC : Ye ⊔ O ≤ C := sup_le hYeC (AS76b.oddCoreIn_le C)
  have hMY : Ye ⊔ O ≤ Yp := sup_le ye_le_sup hOY
  have hcardM : Nat.card ↥(Ye ⊔ O) = Nat.card Ye * Nat.card O := by
    have h := Asc76X.card_sup_mul_card_inf hYeO
    have hinf : Ye ⊓ O = ⊥ := by rw [inf_comm]; exact AS76b.oddCoreIn_inf_eq_bot hYe2
    rw [hinf, card_bot, mul_one] at h
    exact h
  have hsyl : ∀ S' : Subgroup G, S' ≤ Ye ⊔ O → IsPGroup 2 S' → Nat.card S' = Nat.card Ye →
      IsSylowOf 2 S' (Ye ⊔ O) := by
    intro S' hS'M hS'2 hS'card
    refine isSylowOf_iff.mpr ⟨hS'M, hS'2, ?_⟩
    have h := Subgroup.relIndex_mul_card S' (Ye ⊔ O)
    rw [inf_of_le_left hS'M, hS'card, hcardM, mul_comm (Nat.card Ye)] at h
    have hpos : 0 < Nat.card Ye := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_right hpos h]
    exact hOodd.not_two_dvd_nat
  intro c hc
  have hcM : c ∈ normalizer ((Ye ⊔ O : Subgroup G) : Set G) := hCN hc
  set S' := Ye.map (MulAut.conj c).toMonoidHom with hS'def
  have hS'M : S' ≤ Ye ⊔ O := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hcM y).mp (mem_sup_left hy)
  have hS'card : Nat.card S' = Nat.card Ye := card_map_of_injective (MulAut.conj c).injective
  obtain ⟨k, hkM, hk⟩ := IsSylowOf.exists_mem_conj (hsyl Ye le_sup_left hYe2 rfl)
    (hsyl S' hS'M (hYe2.map _) hS'card)
  have hkcN : k⁻¹ * c ∈ normalizer (Ye : Set G) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : c * y * c⁻¹ ∈ S' := ⟨y, hy, rfl⟩
    have h2 := (hk _).mp h1
    show k⁻¹ * c * y * (k⁻¹ * c)⁻¹ ∈ Ye
    rwa [show k⁻¹ * c * y * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * y * c⁻¹) * k by group]
  rw [show c = k * (k⁻¹ * c) by group]
  exact mul_mem (hMY hkM) (hNY _ hkcN)

theorem typeTwoCentralizerAt_of (hGA : Asc76X.GoldschmidtTheoremA)
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) : TypeTwoCentralizerAt Φ := by
  intro π hπ
  have h8 : 2 * 4 ≤ n + 4 := by have := s.five_le; omega
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := pi0A h8) (τ := π)
    (by rw [cycleType_pi0A, hπ]) pi0A_mul_self pi0A_ne_one
  intro x hx
  set y := (Φ β)⁻¹ * x * Φ β with hy
  have hyc : y ∈ centralizer ({Φ (pi0A h8)} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have h1 : Φ π = Φ β * Φ (pi0A h8) * (Φ β)⁻¹ := by rw [← hβ, map_mul, map_mul, map_inv]
    rw [h1] at hx
    rw [hy]
    calc (Φ β)⁻¹ * x * Φ β * Φ (pi0A h8)
        = (Φ β)⁻¹ * (x * (Φ β * Φ (pi0A h8) * (Φ β)⁻¹)) * Φ β := by group
      _ = (Φ β)⁻¹ * ((Φ β * Φ (pi0A h8) * (Φ β)⁻¹) * x) * Φ β := by rw [hx]
      _ = Φ (pi0A h8) * ((Φ β)⁻¹ * x * Φ β) := by group
  have h2 := s.centralizer_pi0A_le hGA hN hF hyc
  have hβY : Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := mem_sup_left ⟨β, rfl⟩
  have h3 : x = Φ β * y * (Φ β)⁻¹ := by rw [hy]; group
  rw [h3]
  exact mul_mem (mul_mem hβY h2) (inv_mem hβY)

end AltGenCore

theorem altTypeTwoCentralizer (hGA : Asc76X.GoldschmidtTheoremA) : AltTypeTwoCentralizer := by
  intro G _ _ A R T g n Φ s hn IH π hπ
  exact s.typeTwoCentralizerAt_of hGA (s.normalizer_le (by omega))
    (s.rootFusionAt altRootFusion hn IH) π hπ

end CFSG.ComponentClassification.RankTwoAlt
