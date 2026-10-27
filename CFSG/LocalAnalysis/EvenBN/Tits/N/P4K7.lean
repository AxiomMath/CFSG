module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K6
public import CFSG.Holt.Witt

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section PCore

variable {Γ : Type*} [Group Γ]

theorem pCoreOf_two_le (K : Subgroup Γ) : pCoreOf 2 K ≤ K := Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf_two (K : Subgroup Γ) : IsPGroup 2 (pCoreOf 2 K) :=
  CFSG.pCore_isPGroup.map _

theorem conj_mem_pCoreOf_two {K : Subgroup Γ} {k : Γ} (hk : k ∈ K) {r : Γ} (hr : r ∈ pCoreOf 2 K) :
    k * r * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨o', ho', rfl⟩ := hr
  exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem le_pCoreOf_two {K W : Subgroup Γ} (hWK : W ≤ K) (hWn : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hW2 : IsPGroup 2 W) : W ≤ pCoreOf 2 K := by
  have hnorm : (W.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hWn g g.2 n hn⟩
  have hp : IsPGroup 2 (W.subgroupOf K) := hW2.comap_subtype
  have h1 : W.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hnorm, hp⟩
  have h2 := Subgroup.map_mono (f := K.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hWK] at h2

end PCore

section K7

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem exists_V1_of_node09 (h09 : Node09 d z₀) : ∃ y₁, IsV1 d z₀ y₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, y₁, hy⟩ := h09
  exact ⟨y₁, hy⟩

theorem Us_le_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Us d ≤ Ks d :=
  le_inf ((le_sup_left : Us d ≤ U0s d).trans Subgroup.le_normalizer) (Us_le_Hs h49 hd hz h10)

theorem U0s_le_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    U0s d ≤ Ks d :=
  le_inf Subgroup.le_normalizer (U0s_le_Hs h49 hd hz h10)

theorem star_t_mem_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    star d d.t ∈ Ks d :=
  U0s_le_Ks h49 hd hz h10 (mem_sup_right (mem_zpowers _))

theorem exists_star_of_mem_Ks {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) : ∃ g ∈ Hg d, star d g = k := by
  obtain ⟨g, hg, -, hgk⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hk.2
  exact ⟨g, hg, hgk⟩

theorem star_conj_of_mem {g y : G} (hg : g ∈ Hg d) (hy : y ∈ Hg d) :
    star d (g * y * g⁻¹) = star d g * star d y * (star d g)⁻¹ := by
  rw [star_eq, star_eq, star_eq, actFun_mul d.s56V (mul_mem hg hy) (inv_mem hg),
    actFun_mul d.s56V hg hy, actFun_inv d.s56V hg]

theorem Ks_conj_DeltaS (h49 : d.Thm49Statement) (hd : d.Hyp) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d)
    {δ : MulAut ↥d.s56V} (hδ : δ ∈ DeltaS d) : k * δ * k⁻¹ ∈ DeltaS d := by
  obtain ⟨hδU, h, hh, hδh⟩ := hδ
  obtain ⟨g, hg, hgk⟩ := exists_star_of_mem_Ks hk
  refine ⟨(mem_normalizer_iff.1 hk.1 δ).1 hδU, g * h, mul_mem hg hh, ?_⟩
  have e : (g * h) * d.t * (g * h)⁻¹ = g * (h * d.t * h⁻¹) * g⁻¹ := by group
  have hht : h * d.t * h⁻¹ ∈ Hg d := mul_mem (mul_mem hh (t_mem_Hg h49 hd)) (inv_mem hh)
  rw [e, star_conj_of_mem hg hht, hgk, hδh]

theorem Ks_conj_tU (h49 : d.Thm49Statement) (hd : d.Hyp) (h18 : Node18 d) :
    ∀ k ∈ Ks d, ∀ u ∈ Us d, ∃ u' ∈ Us d, k * (star d d.t * u) * k⁻¹ = star d d.t * u' := by
  intro k hk u hu
  have hmem : star d d.t * u ∈ DeltaS d := by
    rw [h18.2.2.2]
    exact ⟨u, hu, rfl⟩
  have h2 := Ks_conj_DeltaS h49 hd hk hmem
  rw [h18.2.2.2] at h2
  obtain ⟨u', hu', h⟩ := h2
  exact ⟨u', hu', h.symm⟩

theorem Ks_trans_tU (h18 : Node18 d) :
    ∀ u ∈ Us d, ∃ k ∈ Ks d, k * star d d.t * k⁻¹ = star d d.t * u := by
  intro u hu
  have h1 : star d d.t ∈ DeltaS d := by
    rw [h18.2.2.2]
    exact ⟨1, (Us d).one_mem, mul_one _⟩
  have h2 : star d d.t * u ∈ DeltaS d := by
    rw [h18.2.2.2]
    exact ⟨u, hu, rfl⟩
  exact h18.2.2.1 _ h1 _ h2

theorem centralizer_Ks_le (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) (h17 : Node17 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    ∀ k ∈ Ks d, k * star d d.t = star d d.t * k →
      k ∈ zpowers (star d d.t) ⊔ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) := by
  intro k hk hkt
  obtain ⟨hF, hCe, -, -⟩ := C_data h49 hd hz h10 h17s hy
  rw [← hCe, h17.2.2.2.1]
  exact ⟨mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hkt.symm, hk.2⟩

theorem node19_W0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    Nat.card (Ks d) = 16 * 640 ∧ W0s d ≤ Ks d ∧ (∀ k ∈ Ks d, ∀ w ∈ W0s d, k * w * k⁻¹ ∈ W0s d) ∧
      IsPGroup 2 (W0s d) ∧ U0s d ≤ W0s d ∧ Nat.card (W0s d) = 512 ∧
      (∀ a ∈ W0s d, ∀ b ∈ W0s d, a * b * a⁻¹ * b⁻¹ ∈ U0s d) ∧ (∀ a ∈ W0s d, a * a ∈ U0s d) ∧
      (∀ w ∈ W0s d, w * star d d.t = star d d.t * w → w ∈ U0s d) ∧
      (∀ u ∈ Us d, ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = star d d.t * u) := by
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hCbot, hCt⟩ := C_data h49 hd hz h10 h17s hy
  have hPle : IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) ≤ Ks d := fun p hp =>
    C_le_Ks h49 hd hz h10 h17s hy (by rw [hCe]; exact mem_sup_right hp)
  have htU : ∀ u ∈ Us d, star d d.t * u = u * star d d.t := fun u hu =>
    hCt u (IsF20.U_le_Pgrp _ _ _ hu)
  have htnU : star d d.t ∉ Us d := by
    have := h17.2.2.2.2.2 1 (one_mem _)
    simpa using this
  obtain ⟨hKcard, W, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr, hWmax⟩ :=
    exists_W0 (K := Ks d) hF (star_t_mul_self h49 hd) htU htnU (Us_le_Ks h49 hd hz h10)
      (star_t_mem_Ks h49 hd hz h10) hPle hCt hCbot (fun k hk => hk.1) (Ks_conj_tU h49 hd h18)
      (Ks_trans_tU h18) (centralizer_Ks_le h49 hd hz h10 h17s h17 hy)
  have hWeq : W = W0s d := by
    apply le_antisymm
    · exact le_pCoreOf_two hWK hWst hW2
    · exact hWmax _ (pCoreOf_two_le _) (fun k hk m hm => conj_mem_pCoreOf_two hk hm)
        (isPGroup_pCoreOf_two _)
  subst hWeq
  exact ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩

theorem node19_card (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    ∀ T' : Subgroup (MulAut ↥d.s56V), fusionIsSylowIn 2 T' (img d (CMt d)) →
      Nat.card (Ks d) = Nat.card T' * 5 * 16 := by
  intro T' hT'
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hCbot, hCt⟩ := C_data h49 hd hz h10 h17s hy
  have htnU : star d d.t ∉ Us d := by
    have := h17.2.2.2.2.2 1 (one_mem _)
    simpa using this
  have hcardC : Nat.card ↥(img d (CMt d)) = 640 := by
    rw [hCe]
    exact card_zpowers_sup_Pgrp hF (star_t_mul_self h49 hd) htnU hCt hCbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := CFSG.Holt.card_eq_of_fusionIsSylowIn hT'
  have h640 : (Nat.factorization 640) 2 = 7 := by
    have h : (640 : ℕ) = 2 ^ 7 * 5 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 5)]
    simp
  rw [hcardC, h640] at hT
  have hK := (node19_W0 h49 hd hz h09 h10 h17s h17 h18).1
  rw [hK, hT]
  norm_num

end K7

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
