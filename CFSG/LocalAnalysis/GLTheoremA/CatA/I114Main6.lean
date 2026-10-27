module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem mem_range_of_hom {G H : Type} [Group G] [Group H] (f : G →* H) (m : G) :
    f m ∈ f.range :=
  MonoidHom.mem_range.2 ⟨m, rfl⟩

theorem contra_final [Finite Y] {B K P₀ : Subgroup Y} {x : Y}
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3)
    (hKK₂ : ElemCommute K (cj x K)) (hKK₃ : ElemCommute K (cj (x * x) K))
    (hmax : ∀ F : Subgroup Y, IsElemAbelian 3 F →
      (∃ W : Subgroup Y, W ≠ ⊥ ∧ IsPGroup 2 W ∧ F ≤ Subgroup.normalizer (W : Set Y)) →
      Nat.card F ≤ Nat.card B)
    (hBF : ∀ (H : Subgroup (MulAut ↥K)) (S : Subgroup ↥K), IsElemAbelian 3 H →
      Nat.card H = 9 → S ≠ ⊥ → IsPGroup 2 S →
      (∀ h ∈ H, S.map (MulEquiv.toMonoidHom h) = S) →
      ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ h ∈ H, U.map (MulEquiv.toMonoidHom h) = U) ∧
        ∃ y : ↥K, (∃ z : ↥K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
          y ∈ Subgroup.normalizer (U : Set ↥K) ∧ (∀ h ∈ H, h y = y) ∧
          ∃ α ∈ H, orderOf α = 3 ∧ ¬ ∃ k : ↥K, ∀ z : ↥K, α z = k * z * k⁻¹)
    (hH9 : Nat.card (HK K B) = 9)
    (hP₀K : P₀ ≤ K) (hP₀ne : P₀ ≠ ⊥) (hP₀p : IsPGroup 2 P₀)
    (hP₀n : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) → cj b P₀ = P₀) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHel := isElemAbelian_HK (K := K) hB
  have hcardB := card_B_eq hrel
  have hS'ne : P₀.subgroupOf K ≠ ⊥ := by
    intro h
    apply hP₀ne
    rw [eq_bot_iff]
    intro p hp
    have hpK : p ∈ K := hP₀K hp
    have hmem : (⟨p, hpK⟩ : ↥K) ∈ P₀.subgroupOf K := Subgroup.mem_subgroupOf.2 hp
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  have hS'p : IsPGroup 2 ↥(P₀.subgroupOf K) := by
    intro w
    have hw : (w.1 : Y) ∈ P₀ := Subgroup.mem_subgroupOf.1 w.2
    obtain ⟨n, hn⟩ := hP₀p ⟨(w.1 : Y), hw⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have hn' : (w.1 : Y) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    simpa using hn'
  have hS'inv : ∀ h ∈ HK K B,
      (P₀.subgroupOf K).map (MulEquiv.toMonoidHom h) = P₀.subgroupOf K := by
    intro h hh
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hh
    exact S'_invariant hP₀n m
  obtain ⟨U, hUne, hUp, hUinv, y, hyncK, hy3, hyN, hyfix, α, hαH, hα3, hαout⟩ :=
    hBF (HK K B) (P₀.subgroupOf K) hHel hH9 hS'ne hS'p hS'inv
  have hyK : (y : Y) ∈ K := y.2
  have hyncY : ∃ z ∈ K, z * (y : Y) ≠ (y : Y) * z := by
    obtain ⟨z, hz⟩ := hyncK
    exact ⟨z.1, z.2, fun h => hz (Subtype.ext h)⟩
  have hy3Y : orderOf (y : Y) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hy3
  have hUYK : U.map K.subtype ≤ K := Subgroup.map_subtype_le U
  have hUYne : U.map K.subtype ≠ ⊥ := by
    intro h
    apply hUne
    rw [eq_bot_iff]
    intro u hu
    have hmem : (u : Y) ∈ U.map K.subtype := Subgroup.mem_map_of_mem K.subtype hu
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  have hUYp : IsPGroup 2 ↥(U.map K.subtype) := by
    intro w
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.1 w.2
    obtain ⟨n, hn⟩ := hUp ⟨u, hu⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hu1 : u ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← huw, ← map_pow, hu1, map_one]
  have hyUY : cj (y : Y) (U.map K.subtype) = U.map K.subtype := by
    rw [cj_map_subtype, mem_normalizer_iff_cj.1 hyN]
  obtain ⟨m₀, hm₀⟩ := MonoidHom.mem_range.1 hαH
  have hm0B : (m₀ : Y) ∈ B := NBK_mem_B m₀
  have hm0N : (m₀ : Y) ∈ Subgroup.normalizer (K : Set Y) := NBK_mem_N m₀
  have hUinv' : ∀ m : ↥(NBK K B),
      U.map (MulEquiv.toMonoidHom (psiK K (NBK K B) (NBK_le_normalizer K B) m)) = U :=
    fun m => hUinv _ (mem_range_of_hom (psiK K (NBK K B) (NBK_le_normalizer K B)) m)
  have hU_m : cj (m₀ : Y) (U.map K.subtype) = U.map K.subtype := by
    apply cj_map_eq hm0N
    · exact hUinv' m₀
    · exact hUinv' m₀⁻¹
  have hfix0 : (m₀ : Y) * (y : Y) * (m₀ : Y)⁻¹ = (y : Y) := by
    have h := hyfix (psiK K (NBK K B) (NBK_le_normalizer K B) m₀) (mem_range_of_hom (psiK K (NBK K B) (NBK_le_normalizer K B)) m₀)
    have h2 : ((psiK K (NBK K B) (NBK_le_normalizer K B) m₀ y : ↥K) : Y) = (y : Y) :=
      congrArg Subtype.val h
    rw [psiK_apply] at h2
    exact h2
  have hαout' : ∀ k : ↥K, α ≠ MulAut.conj k := by
    intro k hk
    apply hαout
    exact ⟨k, fun z => by rw [hk, MulAut.conj_apply]⟩
  have hα3' : α ^ 3 = 1 := pow_three_of_orderOf hα3
  have hm0ne : (m₀ : Y) ≠ 1 := by
    intro h
    apply hαout' 1
    rw [← hm₀]
    have h1 : m₀ = 1 := Subtype.ext h
    rw [h1, map_one, map_one]
  have hm03 : (m₀ : Y) ^ 3 = 1 := hB.2 _ hm0B
  have hm0ord : orderOf (m₀ : Y) = 3 := orderOf_eq_prime hm03 hm0ne
  have hm0x : (m₀ : Y) * x = x * (m₀ : Y) := isElemAbelian_commute hB hm0B hxB
  have hm0y : (m₀ : Y) * (y : Y) = (y : Y) * (m₀ : Y) := by
    calc (m₀ : Y) * (y : Y) = ((m₀ : Y) * (y : Y) * (m₀ : Y)⁻¹) * (m₀ : Y) := by group
      _ = (y : Y) * (m₀ : Y) := by rw [hfix0]
  have hm0xx : (m₀ : Y) * (x * x) = (x * x) * (m₀ : Y) := by
    rw [← mul_assoc, hm0x, mul_assoc, hm0x, ← mul_assoc]
  have hm0y1 := comm_conj_gen hm0x hm0y
  have hm0y2 := comm_conj_gen hm0xx hm0y
  have hMs := ms_data hyK hKK₂ hKK₃
  have hy₁3 : orderOf (x * (y : Y) * x⁻¹) = 3 := orderOf_conj3 hy3Y x
  have hy₂3 : orderOf ((x * x) * (y : Y) * (x * x)⁻¹) = 3 := orderOf_conj3 hy3Y (x * x)
  have hnc₁ := noncentral_conj x hyncY
  have hnc₂ := noncentral_conj (x * x) hyncY
  have hEele : IsElemAbelian 3 (Eset x (y : Y)) :=
    isElemAbelian_sup (isElemAbelian_zpowers 3 (pow_three_of_orderOf hy3Y))
      (isElemAbelian_sup (isElemAbelian_zpowers 3 (pow_three_of_orderOf hy₁3))
        (isElemAbelian_zpowers 3 (pow_three_of_orderOf hy₂3)) hMs.1) hMs.2
  have hcE : ElemCommute (Subgroup.zpowers (m₀ : Y)) (Eset x (y : Y)) :=
    commutes_sup_right (zpowers_elemCommute_of hm0y)
      (commutes_sup_right (zpowers_elemCommute_of hm0y1) (zpowers_elemCommute_of hm0y2))
  have hB₀B : IsElemAbelian 3 (CBK K B) := isElemAbelian_mono hB (le_B_CBK K B)
  have hm0el : IsElemAbelian 3 (Subgroup.zpowers (m₀ : Y)) := isElemAbelian_zpowers 3 hm03
  have hB₀m0 : ElemCommute (CBK K B) (Subgroup.zpowers (m₀ : Y)) := by
    intro β hβ c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact isElemAbelian_commute hB (le_B_CBK K B hβ) (B.zpow_mem hm0B j)
  have hAele : IsElemAbelian 3 (CBK K B ⊔ Subgroup.zpowers (m₀ : Y)) :=
    isElemAbelian_sup hB₀B hm0el hB₀m0
  have hAE : ElemCommute (CBK K B ⊔ Subgroup.zpowers (m₀ : Y)) (Eset x (y : Y)) :=
    commutes_sup_left (B0_E_commute hB hxB hyK hKK₂ hKK₃) hcE
  have hFele : IsElemAbelian 3 (CBK K B ⊔ Subgroup.zpowers (m₀ : Y) ⊔ Eset x (y : Y)) :=
    isElemAbelian_sup hAele hEele hAE
  have hA_inter : CBK K B ⊓ Subgroup.zpowers (m₀ : Y) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgB, hgm⟩ := hg
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgm
    have hcg : Cent K g := (cent_CBK hB hxB hgB).1
    have hψ : psiK K (NBK K B) (NBK_le_normalizer K B) (m₀ ^ j) = 1 := by
      rw [psiK_eq_one_iff]
      intro k hk
      have hval : (((m₀ ^ j : ↥(NBK K B))) : Y) = g := by
        rw [Subgroup.coe_zpow, hj]
      rw [hval]
      exact (hcg k hk).symm
    have hαj : α ^ j = MulAut.conj (1 : ↥K) := by
      rw [← hm₀, ← map_zpow, hψ, map_one]
    have h3 := three_dvd_of_pow_eq_conj hα3' hαout' hαj
    have hj1 : (m₀ : Y) ^ j = 1 := by
      rw [zpow_eq_zpow_mod3 hm03 j]
      have hmod : j % 3 = 0 := by omega
      rw [hmod, zpow_zero]
    rw [Subgroup.mem_bot, ← hj]
    exact hj1
  have hAcard : Nat.card ↥(CBK K B ⊔ Subgroup.zpowers (m₀ : Y)) = 3 * Nat.card (CBK K B) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := CBK K B)
      (B := Subgroup.zpowers (m₀ : Y)) (commutes_normalizer hB₀m0)
    rw [hA_inter, Subgroup.card_bot, mul_one, Nat.card_zpowers, hm0ord] at h
    rw [h, mul_comm]
  have hEcard : Nat.card ↥(Eset x (y : Y)) = 27 :=
    card_E_eq hyK hKK₂ hKK₃ hy3Y hyncY hy₁3 hnc₁ hy₂3 hnc₂
  have hAE_inter : (CBK K B ⊔ Subgroup.zpowers (m₀ : Y)) ⊓ Eset x (y : Y) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgE⟩ := hg
    obtain ⟨β, hβ, c, hc, hgβc⟩ := mem_sup_of_commutes hB₀m0 g hgA
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hc
    obtain ⟨a, ha, mm, hmm, hgam⟩ := mem_sup_of_commutes hMs.2 g hgE
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
    have haK : a ∈ K := by
      rw [← hi]
      exact K.zpow_mem hyK i
    have hMsle : Subgroup.zpowers (x * (y : Y) * x⁻¹) ⊔
        Subgroup.zpowers ((x * x) * (y : Y) * (x * x)⁻¹) ≤ cj x K ⊔ cj (x * x) K :=
      sup_le_sup (Subgroup.zpowers_le.2 (conj_mem_cj x hyK))
        (Subgroup.zpowers_le.2 (conj_mem_cj (x * x) hyK))
    have hmK : Cent K mm := cent_of_elemCommute (commutes_sup_right hKK₂ hKK₃) (hMsle hmm)
    have hβK : Cent K β := (cent_CBK hB hxB hβ).1
    have hgn : g = β * (m₀ : Y) ^ j := by
      rw [hj]
      exact hgβc
    have hm0jN : (m₀ : Y) ^ j ∈ Subgroup.normalizer (K : Set Y) :=
      (Subgroup.normalizer (K : Set Y)).zpow_mem hm0N j
    have hαj : α ^ j = MulAut.conj (⟨a, haK⟩ : ↥K) := by
      rw [← hm₀, ← map_zpow]
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      rw [psiK_apply, Subgroup.coe_zpow, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact outer_key hβK hm0jN hmK k.2 hgn hgam
    have h3 := three_dvd_of_pow_eq_conj hα3' hαout' hαj
    have hj1 : (m₀ : Y) ^ j = 1 := by
      rw [zpow_eq_zpow_mod3 hm03 j]
      have hmod : j % 3 = 0 := by omega
      rw [hmod, zpow_zero]
    have hgβ : g = β := by
      rw [hgn, hj1, mul_one]
    have hgB0 : g ∈ CBK K B := by
      rw [hgβ]
      exact hβ
    obtain ⟨hgK, hgK₂, hgK₃⟩ := cent_CBK hB hxB hgB0
    rw [Subgroup.mem_bot]
    exact E_eq_one hyK hKK₂ hKK₃ hy3Y hyncY hy₁3 hnc₁ hy₂3 hnc₂ hgE hgK hgK₂ hgK₃
  have hFcard : Nat.card ↥(CBK K B ⊔ Subgroup.zpowers (m₀ : Y) ⊔ Eset x (y : Y)) =
      Nat.card ↥(CBK K B ⊔ Subgroup.zpowers (m₀ : Y)) * 27 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := CBK K B ⊔ Subgroup.zpowers (m₀ : Y))
      (B := Eset x (y : Y)) (commutes_normalizer hAE)
    rw [hAE_inter, Subgroup.card_bot, mul_one, hEcard] at h
    exact h
  have hUYW : U.map K.subtype ≤ WU x (U.map K.subtype) := le_trans le_sup_left le_sup_left
  have hWne : WU x (U.map K.subtype) ≠ ⊥ := by
    intro hW
    apply hUYne
    rw [hW] at hUYW
    exact le_bot_iff.1 hUYW
  have hU3 : ElemCommute (U.map K.subtype) (cj (x * x) (U.map K.subtype)) :=
    elemCommute_of_le hUYK (cj_mono (x * x) hUYK) hKK₃
  have hUx : ElemCommute (U.map K.subtype) (cj x (U.map K.subtype)) :=
    elemCommute_of_le hUYK (cj_mono x hUYK) hKK₂
  have hx3 : ElemCommute (cj x (U.map K.subtype)) (cj (x * x) (U.map K.subtype)) :=
    elemCommute_of_le (cj_mono x hUYK) (cj_mono (x * x) hUYK) (commute_K₂_K₃ hKK₂)
  have hWp : IsPGroup 2 ↥(WU x (U.map K.subtype)) :=
    isPGroup_sup (isPGroup_sup hUYp (isPGroup_cj hUYp x) hUx) (isPGroup_cj hUYp (x * x))
      (commutes_sup_left hU3 hx3)
  have hFnorm : CBK K B ⊔ Subgroup.zpowers (m₀ : Y) ⊔ Eset x (y : Y) ≤
      Subgroup.normalizer ((WU x (U.map K.subtype) : Subgroup Y) : Set Y) := by
    apply sup_le
    · apply sup_le
      · intro β hβ
        exact gen_B0 hB hxB (le_B_CBK K B hβ) (cent_CBK hB hxB hβ).1 hUYK
      · exact Subgroup.zpowers_le.2 (gen_m0 hB hxB hm0B hU_m)
    · apply sup_le
      · exact Subgroup.zpowers_le.2 (gen_y hKK₂ hKK₃ hyK hyUY hUYK)
      · apply sup_le
        · exact Subgroup.zpowers_le.2 (gen_y1 hKK₂ hKK₃ hyK hyUY hUYK)
        · exact Subgroup.zpowers_le.2 (gen_y2 hKK₂ hKK₃ hyK hyUY hUYK)
  have hmaxF := hmax _ hFele ⟨WU x (U.map K.subtype), hWne, hWp, hFnorm⟩
  rw [hFcard, hAcard, hcardB, hH9] at hmaxF
  have hc : 0 < Nat.card (CBK K B) := Nat.card_pos
  omega

end CFSG.LocalAnalysis.GLTheoremA.I114
