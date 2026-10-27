module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarJ3

open CFSG.Open Subgroup

section Cfg

variable {G : Type} [Group G]

private theorem commute_facts {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    (∀ a ∈ W₁, ∀ b ∈ W₂, Commute a b) ∧ (∀ a ∈ W₁, ∀ c ∈ W₃, Commute a c) ∧
      (∀ b ∈ W₂, ∀ c ∈ W₃, Commute b c) := by
  have : IsMulCommutative V := hc.elem.1
  have hW₁V : W₁ ≤ V := by
    rw [hc.join]
    exact le_sup_left.trans le_sup_left
  have hW₂V : W₂ ≤ V := by
    rw [hc.join]
    exact le_sup_right.trans le_sup_left
  have hW₃V : W₃ ≤ V := by
    rw [hc.join]
    exact le_sup_right
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, Commute a b := fun a ha b hb =>
    (commute_iff_eq a b).mpr (setLike_mul_comm ha hb)
  exact ⟨fun a ha b hb => hcomm a (hW₁V ha) b (hW₂V hb),
    fun a ha c hc₃ => hcomm a (hW₁V ha) c (hW₃V hc₃),
    fun b hb c hc₃ => hcomm b (hW₂V hb) c (hW₃V hc₃)⟩

private theorem le_of_conj_of_mem {D W : Subgroup G} {t v a r : G}
    (hcard : Nat.card W = 3) (ha : a ∈ W) (ha1 : a ≠ 1)
    (hv : v = a * r) (hinv : t * a * t⁻¹ = a⁻¹) (hcent : t * r * t⁻¹ = r)
    (hvD : v ∈ D) (htvD : t * v * t⁻¹ ∈ D) : W ≤ D := by
  have hconj : t * v * t⁻¹ = a⁻¹ * r := by
    rw [hv]
    calc t * (a * r) * t⁻¹ = (t * a * t⁻¹) * (t * r * t⁻¹) := by group
      _ = a⁻¹ * r := by rw [hinv, hcent]
  have hsq : a ^ 2 ∈ D := by
    have hkey : v * (t * v * t⁻¹)⁻¹ = a ^ 2 := by
      rw [hconj, hv, pow_two]
      group
    have hmem : v * (t * v * t⁻¹)⁻¹ ∈ D := D.mul_mem hvD (D.inv_mem htvD)
    rwa [hkey] at hmem
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf a ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W ha
  rw [hcard] at hdvd
  have hne1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf a = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hpow : a ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
  have hzle : Subgroup.zpowers a ≤ W := Subgroup.zpowers_le.mpr ha
  have hcardz : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hWeq : W = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hzle (by simp [hcard, hcardz])).symm
  have haD : a ∈ D := by
    have h := D.pow_mem hsq 2
    have heq : (a ^ 2) ^ 2 = a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hpow, one_mul]
    rwa [heq] at h
  rw [hWeq]
  exact Subgroup.zpowers_le.mpr haD

theorem IsE27InvConfig.exists_centralizes_of_invariant {V W₁ W₂ W₃ : Subgroup G}
    {t₁ t₂ t₃ : G} (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {D : Subgroup G} (hDV : D ≤ V)
    (hD : D ≠ V) (hDt : ∀ t ∈ ({t₁, t₂, t₃} : Set G), ∀ x ∈ D, t * x * t⁻¹ ∈ D) :
    (∀ x ∈ D, t₁ * x = x * t₁) ∨ (∀ x ∈ D, t₂ * x = x * t₂) ∨ (∀ x ∈ D, t₃ * x = x * t₃) := by
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := commute_facts hc
  have hdec : ∀ v ∈ V, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, ∃ w₃ ∈ W₃, v = w₁ * w₂ * w₃ := by
    intro v hv
    have hcf3 : ∀ a ∈ W₁ ⊔ W₂, ∀ c ∈ W₃, Commute a c := by
      intro a ha c hc₃
      have hcent : W₃ ≤ Subgroup.centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) :=
        CFSG.le_centralizer_sup_of_commute_both h₁₂
          (fun a ha b hb => (h₁₃ b hb a ha).symm) (fun a ha b hb => (h₂₃ b hb a ha).symm)
      exact Subgroup.mem_centralizer_iff.mp (hcent hc₃) a ha
    obtain ⟨y, hy, w₃, hw₃, hvw⟩ := (CFSG.mem_sup_of_commute hcf3).mp (hc.join ▸ hv)
    obtain ⟨w₁, hw₁, w₂, hw₂, hyw⟩ := (CFSG.mem_sup_of_commute h₁₂).mp hy
    exact ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, by rw [← hvw, ← hyw]⟩
  have ht₁ : ∀ x ∈ D, t₁ * x * t₁⁻¹ ∈ D := hDt t₁ (by simp)
  have ht₂ : ∀ x ∈ D, t₂ * x * t₂⁻¹ ∈ D := hDt t₂ (by simp)
  have ht₃ : ∀ x ∈ D, t₃ * x * t₃⁻¹ ∈ D := hDt t₃ (by simp)
  have hc₁ : ∀ r ∈ W₂ ⊔ W₃, t₁ * r * t₁⁻¹ = r := fun r hr => by
    rw [hc.comm₁ r hr, mul_inv_cancel_right]
  have hc₂ : ∀ r ∈ W₁ ⊔ W₃, t₂ * r * t₂⁻¹ = r := fun r hr => by
    rw [hc.comm₂ r hr, mul_inv_cancel_right]
  have hc₃ : ∀ r ∈ W₁ ⊔ W₂, t₃ * r * t₃⁻¹ = r := fun r hr => by
    rw [hc.comm₃ r hr, mul_inv_cancel_right]
  have hW₁ : ∀ v ∈ D, ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, v = w₁ * w₂ * w₃ → w₁ ≠ 1 → W₁ ≤ D := by
    intro v hv w₁ hw₁ w₂ hw₂ w₃ hw₃ hvw hw1
    exact le_of_conj_of_mem hc.card₁ hw₁ hw1 (by rw [hvw, mul_assoc]) (hc.inv₁ w₁ hw₁)
      (hc₁ _ (mul_mem_sup hw₂ hw₃)) hv (ht₁ v hv)
  have hW₂ : ∀ v ∈ D, ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, v = w₁ * w₂ * w₃ → w₂ ≠ 1 → W₂ ≤ D := by
    intro v hv w₁ hw₁ w₂ hw₂ w₃ hw₃ hvw hw1
    refine le_of_conj_of_mem hc.card₂ hw₂ hw1 (r := w₁ * w₃) ?_ (hc.inv₂ w₂ hw₂)
      (hc₂ _ (mul_mem_sup hw₁ hw₃)) hv (ht₂ v hv)
    rw [hvw, (h₁₂ w₁ hw₁ w₂ hw₂).eq, mul_assoc]
  have hW₃ : ∀ v ∈ D, ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, v = w₁ * w₂ * w₃ → w₃ ≠ 1 → W₃ ≤ D := by
    intro v hv w₁ hw₁ w₂ hw₂ w₃ hw₃ hvw hw1
    refine le_of_conj_of_mem hc.card₃ hw₃ hw1 (r := w₁ * w₂) ?_ (hc.inv₃ w₃ hw₃)
      (hc₃ _ (mul_mem_sup hw₁ hw₂)) hv (ht₃ v hv)
    rw [hvw, ((h₁₃ w₁ hw₁ w₃ hw₃).mul_left (h₂₃ w₂ hw₂ w₃ hw₃)).eq]
  have hnot : ¬ W₁ ≤ D ∨ ¬ W₂ ≤ D ∨ ¬ W₃ ≤ D := by
    by_contra h
    push Not at h
    apply hD
    refine le_antisymm hDV ?_
    rw [hc.join]
    exact sup_le (sup_le h.1 h.2.1) h.2.2
  rcases hnot with h | h | h
  · left
    intro x hx
    obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, hxw⟩ := hdec x (hDV hx)
    have hw1 : w₁ = 1 := by
      by_contra hne
      exact h (hW₁ x hx w₁ hw₁ w₂ hw₂ w₃ hw₃ hxw hne)
    rw [hxw, hw1, one_mul]
    exact hc.comm₁ _ (mul_mem_sup hw₂ hw₃)
  · right; left
    intro x hx
    obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, hxw⟩ := hdec x (hDV hx)
    have hw1 : w₂ = 1 := by
      by_contra hne
      exact h (hW₂ x hx w₁ hw₁ w₂ hw₂ w₃ hw₃ hxw hne)
    rw [hxw, hw1, mul_one]
    exact hc.comm₂ _ (mul_mem_sup hw₁ hw₃)
  · right; right
    intro x hx
    obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, hxw⟩ := hdec x (hDV hx)
    have hw1 : w₃ = 1 := by
      by_contra hne
      exact h (hW₃ x hx w₁ hw₁ w₂ hw₂ w₃ hw₃ hxw hne)
    rw [hxw, hw1, mul_one]
    exact hc.comm₃ _ (mul_mem_sup hw₁ hw₂)

end Cfg

section J3

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.Quasithin

omit [Finite Y] in
private theorem false_of_inv_of_pow {t : Y} {W : Subgroup Y} {n : ℕ} (hW : Nat.card W = 3)
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (htn : t ^ 3 ^ n = 1) : False := by
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall W).mpr hcon, Subgroup.card_bot] at hW
    norm_num at hW
  have hinv' : t * w⁻¹ * t⁻¹ = w := by
    calc t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ := by group
      _ = w := by rw [hinv w hwW, inv_inv]
  have hcomm : Commute (t * t) w := by
    show t * t * w = w * (t * t)
    calc t * t * w = (t * (t * w * t⁻¹) * t⁻¹) * (t * t) := by group
      _ = w * (t * t) := by rw [hinv w hwW, hinv']
  obtain ⟨j, hj⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  have h1 : t ^ 3 ^ n * w * (t ^ 3 ^ n)⁻¹ = w⁻¹ := by
    rw [hj, pow_succ, pow_mul, pow_two]
    have hu : Commute ((t * t) ^ j) w⁻¹ := (hcomm.pow_left j).inv_right
    generalize (t * t) ^ j = u at hu ⊢
    calc u * t * w * (u * t)⁻¹ = u * (t * w * t⁻¹) * u⁻¹ := by group
      _ = w⁻¹ := by rw [hinv w hwW, hu.eq, mul_inv_cancel_right]
  rw [htn, one_mul, inv_one, mul_one] at h1
  have hw2 : w * w = 1 := by
    nth_rewrite 2 [h1]
    exact mul_inv_cancel w
  have hw3 : w ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard W hwW
    rw [hW] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  apply hw1
  calc w = w ^ 3 * (w * w)⁻¹ := by group
    _ = 1 := by rw [hw3, hw2, inv_one, mul_one]

theorem false_of_j3 (hJS : CFSG.AGLEmbedding.KFactJ3Sylow)
    (hJO : CFSG.AGLEmbedding.KFactJ3OuterInvolution) (hJR : CFSG.AGLEmbedding.KFactJ3OuterRank)
    {K : Subgroup Y} (hKn : K.Normal)
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hC : centralizer (K : Set Y) = ⊥) (T : Sylow 3 Y) {B : Subgroup Y}
    (hNB : normalizer ((T : Subgroup Y) : Set Y) ≤ B) (hne : B ≠ ⊤)
    {V W₁ W₂ W₃ : Subgroup Y} {t₁ t₂ t₃ : Y} (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃)
    (hVB : V ≤ B) (ht₁ : t₁ ∈ B) (ht₂ : t₂ ∈ B) (ht₃ : t₃ ∈ B) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hI := CFSG.AGLEmbedding.j3InSitu_of hJS hJO hJR hKn hK hC T hNB hne
  set T' : Subgroup Y := (T : Subgroup Y) with hT'
  have hBN : B ≤ normalizer (T' : Set Y) := hI.le_normalizer
  have := hKn
  have : Finite (MulAut K) := MulEquiv.finite_left
  obtain ⟨hOut2, -⟩ := hJR K hK
  have hOut3 : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    fun hd => by
      have := Nat.le_of_dvd Nat.card_pos hd
      omega
  have hTK : T' ≤ K := fun t ht => by
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    have h := CFSG.AGLEmbedding.mem_sup_centralizer_of_pow Nat.prime_three hOut3 (x := t)
      (n := n) (by simpa using congrArg Subtype.val hn)
    rwa [hC, sup_bot_eq] at h
  have hF : CFSG.AGLEmbedding.J3SylowFacts K (T'.subgroupOf K) := by
    have h := hJS K hK (T.subtype hTK)
    rwa [Sylow.coe_subtype] at h
  have hZmap : (centerOf (T'.subgroupOf K)).map K.subtype = centerOf T' := by
    rw [CFSG.AGLEmbedding.map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hTK]
  have hZe : IsElemAbelian 3 (centerOf T') :=
    hZmap ▸ CFSG.Open.IsElemAbelian.map hF.center_elem.1 K.subtype
  have hZc : Nat.card (centerOf T') = 9 := by
    rw [← hZmap, Subgroup.card_map_of_injective K.subtype_injective, hF.center_elem.2]
  have hVT : V ≤ T' := by
    have hVp : IsPGroup 3 V := IsPGroup.of_card (n := 3) (by rw [hcfg.card]; norm_num)
    have h := IsPGroup.inf_normalizer_sylow hVp T
    intro v hv
    exact ((le_of_eq h) ⟨hv, hBN (hVB hv)⟩).2
  have hZV : centerOf T' ≤ V := by
    have hE := CFSG.Open.IsElemAbelian.sup_of_commute hcfg.elem hZe fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp hb.2 a (hVT ha)
    obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
    have hk3 : k ≤ 3 := by
      have h : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
        le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three ⊤)
          ⟨_, le_top, hE, hk⟩
      exact h.trans hI.pRank_le
    have hcard : Nat.card (V ⊔ centerOf T' : Subgroup Y) ≤ Nat.card V := by
      rw [hk, hcfg.card]
      calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 27 := by norm_num
    have heq : V = V ⊔ centerOf T' := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    rw [heq]
    exact le_sup_right
  have hZne : centerOf T' ≠ V := fun h => by
    have h27 := hcfg.card
    rw [← h, hZc] at h27
    norm_num at h27
  have hZt : ∀ t ∈ ({t₁, t₂, t₃} : Set Y), ∀ x ∈ centerOf T', t * x * t⁻¹ ∈ centerOf T' := by
    intro t ht x hx
    have htB : t ∈ B := by
      rcases ht with rfl | rfl | rfl
      · exact ht₁
      · exact ht₂
      · exact ht₃
    exact CFSG.AGLEmbedding.conj_mem_centerOf_of_mem_normalizer (hBN htB) hx
  have hkey : ∀ {t : Y} {W : Subgroup Y}, Nat.card W = 3 → (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) →
      (∀ x ∈ centerOf T', t * x = x * t) → False := by
    intro t W hW hinv hcent
    have htT : t ∈ T' :=
      hI.centralizer_center (Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent x hx).symm)
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, htT⟩
    exact false_of_inv_of_pow hW hinv (by simpa using congrArg Subtype.val hn)
  rcases IsE27InvConfig.exists_centralizes_of_invariant hcfg hZV hZne hZt with h | h | h
  · exact hkey hcfg.card₁ hcfg.inv₁ h
  · exact hkey hcfg.card₂ hcfg.inv₂ h
  · exact hkey hcfg.card₃ hcfg.inv₃ h

end J3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarJ3

end
