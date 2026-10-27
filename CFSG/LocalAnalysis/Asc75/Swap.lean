module

public import CFSG.LocalAnalysis.Asc75.Helpers
public import CFSG.LocalAnalysis.Asc75.Conj

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

theorem conj_eq_of_comm {P Q : G} (h : P * Q = Q * P) : Q⁻¹ * P * Q = P := by
  calc Q⁻¹ * P * Q = Q⁻¹ * (P * Q) := by group
    _ = Q⁻¹ * (Q * P) := by rw [h]
    _ = P := by group

section Dichotomy

variable [Finite G] {A₁ A₂ : Subgroup G}

theorem swap_dichotomy_disjoint (hdisj : A₁ ⊓ A₂ = ⊥) (hA₁ : A₁ ≠ ⊥) (hA₂ : A₂ ≠ ⊥) {s : G}
    (hs : s ∈ stabSet (uSet A₁ A₂)) :
    (s ∈ Subgroup.normalizer (A₁ : Set G) ∧ s ∈ Subgroup.normalizer (A₂ : Set G)) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁) := by
  rcases swap_dichotomy hs with h1 | h2 | h3
  · left
    refine ⟨h1, ?_⟩
    rcases SubgroupClass.subset_union.1 (conjugate_subset_uSet hs (A := A₂) (Or.inr rfl)) with
      hle | hle
    · exfalso
      have h' : A₂ ≤ A₁ := by
        have := conjugate_mono hle s⁻¹
        rwa [conjugate_inv_conjugate,
          conjugate_of_mem_normalizer ((Subgroup.normalizer (A₁ : Set G)).inv_mem h1)] at this
      apply hA₂
      rw [eq_bot_iff, ← hdisj]
      exact le_inf h' le_rfl
    · exact mem_normalizer_of_conjugate_eq
        (Subgroup.eq_of_le_of_card_ge hle (card_conjugate A₂ s).ge)
  · left
    refine ⟨?_, h2⟩
    rcases SubgroupClass.subset_union.1 (conjugate_subset_uSet hs (A := A₁) (Or.inl rfl)) with
      hle | hle
    · exact mem_normalizer_of_conjugate_eq
        (Subgroup.eq_of_le_of_card_ge hle (card_conjugate A₁ s).ge)
    · exfalso
      have h' : A₁ ≤ A₂ := by
        have := conjugate_mono hle s⁻¹
        rwa [conjugate_inv_conjugate,
          conjugate_of_mem_normalizer ((Subgroup.normalizer (A₂ : Set G)).inv_mem h2)] at this
      apply hA₁
      rw [eq_bot_iff, ← hdisj]
      exact le_inf le_rfl h'
  · exact Or.inr h3

omit [Finite G] in
theorem not_mem_uSet_of_swap (hdisj : A₁ ⊓ A₂ = ⊥) (hA₁ : A₁ ≠ ⊥) (hA₂ : A₂ ≠ ⊥) {t : G}
    (hswap : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) : t ∉ uSet A₁ A₂ := by
  rintro (ht | ht)
  · have h1 : conjugate A₁ t = A₁ := conjugate_of_mem_normalizer (Subgroup.le_normalizer ht)
    rw [h1] at hswap
    apply hA₁
    rw [eq_bot_iff, ← hdisj]
    exact le_inf le_rfl hswap.1.le
  · have h1 : conjugate A₂ t = A₂ := conjugate_of_mem_normalizer (Subgroup.le_normalizer ht)
    rw [h1] at hswap
    apply hA₂
    rw [eq_bot_iff, ← hdisj]
    exact le_inf hswap.2.le le_rfl

end Dichotomy

section Swapper

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.mem_conjugate_of_swap (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a g : G}
    (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1) (ha2 : a * a = 1) (htS : g⁻¹ * a * g ∈ S)
    (hswap : conjugate A₁ (g⁻¹ * a * g) = A₂ ∧ conjugate A₂ (g⁻¹ * a * g) = A₁) {v : G}
    (hv : v ∈ A₁) (hv2 : v * v = 1) : v ∈ conjugate H g := by
  have hK := h.conj g
  have hB : conjugate A₁ g ⊓ conjugate A₂ g = ⊥ := by
    rw [← conjugate_inf, hdisj, conjugate_bot]
  set t : G := g⁻¹ * a * g with ht
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have ht1 : t ≠ 1 := by
    intro e
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [← ht, e]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hcent : ∀ c : G, c * t = t * c → c ∈ conjugate H g := by
    intro c hc
    rw [mem_conjugate_iff]
    refine h.mem_of_conj_eq ha ha1 ?_
    have hct : c⁻¹ * t * c = t := by
      calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
        _ = c⁻¹ * (c * t) := by rw [hc]
        _ = t := by group
    calc (g * c * g⁻¹)⁻¹ * a * (g * c * g⁻¹) = g * (c⁻¹ * (g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c⁻¹ * t * c) * g⁻¹ := by rw [← ht]
      _ = a := by rw [hct, ht]; group
  have hvt : t⁻¹ * v * t ∈ A₂ := by
    have := conj_mem_conjugate hv t
    rwa [hswap.1] at this
  have hcomm : v * (t⁻¹ * v * t) = (t⁻¹ * v * t) * v := h.comm v hv _ hvt
  rw [htinv] at hcomm
  set u₁ : G := v * t * v with hu₁
  have hcomm_tu : u₁ * t = t * u₁ := by
    rw [hu₁]
    calc v * t * v * t = v * (t * v * t) := by group
      _ = t * v * t * v := hcomm
      _ = t * (v * t * v) := by group
  have htK : t ∈ conjugate H g := hcent t rfl
  have hu₁K : u₁ ∈ conjugate H g := hcent u₁ hcomm_tu
  have hu₁S : u₁ ∈ S := S.mul_mem (S.mul_mem (h.le₁ hv) htS) (h.le₁ hv)
  have hWS : Subgroup.closure ({t, u₁} : Set G) ≤ S :=
    (Subgroup.closure_le _).2 (by
      intro x hx
      rcases hx with rfl | rfl
      · exact htS
      · exact hu₁S)
  have hWK : Subgroup.closure ({t, u₁} : Set G) ≤ conjugate H g :=
    (Subgroup.closure_le _).2 (by
      intro x hx
      rcases hx with rfl | rfl
      · exact htK
      · exact hu₁K)
  obtain ⟨k, hkK, hk⟩ := exists_conj_mem_sylow (conjugate H g) hK.sylowG hK.S_le_H _ hWK
    (h.pgroup.to_le hWS)
  have htk : k⁻¹ * t * k ∈ conjugate S g := hk t (Subgroup.subset_closure (by simp))
  have hu₁k : k⁻¹ * u₁ * k ∈ conjugate S g := hk u₁ (Subgroup.subset_closure (by simp))
  have htB : t ∈ uSet (conjugate A₁ g) (conjugate A₂ g) := by
    rcases ha with ha | ha
    · exact Or.inl (conj_mem_conjugate ha g)
    · exact Or.inr (conj_mem_conjugate ha g)
  have htkU : k⁻¹ * t * k ∈ uSet (conjugate A₁ g) (conjugate A₂ g) :=
    hK.closed_H t htB k hkK htk
  have htk1 : k⁻¹ * t * k ≠ 1 := by
    intro e
    apply ht1
    calc t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hcomm_k : (k⁻¹ * t * k) * (k⁻¹ * u₁ * k) = (k⁻¹ * u₁ * k) * (k⁻¹ * t * k) := by
    calc (k⁻¹ * t * k) * (k⁻¹ * u₁ * k) = k⁻¹ * (t * u₁) * k := by group
      _ = k⁻¹ * (u₁ * t) * k := by rw [hcomm_tu]
      _ = (k⁻¹ * u₁ * k) * (k⁻¹ * t * k) := by group
  have hdich := swap_dichotomy_disjoint hB hK.ne_bot₁ hK.ne_bot₂ (hK.S_le_stab hu₁k)
  set x : G := k⁻¹ * v * k with hx
  have hxconj : x⁻¹ * (k⁻¹ * t * k) * x = k⁻¹ * u₁ * k := by
    rw [hx, hu₁]
    calc (k⁻¹ * v * k)⁻¹ * (k⁻¹ * t * k) * (k⁻¹ * v * k) = k⁻¹ * (v⁻¹ * t * v) * k := by group
      _ = k⁻¹ * (v * t * v) * k := by rw [hvinv]
  have hxK : x ∈ conjugate H g := by
    rcases hdich with ⟨hn1, hn2⟩ | ⟨hs1, hs2⟩
    · rcases htkU with htk' | htk'
      · have hmem := hK.closed₁ _ (Or.inl htk') x (by rw [hxconj]; exact ⟨hu₁k, hn1⟩)
        rcases hmem with hm | hm
        · exact hK.mem_of_conj_mem (Or.inl rfl) (Or.inl rfl) htk' htk1 hm
        · exact hK.mem_of_conj_mem (Or.inl rfl) (Or.inr rfl) htk' htk1 hm
      · have hmem := hK.closed₂ _ (Or.inr htk') x (by rw [hxconj]; exact ⟨hu₁k, hn2⟩)
        rcases hmem with hm | hm
        · exact hK.mem_of_conj_mem (Or.inr rfl) (Or.inl rfl) htk' htk1 hm
        · exact hK.mem_of_conj_mem (Or.inr rfl) (Or.inr rfl) htk' htk1 hm
    · exfalso
      have hfix := conj_eq_of_comm hcomm_k
      rcases htkU with htk' | htk'
      · have : k⁻¹ * t * k ∈ conjugate (conjugate A₁ g) (k⁻¹ * u₁ * k) := by
          have := conj_mem_conjugate htk' (k⁻¹ * u₁ * k)
          rwa [hfix] at this
        rw [hs1] at this
        have h12 : k⁻¹ * t * k ∈ conjugate A₁ g ⊓ conjugate A₂ g := ⟨htk', this⟩
        rw [hB, Subgroup.mem_bot] at h12
        exact htk1 h12
      · have : k⁻¹ * t * k ∈ conjugate (conjugate A₂ g) (k⁻¹ * u₁ * k) := by
          have := conj_mem_conjugate htk' (k⁻¹ * u₁ * k)
          rwa [hfix] at this
        rw [hs2] at this
        have h12 : k⁻¹ * t * k ∈ conjugate A₁ g ⊓ conjugate A₂ g := ⟨this, htk'⟩
        rw [hB, Subgroup.mem_bot] at h12
        exact htk1 h12
  have : v = k * x * k⁻¹ := by rw [hx]; group
  rw [this]
  exact (conjugate H g).mul_mem ((conjugate H g).mul_mem hkK hxK) ((conjugate H g).inv_mem hkK)

theorem Hyp.swapper_not_conj (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a g : G}
    (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1) (ha2 : a * a = 1) (htS : g⁻¹ * a * g ∈ S)
    (hswap : conjugate A₁ (g⁻¹ * a * g) = A₂ ∧ conjugate A₂ (g⁻¹ * a * g) = A₁) : False := by
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two A₁
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A₁ := Nat.pow_le_pow_right (by norm_num) h.rank₁
  have hEK : E ≤ conjugate H g := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← sq]; exact hE.2 x hx
    exact h.mem_conjugate_of_swap hdisj ha ha1 ha2 htS hswap (hEA hx) hx2
  have hfix := h.fixedOnly (X := E) (Or.inl hEA) h4
  have hgH : g ∈ H := by
    have : g⁻¹ ∈ H := by
      refine hfix.2 g⁻¹ ?_
      intro y hy
      have hy' : g⁻¹ * y * (g⁻¹)⁻¹ ∈ E := mem_conjugate_iff.1 hy
      have := mem_conjugate_iff.1 (hEK hy')
      rwa [show g * (g⁻¹ * y * (g⁻¹)⁻¹) * g⁻¹ = y by group] at this
    simpa using H.inv_mem this
  have := h.closed_H a ha g hgH htS
  exact not_mem_uSet_of_swap hdisj h.ne_bot₁ h.ne_bot₂ hswap this

theorem Hyp.fixedOnlyElt_of_involution (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a : G}
    (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1) (ha2 : a * a = 1) : FixedOnlyElt H a := by
  refine ⟨h.uSet_subset_H ha, fun g hg => ?_⟩
  set b : G := g⁻¹ * a * g with hb
  have hb1 : b ≠ 1 := by
    intro e
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [← hb, e]; group
  have hb2 : b * b = 1 := by
    rw [hb]
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hbord : orderOf b = 2 := orderOf_eq_two_of_mul_self_eq_one hb2 hb1
  obtain ⟨k, hkH, hk⟩ := exists_conj_mem_sylow H h.sylowG h.S_le_H (Subgroup.zpowers b)
    ((Subgroup.zpowers_le).2 hg) (isPGroup_zpowers_of_orderOf_eq_two hbord)
  have hbk : k⁻¹ * b * k ∈ S := hk b (Subgroup.mem_zpowers b)
  have hgk : (g * k)⁻¹ * a * (g * k) = k⁻¹ * b * k := by rw [hb]; group
  have htS : (g * k)⁻¹ * a * (g * k) ∈ S := by rw [hgk]; exact hbk
  have hg' : g * k ∈ H := by
    rcases swap_dichotomy_disjoint hdisj h.ne_bot₁ h.ne_bot₂ (h.S_le_stab htS) with
      ⟨hn1, -⟩ | hswap
    · have ht := h.closed₁ a ha (g * k) ⟨htS, hn1⟩
      rcases ha with ha' | ha' <;> rcases ht with ht' | ht'
      · exact h.mem_of_conj_mem (Or.inl rfl) (Or.inl rfl) ha' ha1 ht'
      · exact h.mem_of_conj_mem (Or.inl rfl) (Or.inr rfl) ha' ha1 ht'
      · exact h.mem_of_conj_mem (Or.inr rfl) (Or.inl rfl) ha' ha1 ht'
      · exact h.mem_of_conj_mem (Or.inr rfl) (Or.inr rfl) ha' ha1 ht'
    · exact (h.swapper_not_conj hdisj ha ha1 ha2 htS hswap).elim
  have e : g = (g * k) * k⁻¹ := by group
  rw [e]
  exact H.mul_mem hg' (H.inv_mem hkH)

theorem Hyp.fixedOnlyElt (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a : G}
    (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1) : FixedOnlyElt H a := by
  obtain ⟨n, hn⟩ := exists_pow_orderOf_two h.pgroup (h.mem_S_of_mem_uSet ha) ha1
  have hn2 : a ^ n * a ^ n = 1 := mul_self_eq_one_of_orderOf_eq_two hn
  have hn1 : a ^ n ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hn
    omega
  have han : a ^ n ∈ uSet A₁ A₂ := by
    rcases ha with ha | ha
    · exact Or.inl (A₁.pow_mem ha n)
    · exact Or.inr (A₂.pow_mem ha n)
  exact FixedOnlyElt.of_pow (h.uSet_subset_H ha) (h.fixedOnlyElt_of_involution hdisj han hn1 hn2)

theorem Hyp.closed_G (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a g : G} (ha : a ∈ uSet A₁ A₂)
    (hg : g⁻¹ * a * g ∈ S) : g⁻¹ * a * g ∈ uSet A₁ A₂ := by
  by_cases ha1 : a = 1
  · rw [ha1]
    have : g⁻¹ * (1 : G) * g = 1 := by group
    rw [this]
    exact Or.inl A₁.one_mem
  · have hgH : g ∈ H := (h.fixedOnlyElt hdisj ha ha1).2 g (h.S_le_H hg)
    exact h.closed_H a ha g hgH hg

end Swapper

end CFSG.Asc75
