module

public import CFSG.ClassicalInvolution.Asc77.AscT7AFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7b

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7B

variable {G : Type} [Group G]

theorem mem_closure_pair {a b x : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hc : a * b = b * a) (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hcl : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hcomm : Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hc) i j).eq
  rw [hcl] at hx
  obtain ⟨a', ha', b', hb', rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hx
  rcases T7A.eq_one_or_eq_of_mem_zpowers ha2 ha' with h1 | h1 <;>
    rcases T7A.eq_one_or_eq_of_mem_zpowers hb2 hb' with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2]

theorem natCard_closure_three_eq_eight {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc1 : c ≠ 1)
    (hab' : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hnot : c ∉ Subgroup.closure ({a, b} : Set G)) :
    Nat.card ↥(Subgroup.closure ({a, b, c} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair ha hb ha1 hb1 hab hab'
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc) hc1
  have hcl : Subgroup.closure ({a, b, c} : Set G) =
      Subgroup.closure ({a, b} : Set G) ⊔ Subgroup.zpowers c := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({a, b} : Set G)) (Subgroup.zpowers c) := by
    have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hac
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hbc
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({a, b} : Set G) ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers hc2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply hnot
      rw [← h1]
      exact he.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hc2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end T7B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7B

theorem exists_third_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {L L' L₃ R₁ R₂ : Subgroup G} {z : G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hL₃ : L₃ ∈ Ω)
    (hz : IsUniqueInvolution L z) (hz' : IsUniqueInvolution L' z) (hz₃ : IsUniqueInvolution L₃ z)
    (hne₃ : L₃ ≠ L) (hne₃' : L₃ ≠ L') (hR₁ : IsSylow2In R₁ L)
    (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) :
    ∃ R₃ : Subgroup G, IsSylow2In R₃ L₃ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have hRn : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := T7A.le_normalizer_of_commutes hc.symm
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hRn
  have hLN : L ≤ Subgroup.normalizer (L₃ : Set G) :=
    hΩ.le_normalizer_of_twin hL hL₃ hne₃.symm hz hz₃
  have hL'N : L' ≤ Subgroup.normalizer (L₃ : Set G) :=
    hΩ.le_normalizer_of_twin hL' hL₃ hne₃'.symm hz' hz₃
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (L₃ : Set G) :=
    sup_le (hR₁.1.trans hLN) (hR₂.1.trans hL'N)
  obtain ⟨R₃, hR₃, hfix⟩ := exists_sylow_normalized hP2 hPN
  have hPnR₃ : R₁ ⊔ R₂ ≤ Subgroup.normalizer (R₃ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have hQ2 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) := hP2.to_sup_of_normal_right' hR₃.2.1 hPnR₃
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hR₁S : R₁ ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hR₂S : R₂ ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR₃S : R₃ ≤ (S : Subgroup G) := le_sup_right.trans hS
  have h1set : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hL hR₁
  have h2set : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hL' hR₂
  have h3set : R₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hL₃ hR₃
  have h13 : R₁ ≠ R₃ := by
    intro h
    have := hΩ.card_le_two_of_le_inf hL hL₃ hne₃.symm hR₁.2.1 hR₁.1 (h ▸ hR₃.1)
    have := hΩ.eight_le_of_mem_RSet hp h1set
    omega
  have h23 : R₂ ≠ R₃ := by
    intro h
    have := hΩ.card_le_two_of_le_inf hL' hL₃ hne₃'.symm hR₂.2.1 hR₂.1 (h ▸ hR₃.1)
    have := hΩ.eight_le_of_mem_RSet hp h2set
    omega
  exact ⟨R₃, hR₃, l6_7_proved p f hp hq G Ω hΩ S R₁ h1set R₃ h3set hR₁S hR₃S h13,
    l6_7_proved p f hp hq G Ω hΩ S R₂ h2set R₃ h3set hR₂S hR₃S h23⟩

theorem isElemAbelian2_B (hΩ : HypOmegaMod p f Ω) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hK₃ : K₃ ∈ Ω) (hKK' : K' ≠ K)
    (hKK₃ : K₃ ≠ K) (hK'K₃ : K₃ ≠ K') (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hz₃ : IsUniqueInvolution K₃ z)
    (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K') (h₃ : u₃ ∈ K₃) (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4)
    (o₃ : orderOf u₃ = 4) (c₁₂ : u₁ * u₂ = u₂ * u₁) (c₁₃ : u₁ * u₃ = u₃ * u₁)
    (c₂₃ : u₂ * u₃ = u₃ * u₂) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3 := by
  have s₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz h₁ o₁
  have s₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hz' h₂ o₂
  have s₃ : u₃ * u₃ = z := T7A.sq_eq_of_orderOf_four hz₃ h₃ o₃
  have zc₁ : z * u₁ = u₁ * z := e189_commute_of_mem hz h₁
  have zc₂ : z * u₂ = u₂ * z := e189_commute_of_mem hz' h₂
  have zc₃ : z * u₃ = u₃ * z := e189_commute_of_mem hz₃ h₃
  have hz2 : z * z = 1 := hz.sq
  have q₁₂ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← c₁₂]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [s₁, s₂, hz2]
  have q₂₃ : (u₂ * u₃) * (u₂ * u₃) = 1 := by
    calc (u₂ * u₃) * (u₂ * u₃) = u₂ * (u₃ * u₂) * u₃ := by group
      _ = u₂ * (u₂ * u₃) * u₃ := by rw [← c₂₃]
      _ = (u₂ * u₂) * (u₃ * u₃) := by group
      _ = 1 := by rw [s₂, s₃, hz2]
  have hcu₁₂ : Commute (u₁ * u₂) z := by
    have : Commute u₁ z := zc₁.symm
    have : Commute u₂ z := zc₂.symm
    exact Commute.mul_left (by assumption) (by assumption)
  have hcu₂₃ : Commute (u₂ * u₃) z := Commute.mul_left (zc₂.symm : Commute u₂ z)
    (zc₃.symm : Commute u₃ z)
  have hc12 : Commute u₁ u₂ := c₁₂
  have hc13 : Commute u₁ u₃ := c₁₃
  have hc23 : Commute u₂ u₃ := c₂₃
  have hcomm : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact hcu₁₂.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).eq
    · exact hcu₁₂.symm.eq
    · rfl
    · exact hcu₂₃.symm.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).symm.eq
    · exact hcu₂₃.eq
    · rfl
  have hsq : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact q₁₂
    · exact hz2
    · exact q₂₃
  refine ⟨?_, fun x hx => T7A.sq_closure hsq hcomm x hx⟩
  have hne12 : u₁ * u₂ ≠ z := by
    intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ h₂
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h₁) hz.mem
  have hne1 : u₁ * u₂ ≠ 1 := by
    intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ h₂
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h₁
  have hc1 : u₂ * u₃ ≠ 1 := by
    intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK' hK₃ hK'K₃ o₃ ?_ h₃
    have : u₃ = u₂⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K'.inv_mem h₂
  have hnot : u₂ * u₃ ∉ Subgroup.closure ({u₁ * u₂, z} : Set G) := by
    intro hx
    rcases mem_closure_pair q₁₂ hz2 hne1 hz.ne_one hcu₁₂.eq hx with h | h | h | h
    · exact hc1 h
    · have h3 : u₃ = u₁ := mul_left_cancel (h.trans c₁₂)
      exact T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃ hKK₃ o₃ (h3 ▸ h₁) h₃
    · have h3 : u₃ = u₂⁻¹ * z := by rw [← h]; group
      refine T7A.not_mem_inf_of_orderOf_four hΩ hK' hK₃ hK'K₃ o₃ ?_ h₃
      rw [h3]
      exact K'.mul_mem (K'.inv_mem h₂) hz'.mem
    · have h' : u₂ * u₃ = u₂ * (u₁ * z) := by rw [h, c₁₂]; group
      have h3 : u₃ = u₁ * z := mul_left_cancel h'
      refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃ hKK₃ o₃ ?_ h₃
      rw [h3]
      exact K.mul_mem h₁ hz.mem
  have := natCard_closure_three_eq_eight q₁₂ hz2 q₂₃ hne1 hz.ne_one hne12 hc1
    hcu₁₂.eq (hcomm _ (by simp) _ (by simp)) (hcomm _ (by simp) _ (by simp)) hnot
  rw [this]
  norm_num

theorem hyp22_of_sylows {K K' K₃ : Subgroup G} {z : G} (hs : Std7 p f Ω K K' z)
    (hperp : KPerp Ω K = twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K')
    {R R' R₃ : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hR₃ : IsSylow2In R₃ K₃) (c₁₂ : Commutes R R') (c₁₃ : Commutes R R₃)
    (c₂₃ : Commutes R' R₃) {u₁ u₂ u₃ : G} (h₁ : u₁ ∈ R) (h₂ : u₂ ∈ R') (h₃ : u₃ ∈ R₃)
    (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4) (o₃ : orderOf u₃ = 4) :
    Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hs.hz hK₃
  have hB := isElemAbelian2_B hs.stand.hyp hs.stand.mem hs.hK'.1 hK₃.1 hs.hne
    hK₃K hK₃K' hs.hz hzK' hzK₃ (hR.1 h₁) (hR'.1 h₂) (hR₃.1 h₃) o₁ o₂ o₃ (c₁₂ u₁ h₁ u₂ h₂)
    (c₁₃ u₁ h₁ u₃ h₃) (c₂₃ u₂ h₂ u₃ h₃)
  exact
    { std := hs
      perp := hperp
      hK₃ := hK₃
      hK₃K := hK₃K
      hK₃K' := hK₃K'
      hu₁ := ⟨hR.1 h₁, o₁⟩
      hu₂ := ⟨hR'.1 h₂, o₂⟩
      hu₃ := ⟨hR₃.1 h₃, o₃⟩
      hB := hB }

theorem exists_threeTwinSylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' K₃ : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hne : K' ≠ K) (hne₃ : K₃ ≠ K)
    (hne₃' : K₃ ≠ K') :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hz hK₃
  obtain ⟨R, R', hR, hR', hc⟩ := T7A.exists_commuting_sylow_twin hΩ hK hK'.1 hne hz hzK'
  obtain ⟨R₃, hR₃, hc₁, hc₂⟩ :=
    exists_third_sylow hp hq hΩ hK hK'.1 hK₃.1 hz hzK' hzK₃ hne₃ hne₃' hR hR' hc
  exact ⟨R, R', R₃, hR, hR', hR₃, hc, hc₁, hc₂⟩

end T7B

variable (p f) in
theorem c22_setup : C22_setup p f := by
  intro G _ _ _ Ω K K' z hs hperp hne
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hex : ∃ K₃ ∈ twinSet Ω K, K₃ ≠ K ∧ K₃ ≠ K' := by
    by_contra hcon
    push Not at hcon
    apply hne
    ext J
    constructor
    · intro hJ
      have hJt : J ∈ twinSet Ω K := by rw [← hperp]; exact hJ
      by_cases hJK : J = K
      · exact Or.inl hJK
      · exact Or.inr (hcon J hJt hJK)
    · rintro (rfl | rfl)
      · exact Set.mem_insert _ _
      · rw [hperp]; exact hs.hK'
  obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := hex
  obtain ⟨R, R', R₃, hR, hR', hR₃, c₁₂, c₁₃, c₂₃⟩ :=
    T7B.exists_threeTwinSylow hp hq hΩ hK hs.hz hs.hK' hK₃ hs.hne hK₃K hK₃K'
  obtain ⟨u₁, hu₁, o₁⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨u₂, hu₂, o₂⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hs.hK'.1 hR')
  obtain ⟨u₃, hu₃, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hK₃.1 hR₃)
  exact ⟨K₃, u₁, u₂, u₃, T7B.hyp22_of_sylows hs hperp hK₃ hK₃K hK₃K' hR hR' hR₃ c₁₂ c₁₃ c₂₃
    hu₁ hu₂ hu₃ o₁ o₂ o₃⟩

end CFSG.ClassicalInvolution.Asc77
