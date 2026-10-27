module

public import CFSG.Open.LocalVocabulary

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open CFSG

variable {X : Type} [Group X] [Finite X]

private theorem bddAbove_elemAbelian_exponents (R : Subgroup X) :
    BddAbove {k | ∃ E : Subgroup X, E ≤ R ∧ Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
  refine ⟨Nat.card X, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
  have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  omega

private theorem le_pRank_of_exists {R : Subgroup X} {k : ℕ}
    (h : ∃ E : Subgroup X, E ≤ R ∧ Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k) :
    k ≤ Open.pRank 3 R :=
  le_csSup (bddAbove_elemAbelian_exponents R) h

theorem exists_elemAbelian_card_27 {R : Subgroup X} (h : Open.pRank 3 R = 3) :
    ∃ A : Subgroup X, A ≤ R ∧ Open.IsElemAbelian 3 A ∧ Nat.card A = 27 := by
  have hne : {k | ∃ E : Subgroup X, E ≤ R ∧ Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    unfold Open.pRank at h
    rw [hempty] at h
    simp at h
  have hmem := Nat.sSup_mem hne (bddAbove_elemAbelian_exponents R)
  unfold Open.pRank at h
  rw [h] at hmem
  obtain ⟨E, hER, hE, hcard⟩ := hmem
  exact ⟨E, hER, hE, by rw [hcard]; norm_num⟩

theorem three_le_pRank_of_card {A : Subgroup X} (hA : Open.IsElemAbelian 3 A)
    (h : Nat.card A = 27) : 3 ≤ Open.pRank 3 A :=
  le_pRank_of_exists ⟨A, le_rfl, hA, by rw [h]; norm_num⟩

private theorem mem_center_of_mem_zpowers {z : X} (hz : z ∈ Subgroup.center X) {c : X}
    (hc : c ∈ Subgroup.zpowers z) : c ∈ Subgroup.center X :=
  Subgroup.zpowers_le.2 hz hc

private theorem normal_zpowers_of_mem_center {z : X} (hz : z ∈ Subgroup.center X) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' := Subgroup.mem_center_iff.1 (mem_center_of_mem_zpowers hz hn) g
  rwa [hn', mul_inv_cancel_right]

theorem mem_sylow_of_central (R : Sylow 3 X) {z : X} (hz : z ∈ Subgroup.center X)
    (hz3 : orderOf z = 3) : z ∈ (R : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := normal_zpowers_of_mem_center hz
  have hp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hz3])
  exact hp.le_sylow_of_normal R (Subgroup.mem_zpowers z)

private theorem card_sup_le_mul {H K : Subgroup X} (hc : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    Nat.card (H ⊔ K : Subgroup X) ≤ Nat.card H * Nat.card K := by
  have hrange := MonoidHom.noncommCoprod_range H.subtype K.subtype (fun a b => hc a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  have h := Nat.card_le_card_of_surjective _
    (H.subtype.noncommCoprod K.subtype (fun a b => hc a a.2 b b.2)).rangeRestrict_surjective
  rw [hrange, Nat.card_prod] at h
  exact h

private theorem card_sup_eq_mul {H K : Subgroup X} (hc : ∀ h ∈ H, ∀ k ∈ K, Commute h k)
    (hd : Disjoint H K) : Nat.card (H ⊔ K : Subgroup X) = Nat.card H * Nat.card K := by
  have hinj := (MonoidHom.noncommCoprod_injective H.subtype K.subtype
    (fun a b => hc a a.2 b b.2)).2 ⟨H.subtype_injective, K.subtype_injective, by simpa using hd⟩
  have hrange := MonoidHom.noncommCoprod_range H.subtype K.subtype (fun a b => hc a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem isElemAbelian_sup_zpowers {A : Subgroup X} (hA : Open.IsElemAbelian 3 A) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) :
    Open.IsElemAbelian 3 (A ⊔ Subgroup.zpowers z) := by
  have := normal_zpowers_of_mem_center hz
  have hcen : ∀ c ∈ Subgroup.zpowers z, ∀ g : X, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.1 (mem_center_of_mem_zpowers hz hc) g
  have hc3 : ∀ c ∈ Subgroup.zpowers z, c ^ 3 = 1 := fun c hc => by
    rw [← orderOf_dvd_iff_pow_eq_one, ← hz3]
    exact orderOf_dvd_of_mem_zpowers hc
  obtain ⟨hAcomm, hAexp⟩ := hA
  have hAc := isMulCommutative_iff_of_setLike.1 hAcomm
  refine ⟨isMulCommutative_iff_of_setLike.2 ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨a', ha', c', hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    have h1 : Commute a a' := hAc a ha a' ha'
    have h2 : Commute a c' := hcen c' hc' a
    have h3 : Commute c a' := (hcen c hc a').symm
    have h4 : Commute c c' := hcen c' hc' c
    exact Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)
  · intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    have h1 : Commute a c := hcen c hc a
    rw [h1.mul_pow, hAexp a ha, hc3 c hc, one_mul]

theorem mem_of_pRank_eq_three {R : Subgroup X} (hR : Open.pRank 3 R = 3) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) (hzR : z ∈ R) {A : Subgroup X}
    (hAR : A ≤ R) (hA : Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) : z ∈ A := by
  by_contra hzA
  have := normal_zpowers_of_mem_center hz
  have hZcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have hdisj : Disjoint A (Subgroup.zpowers z) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (A ⊓ Subgroup.zpowers z : Subgroup X) ∣ 3 :=
      hZcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : A ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
      have hzmem : z ∈ A ⊓ Subgroup.zpowers z := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact hzA hzmem.1
  have hcomm : ∀ a ∈ A, ∀ c ∈ Subgroup.zpowers z, Commute a c := fun a _ c hc =>
    Subgroup.mem_center_iff.1 (mem_center_of_mem_zpowers hz hc) a
  have hcardB : Nat.card (A ⊔ Subgroup.zpowers z : Subgroup X) = 3 ^ 4 := by
    rw [card_sup_eq_mul hcomm hdisj, hcard, hZcard]
    norm_num
  have h4 : 4 ≤ Open.pRank 3 R :=
    le_pRank_of_exists ⟨A ⊔ Subgroup.zpowers z, sup_le hAR (Subgroup.zpowers_le.2 hzR),
      isElemAbelian_sup_zpowers hA hz hz3, hcardB⟩
  omega

private theorem conj_mem_centralizer {K : Subgroup X} [K.Normal] {c : X}
    (hc : c ∈ Subgroup.centralizer (K : Set X)) (g : X) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    simpa using Subgroup.Normal.conj_mem ‹K.Normal› k hk g⁻¹
  have h := hc _ hk'
  calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * k := by group

set_option linter.unusedVariables false in
theorem mem_zpowers_of_orderOf_eq_three (R : Sylow 3 X) {K : Subgroup X} [K.Normal] {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    {c : X} (hc : c ∈ Subgroup.centralizer (K : Set X)) (hc3 : orderOf c = 3) :
    c ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hc3])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R Q
  have hcQ : c ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers c)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hcQ
  obtain ⟨r, hrR, hrc⟩ := hcQ
  have hrc' : g * r * g⁻¹ = c := by simpa [MulAut.smul_def, MulAut.conj_apply] using hrc
  have hr : r = g⁻¹ * c * g⁻¹⁻¹ := by rw [← hrc']; group
  have hrK : r ∈ Subgroup.centralizer (K : Set X) := by
    rw [hr]
    exact conj_mem_centralizer hc g⁻¹
  have hr3 : orderOf r = 3 := by
    have h := (MulAut.conj g⁻¹).orderOf_eq c
    rw [hc3] at h
    rw [hr]
    simpa [MulAut.conj_apply] using h
  have hrz : r ∈ Subgroup.zpowers z := hΩ r ⟨hrR, hrK⟩ hr3
  have hcen := Subgroup.mem_center_iff.1 (mem_center_of_mem_zpowers hz hrz) g
  have hcr : c = r := by rw [← hrc', hcen, mul_inv_cancel_right]
  rw [hcr]
  exact hrz

theorem mem_zpowers_of_pow_three_eq_one (R : Sylow 3 X) {K : Subgroup X} [K.Normal] {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    {c : X} (hc : c ∈ Subgroup.centralizer (K : Set X)) (hc3 : c ^ 3 = 1) :
    c ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h1 : c = 1
  · rw [h1]
    exact one_mem _
  · exact mem_zpowers_of_orderOf_eq_three R hz hz3 hΩ hc (orderOf_eq_prime hc3 h1)

theorem exists_mem_not_mem_sup_zpowers {A : Subgroup X} (hA : Open.IsElemAbelian 3 A)
    (hcard : Nat.card A = 27) {z f : X} (hz : z ∈ A) (hf : f ∈ A) :
    ∃ f₂ ∈ A, f₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers f := by
  by_contra hcon
  have hle : A ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers f := fun x hx => by
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  have hzf : Commute z f := isMulCommutative_iff_of_setLike.1 hA.1 z hz f hf
  have hc : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers f, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact hzf.zpow_zpow m n
  have hZle : Nat.card (Subgroup.zpowers z) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 z hz))
  have hFle : Nat.card (Subgroup.zpowers f) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 f hf))
  have h1 := card_sup_le_mul hc
  have h2 := Subgroup.card_le_of_le hle
  have h3 := Nat.mul_le_mul hZle hFle
  omega

theorem not_mem_zpowers_of_not_mem_sup {z f₁ f₂ : X} (hf₂ : f₂ ^ 3 = 1)
    (h : f₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers f₁) :
    f₁ * f₂ ∉ Subgroup.zpowers z ∧ f₁ * f₂ ^ 2 ∉ Subgroup.zpowers z := by
  have hf1 : f₁⁻¹ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers f₁ :=
    Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers f₁))
  refine ⟨fun hmem => h ?_, fun hmem => h ?_⟩
  · have h1 : f₂ = f₁⁻¹ * (f₁ * f₂) := by group
    rw [h1]
    exact mul_mem hf1 (Subgroup.mem_sup_left hmem)
  · have h1 : f₂ ^ 2 = f₁⁻¹ * (f₁ * f₂ ^ 2) := by group
    have h2 : f₂ ^ 2 ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers f₁ := by
      rw [h1]
      exact mul_mem hf1 (Subgroup.mem_sup_left hmem)
    have h3 : f₂ = (f₂ ^ 2) ^ 2 := by
      calc f₂ = f₂ ^ 3 * f₂ := by rw [hf₂, one_mul]
        _ = (f₂ ^ 2) ^ 2 := by group
    rw [h3]
    exact pow_mem h2 2

theorem conj_aux_mem {K : Subgroup X} [K.Normal] {f₁ f₂ κ c : X} (hf : f₁ * f₂ = f₂ * f₁)
    (hκ : κ ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set X)) (h1 : f₁ = κ * c) :
    κ⁻¹ * (f₂ * κ * f₂⁻¹) = c * (f₂ * c * f₂⁻¹)⁻¹ ∧
      κ⁻¹ * (f₂ * κ * f₂⁻¹) ∈ K ⊓ Subgroup.centralizer (K : Set X) := by
  have key : κ⁻¹ * (f₂ * κ * f₂⁻¹) = c * (f₂ * c * f₂⁻¹)⁻¹ := by
    have hcomm : κ * c * f₂ = f₂ * κ * c := by
      rw [h1] at hf
      rw [hf, mul_assoc]
    calc κ⁻¹ * (f₂ * κ * f₂⁻¹) = κ⁻¹ * (f₂ * κ * c) * c⁻¹ * f₂⁻¹ := by group
      _ = κ⁻¹ * (κ * c * f₂) * c⁻¹ * f₂⁻¹ := by rw [hcomm]
      _ = c * (f₂ * c * f₂⁻¹)⁻¹ := by group
  refine ⟨key, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · exact mul_mem (inv_mem hκ) (Subgroup.Normal.conj_mem ‹K.Normal› κ hκ f₂)
  · rw [key]
    exact mul_mem hc (inv_mem (conj_mem_centralizer hc f₂))

theorem conj_eq_of_mem_zpowers {z : X} (hz : z ∈ Subgroup.center X) {c : X}
    (hc : c ∈ Subgroup.zpowers z) (f : X) : f * c * f⁻¹ = c := by
  have h := Subgroup.mem_center_iff.1 (mem_center_of_mem_zpowers hz hc) f
  rw [h, mul_inv_cancel_right]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
