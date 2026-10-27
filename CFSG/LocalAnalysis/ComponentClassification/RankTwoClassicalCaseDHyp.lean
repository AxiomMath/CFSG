module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseD

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Sec3

variable {R T' : Subgroup G} {x : G} (h' : Sec3 A R T' x)
include h'

theorem le_sup_of_aParts (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    {X : Subgroup G} (hX : ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R → p' ∈ X) :
    T' ≤ R ⊔ X := by
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact one_mem _
  obtain ⟨p', hp', hρ'⟩ := h'.exists_aPart h32 h4 h34 hs
  have h1 : s = p' * (s⁻¹ * p')⁻¹ := by group
  rw [h1]
  exact mul_mem (mem_sup_right (hX s hs hs1 p' hp' hρ')) (mem_sup_left (inv_mem hρ'))

theorem inf_sup_eq_bot_of_aParts (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hZ : Odd (Nat.card (center ↥A))) {V X : Subgroup G} (htwo : ∀ v ∈ V, v * v = 1)
    (hRV : R ≤ V) (hXV : X ≤ V) (hXA : X ≤ A)
    (hX : ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R → p' ∉ X) : T' ⊓ (R ⊔ X) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [mem_bot]
  by_contra hs1
  obtain ⟨hsT, hsRX⟩ := mem_inf.mp hs
  obtain ⟨r, hr, u, hu, hsru⟩ := exists_mul_of_mem_sup htwo hRV hXV hsRX
  obtain ⟨p', hp', hρ'⟩ := h'.exists_aPart h32 h4 h34 hsT
  have hp'u : p' = u := h'.aPart_eq_of_mul hZ hp' hρ' hr (hXA hu) hsru.symm
  exact hX _ hsT hs1 p' hp' hρ' (hp'u ▸ hu)

end Sec3

namespace Case23Setup

variable {D : ClassicalModel A} {R T : Subgroup G} {p : G} {U W : Subgroup G} {y₁ y₂ : G}
  {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ) {g : G} (hc : Sec3 A R T g)
include hS hc

theorem aPart_mem_of_le (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    {T' : Subgroup G} (hT'V : T' ≤ sec3V R T) {s p' : G} (hs : s ∈ T') (hp' : p' ∈ A)
    (hρ' : s⁻¹ * p' ∈ R) : p' ∈ jGroup A p := by
  rw [← hS.inf_sec3V_eq hc h32 h4 h34]
  refine mem_inf.mpr ⟨?_, hp'⟩
  have h1 : p' = s * (s⁻¹ * p') := by group
  rw [h1]
  exact mul_mem (hT'V hs) (hc.R_le_sec3V hρ')

theorem trichotomy (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    {T' : Subgroup G} {x : G} (h' : Sec3 A R T' x) (hT'V : T' ≤ sec3V R T) :
    (∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R → p' ∈ U) ∨
      (∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R → p' ∈ W) ∨
      (∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R → p' ∉ U ∧ p' ∉ W) := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hfus :=
    (I.h222.conclusion D hS.four_le (h'.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).2.1
  obtain ⟨s₀, hs₀, hs₀1⟩ := T'.bot_or_exists_ne_one.resolve_left h'.T_ne_bot
  obtain ⟨p₀, hp₀, hρ₀⟩ := h'.exists_aPart I.h32 I.h4 I.h34 hs₀
  have hp₀J := hS.aPart_mem_of_le hc I.h32 I.h4 I.h34 hT'V hs₀ hp₀ hρ₀
  have hp₀1 := h'.aPart_ne_one hs₀ hs₀1 hρ₀
  have htr : ∀ s ∈ T', s ≠ 1 → ∀ p' ∈ A, s⁻¹ * p' ∈ R →
      (p₀ ∈ U ↔ p' ∈ U) ∧ (p₀ ∈ W ↔ p' ∈ W) := by
    intro s hs hs1 p' hp' hρ'
    obtain ⟨a, ha, hap⟩ := hfus s₀ hs₀ hs₀1 s hs hs1 p₀ p' (h'.isAPart I.h32 hs₀ hp₀ hρ₀)
      (h'.isAPart I.h32 hs hp' hρ')
    have hp'J := hS.aPart_mem_of_le hc I.h32 I.h4 I.h34 hT'V hs hp' hρ'
    have h1 := hS.diag.sep a ha p₀ hp₀J hp₀1 (hap ▸ hp'J)
    rw [hap] at h1
    exact h1
  by_cases hU : p₀ ∈ U
  · exact Or.inl fun s hs hs1 p' hp' hρ' => (htr s hs hs1 p' hp' hρ').1.mp hU
  · by_cases hW : p₀ ∈ W
    · exact Or.inr (Or.inl fun s hs hs1 p' hp' hρ' => (htr s hs hs1 p' hp' hρ').2.mp hW)
    · refine Or.inr (Or.inr fun s hs hs1 p' hp' hρ' => ?_)
      have h1 := htr s hs hs1 p' hp' hρ'
      exact ⟨fun h => hU (h1.1.mpr h), fun h => hW (h1.2.mpr h)⟩

omit hS in
theorem two (h32 : Lemma32) : ∀ v ∈ sec3V R T, v * v = 1 := fun v hv => by
  have := (hc.isElemAbelian_V h32).2 v hv
  rwa [sq] at this

theorem normalizer_le_V (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    A ⊓ normalizer (jGroup A p : Set G) ≤ normalizer (sec3V R T : Set G) := by
  intro a ha
  rw [hS.sec3V_eq_sup hc h32 h4 h34]
  refine mem_normalizer_sup (centralizer_le_normalizer _ ?_) (mem_inf.mp ha).2
  rw [mem_centralizer_iff]
  intro r hr
  exact (hc.commute_of_mem (mem_inf.mp ha).1 hr).eq.symm

omit hS in
theorem le_centralizer_R : A ≤ centralizer (R : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro r hr
  exact (hc.commute_of_mem ha hr).eq.symm

omit [Finite G] hc in
theorem fix_of {X Y : Subgroup G} (hYJ : Y ≤ jGroup A p) (hX3 : 3 ≤ Nat.card X)
    (hXY : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → x * y ∈ diagSet (jGroup A p) U W) :
    ∀ a ∈ A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (X : Set G), ∀ y ∈ Y, y ≠ 1 →
      a⁻¹ * y * a = y → a ∈ centralizer (Y : Set G) := by
  intro a ha y hy hy1 hfix
  obtain ⟨haAN, haX⟩ := mem_inf.mp ha
  obtain ⟨x, hx, hx1, -⟩ := exists_ne_ne_of_three_le hX3 1 1
  have ha' : a⁻¹ ∈ A ⊓ normalizer (jGroup A p : Set G) := inv_mem haAN
  have hax : a⁻¹ * x * a = x := by
    have h1 := mem_centralizer_iff.mp haX x hx
    calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
      _ = a⁻¹ * (a * x) := by rw [h1]
      _ = x := by group
  have hfix' : a⁻¹ * (x * y) * a⁻¹⁻¹ = x * y := by
    calc a⁻¹ * (x * y) * a⁻¹⁻¹ = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
      _ = x * y := by rw [hax, hfix]
  have h1 := hS.diag.free a⁻¹ ha' _ (hXY x hx hx1 y hy hy1) hfix'
  have h2 : a ∈ centralizer (jGroup A p : Set G) := by simpa using inv_mem h1
  exact centralizer_le (fun z hz => hYJ hz) h2

theorem normal_field (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    ∀ n ∈ normalizer (sec3V R T : Set G), n ∈ normalizer (R : Set G) →
      ∀ a ∈ A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (U : Set G),
      ∀ b ∈ A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (W : Set G),
      ∃ a' ∈ A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (U : Set G),
      ∃ b' ∈ A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (W : Set G),
      ∃ c ∈ centralizer (sec3V R T : Set G), n⁻¹ * (a * b) * n = a' * b' * c := by
  intro n hnX hnR a ha b hb
  have hnA : n ∈ normalizer (A : Set G) := by
    have h1 := Lemma36.normalizer_le hc.hyp hc.sylowR 1
    rw [rightConjugate_one, rightConjugate_one] at h1
    exact h1 hnR
  have hnJ : n ∈ normalizer (jGroup A p : Set G) := by
    rw [← hS.inf_sec3V_eq hc h32 h4 h34, mem_normalizer_iff]
    intro x
    simp only [mem_inf]
    rw [mem_normalizer_iff.mp hnX x, mem_normalizer_iff.mp hnA x]
  have hab : a * b ∈ A ⊓ normalizer (jGroup A p : Set G) :=
    mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1
  have hd : n⁻¹ * (a * b) * n ∈ A ⊓ normalizer (jGroup A p : Set G) := by
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hnJ) (mem_inf.mp hab).2) hnJ⟩
    have h1 := (mem_normalizer_iff.mp (inv_mem hnA) (a * b)).mp (mem_inf.mp hab).1
    simpa using h1
  obtain ⟨k₁, k₂, hk⟩ := hS.diag.gen _ hd
  refine ⟨y₁ ^ k₁, pow_mem (mem_inf.mpr ⟨hS.diag.y₁_mem, hS.diag.y₁_cent⟩) k₁, y₂ ^ k₂,
    pow_mem (mem_inf.mpr ⟨hS.diag.y₂_mem, hS.diag.y₂_cent⟩) k₂,
    (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * (n⁻¹ * (a * b) * n), ?_, by group⟩
  have hcA : (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * (n⁻¹ * (a * b) * n) ∈ A :=
    mul_mem (inv_mem (mul_mem (pow_mem (mem_inf.mp hS.diag.y₁_mem).1 k₁)
      (pow_mem (mem_inf.mp hS.diag.y₂_mem).1 k₂))) (mem_inf.mp hd).1
  rw [hS.sec3V_eq_sup hc h32 h4 h34]
  exact mem_centralizer_sup (le_centralizer_R hc hcA) hk

theorem one_field (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) :
    ∀ T' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T' ≠ R → T' ⊓ R = ⊥ ∧
      (T' ≤ R ⊔ U ∨ T' ≤ R ⊔ W ∨ (T' ⊓ (R ⊔ U) = ⊥ ∧ T' ⊓ (R ⊔ W) = ⊥)) := by
  rintro T' ⟨x, hx, rfl⟩ hne
  have h' := hc.of_mem_normalizer I.h32 hx hne
  have hT'V := Lemma36.rightConjugate_le hc.R_le_sec3V hx
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  refine ⟨by rw [inf_comm]; exact h'.inf_eq_bot, ?_⟩
  rcases hS.trichotomy hc I hTy h' hT'V with hU | hW | hΓ
  · exact Or.inl (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hU)
  · exact Or.inr (Or.inl (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hW))
  · exact Or.inr (Or.inr ⟨h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hS.oddCenter
      (Case23Setup.two hc I.h32) hc.R_le_sec3V (hS.diag.U_le.trans hJV) (hS.diag.U_le.trans hJA)
      (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').1),
      h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hS.oddCenter (Case23Setup.two hc I.h32)
      hc.R_le_sec3V (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA)
      (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').2)⟩)

theorem gHyp51 (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (hU : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ U → (rightConjugate R x = U ∧
        ∀ T'' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T'' ≤ R ⊔ U →
          T'' = R ∨ T'' = U) ∨ rightConjugate R x ⊓ U = ⊥)
    (hW : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ W → (rightConjugate R x = W ∧
        ∀ T'' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T'' ≤ R ⊔ W →
          T'' = R ∨ T'' = W) ∨ rightConjugate R x ⊓ W = ⊥)
    (h3 : ∃ T' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T' ≠ R ∧
      T' ⊓ (R ⊔ U) = ⊥ ∧ T' ⊓ (R ⊔ W) = ⊥) :
    GHyp51 (sec3V R T) R U W (normalizer (sec3V R T : Set G))
      (A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (U : Set G))
      (A ⊓ normalizer (jGroup A p : Set G) ⊓ centralizer (W : Set G)) := by
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  have hNV := hS.normalizer_le_V hc I.h32 I.h4 I.h34
  have hAC := le_centralizer_R hc
  exact
    { two := Case23Setup.two hc I.h32
      R_le := hc.R_le_sec3V
      U_le := hS.diag.U_le.trans hJV
      W_le := hS.diag.W_le.trans hJV
      sup_eq := by rw [sup_assoc, ← hS.diag.J_eq, ← hS.sec3V_eq_sup hc I.h32 I.h4 I.h34]
      inf_R := by
        rw [← hS.diag.J_eq]
        exact eq_bot_iff.mpr ((inf_le_inf_left R hJA).trans (hc.R_inf_A hZ).le)
      inf_U := hS.diag.inf_eq
      two_lt := by
        have := hc.four_le
        omega
      card_eq := by rw [hS.card_U, hS.card_W]
      X_le := le_rfl
      A_le := fun a ha => hNV (mem_inf.mp ha).1
      B_le := fun a ha => hNV (mem_inf.mp ha).1
      A_centR := fun a ha => hAC (mem_inf.mp (mem_inf.mp ha).1).1
      A_centU := fun a ha => (mem_inf.mp ha).2
      A_normW := fun a ha => hS.diag.normalizer_le_W (mem_inf.mp ha).1
      B_centR := fun a ha => hAC (mem_inf.mp (mem_inf.mp ha).1).1
      B_centW := fun a ha => (mem_inf.mp ha).2
      B_normU := fun a ha => hS.diag.normalizer_le_U (mem_inf.mp ha).1
      A_trans := fun w hw w' hw' hw1 hw'1 => by
        obtain ⟨a, ha, he⟩ := hS.diag.trans_W hw hw1 hw' hw'1
        exact ⟨a, (zpowers_le.mpr (mem_inf.mpr ⟨hS.diag.y₁_mem, hS.diag.y₁_cent⟩)) ha, he⟩
      A_fix := hS.fix_of hS.diag.W_le hS.diag.three_le_U
        (fun u hu hu1 w hw hw1 => hS.diag.mul_mem_diagSet hu hu1 hw hw1)
      B_trans := fun u hu u' hu' hu1 hu'1 => by
        obtain ⟨a, ha, he⟩ := hS.diag.trans_U hu hu1 hu' hu'1
        exact ⟨a, (zpowers_le.mpr (mem_inf.mpr ⟨hS.diag.y₂_mem, hS.diag.y₂_cent⟩)) ha, he⟩
      B_fix := hS.fix_of hS.diag.U_le hS.diag.three_le_W
        (fun w hw hw1 u hu hu1 => hS.diag.mul_mem_diagSet' hu hu1 hw hw1)
      normal := hS.normal_field hc I.h32 I.h4 I.h34
      one := hS.one_field hc I hTy
      twoU := by
        rintro T' ⟨x, hx, rfl⟩ hle
        by_cases hne : rightConjugate R x = R
        · rw [hne]
          exact Or.inr (eq_bot_iff.mpr
            ((inf_le_inf_left R (hS.diag.U_le.trans hJA)).trans (hc.R_inf_A hZ).le))
        · exact hU x hx hne hle
      twoW := by
        rintro T' ⟨x, hx, rfl⟩ hle
        by_cases hne : rightConjugate R x = R
        · rw [hne]
          exact Or.inr (eq_bot_iff.mpr
            ((inf_le_inf_left R (hS.diag.W_le.trans hJA)).trans (hc.R_inf_A hZ).le))
        · exact hW x hx hne hle
      three := h3 }

end Case23Setup

end CFSG.ComponentClassification.RankTwoClassical
