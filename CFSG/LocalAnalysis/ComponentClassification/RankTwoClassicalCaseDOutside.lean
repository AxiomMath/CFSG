module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDHyp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b.Sec5

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Sec3.exists_aPart_mem_of_le {R T' : Subgroup G} {x : G} (h' : Sec3 A R T' x)
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (hZ : Odd (Nat.card (center ↥A)))
    {V X : Subgroup G} (htwo : ∀ v ∈ V, v * v = 1) (hRV : R ≤ V) (hXV : X ≤ V) (hXA : X ≤ A)
    (hle : T' ≤ R ⊔ X) : ∃ s ∈ T', s ≠ 1 ∧ ∃ p' ∈ X, p' ≠ 1 ∧ s⁻¹ * p' ∈ R := by
  obtain ⟨s, hs, hs1⟩ := T'.bot_or_exists_ne_one.resolve_left h'.T_ne_bot
  obtain ⟨p', hp', hρ'⟩ := h'.exists_aPart h32 h4 h34 hs
  obtain ⟨r, hr, u, hu, hsru⟩ := exists_mul_of_mem_sup htwo hRV hXV (hle hs)
  have hp'u : p' = u := h'.aPart_eq_of_mul hZ hp' hρ' hr (hXA hu) hsru.symm
  exact ⟨s, hs, hs1, p', hp'u ▸ hu, h'.aPart_ne_one hs hs1 hρ', hρ'⟩

namespace Case23Setup

variable {D : ClassicalModel A} {R T : Subgroup G} {p : G} {U W : Subgroup G} {y₁ y₂ : G}
  {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ)
include hS

omit [Finite G] in
theorem two_le_ℓ : 2 ≤ ℓ := by
  rcases hS.types with ⟨hℓ, -, -⟩ | ⟨hpc, -⟩
  · omega
  · have hev := D.even_of_suzukiType hpc (by intro h; cases h)
    have hpos := D.pos_of_hasRank (D.hasRank_of_suzukiType hpc)
    obtain ⟨k, hk⟩ := hev
    omega

omit [Finite G] in
theorem seven_le {n : ℕ} (hpn : D.HasMeasure p n) (hnp : ¬ D.IsPrimary p) : 7 ≤ n := by
  have hℓ := hS.two_le_ℓ
  rcases hS.types with ⟨-, hpb, -⟩ | ⟨hpc, -⟩
  · have := hpn.ge_of_not_isPrimary (D.hasRank_of_suzukiType hpb) hnp
    omega
  · have := hpn.ge_of_not_isPrimary (D.hasRank_of_suzukiType hpc) hnp
    omega

end Case23Setup

variable {R T : Subgroup G} {g : G}

theorem MinChoice.false_of_case23 (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (D : ClassicalModel A) (hfam : D.family = .symplectic) (hq : 4 ≤ D.q)
    (hm : MinChoice D R T g) (hTA : ¬ T ≤ A) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) (hpn : D.HasMeasure p (choiceMeasure D R T)) (h23 : Case23 D p) :
    False := by
  have hc := hm.sec3
  have hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A :=
    fun T' x h' hT' => hTA (hm.le_of_le T' x h' hT')
  obtain ⟨U, W, y₁, y₂, ℓ, hS⟩ := hc.exists_case23Setup I hTy D hfam hq ht ht1 hp hρ h23
  have hZ := hS.oddCenter
  have hJV := hS.jGroup_le_sec3V hc I.h32 I.h4 I.h34
  have hJA : jGroup A p ≤ A := hS.vdata.le
  have htwo := Case23Setup.two hc I.h32
  have hnp : ¬ D.IsPrimary p := fun h => D.not_case23_of_isPrimary h h23
  have hn7 := hS.seven_le hpn hnp
  have hWbad : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ W → False := by
    intro x hx hne hle
    have h' := hc.of_mem_normalizer I.h32 hx hne
    obtain ⟨s, hs, hs1, w, hw, hw1, hρ'⟩ := h'.exists_aPart_mem_of_le I.h32 I.h4 I.h34 hZ htwo
      hc.R_le_sec3V (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA) hle
    have h1 := hm.le_of_mem h' (Or.inr hTA) hs hs1 (hS.diag.W_le.trans hJA hw) hρ'
      (D.hasMeasure_three_of_isPrimary hfam (hS.prim_W w hw hw1))
    omega
  have hU : ∀ x ∈ normalizer (sec3V R T : Set G), rightConjugate R x ≠ R →
      rightConjugate R x ≤ R ⊔ U → rightConjugate R x ⊓ U = ⊥ := by
    intro x hx hne hle
    have h' := hc.of_mem_normalizer I.h32 hx hne
    rcases hS.types with ⟨hℓ, hpb, hUa⟩ | ⟨-, hUa⟩
    ·
      exfalso
      obtain ⟨s, hs, hs1, u, hu, hu1, hρ'⟩ := h'.exists_aPart_mem_of_le I.h32 I.h4 I.h34 hZ
        htwo hc.R_le_sec3V (hS.diag.U_le.trans hJV) (hS.diag.U_le.trans hJA) hle
      have hta := hUa u hu hu1
      have hev := D.even_of_suzukiType hta (by intro h; cases h)
      have hpos := D.pos_of_hasRank (D.hasRank_of_suzukiType hta)
      obtain ⟨k, hk⟩ := hev
      have hℓ1 : 1 < ℓ - 1 := by omega
      have hn := hpn.unique (D.hasMeasure_of_suzukiType_b hpb hℓ hfam)
      have h1 := hm.le_of_mem h' (Or.inr hTA) hs hs1 (hS.diag.U_le.trans hJA hu) hρ'
        (D.hasMeasure_of_suzukiType_a hta hℓ1 hfam)
      omega
    ·
      by_contra hUne
      obtain ⟨u, hu, hu1⟩ := (rightConjugate R x ⊓ U).bot_or_exists_ne_one.resolve_left hUne
      obtain ⟨huT, huU⟩ := mem_inf.mp hu
      have huA : u ∈ A := hS.diag.U_le.trans hJA huU
      rcases h'.inf_eq_bot_or_le_of_typeA I hTy D hfam hq huT hu1 huA
        (by rw [inv_mul_cancel]; exact one_mem _) (hUa u huU hu1) with h | h
      · have h1 : u ∈ rightConjugate R x ⊓ A := mem_inf.mpr ⟨huT, huA⟩
        rw [h, mem_bot] at h1
        exact hu1 h1
      · exact hno _ x h' h
  have h3 : ∃ T' ∈ gMembers (normalizer (sec3V R T : Set G)) R, T' ≠ R ∧
      T' ⊓ (R ⊔ U) = ⊥ ∧ T' ⊓ (R ⊔ W) = ⊥ := by
    obtain ⟨x, hx, hnle⟩ := hc.exists_not_le I hTy D hfam hq hS hno
    have hne : rightConjugate R x ≠ R := by
      intro h
      apply hnle
      rw [h]
      exact le_sup_left
    have h' := hc.of_mem_normalizer I.h32 hx hne
    have hT'V := Lemma36.rightConjugate_le hc.R_le_sec3V hx
    refine ⟨rightConjugate R x, ⟨x, hx, rfl⟩, hne, ?_⟩
    rcases hS.trichotomy hc I hTy h' hT'V with hU' | hW' | hΓ
    · exact absurd (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hU') hnle
    · exact (hWbad x hx hne (h'.le_sup_of_aParts I.h32 I.h4 I.h34 hW')).elim
    · exact ⟨h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.U_le.trans hJV) (hS.diag.U_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').1),
        h'.inf_sup_eq_bot_of_aParts I.h32 I.h4 I.h34 hZ htwo hc.R_le_sec3V
        (hS.diag.W_le.trans hJV) (hS.diag.W_le.trans hJA)
        (fun s hs hs1 p' hp' hρ' => (hΓ s hs hs1 p' hp' hρ').2)⟩
  have hG := hS.gHyp51 hc I hTy (fun x hx hne hle => Or.inr (hU x hx hne hle))
    (fun x hx hne hle => (hWbad x hx hne hle).elim) h3
  rcases fusionLemmaG_rot hG with ⟨-, -, T'', ⟨x, hx, rfl⟩, hle, -, hR⟩ | ⟨-, -, -, x, hx, hWx⟩
  · have hne : rightConjugate R x ≠ R := by
      intro h
      rw [h, inf_idem] at hR
      exact hc.R_ne_bot hR
    exact hWbad x hx hne hle
  · have hWA' : rightConjugate R x ≤ A := by
      rw [hWx]
      exact hS.diag.W_le.trans hJA
    exact hno _ _ (hc.sec3_of_le I.h32 hZ hWA') hWA'

end CFSG.ComponentClassification.RankTwoClassical
