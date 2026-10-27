module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.FusionStepA
public import CFSG.ClassicalInvolution.LBalance.Glauberman.FusionEngine
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools

section Lemma1

variable {Ω : Type*} [Group Ω] [Finite Ω] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_not_mem_of_lt {D S : Subgroup Ω} (hS : IsPGroup p S)
    (hDS : D ≤ S) (hne : D ≠ S) :
    ∃ t ∈ S, t ∈ Subgroup.normalizer (D : Set Ω) ∧ t ∉ D := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : D.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hDS (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨t, htN, htD⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hDS, Subgroup.mem_subgroupOf] at htN
  exact ⟨t, t.2, htN, fun h => htD (Subgroup.mem_subgroupOf.mpr h)⟩

omit [Finite Ω] [Fact p.Prime] in
theorem closure_genSet_spec {H P R : Subgroup Ω} (hPR : P ≤ R) :
    Subgroup.closure (genSet H P R) ≤ R ∧ P ≤ Subgroup.closure (genSet H P R) ∧
      H ⊓ Subgroup.normalizer (R : Set Ω) ≤
        Subgroup.normalizer (Subgroup.closure (genSet H P R) : Set Ω) ∧
      Generated H P (Subgroup.closure (genSet H P R)) := by
  have h1 : Subgroup.closure (genSet H P R) ≤ R := by
    rw [Subgroup.closure_le]
    rintro x ⟨k, ⟨-, hkN⟩, hkx⟩
    exact (Subgroup.mem_normalizer_iff.1 hkN x).2 (hPR hkx)
  have h2 : P ≤ Subgroup.closure (genSet H P R) := by
    intro x hx
    apply Subgroup.subset_closure
    exact ⟨1, ⟨H.one_mem, (Subgroup.normalizer (R : Set Ω)).one_mem⟩, by simpa using hx⟩
  have key : ∀ k ∈ H ⊓ Subgroup.normalizer (R : Set Ω), ∀ y ∈ Subgroup.closure (genSet H P R),
      k * y * k⁻¹ ∈ Subgroup.closure (genSet H P R) := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      obtain ⟨k', hk', hk'x⟩ := hx
      refine ⟨k' * k⁻¹, (H ⊓ Subgroup.normalizer (R : Set Ω)).mul_mem hk'
        ((H ⊓ Subgroup.normalizer (R : Set Ω)).inv_mem hk), ?_⟩
      have e : k' * k⁻¹ * (k * x * k⁻¹) * (k' * k⁻¹)⁻¹ = k' * x * k'⁻¹ := by group
      rw [e]
      exact hk'x
    | one => simp
    | mul y z hy hz ihy ihz =>
      have := Subgroup.mul_mem _ ihy ihz
      simpa [mul_assoc] using this
    | inv y hy ih =>
      have := Subgroup.inv_mem _ ih
      simpa [mul_assoc] using this
  have h3 : H ⊓ Subgroup.normalizer (R : Set Ω) ≤
      Subgroup.normalizer (Subgroup.closure (genSet H P R) : Set Ω) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key k hk y, fun hy => ?_⟩
    have := key k⁻¹ ((H ⊓ Subgroup.normalizer (R : Set Ω)).inv_mem hk) _ hy
    simpa [mul_assoc] using this
  refine ⟨h1, h2, h3, ?_⟩
  unfold Generated
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro x ⟨k, hk, hkx⟩
    exact ⟨k, ⟨hk.1, h3 hk⟩, hkx⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨k, ⟨-, hkN⟩, hkx⟩
    exact (Subgroup.mem_normalizer_iff.1 hkN x).2 (h2 hkx)

theorem lemma1_caseI {H T P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (hPleT : P ≤ T) {g : Ω} (hg : g ∈ H)
    (hgP : g ∉ Subgroup.normalizer (P : Set Ω))
    (hgn : T ≤ Subgroup.normalizer (cj g P : Set Ω)) :
    (∃ Q, Good p H P T Q ∧ T ⊓ Subgroup.centralizer (T : Set Ω) ≤ Q) ∧
      ∃ Q, Good p H P T Q ∧ Generated H P Q := by
  obtain ⟨k, hk, hkP⟩ := exists_mem_normalizer_cj_eq hT hPT hg hgn
  have hkP' : k ∉ Subgroup.normalizer (P : Set Ω) := by
    intro hkN
    apply hgP
    have h1 : cj g P = P := by rw [← hkP]; exact cj_of_mem_normalizer hkN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h2 : x ∈ cj g P ↔ x ∈ P := by rw [h1]
    rw [mem_cj] at h2
    exact h2.symm
  have hTN : T ≤ H ⊓ Subgroup.normalizer (T : Set Ω) := le_inf hT.le Subgroup.le_normalizer
  refine ⟨⟨T, ⟨hPleT, le_rfl, ?_, k, hk, hkP'⟩, inf_le_left⟩, ?_⟩
  · rw [inf_eq_left.2 Subgroup.le_normalizer]
    exact hT.of_le hTN inf_le_left
  · obtain ⟨h1, h2, h3, h4⟩ := closure_genSet_spec (H := H) (R := T) hPleT
    have hTQ : T ≤ Subgroup.normalizer (Subgroup.closure (genSet H P T) : Set Ω) :=
      fun x hx => h3 (hTN hx)
    refine ⟨Subgroup.closure (genSet H P T), ⟨h2, h1, ?_, k, ⟨hk.1, h3 hk⟩, hkP'⟩, h4⟩
    rw [inf_eq_left.2 hTQ]
    exact hT.of_le (le_inf hT.le hTQ) inf_le_left

theorem lemma1_caseII_core {H T P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) {g : Ω} (hg : g ∈ H)
    (hgT : cj g P ≤ T) (hgn : ¬ T ≤ Subgroup.normalizer (cj g P : Set Ω)) :
    (∃ T₁ D : Subgroup Ω, IsSylowOf p T₁ H ∧ T₁ ≤ Subgroup.normalizer (P : Set Ω) ∧
        Good p H P T₁ D ∧ T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω) ≤ D) ∧
      ∃ T₂ Q : Subgroup Ω, IsSylowOf p T₂ H ∧ T₂ ≤ Subgroup.normalizer (P : Set Ω) ∧
        Good p H P T₂ Q ∧ Generated H P Q := by
  classical
  set NP : Subgroup Ω := Subgroup.normalizer (P : Set Ω) with hNP
  let 𝒮 : Set (Subgroup Ω) := {S | IsSylowOf p S H ∧ P ≤ S ∧ ¬ S ≤ NP}
  have hH : cj g⁻¹ H = H := cj_of_mem_normalizer (Subgroup.le_normalizer (H.inv_mem hg))
  have hS0 : cj g⁻¹ T ∈ 𝒮 := by
    refine ⟨?_, ?_, ?_⟩
    · have := (isSylowOf_cj_iff (p := p) g⁻¹).2 hT
      rwa [hH] at this
    · intro x hx
      have h1 : g⁻¹ * x * g ∈ T := by
        apply hgT
        show g * (g⁻¹ * x * g) * g⁻¹ ∈ P
        have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [e]
        exact hx
      show g⁻¹ * x * g⁻¹⁻¹ ∈ T
      simpa using h1
    · intro hle
      apply hgn
      intro t ht
      apply mem_normalizer_cj_iff.2
      apply hle
      show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ ∈ T
      have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
      rw [e]
      exact ht
  obtain ⟨S, ⟨hSsyl, hPS, hSnn⟩, hmax⟩ :=
    Set.exists_max_image 𝒮 (fun S => Nat.card ↥(NP ⊓ S)) (Set.toFinite _) ⟨_, hS0⟩
  set D : Subgroup Ω := NP ⊓ S with hD
  have hM : ∀ S' : Subgroup Ω, IsSylowOf p S' H → P ≤ S' → ¬ S' ≤ NP →
      Nat.card ↥(NP ⊓ S') ≤ Nat.card ↥D := fun S' h1 h2 h3 => hmax S' ⟨h1, h2, h3⟩
  have hDS : D ≤ S := inf_le_right
  have hDNP : D ≤ NP := inf_le_left
  have hPD : P ≤ D := le_inf Subgroup.le_normalizer hPS
  have hDH : D ≤ H := hDS.trans hSsyl.le
  have hSp : IsPGroup p S := hSsyl.isPGroup
  have hDp : IsPGroup p D := hSp.to_le hDS
  have hDne : D ≠ S := fun h => hSnn (by rw [← h]; exact hDNP)
  obtain ⟨n₁, hn₁S, hn₁N, hn₁D⟩ := exists_mem_normalizer_not_mem_of_lt hSp hDS hDne
  have hn₁P : n₁ ∉ NP := fun h => hn₁D ⟨h, hn₁S⟩
  have hn₁H : n₁ ∈ H := hSsyl.le hn₁S
  have hTN : IsSylowOf p T (H ⊓ NP) := hT.of_le (le_inf hT.le hPT) inf_le_left
  have hDHN : D ≤ H ⊓ NP := le_inf hDH hDNP
  obtain ⟨T', hDT', hT'⟩ := exists_isSylowOf_ge hDp hDHN
  have hcardT' : Nat.card T' = Nat.card S := by
    rw [hT'.card_eq, ← hTN.card_eq, hT.card_eq, ← hSsyl.card_eq]
  have hDT'ne : D ≠ T' := by
    intro h
    apply hDne
    apply Subgroup.eq_of_le_of_card_ge hDS
    rw [← hcardT', ← h]
  obtain ⟨n₂, hn₂T', hn₂N, hn₂D⟩ :=
    exists_mem_normalizer_not_mem_of_lt hT'.isPGroup hDT' hDT'ne
  set E : Subgroup Ω := T' ⊓ Subgroup.normalizer (D : Set Ω) with hE
  have hT'H : T' ≤ H := hT'.le.trans inf_le_left
  have hT'NP : T' ≤ NP := hT'.le.trans inf_le_right
  have hEH : E ≤ H ⊓ Subgroup.normalizer (D : Set Ω) := inf_le_inf_right _ hT'H
  have hENP : E ≤ NP := inf_le_left.trans hT'NP
  have hEp : IsPGroup p E := hT'.isPGroup.to_inf_left
  have hDE : D < E := lt_of_le_of_ne (le_inf hDT' Subgroup.le_normalizer) fun h =>
    hn₂D (by rw [h]; exact ⟨hn₂T', hn₂N⟩)
  have hEM : Nat.card ↥D < Nat.card ↥E := Subgroup.card_lt_of_lt hDE
  obtain ⟨T₁, hT₁, hT₁P, hDT₁, hb⟩ := engine hM hPD hDH hDp hEH hENP hEp hEM
  have hgood : Good p H P T₁ D := ⟨hPD, hDT₁, hb, n₁, ⟨hn₁H, hn₁N⟩, hn₁P⟩
  have hZ : T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω) ≤ D := by
    have hX₀p : IsPGroup p ↥(S ⊓ Subgroup.normalizer (D : Set Ω)) := hSp.to_inf_left
    have hX₀H : S ⊓ Subgroup.normalizer (D : Set Ω) ≤ H ⊓ Subgroup.normalizer (D : Set Ω) :=
      inf_le_inf_right _ hSsyl.le
    obtain ⟨S₀, hXS₀, hS₀⟩ := exists_isSylowOf_ge hX₀p hX₀H
    have hS₀H : S₀ ≤ H := hS₀.le.trans inf_le_left
    obtain ⟨S₁, hS₀S₁, hS₁⟩ := exists_isSylowOf_ge hS₀.isPGroup hS₀H
    have hDS₀ : D ≤ S₀ := (le_inf hDS Subgroup.le_normalizer).trans hXS₀
    have hn₁S₁ : n₁ ∈ S₁ := hS₀S₁ (hXS₀ ⟨hn₁S, hn₁N⟩)
    have h1 := hM S₁ hS₁ (hPD.trans (hDS₀.trans hS₀S₁)) (fun h => hn₁P (h hn₁S₁))
    set CD := Subgroup.centralizer (D : Set Ω) with hCD
    have hCDNP : CD ≤ NP :=
      (Subgroup.centralizer_le (by exact_mod_cast hPD)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hsup : D ⊔ (S₀ ⊓ CD) ≤ NP ⊓ S₁ :=
      sup_le (le_inf hDNP (hDS₀.trans hS₀S₁))
        (le_inf (inf_le_right.trans hCDNP) (inf_le_left.trans hS₀S₁))
    have hcard := Subgroup.card_le_of_le hsup
    have heq : D ⊔ (S₀ ⊓ CD) = D :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left (hcard.trans h1)).symm
    have hZle : S₀ ⊓ CD ≤ D := heq ▸ le_sup_right
    have hYD : IsSylowOf p (S₀ ⊓ (H ⊓ CD)) (H ⊓ CD) :=
      hS₀.inf_of_le_normalizer (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
        (inf_normalizer_le_normalizer_inf_centralizer H D)
    have hS₀CD : S₀ ⊓ (H ⊓ CD) = D ⊓ CD := by
      ext x
      constructor
      · intro hx
        exact ⟨hZle ⟨hx.1, hx.2.2⟩, hx.2.2⟩
      · intro hx
        exact ⟨hDS₀ hx.1, hDH hx.1, hx.2⟩
    rw [hS₀CD] at hYD
    have hXT₁ : (D ⊓ CD) ⊔ (T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω)) ≤ T₁ :=
      sup_le (inf_le_left.trans hDT₁) inf_le_left
    have hXp : IsPGroup p ↥((D ⊓ CD) ⊔ (T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω))) :=
      hT₁.isPGroup.to_le hXT₁
    have hXY : (D ⊓ CD) ⊔ (T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω)) ≤ H ⊓ CD := by
      refine sup_le (inf_le_inf_right _ hDH) (fun x hx => ⟨hT₁.le hx.1, ?_⟩)
      exact Subgroup.centralizer_le (by exact_mod_cast hDT₁) hx.2
    have heqX := hYD.eq_of_le le_sup_left hXY hXp
    intro x hx
    have : x ∈ (D ⊓ CD) ⊔ (T₁ ⊓ Subgroup.centralizer (T₁ : Set Ω)) := Subgroup.mem_sup_right hx
    rw [heqX] at this
    exact this.1
  obtain ⟨c1, c2, c3, c4⟩ := closure_genSet_spec (H := H) (R := D) hPD
  set Q : Subgroup Ω := Subgroup.closure (genSet H P D) with hQ
  have hQp : IsPGroup p Q := hDp.to_le c1
  have hQH : Q ≤ H := c1.trans hDH
  have hEQ : E ≤ H ⊓ Subgroup.normalizer (Q : Set Ω) := fun x hx => ⟨(hEH hx).1, c3 (hEH hx)⟩
  obtain ⟨T₂, hT₂, hT₂P, hQT₂, hb₂⟩ := engine hM c2 hQH hQp hEQ hENP hEp hEM
  have hgood₂ : Good p H P T₂ Q := ⟨c2, hQT₂, hb₂, n₁, ⟨hn₁H, c3 ⟨hn₁H, hn₁N⟩⟩, hn₁P⟩
  exact ⟨⟨T₁, D, hT₁, hT₁P, hgood, hZ⟩, ⟨T₂, Q, hT₂, hT₂P, hgood₂, c4⟩⟩

theorem exists_cj_eq_of_isSylowOf {H T T₁ P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (hT₁ : IsSylowOf p T₁ H)
    (hT₁P : T₁ ≤ Subgroup.normalizer (P : Set Ω)) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (P : Set Ω), cj n T₁ = T := by
  have h1 : IsSylowOf p T (H ⊓ Subgroup.normalizer (P : Set Ω)) :=
    hT.of_le (le_inf hT.le hPT) inf_le_left
  have h2 : IsSylowOf p T₁ (H ⊓ Subgroup.normalizer (P : Set Ω)) :=
    hT₁.of_le (le_inf hT₁.le hT₁P) inf_le_left
  obtain ⟨n, hn, hconj⟩ := isSylowOf_exists_conj h1 h2
  refine ⟨n, hn, ?_⟩
  ext x
  rw [mem_cj, hconj]
  have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
  rw [e]

@[expose] def LocalControl (p : ℕ) (H T P Q : Subgroup Ω) : Prop :=
  P ≤ Q ∧ Q ≤ T ∧
    IsSylowOf p (T ⊓ Subgroup.normalizer (Q : Set Ω)) (H ⊓ Subgroup.normalizer (Q : Set Ω)) ∧
    IsSylowOf p (T ⊓ Subgroup.normalizer (Q : Set Ω))
      (H ⊓ Subgroup.normalizer (Q : Set Ω) ⊓
        Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Q : Set Ω) : Subgroup Ω) : Set Ω)) ∧
    ∃ h ∈ H ⊓ Subgroup.normalizer (Q : Set Ω) ⊓
        Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Q : Set Ω) : Subgroup Ω) : Set Ω),
      (∃ r : ℕ, r.Prime ∧ r ≠ p ∧ ∃ n : ℕ, orderOf h = r ^ n) ∧
        h ∉ Subgroup.normalizer (P : Set Ω)

theorem Good.localControl {H T P Q : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (h : Good p H P T Q) :
    LocalControl p H T P Q := by
  obtain ⟨hPQ, hQT, hb, k, hk, hkP⟩ := h
  obtain ⟨hc, hd⟩ := step_cd hPT hT.le hPQ hb hk hkP
  exact ⟨hPQ, hQT, hb, hc, hd⟩

theorem lemma1_central {H T P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (hPleT : P ≤ T) {g : Ω} (hg : g ∈ H)
    (hgT : cj g P ≤ T) (hgP : g ∉ Subgroup.normalizer (P : Set Ω)) :
    ∃ Q : Subgroup Ω, LocalControl p H T P Q ∧ T ⊓ Subgroup.centralizer (T : Set Ω) ≤ Q := by
  by_cases hn : T ≤ Subgroup.normalizer (cj g P : Set Ω)
  · obtain ⟨⟨Q, hQ, hZ⟩, -⟩ := lemma1_caseI hT hPT hPleT hg hgP hn
    exact ⟨Q, hQ.localControl hT hPT, hZ⟩
  · obtain ⟨⟨T₁, D, hT₁, hT₁P, hD, hZ⟩, -⟩ := lemma1_caseII_core hT hPT hg hgT hn
    obtain ⟨n, hn, hTn⟩ := exists_cj_eq_of_isSylowOf hT hPT hT₁ hT₁P
    refine ⟨cj n D, ?_, ?_⟩
    · have := good_cj hn.1 hn.2 hD
      rw [hTn] at this
      exact this.localControl hT hPT
    · rw [← hTn, ← cj_centralizer, ← cj_inf]
      exact cj_le_cj hZ

theorem lemma1_generated {H T P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (hPleT : P ≤ T) {g : Ω} (hg : g ∈ H)
    (hgT : cj g P ≤ T) (hgP : g ∉ Subgroup.normalizer (P : Set Ω)) :
    ∃ Q : Subgroup Ω, LocalControl p H T P Q ∧ Generated H P Q := by
  by_cases hn : T ≤ Subgroup.normalizer (cj g P : Set Ω)
  · obtain ⟨-, ⟨Q, hQ, hG⟩⟩ := lemma1_caseI hT hPT hPleT hg hgP hn
    exact ⟨Q, hQ.localControl hT hPT, hG⟩
  · obtain ⟨-, ⟨T₂, Q, hT₂, hT₂P, hQ, hG⟩⟩ := lemma1_caseII_core hT hPT hg hgT hn
    obtain ⟨n, hn, hTn⟩ := exists_cj_eq_of_isSylowOf hT hPT hT₂ hT₂P
    refine ⟨cj n Q, ?_, generated_cj hn.1 hn.2 hG⟩
    have := good_cj hn.1 hn.2 hQ
    rw [hTn] at this
    exact this.localControl hT hPT

end Lemma1

end CFSG.ClassicalInvolution.GlaubermanAut
