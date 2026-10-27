module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
public import CFSG.ClassicalInvolution.LBalance.Glauberman.ConjTools

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools

section Fusion

variable {Ω : Type*} [Group Ω] [Finite Ω] {p : ℕ} [Fact p.Prime]

@[expose] def Good (p : ℕ) (H P T Q : Subgroup Ω) : Prop :=
  P ≤ Q ∧ Q ≤ T ∧
    IsSylowOf p (T ⊓ Subgroup.normalizer (Q : Set Ω)) (H ⊓ Subgroup.normalizer (Q : Set Ω)) ∧
    ∃ k ∈ H ⊓ Subgroup.normalizer (Q : Set Ω), k ∉ Subgroup.normalizer (P : Set Ω)

@[expose] def Generated (H P Q : Subgroup Ω) : Prop :=
  Q = Subgroup.closure {x : Ω | ∃ k ∈ H ⊓ Subgroup.normalizer (Q : Set Ω), k * x * k⁻¹ ∈ P}

omit [Finite Ω] in
theorem mem_normalizer_cj_iff {g t : Ω} {P : Subgroup Ω} :
    t ∈ Subgroup.normalizer (cj g P : Set Ω) ↔ g * t * g⁻¹ ∈ Subgroup.normalizer (P : Set Ω) := by
  rw [← cj_normalizer, mem_cj]

theorem good_cj {H P T Q : Subgroup Ω} {n : Ω} (hnH : n ∈ H)
    (hnP : n ∈ Subgroup.normalizer (P : Set Ω)) (h : Good p H P T Q) :
    Good p H P (cj n T) (cj n Q) := by
  obtain ⟨hPQ, hQT, hb, k, hk, hkP⟩ := h
  have hH : cj n H = H := cj_of_mem_normalizer (Subgroup.le_normalizer hnH)
  refine ⟨?_, cj_le_cj hQT, ?_, ?_⟩
  · intro x hx
    exact hPQ ((Subgroup.mem_normalizer_iff.1 hnP x).1 hx)
  · have := (isSylowOf_cj_iff (p := p) n).2 hb
    rwa [cj_inf, cj_inf, cj_normalizer, hH] at this
  · refine ⟨n⁻¹ * k * n, ?_, ?_⟩
    · have e : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
      have hkN : n⁻¹ * k * n ∈ Subgroup.normalizer (cj n Q : Set Ω) := by
        rw [← cj_normalizer, mem_cj, e]
        exact hk.2
      exact ⟨H.mul_mem (H.mul_mem (H.inv_mem hnH) hk.1) hnH, hkN⟩
    · intro h
      apply hkP
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hnP h) (inv_mem hnP)
      simpa [mul_assoc] using this

omit [Finite Ω] [Fact p.Prime] in
theorem cj_closure (n : Ω) (S : Set Ω) :
    cj n (Subgroup.closure S) = Subgroup.closure ((fun x => n * x * n⁻¹) ⁻¹' S) := by
  apply le_antisymm
  · intro x hx
    have hx' : n * x * n⁻¹ ∈ Subgroup.closure S := hx
    have key : ∀ y ∈ Subgroup.closure S,
        n⁻¹ * y * n ∈ Subgroup.closure ((fun x => n * x * n⁻¹) ⁻¹' S) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        apply Subgroup.subset_closure
        show n * (n⁻¹ * y * n) * n⁻¹ ∈ S
        have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
        rw [e]
        exact hy
      | one => simp
      | mul y z hy hz ihy ihz =>
        have := Subgroup.mul_mem _ ihy ihz
        simpa [mul_assoc] using this
      | inv y hy ih =>
        have := Subgroup.inv_mem _ ih
        simpa [mul_assoc] using this
    have := key _ hx'
    simpa [mul_assoc] using this
  · rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure hx

@[expose] def genSet (H P Q : Subgroup Ω) : Set Ω :=
  {x : Ω | ∃ k ∈ H ⊓ Subgroup.normalizer (Q : Set Ω), k * x * k⁻¹ ∈ P}

omit [Finite Ω] [Fact p.Prime] in
theorem genSet_cj {H P Q : Subgroup Ω} {n : Ω} (hnH : n ∈ H)
    (hnP : n ∈ Subgroup.normalizer (P : Set Ω)) :
    genSet H P (cj n Q) = (fun x => n * x * n⁻¹) ⁻¹' genSet H P Q := by
  ext x
  constructor
  · rintro ⟨k', ⟨hk'H, hk'N⟩, hk'x⟩
    refine ⟨n * k' * n⁻¹, ⟨H.mul_mem (H.mul_mem hnH hk'H) (H.inv_mem hnH), ?_⟩, ?_⟩
    · exact mem_normalizer_cj_iff.1 hk'N
    · have h1 := (Subgroup.mem_normalizer_iff.1 hnP _).1 hk'x
      have e : n * (k' * x * k'⁻¹) * n⁻¹ = n * k' * n⁻¹ * (n * x * n⁻¹) * (n * k' * n⁻¹)⁻¹ := by
        group
      rw [← e]
      exact h1
  · rintro ⟨k, ⟨hkH, hkN⟩, hkx⟩
    refine ⟨n⁻¹ * k * n, ⟨H.mul_mem (H.mul_mem (H.inv_mem hnH) hkH) hnH, ?_⟩, ?_⟩
    · apply mem_normalizer_cj_iff.2
      have e : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
      rw [e]
      exact hkN
    · have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnP) _).1 hkx
      have e : n⁻¹ * (k * (n * x * n⁻¹) * k⁻¹) * n⁻¹⁻¹ = n⁻¹ * k * n * x * (n⁻¹ * k * n)⁻¹ := by
        group
      rw [← e]
      exact h1

omit [Finite Ω] in
theorem generated_cj {H P Q : Subgroup Ω} {n : Ω} (hnH : n ∈ H)
    (hnP : n ∈ Subgroup.normalizer (P : Set Ω)) (h : Generated H P Q) :
    Generated H P (cj n Q) := by
  unfold Generated at h ⊢
  rw [← genSet, genSet_cj hnH hnP]
  conv_lhs => rw [h]
  rw [cj_closure]
  rfl

theorem exists_mem_normalizer_cj_eq {H T P : Subgroup Ω} (hT : IsSylowOf p T H)
    (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) {g : Ω} (hg : g ∈ H)
    (hgT : T ≤ Subgroup.normalizer (cj g P : Set Ω)) :
    ∃ k ∈ H ⊓ Subgroup.normalizer (T : Set Ω), cj k P = cj g P := by
  have hH : cj g⁻¹ H = H := cj_of_mem_normalizer (Subgroup.le_normalizer (H.inv_mem hg))
  have hT'N : cj g⁻¹ T ≤ Subgroup.normalizer (P : Set Ω) := by
    intro x hx
    have hxT : g⁻¹ * x * g ∈ T := by simpa using hx
    have := mem_normalizer_cj_iff.1 (hgT hxT)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  have hT'S : IsSylowOf p (cj g⁻¹ T) H := by
    have := (isSylowOf_cj_iff (p := p) g⁻¹).2 hT
    rwa [hH] at this
  have hT1 : IsSylowOf p T (H ⊓ Subgroup.normalizer (P : Set Ω)) :=
    hT.of_le (le_inf hT.le hPT) inf_le_left
  have hT2 : IsSylowOf p (cj g⁻¹ T) (H ⊓ Subgroup.normalizer (P : Set Ω)) :=
    hT'S.of_le (le_inf hT'S.le hT'N) inf_le_left
  obtain ⟨n, hn, hconj⟩ := isSylowOf_exists_conj hT1 hT2
  have hconj' : ∀ y : Ω, g⁻¹ * y * g ∈ T ↔ n⁻¹ * y * n ∈ T := fun y => by
    simpa using hconj y
  refine ⟨n⁻¹ * g, ⟨H.mul_mem (H.inv_mem hn.1) hg, ?_⟩, ?_⟩
  · show n⁻¹ * g ∈ Subgroup.normalizer (T : Set Ω)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := hconj' (g * y * g⁻¹)
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e] at h1
    have e2 : n⁻¹ * g * y * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * y * g⁻¹) * n := by group
    rw [e2]
    exact h1
  · ext x
    rw [mem_cj, mem_cj]
    have e2 : n⁻¹ * g * x * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * x * g⁻¹) * n⁻¹⁻¹ := by group
    rw [e2]
    exact ((Subgroup.mem_normalizer_iff.1 (inv_mem hn.2) (g * x * g⁻¹)).symm)

theorem engine {H P Q E : Subgroup Ω} {M : ℕ}
    (hM : ∀ S : Subgroup Ω, IsSylowOf p S H → P ≤ S → ¬ S ≤ Subgroup.normalizer (P : Set Ω) →
      Nat.card ↥(Subgroup.normalizer (P : Set Ω) ⊓ S) ≤ M)
    (hPQ : P ≤ Q) (hQH : Q ≤ H) (hQp : IsPGroup p Q)
    (hE : E ≤ H ⊓ Subgroup.normalizer (Q : Set Ω)) (hEP : E ≤ Subgroup.normalizer (P : Set Ω))
    (hEp : IsPGroup p E) (hEM : M < Nat.card E) :
    ∃ T₁ : Subgroup Ω, IsSylowOf p T₁ H ∧ T₁ ≤ Subgroup.normalizer (P : Set Ω) ∧ Q ≤ T₁ ∧
      IsSylowOf p (T₁ ⊓ Subgroup.normalizer (Q : Set Ω)) (H ⊓ Subgroup.normalizer (Q : Set Ω)) := by
  obtain ⟨T₀, hET₀, hT₀⟩ := exists_isSylowOf_ge hEp hE
  have hT₀H : T₀ ≤ H := hT₀.le.trans inf_le_left
  obtain ⟨T₁, hT₀T₁, hT₁⟩ := exists_isSylowOf_ge hT₀.isPGroup hT₀H
  have hQH' : Q ≤ H ⊓ Subgroup.normalizer (Q : Set Ω) := le_inf hQH Subgroup.le_normalizer
  have hQT₀ : Q ≤ T₀ :=
    isSylowOf_le_of_le_normalizer hT₀ hQp hQH' inf_le_right
  have hPT₁ : P ≤ T₁ := hPQ.trans (hQT₀.trans hT₀T₁)
  have hT₁P : T₁ ≤ Subgroup.normalizer (P : Set Ω) := by
    by_contra hcon
    have h1 := hM T₁ hT₁ hPT₁ hcon
    have h2 : Nat.card E ≤ Nat.card ↥(Subgroup.normalizer (P : Set Ω) ⊓ T₁) :=
      Subgroup.card_le_of_le (le_inf hEP (hET₀.trans hT₀T₁))
    omega
  refine ⟨T₁, hT₁, hT₁P, hQT₀.trans hT₀T₁, ?_⟩
  have hle : T₀ ≤ T₁ ⊓ Subgroup.normalizer (Q : Set Ω) :=
    le_inf hT₀T₁ (hT₀.le.trans inf_le_right)
  have hle2 : T₁ ⊓ Subgroup.normalizer (Q : Set Ω) ≤ H ⊓ Subgroup.normalizer (Q : Set Ω) :=
    inf_le_inf_right _ hT₁.le
  have heq := hT₀.eq_of_le hle hle2 (hT₁.isPGroup.to_inf_left)
  rw [heq]
  exact hT₀

end Fusion

end CFSG.ClassicalInvolution.GlaubermanAut
