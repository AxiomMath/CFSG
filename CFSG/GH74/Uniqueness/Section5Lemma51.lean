module

public import CFSG.GH74.Uniqueness.Prop38
public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Swap

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X}

theorem even_orderOf_of_swap {s : X} {β γ : Subgroup X} (hβγ : β ≠ γ)
    (h1 : conjugate β s = γ) (h2 : conjugate γ s = β) : Even (orderOf s) := by
  by_contra hodd
  have hodd' : Odd (orderOf s) := Nat.not_even_iff_odd.mp hodd
  obtain ⟨k, hk⟩ := hodd'
  have hpow : ∀ n : ℕ, conjugate β (s ^ (2 * n)) = β ∧ conjugate β (s ^ (2 * n + 1)) = γ := by
    intro n
    induction n with
    | zero => exact ⟨by simp [conjugate_one], by simpa using h1⟩
    | succ n ih =>
      have e1 : s ^ (2 * (n + 1)) = s ^ (2 * n + 1) * s := by
        rw [← pow_succ]; ring_nf
      have e2 : s ^ (2 * (n + 1) + 1) = s ^ (2 * (n + 1)) * s := by rw [← pow_succ]
      have a1 : conjugate β (s ^ (2 * (n + 1))) = β := by
        rw [e1, ← conjugate_conjugate, ih.2, h2]
      refine ⟨a1, ?_⟩
      rw [e2, ← conjugate_conjugate, a1, h1]
  have h3 := (hpow k).2
  rw [← hk, pow_orderOf_eq_one] at h3
  rw [conjugate_one] at h3
  exact hβγ h3

end Swap

section Lemma51

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

@[expose] def IsMaxFixingThree (M : Subgroup X) (p : ℕ) (P : Subgroup X) : Prop :=
  Maximal (fun R : Subgroup X => IsPGroup p R ∧ 3 ≤ (omegaFix M (R : Set X)).ncard) P

theorem IsProductDisconnected.exists_swap_of_isSylowOf (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P β γ : Subgroup X}
    (hβ : β ∈ omega M) (hγ : γ ∈ omega M) (hβγ : β ≠ γ)
    (hP : ABGLocalTools.IsSylowOf p P (β ⊓ γ)) :
    ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ conjugate β s = γ ∧ conjugate γ s = β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, Q, htβ, hQ, htQ⟩ := h.lemma39_exists hZ hβ hγ hβγ hp hp2
  obtain ⟨x, hx, hxQ⟩ := exists_conj_of_isSylowOf hQ hP
  have hxβ : x ∈ β := (Subgroup.mem_inf.mp hx).1
  have hxγ : x ∈ γ := (Subgroup.mem_inf.mp hx).2
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have htγβ : conjugate γ t = β := by
    rw [← htβ, conjugate_conjugate, ht2, conjugate_one]
  have hxβ' : conjugate β x⁻¹ = β :=
    (h.conjugate_eq_iff_mem hβ).mpr (β.inv_mem hxβ)
  have hxγ' : conjugate γ x⁻¹ = γ :=
    (h.conjugate_eq_iff_mem hγ).mpr (γ.inv_mem hxγ)
  have hxβ'' : conjugate β x = β := (h.conjugate_eq_iff_mem hβ).mpr hxβ
  have hxγ'' : conjugate γ x = γ := (h.conjugate_eq_iff_mem hγ).mpr hxγ
  have hQ' : conjugate Q t = Q := conjugate_eq_iff_mem_normalizer.mpr htQ
  have hPx : conjugate P x⁻¹ = Q := by
    rw [← hxQ, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  refine ⟨x⁻¹ * t * x, ?_, ?_, ?_, ?_⟩
  · simpa [mul_assoc] using hZ.2 t ht x
  · rw [← conjugate_eq_iff_mem_normalizer]
    rw [conjugate_mul_mul, hPx, hQ', hxQ]
  · rw [conjugate_mul_mul, hxβ', htβ, hxγ'']
  · rw [conjugate_mul_mul, hxγ', htγβ, hxβ'']

theorem IsProductDisconnected.sylow_or_exists_larger (h : IsProductDisconnected Z M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsMaxFixingThree M p P)
    {β γ : Subgroup X} (hβ : β ∈ omegaFix M (P : Set X)) (hγ : γ ∈ omegaFix M (P : Set X))
    (hβγ : β ≠ γ) :
    ABGLocalTools.IsSylowOf p P (β ⊓ γ) ∨
      ∃ R : Subgroup X, P < R ∧ ABGLocalTools.IsSylowOf p R (normalizer (P : Set X) ⊓ β ⊓ γ) ∧
        omegaFix M (R : Set X) = {β, γ} ∧
        ABGLocalTools.IsSylowOf p R (normalizer (P : Set X)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hβΩ, hPβ⟩ := h.mem_omegaFix_iff.mp hβ
  obtain ⟨hγΩ, hPγ⟩ := h.mem_omegaFix_iff.mp hγ
  have hPp := hP.1.1
  have hPβγ : P ≤ β ⊓ γ := le_inf hPβ hPγ
  by_cases hsyl : ABGLocalTools.IsSylowOf p P (β ⊓ γ)
  · exact Or.inl hsyl
  · right
    obtain ⟨Q, hQ⟩ := (hPp.comap_subtype (K := β ⊓ γ)).exists_le_sylow
    set R₀ : Subgroup X := (Q : Subgroup ↥(β ⊓ γ)).map (β ⊓ γ).subtype with hR₀
    have hR₀syl : ABGLocalTools.IsSylowOf p R₀ (β ⊓ γ) := ⟨Q, rfl⟩
    have hPR₀ : P ≤ R₀ := by
      intro x hx
      exact ⟨⟨x, hPβγ hx⟩, hQ (show (⟨x, hPβγ hx⟩ : ↥(β ⊓ γ)) ∈ P.subgroupOf (β ⊓ γ) from hx), rfl⟩
    have hlt : P < R₀ := lt_of_le_of_ne hPR₀ (fun heq => hsyl (heq ▸ hR₀syl))
    obtain ⟨R₁, hR₁p, hPR₁, hR₁R₀, hR₁N⟩ :=
      CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hR₀syl.isPGroup hlt
    have hR₁βγ : R₁ ≤ normalizer (P : Set X) ⊓ β ⊓ γ :=
      le_inf (le_inf hR₁N (hR₁R₀.trans (hR₀syl.le.trans inf_le_left)))
        (hR₁R₀.trans (hR₀syl.le.trans inf_le_right))
    obtain ⟨Q', hQ'⟩ := (hR₁p.comap_subtype (K := normalizer (P : Set X) ⊓ β ⊓ γ)).exists_le_sylow
    set R : Subgroup X := (Q' : Subgroup ↥(normalizer (P : Set X) ⊓ β ⊓ γ)).map
      (normalizer (P : Set X) ⊓ β ⊓ γ).subtype with hR
    have hRsyl : ABGLocalTools.IsSylowOf p R (normalizer (P : Set X) ⊓ β ⊓ γ) := ⟨Q', rfl⟩
    have hR₁R : R₁ ≤ R := by
      intro x hx
      exact ⟨⟨x, hR₁βγ hx⟩,
        hQ' (show (⟨x, hR₁βγ hx⟩ : ↥(normalizer (P : Set X) ⊓ β ⊓ γ)) ∈
          R₁.subgroupOf (normalizer (P : Set X) ⊓ β ⊓ γ) from hx), rfl⟩
    have hPR : P < R := lt_of_lt_of_le hPR₁ hR₁R
    have hRp : IsPGroup p R := hRsyl.isPGroup
    have hRβγ : R ≤ β ⊓ γ := hRsyl.le.trans (inf_le_left.trans le_rfl) |>.trans le_rfl |> fun h' => by
      exact le_inf (hRsyl.le.trans (inf_le_left.trans inf_le_right))
        (hRsyl.le.trans inf_le_right)
    have hβR : β ∈ omegaFix M (R : Set X) := h.mem_omegaFix_iff.mpr ⟨hβΩ, hRβγ.trans inf_le_left⟩
    have hγR : γ ∈ omegaFix M (R : Set X) := h.mem_omegaFix_iff.mpr ⟨hγΩ, hRβγ.trans inf_le_right⟩
    have hΩR : omegaFix M (R : Set X) = {β, γ} := by
      have hle2 : (omegaFix M (R : Set X)).ncard ≤ 2 := by
        by_contra hlt3
        have h3 : 3 ≤ (omegaFix M (R : Set X)).ncard := by omega
        have := hP.2 ⟨hRp, h3⟩ hPR.le
        exact absurd hPR (not_lt_of_ge this)
      symm
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · intro x hx
        rcases hx with rfl | rfl
        · exact hβR
        · exact hγR
      · rw [Set.ncard_pair hβγ]
        exact hle2
    exact ⟨R, hPR, hRsyl, hΩR, h.isSylowOf_of_omegaFix_pair hp hp2 hβγ hRsyl hΩR⟩

theorem IsProductDisconnected.lemma51 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsMaxFixingThree M p P) :
    (∃ n ∈ normalizer (P : Set X), ∃ β ∈ omegaFix M (P : Set X), conjugate β n ≠ β) ∧
      ∀ β ∈ omegaFix M (P : Set X), ∀ γ ∈ omegaFix M (P : Set X), β ≠ γ →
        (∃ n ∈ normalizer (P : Set X), conjugate β n = γ) →
          ∃ s ∈ normalizer (P : Set X), Even (orderOf s) ∧ conjugate β s = γ ∧
            conjugate γ s = β := by
  have : Fact p.Prime := ⟨hp⟩
  have hthree : 3 ≤ (omegaFix M (P : Set X)).ncard := hP.1.2
  have hb : ∀ β ∈ omegaFix M (P : Set X), ∀ γ ∈ omegaFix M (P : Set X), β ≠ γ →
      (∃ n ∈ normalizer (P : Set X), conjugate β n = γ) →
        ∃ s ∈ normalizer (P : Set X), Even (orderOf s) ∧ conjugate β s = γ ∧
          conjugate γ s = β := by
    intro β hβ γ hγ hβγ ⟨n, hn, hnβγ⟩
    rcases h.sylow_or_exists_larger hp hp2 hP hβ hγ hβγ with hsyl | ⟨R, hPR, hRsyl, hΩR, hRN⟩
    · obtain ⟨s, -, hsN, hs1, hs2⟩ := h.exists_swap_of_isSylowOf hZ hp hp2
        (h.mem_omegaFix_iff.mp hβ).1 (h.mem_omegaFix_iff.mp hγ).1 hβγ hsyl
      exact ⟨s, hsN, even_orderOf_of_swap hβγ hs1 hs2, hs1, hs2⟩
    ·
      set N := normalizer (P : Set X) with hN
      have hRβ : R ≤ β := by
        have : β ∈ omegaFix M (R : Set X) := by rw [hΩR]; exact Or.inl rfl
        exact (h.mem_omegaFix_iff.mp this).2
      have hRγ : R ≤ γ := by
        have : γ ∈ omegaFix M (R : Set X) := by rw [hΩR]; exact Or.inr rfl
        exact (h.mem_omegaFix_iff.mp this).2
      have hRN' : R ≤ N := hRsyl.le.trans (inf_le_left.trans inf_le_left)
      have hRNβ : ABGLocalTools.IsSylowOf p R (N ⊓ β) :=
        hRN.of_le (le_inf hRN' hRβ) inf_le_left
      have hRγ' : R ≤ conjugate (N ⊓ β) n := by
        have : conjugate (N ⊓ β) n = N ⊓ γ := by
          rw [conjugate_inf, ← hnβγ]
          congr 1
          exact conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hn)
        rw [this]
        exact le_inf hRN' hRγ
      obtain ⟨e, he, hen⟩ := exists_mul_mem_normalizer_of_isSylowOf hp hRNβ hRγ'
      have heβ : e ∈ β := (Subgroup.mem_inf.mp he).2
      have heN : e ∈ N := (Subgroup.mem_inf.mp he).1
      have hβΩ : β ∈ omega M := (h.mem_omegaFix_iff.mp hβ).1
      have hs1 : conjugate β (e * n) = γ := by
        rw [← conjugate_conjugate, (h.conjugate_eq_iff_mem hβΩ).mpr heβ, hnβγ]
      have hsΩ : conjugate γ (e * n) ∈ omegaFix M (R : Set X) := by
        refine conjugate_mem_omegaFix_of_mem_normalizer hen ?_
        rw [hΩR]; exact Or.inr rfl
      rw [hΩR] at hsΩ
      have hs2 : conjugate γ (e * n) = β := by
        rcases hsΩ with hsΩ | hsΩ
        · exact hsΩ
        · exfalso
          exact hβγ (conjugate_injective (e * n) (hs1.trans hsΩ.symm))
      exact ⟨e * n, N.mul_mem heN hn, even_orderOf_of_swap hβγ hs1 hs2, hs1, hs2⟩
  refine ⟨?_, hb⟩
  have h1lt : 1 < (omegaFix M (P : Set X)).ncard := by omega
  obtain ⟨β, γ, hβ, hγ, hβγ⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1lt
  rcases h.sylow_or_exists_larger hp hp2 hP hβ hγ hβγ with hsyl | ⟨R, hPR, hRsyl, hΩR, hRN⟩
  · obtain ⟨s, -, hsN, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2
      (h.mem_omegaFix_iff.mp hβ).1 (h.mem_omegaFix_iff.mp hγ).1 hβγ hsyl
    exact ⟨s, hsN, β, hβ, by rw [hs1]; exact fun heq => hβγ heq.symm⟩
  ·
    have hRN' : R ≤ normalizer (P : Set X) := hRsyl.le.trans (inf_le_left.trans inf_le_left)
    have hcard : (omegaFix M (R : Set X)).ncard = 2 := by rw [hΩR, Set.ncard_pair hβγ]
    have hsub : omegaFix M (R : Set X) ⊆ omegaFix M (P : Set X) :=
      omegaFix_anti (fun x hx => hPR.le hx)
    obtain ⟨δ, hδP, hδR⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (by omega : (omegaFix M
      (R : Set X)).ncard < (omegaFix M (P : Set X)).ncard) (Set.toFinite _)
    have hδΩ : δ ∈ omega M := hδP.1
    have hnR : ¬ R ≤ δ := fun hle => hδR (h.mem_omegaFix_iff.mpr ⟨hδΩ, hle⟩)
    obtain ⟨r, hrR, hrδ⟩ := IsConcreteLE.not_le_iff_exists.mp hnR
    exact ⟨r, hRN' hrR, δ, hδP, fun heq => hrδ ((h.conjugate_eq_iff_mem hδΩ).mp heq)⟩

end Lemma51

end CFSG.GH74.Uniqueness
