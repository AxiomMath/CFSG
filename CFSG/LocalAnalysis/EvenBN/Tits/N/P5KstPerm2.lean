module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstPerm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace SixData

variable {G : Subgroup (Perm Ω)} {ω₀ : Ω} {a b : Perm Ω}

theorem card_le_of_forall_mem {E : Subgroup (Perm Ω)} {F : Finset (Perm Ω)} (hEF : ∀ e ∈ E, e ∈ F) :
    Nat.card E ≤ F.card := by
  classical
  calc Nat.card E ≤ Nat.card ↥F :=
        Nat.card_le_card_of_injective (fun e => ⟨(e : Perm Ω), hEF e e.2⟩)
          (fun u v huv => Subtype.ext (Subtype.mk.inj huv))
    _ = F.card := by simp [Nat.card_eq_fintype_card]

theorem card_elemAb_le (h : SixData G ω₀ a b) {E : Subgroup (Perm Ω)} (hE : E ≤ G)
    (hsq : ∀ g ∈ E, g * g = 1) (hcomm : ∀ g ∈ E, ∀ k ∈ E, g * k = k * g) : Nat.card E ≤ 4 := by
  classical
  by_cases hA : ∃ g ∈ E, g ≠ 1 ∧ ∃ p, g p = p
  ·
    obtain ⟨g, hgE, hg1, p, hgp⟩ := hA
    have hgG := hE hgE
    have hfc : fixCount g = 2 := by
      rcases h.fixCount_invol hgG hg1 (hsq g hgE) with hf | hf
      · exfalso
        have hmem : p ∈ Finset.univ.filter (fun ω => g ω = ω) := by simp [hgp]
        have h0 : (Finset.univ.filter fun ω => g ω = ω) = ∅ := Finset.card_eq_zero.1 hf
        rw [h0] at hmem
        exact absurd hmem (Finset.notMem_empty p)
      · exact hf
    obtain ⟨q, hqmem, hqp⟩ := Finset.exists_mem_ne (s := Finset.univ.filter fun ω => g ω = ω)
      (by unfold fixCount at hfc; omega) p
    have hgq : g q = q := by simpa using hqmem
    have hpq : p ≠ q := hqp.symm
    have hfix : ∀ r, g r = r → r = p ∨ r = q := by
      intro r hr
      by_contra hcon
      push Not at hcon
      have hle := h.fixCount_le_two hgG hg1
      have hsub : ({p, q, r} : Finset Ω) ⊆ Finset.univ.filter fun ω => g ω = ω := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard := Finset.card_le_card hsub
      have h3 : ({p, q, r} : Finset Ω).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hpq, hcon.1.symm]),
          Finset.card_pair (Ne.symm hcon.2)]
      unfold fixCount at hle
      omega
    have hfixmap : ∀ e ∈ E, ∀ r, g r = r → g (e r) = e r := by
      intro e he r hr
      have hc : g * e = e * g := hcomm g hgE e he
      calc g (e r) = (g * e) r := rfl
        _ = (e * g) r := by rw [hc]
        _ = e (g r) := rfl
        _ = e r := by rw [hr]
    have hperm : ∀ e ∈ E, e p = p ∨ e p = q := fun e he => hfix _ (hfixmap e he p hgp)
    have hstab : ∀ e ∈ E, e p = p → e = 1 ∨ e = g := by
      intro e he hep
      by_cases he1 : e = 1
      · exact Or.inl he1
      · right
        have heq : e q = q := by
          rcases hfix (e q) (hfixmap e he q hgq) with h2 | h2
          · exact absurd (e.injective (h2.trans hep.symm)) hqp
          · exact h2
        exact h.invol_eq_of_fix_two hpq (hE he) hgG he1 hg1 (hsq e he) (hsq g hgE) hep heq hgp hgq
    by_cases hmove : ∃ e₁ ∈ E, e₁ p ≠ p
    · obtain ⟨e₁, he₁E, he₁p⟩ := hmove
      have he₁q : e₁ p = q := (hperm e₁ he₁E).resolve_left he₁p
      have hsub : ∀ e ∈ E, e ∈ ({1, g, e₁, e₁ * g} : Finset (Perm Ω)) := by
        intro e he
        rcases hperm e he with hep | heq
        · rcases hstab e he hep with rfl | rfl <;> simp
        · have hfp : (e₁⁻¹ * e) p = p := by
            show e₁⁻¹ (e p) = p
            rw [heq, ← he₁q]
            simp
          have hmem : e₁⁻¹ * e ∈ E := mul_mem (inv_mem he₁E) he
          rcases hstab _ hmem hfp with h1 | h1
          · have : e = e₁ := by
              calc e = e₁ * (e₁⁻¹ * e) := by group
                _ = e₁ := by rw [h1, mul_one]
            simp [this]
          · have : e = e₁ * g := by
              calc e = e₁ * (e₁⁻¹ * e) := by group
                _ = e₁ * g := by rw [h1]
            simp [this]
      exact (card_le_of_forall_mem hsub).trans Finset.card_le_four
    · push Not at hmove
      have hsub : ∀ e ∈ E, e ∈ ({1, g} : Finset (Perm Ω)) := by
        intro e he
        rcases hstab e he (hmove e he) with rfl | rfl <;> simp
      exact (card_le_of_forall_mem hsub).trans (Finset.card_le_two.trans (by norm_num))
  ·
    push Not at hA
    have hinj : Function.Injective (fun e : E => (e : Perm Ω) ω₀) := by
      intro u v huv
      have hu : ((u : Perm Ω)⁻¹ * v) ω₀ = ω₀ := by
        show (u : Perm Ω)⁻¹ ((v : Perm Ω) ω₀) = ω₀
        have huv' : (u : Perm Ω) ω₀ = (v : Perm Ω) ω₀ := huv
        rw [← huv']
        simp
      have hmem : (u : Perm Ω)⁻¹ * v ∈ E := mul_mem (inv_mem u.2) v.2
      by_contra hne
      have h1 : (u : Perm Ω)⁻¹ * v ≠ 1 := by
        intro h1
        apply hne
        exact Subtype.ext (inv_mul_eq_one.1 h1)
      exact hA _ hmem h1 ω₀ hu
    have h6 : Nat.card E ≤ 6 := by
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := Ω), h.card_Ω] at this
      exact this
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥E := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hsq g g.2)⟩
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra h3
      push Not at h3
      have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      omega
    calc Nat.card E = 2 ^ n := hn
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2

theorem klein_even (h : SixData G ω₀ a b) {E : Subgroup (Perm Ω)} (hE : E ≤ G)
    (hsq : ∀ g ∈ E, g * g = 1) (hcomm : ∀ g ∈ E, ∀ k ∈ E, g * k = k * g) (hcard : Nat.card E = 4) :
    ∃ g ∈ E, g ≠ 1 ∧ fixCount g = 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hfree : ∀ g ∈ E, g ≠ 1 → ∀ ω, g ω ≠ ω := by
    intro g hg hg1 ω hω
    have hf := h.fixCount_invol (hE hg) hg1 (hsq g hg)
    have hne2 := hcon g hg hg1
    have h0 : fixCount g = 0 := by omega
    have hmem : ω ∈ Finset.univ.filter (fun x => g x = x) := by simp [hω]
    have h00 : (Finset.univ.filter fun x => g x = x) = ∅ := Finset.card_eq_zero.1 h0
    rw [h00] at hmem
    exact absurd hmem (Finset.notMem_empty ω)
  have hinj : ∀ ω, Function.Injective (fun e : E => (e : Perm Ω) ω) := by
    intro ω u v huv
    have hu : ((u : Perm Ω)⁻¹ * v) ω = ω := by
      show (u : Perm Ω)⁻¹ ((v : Perm Ω) ω) = ω
      have huv' : (u : Perm Ω) ω = (v : Perm Ω) ω := huv
      rw [← huv']
      simp
    have hmem : (u : Perm Ω)⁻¹ * v ∈ E := mul_mem (inv_mem u.2) v.2
    by_contra hne
    have h1 : (u : Perm Ω)⁻¹ * v ≠ 1 := by
      intro h1
      apply hne
      exact Subtype.ext (inv_mul_eq_one.1 h1)
    exact hfree _ hmem h1 ω hu
  have hFcard : Fintype.card E = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hO : ∀ ω, (Finset.univ.image fun e : E => (e : Perm Ω) ω).card = 4 := by
    intro ω
    rw [Finset.card_image_of_injective _ (hinj ω), Finset.card_univ, hFcard]
  obtain ⟨ω₂, hω₂⟩ : ∃ ω₂ : Ω, ω₂ ∉ Finset.univ.image fun e : E => (e : Perm Ω) ω₀ := by
    by_contra hall
    push Not at hall
    have : (Finset.univ.image fun e : E => (e : Perm Ω) ω₀) = Finset.univ :=
      Finset.eq_univ_of_forall hall
    have h6 := hO ω₀
    rw [this, Finset.card_univ, h.card_Ω] at h6
    omega
  have hdisj : Disjoint (Finset.univ.image fun e : E => (e : Perm Ω) ω₀)
      (Finset.univ.image fun e : E => (e : Perm Ω) ω₂) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨e', -, he'⟩ := Finset.mem_image.1 hx2
    apply hω₂
    refine Finset.mem_image.2 ⟨⟨(e' : Perm Ω)⁻¹ * e, mul_mem (inv_mem e'.2) e.2⟩, Finset.mem_univ _, ?_⟩
    show (e' : Perm Ω)⁻¹ ((e : Perm Ω) ω₀) = ω₂
    rw [← he']
    simp
  have h8 := Finset.card_union_of_disjoint hdisj
  rw [hO ω₀, hO ω₂] at h8
  have hle := Finset.card_le_univ
    ((Finset.univ.image fun e : E => (e : Perm Ω) ω₀) ∪
      (Finset.univ.image fun e : E => (e : Perm Ω) ω₂))
  rw [h8, h.card_Ω] at hle
  omega

theorem invol_conj (h : SixData G ω₀ a b) {g g' : Perm Ω} (hg : g ∈ G) (hg' : g' ∈ G) (hg1 : g ≠ 1)
    (hg1' : g' ≠ 1) (hgg : g * g = 1) (hgg' : g' * g' = 1) (hf : fixCount g = 2)
    (hf' : fixCount g' = 2) : ∃ c ∈ G, c * g * c⁻¹ = g' := by
  classical
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.1 hf
  obtain ⟨p', q', hpq', hs'⟩ := Finset.card_eq_two.1 hf'
  have hgp : g p = p := by
    have hp : p ∈ Finset.univ.filter fun ω => g ω = ω := by
      rw [hs]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_filter.1 hp).2
  have hgq : g q = q := by
    have hq : q ∈ Finset.univ.filter fun ω => g ω = ω := by
      rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_filter.1 hq).2
  have hgp' : g' p' = p' := by
    have hp : p' ∈ Finset.univ.filter fun ω => g' ω = ω := by
      rw [hs']; exact Finset.mem_insert_self _ _
    exact (Finset.mem_filter.1 hp).2
  have hgq' : g' q' = q' := by
    have hq : q' ∈ Finset.univ.filter fun ω => g' ω = ω := by
      rw [hs']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_filter.1 hq).2
  obtain ⟨c, hcG, hcp, hcq⟩ := h.two_trans p p' q q' hpq hpq'
  refine ⟨c, hcG, ?_⟩
  have hc1 : c * g * c⁻¹ ≠ 1 := by
    intro h1
    apply hg1
    have : c * g = c := by simpa [mul_inv_eq_one] using h1
    exact mul_eq_left.1 this
  have hcc : c * g * c⁻¹ * (c * g * c⁻¹) = 1 := by
    calc c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ := by group
      _ = 1 := by rw [hgg]; group
  have hfix : ∀ r, g r = r → (c * g * c⁻¹) (c r) = c r := by
    intro r hr
    show c (g (c⁻¹ (c r))) = c r
    simp [hr]
  refine h.invol_eq_of_fix_two hpq' (mul_mem (mul_mem hcG hg) (inv_mem hcG)) hg' hc1 hg1' hcc hgg' ?_ ?_
    hgp' hgq'
  · have := hfix p hgp
    rwa [hcp] at this
  · have := hfix q hgq
    rwa [hcq] at this

end SixData

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
