module

public import CFSG.CGT.Foote82.T66.Perm310
import CFSG.CGT.Foote82.T66.CaseIPerm

public section

namespace CFSG.CGT.Foote82

namespace CaseIS8Perm

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_mul_self {a b d e : α} (had : a ≠ d) (hab : a ≠ b) (hae : a ≠ e)
    (hdb : d ≠ b) (hde : d ≠ e) (hbe : b ≠ e) :
    (swap a d * swap b e) * (swap a d * swap b e) = 1 := by
  have hc : swap a d * swap b e = swap b e * swap a d := by
    refine (Equiv.Perm.Disjoint.commute ?_).eq
    intro x
    by_cases hxa : x = a
    · right; rw [hxa]; exact swap_apply_of_ne_of_ne hab hae
    by_cases hxd : x = d
    · right; rw [hxd]; exact swap_apply_of_ne_of_ne hdb hde
    · left; exact swap_apply_of_ne_of_ne hxa hxd
  calc swap a d * swap b e * (swap a d * swap b e) = swap a d * (swap b e * swap a d) * swap b e
        := by group
    _ = swap a d * (swap a d * swap b e) * swap b e := by rw [hc]
    _ = 1 := by
      rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]

theorem swap_mul_swap_ne_one {a b d e : α} (had : a ≠ d) (hab : a ≠ b) (hae : a ≠ e) :
    swap a d * swap b e ≠ 1 := by
  intro h
  have := congrArg (fun f : Perm α => f a) h
  simp only [Perm.mul_apply, Perm.one_apply] at this
  rw [swap_apply_of_ne_of_ne hab hae, swap_apply_left] at this
  exact had this.symm

theorem exists_involution_of_conj_closed [Fintype α] (Δ : Finset α) (hΔ : 4 ≤ Δ.card)
    (M : Subgroup (Perm α)) (hsupp : ∀ σ ∈ M, ∀ x, x ∉ Δ → σ x = x)
    (hconj : ∀ σ ∈ M, ∀ a ∈ Δ, ∀ b ∈ Δ, swap a b * σ * swap a b ∈ M)
    {σ : Perm α} (hσM : σ ∈ M) (hσ1 : σ ≠ 1) : ∃ u ∈ M, u * u = 1 ∧ u ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hc; push Not at hc; exact hσ1 (Perm.ext hc)
  have haΔ : a ∈ Δ := by
    by_contra h; exact ha (hsupp σ hσM a h)
  obtain ⟨b, hb⟩ : ∃ b, b = σ a := ⟨_, rfl⟩
  have hbΔ : b ∈ Δ := by
    by_contra h
    have := hsupp σ hσM b h
    rw [hb] at this
    exact ha (σ.injective this)
  have hab : a ≠ b := fun h => ha (by rw [← hb]; exact h.symm)
  obtain ⟨d, hdΔ, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, σ⁻¹ a} : Finset α)) (t := Δ) (by
      calc ({a, b, σ⁻¹ a} : Finset α).card ≤ 3 := Finset.card_le_three
        _ < Δ.card := by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  have hda : d ≠ a := hd.1
  have hdb : d ≠ b := hd.2.1
  have hda' : d ≠ σ⁻¹ a := hd.2.2
  have hσd_b : σ d ≠ b := fun h => hda (σ.injective (h.trans hb))
  have hσd_a : σ d ≠ a := fun h => hda' (by rw [← h]; exact (CaseIPerm.perm_inv_apply σ d).symm)
  have hcM : σ * (swap a d * σ⁻¹ * swap a d) ∈ M :=
    M.mul_mem hσM (hconj _ (M.inv_mem hσM) a haΔ d hdΔ)
  have hceq : σ * (swap a d * σ⁻¹ * swap a d) = swap b (σ d) * swap a d := by
    rw [hb, swap_apply_apply]; group
  by_cases hσdd : σ d = d
  ·
    rw [hceq, hσdd] at hcM
    obtain ⟨e, heΔ, he⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, b, d} : Finset α)) (t := Δ) (by
        calc ({a, b, d} : Finset α).card ≤ 3 := Finset.card_le_three
          _ < Δ.card := by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    have hea : e ≠ a := he.1
    have heb : e ≠ b := he.2.1
    have hed : e ≠ d := he.2.2
    have hc'M : swap d e * (swap b d * swap a d) * swap d e ∈ M := hconj _ hcM d hdΔ e heΔ
    have hc'eq : swap d e * (swap b d * swap a d) * swap d e = swap b e * swap a e := by
      have e1 : swap d e * (swap b d * swap a d) * swap d e =
          (swap d e * swap b d * (swap d e)⁻¹) * (swap d e * swap a d * (swap d e)⁻¹) := by
        rw [swap_inv]; simp only [mul_assoc, swap_mul_self_mul]
      rw [e1, ← swap_apply_apply, ← swap_apply_apply, swap_apply_of_ne_of_ne hdb.symm heb.symm,
        swap_apply_left, swap_apply_of_ne_of_ne hda.symm hea.symm]
    rw [hc'eq] at hc'M
    refine ⟨(swap b d * swap a d) * (swap b e * swap a e), M.mul_mem hcM hc'M, ?_⟩
    have hu : (swap b d * swap a d) * (swap b e * swap a e) = swap a d * swap b e := by
      refine Perm.ext fun x => ?_
      simp only [Perm.mul_apply]
      by_cases hxa : x = a
      · rw [hxa, swap_apply_left a e, swap_apply_right b e,
          swap_apply_of_ne_of_ne hab.symm hdb.symm, swap_apply_left b d,
          swap_apply_of_ne_of_ne hab hea.symm, swap_apply_left a d]
      by_cases hxb : x = b
      · rw [hxb, swap_apply_of_ne_of_ne hab.symm heb.symm, swap_apply_left b e,
          swap_apply_of_ne_of_ne hea hed, swap_apply_of_ne_of_ne heb hed]
      by_cases hxd : x = d
      · rw [hxd, swap_apply_of_ne_of_ne hda hed.symm, swap_apply_of_ne_of_ne hdb hed.symm,
          swap_apply_right a d, swap_apply_of_ne_of_ne hab hda.symm]
      by_cases hxe : x = e
      · rw [hxe, swap_apply_right a e, swap_apply_of_ne_of_ne hab hea.symm, swap_apply_left a d,
          swap_apply_right b d, swap_apply_right b e, swap_apply_of_ne_of_ne hab.symm hdb.symm]
      · rw [swap_apply_of_ne_of_ne hxa hxe, swap_apply_of_ne_of_ne hxb hxe,
          swap_apply_of_ne_of_ne hxa hxd, swap_apply_of_ne_of_ne hxb hxd]
    rw [hu]
    exact ⟨swap_mul_swap_mul_self hda.symm hab hea.symm hdb hed.symm heb.symm,
      swap_mul_swap_ne_one hda.symm hab hea.symm⟩
  ·
    rw [hceq] at hcM
    exact ⟨swap b (σ d) * swap a d, hcM,
      swap_mul_swap_mul_self hσd_b.symm hab.symm hdb.symm hσd_a hσdd hda.symm,
      swap_mul_swap_ne_one hσd_b.symm hab.symm hdb.symm⟩

theorem altOn_le_closure_threeCycles {m : ℕ} (F : Set (Fin m)) :
    altOn F ≤ Subgroup.closure {σ | σ ∈ altOn F ∧ σ.IsThreeCycle} := by
  classical
  intro σ hσ
  obtain ⟨hA, hfix⟩ := CaseIPerm.mem_altOn_iff.1 hσ
  have h1 : ∀ x, σ x ∈ F ↔ x ∈ F := by
    intro x
    constructor
    · intro h
      by_contra hx
      rw [hfix x hx] at h
      exact hx h
    · intro hx
      by_contra h
      exact h (by rw [σ.injective (hfix _ h)]; exact hx)
  set τ := σ.subtypePerm h1 with hτdef
  have hτ : ofSubtype τ = σ := ofSubtype_subtypePerm h1 fun x hx => by
    by_contra h; exact hx (hfix x h)
  have hτA : τ ∈ alternatingGroup {x // x ∈ F} := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hτ]
    exact hA
  have hτC : τ ∈ Subgroup.closure {τ : Perm {x // x ∈ F} | τ.IsThreeCycle} := by
    rw [closure_three_cycles_eq_alternating]; exact hτA
  have hmem : ofSubtype τ ∈ (Subgroup.closure {τ : Perm {x // x ∈ F} | τ.IsThreeCycle}).map
      (ofSubtype : Perm {x // x ∈ F} →* Perm (Fin m)) := ⟨τ, hτC, rfl⟩
  rw [MonoidHom.map_closure] at hmem
  rw [← hτ]
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨c, hc, rfl⟩
  have hc3 : (ofSubtype c : Perm (Fin m)).IsThreeCycle := by
    unfold IsThreeCycle
    rw [cycleType_ofSubtype]
    exact hc
  exact ⟨CaseIPerm.mem_altOn_iff.2 ⟨hc3.mem_alternatingGroup,
    fun x hx => ofSubtype_apply_of_not_mem c hx⟩, hc3⟩

end CaseIS8Perm

end CFSG.CGT.Foote82
