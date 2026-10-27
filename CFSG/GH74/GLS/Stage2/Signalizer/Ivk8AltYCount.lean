module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY

open Equiv Equiv.Perm Subgroup

variable {n : ℕ}

theorem two_mul_card_dvd (F : Finset (Fin n)) (h2 : 2 ≤ F.card ∨ 2 ≤ n - F.card)
    (P : Subgroup (Perm (Fin n))) (hPA : P ≤ alternatingGroup (Fin n))
    (hPF : ∀ p ∈ P, ∀ x, p x ∈ F ↔ x ∈ F) :
    2 * Nat.card P ∣ F.card.factorial * (n - F.card).factorial := by
  classical
  let q : Fin n → Prop := fun x => x ∈ F
  let Φ := subtypeCongrHom q
  let σ : (Perm {a // q a} × Perm {a // ¬ q a}) →* ℤˣ := Perm.sign.comp Φ
  have hΦ : Function.Injective Φ := subtypeCongrHom_injective q
  have hPrange : P ≤ Φ.range := by
    intro g hg
    have h1 : ∀ x, q (g x) ↔ q x := fun x => hPF g hg x
    have h2' : ∀ x, ¬ q (g x) ↔ ¬ q x := fun x => not_congr (h1 x)
    refine ⟨(g.subtypePerm h1, g.subtypePerm h2'), ?_⟩
    ext x
    by_cases hx : q x
    · simp [Φ, hx, Perm.subtypePerm]
    · simp [Φ, hx, Perm.subtypePerm]
  have hQ : Nat.card (Perm {a // q a} × Perm {a // ¬ q a}) =
      F.card.factorial * (n - F.card).factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_perm]
    have h3 : Fintype.card {a // q a} = F.card := Fintype.card_coe F
    have h4 : Fintype.card {a // ¬ q a} = n - F.card := by
      rw [Fintype.card_subtype_compl, h3, Fintype.card_fin]
    rw [h3, h4]
  have hodd : ∃ x : Perm {a // q a} × Perm {a // ¬ q a}, σ x = -1 := by
    rcases h2 with h | h
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < F.card)
      refine ⟨(swap ⟨a, ha⟩ ⟨b, hb⟩, 1), ?_⟩
      simp [σ, Φ, hab]
    · have hc : 1 < (Finset.univ \ F).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
      have ha' : ¬ q a := by simpa [q] using ha
      have hb' : ¬ q b := by simpa [q] using hb
      refine ⟨(1, swap ⟨a, ha'⟩ ⟨b, hb'⟩), ?_⟩
      simp [σ, Φ, hab]
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨x, hx⟩ := hodd
    rcases Int.units_eq_one_or u with h | h
    · rw [h]; exact one_mem _
    · rw [h, ← hx]; exact ⟨x, rfl⟩
  have hker : 2 * Nat.card σ.ker = F.card.factorial * (n - F.card).factorial := by
    have h := Subgroup.card_ker_mul_card_range σ
    have hz : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_units_int
    rw [hrange, Subgroup.card_top, hz, hQ] at h
    omega
  have hP' : Nat.card (P.comap Φ) = Nat.card P := by
    rw [← Subgroup.card_map_of_injective hΦ (K := P.comap Φ), Subgroup.map_comap_eq,
      inf_eq_right.2 hPrange]
  have hle : P.comap Φ ≤ σ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Perm.mem_alternatingGroup.1 (hPA hx)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hP'] at hdvd
  rw [← hker]
  exact Nat.mul_dvd_mul_left 2 hdvd


@[expose] noncomputable def movedSet (W : Subgroup (Perm (Fin n))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => ¬ ∀ w ∈ W, w x = x

theorem mem_movedSet {W : Subgroup (Perm (Fin n))} {x : Fin n} :
    x ∈ movedSet W ↔ ∃ w ∈ W, w x ≠ x := by
  classical
  simp [movedSet]

theorem movedSet_eq_empty_iff {W : Subgroup (Perm (Fin n))} : movedSet W = ∅ ↔ W = ⊥ := by
  rw [Finset.eq_empty_iff_forall_notMem, Subgroup.eq_bot_iff_forall]
  constructor
  · intro h w hw
    refine Equiv.ext fun x => ?_
    by_contra hx
    exact h x (mem_movedSet.2 ⟨w, hw, hx⟩)
  · intro h x hx
    obtain ⟨w, hw, hwx⟩ := mem_movedSet.1 hx
    exact hwx (by rw [h w hw]; rfl)

theorem movedSet_invariant {P W : Subgroup (Perm (Fin n))}
    (hN : P ≤ normalizer (W : Set (Perm (Fin n)))) :
    ∀ p ∈ P, ∀ x, p x ∈ movedSet W ↔ x ∈ movedSet W := by
  have fwd : ∀ p ∈ P, ∀ x, x ∈ movedSet W → p x ∈ movedSet W := by
    intro p hp x hx
    obtain ⟨w, hw, hwx⟩ := mem_movedSet.1 hx
    refine mem_movedSet.2 ⟨p * w * p⁻¹, (Subgroup.mem_normalizer_iff.1 (hN hp) w).1 hw, ?_⟩
    simpa using hwx
  intro p hp x
  refine ⟨fun h => ?_, fwd p hp x⟩
  simpa using fwd p⁻¹ (P.inv_mem hp) (p x) h

theorem card_movedSet_mod {W : Subgroup (Perm (Fin n))} (hW : IsPGroup 3 ↥W) :
    (movedSet W).card % 3 = 0 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hW (Fin n)
  rw [Nat.card_fin, Nat.card_eq_card_toFinset] at hmod
  have hfix : (MulAction.fixedPoints ↥W (Fin n)).toFinset =
      Finset.univ.filter fun x => ∀ w ∈ W, w x = x := by
    ext x
    simp only [Set.mem_toFinset, MulAction.mem_fixedPoints, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h w hw
      exact h ⟨w, hw⟩
    · intro h m
      exact h m m.2
  rw [hfix] at hmod
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun x => ∀ w ∈ W, w x = x)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hmv : (movedSet W).card = (Finset.univ.filter fun x => ¬ ∀ w ∈ W, w x = x).card := by
    simp only [movedSet]
  rw [hmv]
  unfold Nat.ModEq at hmod
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY
