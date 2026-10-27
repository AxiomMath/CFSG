module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdAux

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm Subgroup

@[expose] def fixAll (S : Finset (Fin 8)) : Subgroup (Perm (Fin 8)) where
  carrier := {σ | ∀ x ∈ S, σ x = x}
  mul_mem' := by
    intro a b ha hb x hx
    show a (b x) = x
    rw [hb x hx, ha x hx]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro a ha x hx
    show a⁻¹ x = x
    exact Equiv.Perm.inv_eq_iff_eq.mpr (ha x hx).symm

theorem mem_fixAll {S : Finset (Fin 8)} {σ : Perm (Fin 8)} :
    σ ∈ fixAll S ↔ ∀ x ∈ S, σ x = x := Iff.rfl

@[expose] def fixerAlt (S : Finset (Fin 8)) : Subgroup (Perm (Fin 8)) :=
  fixAll S ⊓ alternatingGroup (Fin 8)

theorem mem_fixerAlt {S : Finset (Fin 8)} {σ : Perm (Fin 8)} :
    σ ∈ fixerAlt S ↔ (∀ x ∈ S, σ x = x) ∧ sign σ = 1 := by
  rw [fixerAlt, Subgroup.mem_inf, mem_fixAll, mem_alternatingGroup]

theorem not_mem_iff_of_mem_fixAll {S : Finset (Fin 8)} {σ : Perm (Fin 8)} (hσ : σ ∈ fixAll S)
    (x : Fin 8) : σ x ∉ S ↔ x ∉ S := by
  constructor
  · intro h hx
    exact h (by rw [hσ x hx]; exact hx)
  · intro h hy
    apply h
    have h1 : σ (σ x) = σ x := hσ _ hy
    have h2 : σ x = x := σ.injective h1
    rw [h2] at hy
    exact hy

theorem card_fixerAlt_le (S : Finset (Fin 8)) (hS : 1 < Fintype.card {x : Fin 8 // x ∉ S}) :
    Nat.card (fixerAlt S) ≤ (Fintype.card {x : Fin 8 // x ∉ S}).factorial / 2 := by
  classical
  have : Nontrivial {x : Fin 8 // x ∉ S} := Fintype.one_lt_card_iff_nontrivial.mp hS
  have hpres : ∀ σ : ↥(fixerAlt S), ∀ x, (σ.1 x ∉ S ↔ x ∉ S) := fun σ =>
    not_mem_iff_of_mem_fixAll (Subgroup.mem_inf.mp σ.2).1
  have hsupp : ∀ σ : ↥(fixerAlt S), ∀ x, σ.1 x ≠ x → x ∉ S := by
    intro σ x hx hxS
    exact hx ((mem_fixerAlt.mp σ.2).1 x hxS)
  let f : ↥(fixerAlt S) → ↥(alternatingGroup {x : Fin 8 // x ∉ S}) := fun σ =>
    ⟨subtypePerm σ.1 (hpres σ), by
      rw [mem_alternatingGroup, sign_subtypePerm σ.1 (hpres σ) (hsupp σ)]
      exact (mem_fixerAlt.mp σ.2).2⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    refine Equiv.ext (fun x => ?_)
    by_cases hx : x ∈ S
    · rw [(mem_fixerAlt.mp σ.2).1 x hx, (mem_fixerAlt.mp τ.2).1 x hx]
    · have h' := congrArg (fun g : ↥(alternatingGroup {x : Fin 8 // x ∉ S}) =>
        ((g : Perm {x : Fin 8 // x ∉ S}) ⟨x, hx⟩ : {x : Fin 8 // x ∉ S}).1) h
      simpa [f] using h'
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card {x : Fin 8 // x ∉ S} = Fintype.card {x : Fin 8 // x ∉ S} :=
    Nat.card_eq_fintype_card
  rw [nat_card_alternatingGroup, h2] at h1
  exact h1

theorem conj_mem_fixerAlt {S : Finset (Fin 8)} {g h : Perm (Fin 8)} (hg : ∀ x, g x ∈ S ↔ x ∈ S)
    (hh : h ∈ fixerAlt S) : g * h * g⁻¹ ∈ fixerAlt S := by
  obtain ⟨hfix, hsign⟩ := mem_fixerAlt.mp hh
  refine mem_fixerAlt.mpr ⟨fun x hx => ?_, by simp [hsign]⟩
  have hx' : g⁻¹ x ∈ S := by
    rw [← hg (g⁻¹ x)]
    simpa using hx
  have h1 : g (h (g⁻¹ x)) = x := by
    rw [hfix _ hx']
    exact Equiv.apply_symm_apply g x
  exact h1

theorem mem_normalizer_fixerAlt {S : Finset (Fin 8)} {g : Perm (Fin 8)}
    (hg : ∀ x, g x ∈ S ↔ x ∈ S) : g ∈ normalizer (fixerAlt S : Set (Perm (Fin 8))) := by
  have hg' : ∀ x, g⁻¹ x ∈ S ↔ x ∈ S := fun x => by simpa using (hg (g⁻¹ x)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_fixerAlt hg
  · intro hh
    have := conj_mem_fixerAlt hg' hh
    simpa [mul_assoc] using this

theorem fix_pair_of_comm {k : Perm (Fin 8)} (hk : swap (0 : Fin 8) 1 * k = k * swap 0 1) :
    (k 0 = 0 ∧ k 1 = 1) ∨ (k 0 = 1 ∧ k 1 = 0) := by
  have h1 : swap (k 0) (k 1) = swap 0 1 := by
    rw [Equiv.swap_apply_apply, ← hk, mul_inv_cancel_right]
  have h2 : ∀ a b : Fin 8, a ≠ b → swap a b = swap 0 1 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    decide
  exact h2 _ _ (k.injective.ne (by decide)) h1

theorem le_fixAll_of_perfect {K : Subgroup (Perm (Fin 8))} (hK : ⁅K, K⁆ = K)
    (hc : K ≤ Subgroup.centralizer {swap (0 : Fin 8) 1}) : K ≤ fixAll {0, 1} := by
  have hpair : ∀ k ∈ K, (k 0 = 0 ∧ k 1 = 1) ∨ (k 0 = 1 ∧ k 1 = 0) := fun k hk =>
    fix_pair_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hc hk)).symm
  have hidx : (fixAll {0}).relIndex K ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hex : ∃ a ∈ K, a 0 = 1
    · obtain ⟨a, haK, ha⟩ := hex
      refine ⟨a, haK, fun b hb => ?_⟩
      rcases hpair b hb with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · right
        intro x hx
        obtain rfl : x = 0 := by simpa using hx
        exact h0
      · left
        intro x hx
        obtain rfl : x = 0 := by simpa using hx
        show b (a 0) = 0
        rw [ha]
        exact h1
    · refine ⟨1, K.one_mem, fun b hb => ?_⟩
      right
      rcases hpair b hb with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · intro x hx
        obtain rfl : x = 0 := by simpa using hx
        exact h0
      · exact absurd ⟨b, hb, h0⟩ hex
  have hle : K ≤ fixAll {0} :=
    CFSG.QuasithinUnique.Id2519.le_of_perfect_of_relIndex_le_two hK (Nat.le_of_dvd two_pos hidx)
  intro k hk x hx
  have h0 : k 0 = 0 := hle hk 0 (by simp)
  rcases hpair k hk with ⟨-, h1⟩ | ⟨h0', -⟩
  · obtain rfl | rfl : x = 0 ∨ x = 1 := by simpa using hx
    · exact h0
    · exact h1
  · rw [h0] at h0'
    exact absurd h0' (by decide)

theorem eq_one_of_comm_alternatingGroup {g : Perm (Fin 8)}
    (h : ∀ a ∈ alternatingGroup (Fin 8), g * a = a * g) : g = 1 := by
  have hsupp : ∀ c ∈ alternatingGroup (Fin 8), ∀ w ∈ c.support, g w ∈ c.support := by
    intro c hc w hw
    have h1 : g * c * g⁻¹ = c := by rw [h c hc, mul_inv_cancel_right]
    have h2 := Equiv.Perm.support_conj (σ := g) (τ := c)
    rw [h1] at h2
    have h3 : g w ∈ c.support.map g.toEmbedding := Finset.mem_map_of_mem _ hw
    rw [← h2] at h3
    exact h3
  have h3cyc : ∀ x y z : Fin 8, x ≠ y → y ≠ z → x ≠ z → (swap x y * swap y z) ∈
      alternatingGroup (Fin 8) := by
    intro x y z hxy hyz hxz
    rw [mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.sign_swap hyz]
    decide
  have hfin : ∀ x w : Fin 8, w ∈ ({x, x + 1, x + 2} : Finset (Fin 8)) →
      w ∈ ({x, x + 3, x + 4} : Finset (Fin 8)) → w = x := by decide
  have hnd1 : ∀ x : Fin 8, List.Nodup [x, x + 1, x + 2] := by decide
  have hnd2 : ∀ x : Fin 8, List.Nodup [x, x + 3, x + 4] := by decide
  have hne : ∀ x : Fin 8, x ≠ x + 1 ∧ x + 1 ≠ x + 2 ∧ x ≠ x + 2 ∧ x ≠ x + 3 ∧ x + 3 ≠ x + 4 ∧
      x ≠ x + 4 := by decide
  refine Equiv.ext (fun x => ?_)
  have hx1 : g x ∈ (swap x (x + 1) * swap (x + 1) (x + 2)).support := by
    refine hsupp _ (h3cyc _ _ _ (hne x).1 (hne x).2.1 (hne x).2.2.1) x ?_
    rw [Equiv.Perm.support_swap_mul_swap (hnd1 x)]
    simp
  have hx2 : g x ∈ (swap x (x + 3) * swap (x + 3) (x + 4)).support := by
    refine hsupp _ (h3cyc _ _ _ (hne x).2.2.2.1 (hne x).2.2.2.2.1 (hne x).2.2.2.2.2) x ?_
    rw [Equiv.Perm.support_swap_mul_swap (hnd2 x)]
    simp
  rw [Equiv.Perm.support_swap_mul_swap (hnd1 x)] at hx1
  rw [Equiv.Perm.support_swap_mul_swap (hnd2 x)] at hx2
  exact hfin x _ hx1 hx2

end CFSG.QuasithinUnique.DoubleA3
