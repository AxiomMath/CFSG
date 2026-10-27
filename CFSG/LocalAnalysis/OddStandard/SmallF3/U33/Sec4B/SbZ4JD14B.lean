module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

theorem mem_closure_pair_iff {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} :
    x ∈ closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have habb : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have haba : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, habb]
  have habab : (a * b) * (a * b) = 1 := by rw [← mul_assoc, haba, hb]
  let P : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;>
          rcases hy with hy | hy | hy | hy <;> rw [hy] <;>
            simp [ha, hb, hba, haab, habb, haba, hbab, habab]
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;>
          simp [inv_one, mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
            inv_eq_of_mul_eq_one_right hb, hba] }
  constructor
  · intro hx
    have hsub : closure ({a, b} : Set G) ≤ P :=
      (Subgroup.closure_le (k := ({a, b} : Set G)) P).mpr (by
        intro g hg
        rcases (by simpa using hg : g = a ∨ g = b) with hg | hg <;> rw [hg]
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl)))
    exact hsub hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Vq_le_Vh : Mc ⊔ closure ({τ, l} : Set H) ≤ zjVh Mc t τ l := by
  change Mc ⊔ closure ({τ, l} : Set H) ≤ Mc ⊔ closure ({t, τ, l} : Set H)
  refine sup_le le_sup_left ?_
  refine (Subgroup.closure_le (k := ({τ, l} : Set H))
    (Mc ⊔ closure ({t, τ, l} : Set H))).mpr ?_
  intro g hg
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto))

private lemma closure_tau_l_le_normalizer_Mc :
    closure ({τ, l} : Set H) ≤ normalizer (Mc : Set H) :=
  (Subgroup.closure_mono (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto)).trans (E_le_normalizer_Mc h hMh hMc)

private lemma closure_t_tau_le_normalizer_Mc :
    closure ({t, τ} : Set H) ≤ normalizer (Mc : Set H) :=
  (Subgroup.closure_mono (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto)).trans (E_le_normalizer_Mc h hMh hMc)

private lemma mem_sup_Mc_iff_exists {E : Subgroup H}
    (hE : E ≤ normalizer (Mc : Set H)) {g : H} :
    g ∈ Mc ⊔ E ↔ ∃ m ∈ Mc, ∃ e ∈ E, m * e = g := by
  change g ∈ (↑(Mc ⊔ E) : Set H) ↔ _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mc E hE]
  exact Set.mem_mul

theorem mem_Vq_iff {g : H} : g ∈ Mc ⊔ closure ({τ, l} : Set H) ↔
    ∃ m ∈ Mc, g = m ∨ g = m * τ ∨ g = m * l ∨ g = m * (τ * l) := by
  rw [mem_sup_Mc_iff_exists h hMh hMc (closure_tau_l_le_normalizer_Mc h hMh hMc)]
  constructor
  · rintro ⟨m, hm, e, he, rfl⟩
    refine ⟨m, hm, ?_⟩
    rcases (mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l).mp he with rfl | rfl | rfl | rfl <;>
      simp
  · rintro ⟨m, hm, h1 | h2 | h3 | h4⟩
    · exact ⟨m, hm, 1, (mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l).mpr (Or.inl rfl),
        by rw [h1]; simp⟩
    · exact ⟨m, hm, τ, (mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l).mpr (Or.inr (Or.inl rfl)),
        h2.symm⟩
    · exact ⟨m, hm, l,
        (mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l).mpr (Or.inr (Or.inr (Or.inl rfl))),
        h3.symm⟩
    · exact ⟨m, hm, τ * l,
        (mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l).mpr (Or.inr (Or.inr (Or.inr rfl))),
        h4.symm⟩

private lemma card_closure_tau_l : Nat.card ↥(closure ({τ, l} : Set H)) = 4 := by
  have hτ1 : τ ≠ 1 := fun h1 =>
    tau_not_mem_Mc h hMh hMc (by rw [h1]; exact Mc.one_mem)
  have hl1 : l ≠ 1 := fun h1 =>
    l_not_mem_Mh h hMh (by rw [h1]; exact Mh.one_mem)
  have hlτ : l ≠ τ := fun h1 =>
    l_not_mem_Mh h hMh (h1 ▸ tau_mem_Mh h hMh)
  have hτl : τ ≠ l := Ne.symm hlτ
  have hτl1 : τ * l ≠ 1 := by
    intro h1
    have h2 : τ * l = τ * τ := by rw [h.tau_sq]; exact h1
    have hl : l = τ := mul_left_cancel h2
    exact l_not_mem_Mh h hMh (hl ▸ tau_mem_Mh h hMh)
  have hτlτ : τ * l ≠ τ := by
    intro h1
    have h2 : τ * l = τ * 1 := by rw [mul_one]; exact h1
    exact hl1 (mul_left_cancel h2)
  have hτll : τ * l ≠ l := by
    intro h1
    have h2 : τ * l = 1 * l := by rw [one_mul]; exact h1
    exact hτ1 (mul_right_cancel h2)
  have hset : (↑(closure ({τ, l} : Set H)) : Set H) = {1, τ, l, τ * l} := by
    ext x
    change x ∈ closure ({τ, l} : Set H) ↔ x ∈ ({1, τ, l, τ * l} : Set H)
    rw [mem_closure_pair_iff h.tau_sq h.l_sq h.tau_l]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  change Nat.card ↥((closure ({τ, l} : Set H) : Set H)) = 4
  rw [Nat.card_coe_set_eq, hset,
    Set.ncard_insert_of_notMem (by simp [Ne.symm hτ1, Ne.symm hl1, Ne.symm hτl1]),
    Set.ncard_insert_of_notMem (by simp [hτl, Ne.symm hτlτ]),
    Set.ncard_insert_of_notMem (by simp [Ne.symm hτll]),
    Set.ncard_singleton]

private lemma Mc_inf_closure_tau_l : Mc ⊓ closure ({τ, l} : Set H) = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_left Mc (Subgroup.closure_mono (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto))).trans (Mc_inf_E h hMh hMc).le)

theorem card_Vq : Nat.card ↥(Mc ⊔ closure ({τ, l} : Set H)) = 1024 := by
  rw [card_sup_of_le_normalizer (closure_tau_l_le_normalizer_Mc h hMh hMc)
      (Mc_inf_closure_tau_l h hMh hMc),
    card_Mc h hMh hMc, card_closure_tau_l h hMh hMc]

theorem t_not_mem_Vq : t ∉ Mc ⊔ closure ({τ, l} : Set H) := by
  intro ht
  obtain ⟨m, hm, e1 | e2 | e3 | e4⟩ := (mem_Vq_iff h hMh hMc).mp ht
  · exact t_not_mem_Mh h hMh (by rw [e1]; exact Mc_le_Mh h hMh hMc hm)
  · exact t_not_mem_Mh h hMh
      (by rw [e2]; exact Mh.mul_mem (Mc_le_Mh h hMh hMc hm) (tau_mem_Mh h hMh))
  · have htl : t * l ∈ Mh := by
      rw [e3, show m * l * l = m by
        calc m * l * l = m * (l * l) := by group
          _ = m := by rw [h.l_sq, mul_one]]
      exact Mc_le_Mh h hMh hMc hm
    exact tl_not_mem_Mh h hMh htl
  · have htl : t * l ∈ Mh := by
      rw [e4, show m * (τ * l) * l = m * τ by
        calc m * (τ * l) * l = m * τ * (l * l) := by group
          _ = m * τ := by rw [h.l_sq, mul_one]]
      exact Mh.mul_mem (Mc_le_Mh h hMh hMc hm) (tau_mem_Mh h hMh)
    exact tl_not_mem_Mh h hMh htl

theorem mem_McTT_iff {g : H} : g ∈ Mc ⊔ closure ({t, τ} : Set H) ↔
    ∃ m ∈ Mc, g = m ∨ g = m * t ∨ g = m * τ ∨ g = m * (t * τ) := by
  rw [mem_sup_Mc_iff_exists h hMh hMc (closure_t_tau_le_normalizer_Mc h hMh hMc)]
  constructor
  · rintro ⟨m, hm, e, he, rfl⟩
    refine ⟨m, hm, ?_⟩
    rcases (mem_closure_pair_iff h.t_sq h.tau_sq h.t_tau).mp he with rfl | rfl | rfl | rfl <;>
      simp
  · rintro ⟨m, hm, h1 | h2 | h3 | h4⟩
    · exact ⟨m, hm, 1, (mem_closure_pair_iff h.t_sq h.tau_sq h.t_tau).mpr (Or.inl rfl),
        by rw [h1]; simp⟩
    · exact ⟨m, hm, t, (mem_closure_pair_iff h.t_sq h.tau_sq h.t_tau).mpr (Or.inr (Or.inl rfl)),
        h2.symm⟩
    · exact ⟨m, hm, τ,
        (mem_closure_pair_iff h.t_sq h.tau_sq h.t_tau).mpr (Or.inr (Or.inr (Or.inl rfl))),
        h3.symm⟩
    · exact ⟨m, hm, t * τ,
        (mem_closure_pair_iff h.t_sq h.tau_sq h.t_tau).mpr (Or.inr (Or.inr (Or.inr rfl))),
        h4.symm⟩

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
