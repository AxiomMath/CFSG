module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48NTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Ref

public section

namespace CFSG.ComponentClassification.AS81.N48

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Q47

@[expose] def fixS (α β : Equiv.Perm (Fin 64)) : Set (Fin 64) := {c | α c = c ∧ β c = c}

@[expose] def spanS (α β : Equiv.Perm (Fin 64)) : Set (Fin 64) :=
  {w | ∃ v, ∃ d ∈ ({1, α, β, α * β} : Set (Equiv.Perm (Fin 64))), xr (xr w v) (d v) ∈ fixS α β}

structure Facts : Prop where
  rank : ∀ α ∈ nstar, ∀ β ∈ nstar, ∀ γ ∈ nstar, α * α = 1 → β * β = 1 → γ * γ = 1 →
    α * β = β * α → α * γ = γ * α → β * γ = γ * β →
    α = 1 ∨ β = 1 ∨ β = α ∨ γ = 1 ∨ γ = α ∨ γ = β ∨ γ = α * β
  span : ∀ α ∈ nstar, ∀ β ∈ nstar, α * α = 1 → β * β = 1 → α * β = β * α →
    ¬ (α = 1 ∧ β = 1) → (spanS α β).ncard ≤ 16
  four : ∀ α ∈ nstar, ∀ β ∈ nstar, α * α = 1 → β * β = 1 → α * β = β * α → α ≠ 1 → β ≠ 1 →
    α ≠ β → (∃ τ ∈ ({α, β, α * β} : Set (Equiv.Perm (Fin 64))), 16 ≤ (fixS τ τ).ncard) ∧
      (16 ≤ (spanS α β).ncard → (fixS α β).ncard ≤ 4 ∧
        ∃ x ∉ spanS α β, ∃ τ ∈ ({α, β, α * β} : Set (Equiv.Perm (Fin 64))),
          xr x (τ x) ∈ fixS α β)

theorem getElem!_ofFn_bool {m : ℕ} (f : Fin m → Bool) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem ncard_eq_cnt {t : Array Bool} {S : Set (Fin 64)}
    (h : ∀ w : Fin 64, t[w.val]! = true ↔ w ∈ S) : S.ncard = cnt t := by
  have hS : S = ↑(Finset.univ.filter fun w : Fin 64 => t[w.val]! = true) := by
    ext w
    simp [h]
  rw [hS, Set.ncard_coe_finset]
  rfl

variable {a b : Array ℕ} {α β : Equiv.Perm (Fin 64)}

theorem fixTab_get (ha : Rep 64 a α) (hb : Rep 64 b β) (c : Fin 64) :
    (fixTab a b)[c.val]! = true ↔ c ∈ fixS α β := by
  rw [fixTab, getElem!_ofFn_bool _ c.2, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ha c, hb c]
  exact ⟨fun h => ⟨Fin.ext h.1, Fin.ext h.2⟩, fun h => ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩⟩

theorem fixTab_get_xr (ha : Rep 64 a α) (hb : Rep 64 b β) (u v : Fin 64) :
    (fixTab a b)[u.val ^^^ v.val]! = true ↔ xr u v ∈ fixS α β := by
  rw [← fixTab_get ha hb]
  rfl

theorem spanTab_get (ha : Rep 64 a α) (hb : Rep 64 b β) (w : Fin 64) :
    (spanTab a b (fixTab a b))[w.val]! = true ↔ w ∈ spanS α β := by
  rw [spanTab, getElem!_ofFn_bool _ w.2, Bool.or_eq_true, List.any_eq_true]
  simp only [List.mem_range, Bool.or_eq_true]
  constructor
  · rintro (hw | ⟨v, hv, (h1 | h2) | h3⟩)
    · refine ⟨0, 1, Or.inl rfl, ?_⟩
      rw [Equiv.Perm.one_apply, xr_xr_cancel]
      exact (fixTab_get ha hb w).1 hw
    · refine ⟨⟨v, hv⟩, α, Or.inr (Or.inl rfl), ?_⟩
      rw [← fixTab_get_xr ha hb, xr_val, ← ha ⟨v, hv⟩]
      exact h1
    · refine ⟨⟨v, hv⟩, β, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rw [← fixTab_get_xr ha hb, xr_val, ← hb ⟨v, hv⟩]
      exact h2
    · refine ⟨⟨v, hv⟩, α * β, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      rw [← fixTab_get_xr ha hb, xr_val, Equiv.Perm.mul_apply, ← ha (β ⟨v, hv⟩), ← hb ⟨v, hv⟩]
      exact h3
  · rintro ⟨v, d, hd, hw⟩
    rcases hd with rfl | rfl | rfl | rfl
    · left
      rw [Equiv.Perm.one_apply, xr_xr_cancel] at hw
      exact (fixTab_get ha hb w).2 hw
    · refine Or.inr ⟨v.val, v.2, Or.inl (Or.inl ?_)⟩
      rw [ha v, ← xr_val, fixTab_get_xr ha hb]
      exact hw
    · refine Or.inr ⟨v.val, v.2, Or.inl (Or.inr ?_)⟩
      rw [hb v, ← xr_val, fixTab_get_xr ha hb]
      exact hw
    · refine Or.inr ⟨v.val, v.2, Or.inr ?_⟩
      rw [hb v, ha (β v), ← xr_val, fixTab_get_xr ha hb]
      exact hw

theorem cnt_fixTab (ha : Rep 64 a α) (hb : Rep 64 b β) : cnt (fixTab a b) = (fixS α β).ncard :=
  (ncard_eq_cnt (fixTab_get ha hb)).symm

theorem cnt_spanTab (ha : Rep 64 a α) (hb : Rep 64 b β) :
    cnt (spanTab a b (fixTab a b)) = (spanS α β).ncard :=
  (ncard_eq_cnt (spanTab_get ha hb)).symm

theorem n48Check_parts (h : n48Check = true) :
    enumCheckN 64 q47NGens 336 = true ∧ rankCheck = true ∧
      ∀ a ∈ nInv, ∀ b ∈ nInv, pairCheck a b = true := by
  simp only [n48Check, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem exists_mem_nInv (hE : enumCheckN 64 q47NGens 336 = true) {α : Equiv.Perm (Fin 64)}
    (hα : α ∈ nstar) (hαα : α * α = 1) : ∃ t ∈ nInv, Rep 64 t α := by
  obtain ⟨t, ht, hr⟩ := (mem_grpN_iff hE).1 hα
  exact ⟨t, List.mem_filter.2 ⟨ht, (eqA_iff (rep_mulN hr hr) rep_idA).2 hαα⟩, hr⟩

theorem fourCheck_spec (ha : Rep 64 a α) (hb : Rep 64 b β)
    (h : fourCheck a b (fixTab a b) (spanTab a b (fixTab a b)) = true) :
    (∃ τ ∈ ({α, β, α * β} : Set (Equiv.Perm (Fin 64))), 16 ≤ (fixS τ τ).ncard) ∧
      (16 ≤ (spanS α β).ncard → (fixS α β).ncard ≤ 4 ∧
        ∃ x ∉ spanS α β, ∃ τ ∈ ({α, β, α * β} : Set (Equiv.Perm (Fin 64))),
          xr x (τ x) ∈ fixS α β) := by
  have hab := rep_mulN ha hb
  simp only [fourCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun h16 => ?_⟩
  · rw [cnt_fixTab ha ha, cnt_fixTab hb hb, cnt_fixTab hab hab] at h1
    rcases h1 with (h1 | h1) | h1
    · exact ⟨α, Or.inl rfl, h1⟩
    · exact ⟨β, Or.inr (Or.inl rfl), h1⟩
    · exact ⟨α * β, Or.inr (Or.inr rfl), h1⟩
  · rw [cnt_spanTab ha hb] at h2
    rcases h2 with h2 | ⟨hC, x, hx, hxS, hxC⟩
    · omega
    refine ⟨by rw [← cnt_fixTab ha hb]; exact hC, ⟨x, hx⟩, fun hm => ?_, ?_⟩
    · rw [← spanTab_get ha hb] at hm
      simp only at hm
      rw [hm] at hxS
      exact absurd hxS (by decide)
    · rcases hxC with (h3 | h3) | h3
      · refine ⟨α, Or.inl rfl, ?_⟩
        rw [← fixTab_get_xr ha hb, ← ha ⟨x, hx⟩]
        exact h3
      · refine ⟨β, Or.inr (Or.inl rfl), ?_⟩
        rw [← fixTab_get_xr ha hb, ← hb ⟨x, hx⟩]
        exact h3
      · refine ⟨α * β, Or.inr (Or.inr rfl), ?_⟩
        rw [← fixTab_get_xr ha hb, Equiv.Perm.mul_apply, ← ha (β ⟨x, hx⟩), ← hb ⟨x, hx⟩]
        exact h3

theorem facts_of (h : n48Check = true) : Facts := by
  obtain ⟨hE, hR, hP⟩ := n48Check_parts h
  refine ⟨fun α hα β hβ γ hγ hαα hββ hγγ hab hac hbc => ?_,
    fun α hα β hβ hαα hββ hab hne => ?_, fun α hα β hβ hαα hββ hab ha1 hb1 hne => ?_⟩
  · obtain ⟨a, ha, hra⟩ := exists_mem_nInv hE hα hαα
    obtain ⟨b, hb, hrb⟩ := exists_mem_nInv hE hβ hββ
    obtain ⟨c, hc, hrc⟩ := exists_mem_nInv hE hγ hγγ
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hR a ha) b hb) c hc
    have e1 : commN 64 a b = true := (commN_iff hra hrb).2 hab
    have e2 : commN 64 a c = true := (commN_iff hra hrc).2 hac
    have e3 : commN 64 b c = true := (commN_iff hrb hrc).2 hbc
    simp only [e1, e2, e3, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
    rw [eqA_iff hra rep_idA, eqA_iff hrb rep_idA, eqA_iff hrb hra, eqA_iff hrc rep_idA,
      eqA_iff hrc hra, eqA_iff hrc hrb, eqA_iff hrc (rep_mulN hra hrb)] at h1
    tauto
  · obtain ⟨a, ha, hra⟩ := exists_mem_nInv hE hα hαα
    obtain ⟨b, hb, hrb⟩ := exists_mem_nInv hE hβ hββ
    have h1 := hP a ha b hb
    have e1 : commN 64 a b = true := (commN_iff hra hrb).2 hab
    simp only [pairCheck, e1, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h1
    rw [eqA_iff hra rep_idA, eqA_iff hrb rep_idA, cnt_spanTab hra hrb] at h1
    rcases h1 with h1 | ⟨h1, -⟩
    · exact absurd h1 hne
    · exact h1
  · obtain ⟨a, ha, hra⟩ := exists_mem_nInv hE hα hαα
    obtain ⟨b, hb, hrb⟩ := exists_mem_nInv hE hβ hββ
    have h1 := hP a ha b hb
    have e1 : commN 64 a b = true := (commN_iff hra hrb).2 hab
    simp only [pairCheck, e1, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h1
    rw [eqA_iff hra rep_idA, eqA_iff hrb rep_idA, eqA_iff hra hrb] at h1
    rcases h1 with h1 | ⟨-, ((h1 | h1) | h1) | h1⟩
    · exact absurd h1.1 ha1
    · exact absurd h1 ha1
    · exact absurd h1 hb1
    · exact absurd h1 hne
    · exact fourCheck_spec hra hrb h1

end CFSG.ComponentClassification.AS81.N48
