module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Equiv

variable {n : ℕ}

@[expose] def IsBlock4 (S : Set (Finset (Fin n))) : Prop :=
  ∀ σ ∈ alternatingGroup (Fin n), ∀ γ ∈ S, γ.map σ.toEmbedding ∈ S →
    ∀ δ ∈ S, δ.map σ.toEmbedding ∈ S

@[expose] def Adj3 (γ δ : Finset (Fin n)) : Prop :=
  ∃ p ∈ γ, ∃ q ∉ γ, δ = insert q (γ.erase p)

namespace Block4

theorem swap_mul_swap_mem {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

theorem map_eq_of_mapsTo {σ : Perm (Fin n)} {γ γ' : Finset (Fin n)} (h : ∀ z ∈ γ, σ z ∈ γ')
    (hc : γ'.card ≤ γ.card) : γ.map σ.toEmbedding = γ' := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map]; exact hc)
  intro x hx
  rw [Finset.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact h z hz

theorem card_insert_erase {γ : Finset (Fin n)} {p q : Fin n} (hp : p ∈ γ) (hq : q ∉ γ) :
    (insert q (γ.erase p)).card = γ.card := by
  have hq' : q ∉ γ.erase p := fun h => hq (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hq', Finset.card_erase_of_mem hp]
  have : 0 < γ.card := Finset.card_pos.mpr ⟨p, hp⟩
  omega

theorem Adj3.symm {γ δ : Finset (Fin n)} (h : Adj3 γ δ) : Adj3 δ γ := by
  obtain ⟨p, hp, q, hq, rfl⟩ := h
  refine ⟨q, Finset.mem_insert_self _ _, p, ?_, ?_⟩
  · intro h'
    rcases Finset.mem_insert.mp h' with h'' | h''
    · exact hq (h'' ▸ hp)
    · exact (Finset.notMem_erase p γ) h''
  · ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxp : x = p
    · subst hxp
      simp [hp]
    · by_cases hxq : x = q
      · subst hxq
        simp [hq, hxp]
      · simp [hxp, hxq]

theorem Adj3.card {γ δ : Finset (Fin n)} (h : Adj3 γ δ) : δ.card = γ.card := by
  obtain ⟨p, hp, q, hq, rfl⟩ := h
  exact card_insert_erase hp hq

variable {S : Set (Finset (Fin n))}

theorem map_mem_of_fix (hS : IsBlock4 S) {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n))
    {γ : Finset (Fin n)} (hγ : γ ∈ S) (hfix : γ.map σ.toEmbedding = γ) {δ : Finset (Fin n)}
    (hδ : δ ∈ S) : δ.map σ.toEmbedding ∈ S :=
  hS σ hσ γ hγ (by rw [hfix]; exact hγ) δ hδ

theorem exists_two_of_card {s : Finset (Fin n)} (hs : 2 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y :=
  Finset.one_lt_card.mp (by omega)

theorem exists_not_mem {s : Finset (Fin n)} (hs : s.card < n) : ∃ c, c ∉ s := by
  by_contra h
  push Not at h
  have : (Finset.univ : Finset (Fin n)) ⊆ s := fun x _ => h x
  have h2 := Finset.card_le_card this
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem adj_mem (hn : 7 ≤ n) (hS : IsBlock4 S) {γ γ' : Finset (Fin n)} (hγ4 : γ.card = 4)
    (hγ : γ ∈ S) (hγ' : γ' ∈ S) (h : Adj3 γ γ') {δ : Finset (Fin n)} (hδ : Adj3 γ δ) : δ ∈ S := by
  classical
  obtain ⟨p, hp, q, hq, rfl⟩ := h
  obtain ⟨p', hp', q', hq', rfl⟩ := hδ
  suffices ∃ σ ∈ alternatingGroup (Fin n), γ.map σ.toEmbedding = γ ∧
      (insert q (γ.erase p)).map σ.toEmbedding = insert q' (γ.erase p') by
    obtain ⟨σ, hσ, hfix, hmap⟩ := this
    rw [← hmap]
    exact map_mem_of_fix hS hσ hγ hfix hγ'
  by_cases hpp : p = p'
  · subst hpp
    by_cases hqq : q = q'
    · subst hqq
      exact ⟨1, Subgroup.one_mem _, map_eq_of_mapsTo (fun z hz => hz) le_rfl,
        map_eq_of_mapsTo (fun z hz => hz) le_rfl⟩
    ·
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_of_card (s := γ.erase p)
        (by rw [Finset.card_erase_of_mem hp, hγ4]; norm_num)
      have hxγ := Finset.mem_of_mem_erase hx
      have hyγ := Finset.mem_of_mem_erase hy
      have hxq : x ≠ q := fun e => hq (e ▸ hxγ)
      have hxq' : x ≠ q' := fun e => hq' (e ▸ hxγ)
      have hyq : y ≠ q := fun e => hq (e ▸ hyγ)
      have hyq' : y ≠ q' := fun e => hq' (e ▸ hyγ)
      refine ⟨swap q q' * swap x y, swap_mul_swap_mem hqq hxy, ?_, ?_⟩
      · refine map_eq_of_mapsTo (fun z hz => ?_) le_rfl
        have hzq : z ≠ q := fun e => hq (e ▸ hz)
        have hzq' : z ≠ q' := fun e => hq' (e ▸ hz)
        rw [Perm.mul_apply]
        by_cases hzx : z = x
        · subst hzx
          rw [swap_apply_left, swap_apply_of_ne_of_ne hyq hyq']
          exact hyγ
        · by_cases hzy : z = y
          · subst hzy
            rw [swap_apply_right, swap_apply_of_ne_of_ne hxq hxq']
            exact hxγ
          · rw [swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hzq hzq']
            exact hz
      · refine map_eq_of_mapsTo (fun z hz => ?_) (by
          rw [card_insert_erase hp hq', card_insert_erase hp hq])
        rw [Perm.mul_apply]
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · rw [swap_apply_of_ne_of_ne hxq.symm hyq.symm, swap_apply_left]
          exact Finset.mem_insert_self _ _
        · have hzγ := Finset.mem_of_mem_erase hz'
          have hzq : z ≠ q := fun e => hq (e ▸ hzγ)
          have hzq' : z ≠ q' := fun e => hq' (e ▸ hzγ)
          by_cases hzx : z = x
          · subst hzx
            rw [swap_apply_left, swap_apply_of_ne_of_ne hyq hyq']
            exact Finset.mem_insert_of_mem hy
          · by_cases hzy : z = y
            · subst hzy
              rw [swap_apply_right, swap_apply_of_ne_of_ne hxq hxq']
              exact Finset.mem_insert_of_mem hx
            · rw [swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hzq hzq']
              exact Finset.mem_insert_of_mem hz'
  · by_cases hqq : q = q'
    · subst hqq
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_of_card (s := (insert q γ)ᶜ) (by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hq, hγ4]
        omega)
      rw [Finset.mem_compl, Finset.mem_insert, not_or] at hx hy
      refine ⟨swap p p' * swap x y, swap_mul_swap_mem hpp hxy, ?_, ?_⟩
      · refine map_eq_of_mapsTo (fun z hz => ?_) le_rfl
        have hzx : z ≠ x := fun e => hx.2 (e ▸ hz)
        have hzy : z ≠ y := fun e => hy.2 (e ▸ hz)
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy]
        by_cases hzp : z = p
        · subst hzp
          rw [swap_apply_left]
          exact hp'
        · by_cases hzp' : z = p'
          · subst hzp'
            rw [swap_apply_right]
            exact hp
          · rw [swap_apply_of_ne_of_ne hzp hzp']
            exact hz
      · refine map_eq_of_mapsTo (fun z hz => ?_) (by
          rw [card_insert_erase hp' hq, card_insert_erase hp hq])
        rw [Perm.mul_apply]
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · have hqp : z ≠ p := fun e => hq (e ▸ hp)
          have hqp' : z ≠ p' := fun e => hq (e ▸ hp')
          rw [swap_apply_of_ne_of_ne (Ne.symm hx.1) (Ne.symm hy.1),
            swap_apply_of_ne_of_ne hqp hqp']
          exact Finset.mem_insert_self _ _
        · have hzγ := Finset.mem_of_mem_erase hz'
          have hzp : z ≠ p := Finset.ne_of_mem_erase hz'
          have hzx : z ≠ x := fun e => hx.2 (e ▸ hzγ)
          have hzy : z ≠ y := fun e => hy.2 (e ▸ hzγ)
          rw [swap_apply_of_ne_of_ne hzx hzy]
          by_cases hzp' : z = p'
          · subst hzp'
            rw [swap_apply_right]
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hpp, hp⟩)
          · rw [swap_apply_of_ne_of_ne hzp hzp']
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzp', hzγ⟩)
    ·
      refine ⟨swap p p' * swap q q', swap_mul_swap_mem hpp hqq, ?_, ?_⟩
      · refine map_eq_of_mapsTo (fun z hz => ?_) le_rfl
        have hzq : z ≠ q := fun e => hq (e ▸ hz)
        have hzq' : z ≠ q' := fun e => hq' (e ▸ hz)
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzq hzq']
        by_cases hzp : z = p
        · subst hzp
          rw [swap_apply_left]
          exact hp'
        · by_cases hzp' : z = p'
          · subst hzp'
            rw [swap_apply_right]
            exact hp
          · rw [swap_apply_of_ne_of_ne hzp hzp']
            exact hz
      · refine map_eq_of_mapsTo (fun z hz => ?_) (by
          rw [card_insert_erase hp' hq', card_insert_erase hp hq])
        rw [Perm.mul_apply]
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · have h1 : q' ≠ p := fun e => hq' (e ▸ hp)
          have h2 : q' ≠ p' := fun e => hq' (e ▸ hp')
          rw [swap_apply_left, swap_apply_of_ne_of_ne h1 h2]
          exact Finset.mem_insert_self _ _
        · have hzγ := Finset.mem_of_mem_erase hz'
          have hzp : z ≠ p := Finset.ne_of_mem_erase hz'
          have hzq0 : z ≠ q := fun e => hq (e ▸ hzγ)
          have hzq' : z ≠ q' := fun e => hq' (e ▸ hzγ)
          rw [swap_apply_of_ne_of_ne hzq0 hzq']
          by_cases hzp' : z = p'
          · subst hzp'
            rw [swap_apply_right]
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hpp, hp⟩)
          · rw [swap_apply_of_ne_of_ne hzp hzp']
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzp', hzγ⟩)

theorem exists_adj (hn : 9 ≤ n) (hS : IsBlock4 S) {α β : Finset (Fin n)} (hα4 : α.card = 4)
    (hβ4 : β.card = 4) (hα : α ∈ S) (hβ : β ∈ S) (hne : α ≠ β) :
    ∃ γ ∈ S, ∃ γ' ∈ S, Adj3 γ γ' := by
  classical
  have hsd : (α \ β).card + (α ∩ β).card = 4 := by rw [Finset.card_sdiff_add_card_inter, hα4]
  have hsd' : (β \ α).card + (α ∩ β).card = 4 := by
    rw [Finset.inter_comm, Finset.card_sdiff_add_card_inter, hβ4]
  have hle : (α ∩ β).card ≤ 3 := by
    by_contra h
    have h4 : (α ∩ β).card = 4 := by
      have := Finset.card_le_card (Finset.inter_subset_left : α ∩ β ⊆ α)
      omega
    have e1 : α ∩ β = α := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have e2 : α ∩ β = β := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)
  by_cases h3 : (α ∩ β).card = 3
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show (α \ β).card = 1 by omega)
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (show (β \ α).card = 1 by omega)
    have hpα : p ∈ α \ β := by rw [hp]; exact Finset.mem_singleton_self p
    have hqβ : q ∈ β \ α := by rw [hq]; exact Finset.mem_singleton_self q
    rw [Finset.mem_sdiff] at hpα hqβ
    refine ⟨α, hα, β, hβ, p, hpα.1, q, hqβ.2, ?_⟩
    symm
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [card_insert_erase hpα.1 hqβ.2, hα4, hβ4])
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hqβ.1
    · by_contra hzβ
      have : z ∈ α \ β := Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz', hzβ⟩
      rw [hp, Finset.mem_singleton] at this
      exact Finset.ne_of_mem_erase hz' this
  · obtain ⟨b, hb⟩ : (β \ α).Nonempty := Finset.card_pos.mp (by omega)
    rw [Finset.mem_sdiff] at hb
    obtain ⟨c, hc⟩ := exists_not_mem (s := α ∪ β) (by
      have := Finset.card_union_le α β
      omega)
    rw [Finset.mem_union, not_or] at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_of_card (s := α \ β) (by omega)
    rw [Finset.mem_sdiff] at hx hy
    have hbc : b ≠ c := fun e => hc.2 (e ▸ hb.1)
    have hxb : x ≠ b := fun e => hb.2 (e ▸ hx.1)
    have hxc : x ≠ c := fun e => hc.1 (e ▸ hx.1)
    have hyb : y ≠ b := fun e => hb.2 (e ▸ hy.1)
    have hyc : y ≠ c := fun e => hc.1 (e ▸ hy.1)
    set σ := swap b c * swap x y with hσdef
    have hσ : σ ∈ alternatingGroup (Fin n) := swap_mul_swap_mem hbc hxy
    have hfix : α.map σ.toEmbedding = α := by
      refine map_eq_of_mapsTo (fun z hz => ?_) le_rfl
      have hzb : z ≠ b := fun e => hb.2 (e ▸ hz)
      have hzc : z ≠ c := fun e => hc.1 (e ▸ hz)
      rw [hσdef, Perm.mul_apply]
      by_cases hzx : z = x
      · subst hzx
        rw [swap_apply_left, swap_apply_of_ne_of_ne hyb hyc]
        exact hy.1
      · by_cases hzy : z = y
        · subst hzy
          rw [swap_apply_right, swap_apply_of_ne_of_ne hxb hxc]
          exact hx.1
        · rw [swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hzb hzc]
          exact hz
    have hmap : β.map σ.toEmbedding = insert c (β.erase b) := by
      refine map_eq_of_mapsTo (fun z hz => ?_) (by rw [card_insert_erase hb.1 hc.2])
      have hzx : z ≠ x := fun e => hx.2 (e ▸ hz)
      have hzy : z ≠ y := fun e => hy.2 (e ▸ hz)
      have hzc : z ≠ c := fun e => hc.2 (e ▸ hz)
      rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy]
      by_cases hzb : z = b
      · subst hzb
        rw [swap_apply_left]
        exact Finset.mem_insert_self _ _
      · rw [swap_apply_of_ne_of_ne hzb hzc]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzb, hz⟩)
    refine ⟨β, hβ, insert c (β.erase b), ?_, b, hb.1, c, hc.2, rfl⟩
    rw [← hmap]
    exact map_mem_of_fix hS hσ hα hfix hβ

theorem mem_of_closed {T : Set (Finset (Fin n))} (hT : ∀ γ ∈ T, ∀ δ, Adj3 γ δ → δ ∈ T)
    {γ₀ : Finset (Fin n)} (h₀ : γ₀ ∈ T) (hγ₀ : γ₀.card = 4) {δ : Finset (Fin n)}
    (hδ : δ.card = 4) : δ ∈ T := by
  classical
  suffices ∀ k, ∀ γ ∈ T, γ.card = 4 → (γ \ δ).card ≤ k → δ ∈ T from this _ γ₀ h₀ hγ₀ le_rfl
  intro k
  induction k with
  | zero =>
    intro γ hγ hγ4 hk
    have he : γ \ δ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsub : γ ⊆ δ := Finset.sdiff_eq_empty_iff_subset.mp he
    rw [← Finset.eq_of_subset_of_card_le hsub (by rw [hγ4, hδ])]
    exact hγ
  | succ k ih =>
    intro γ hγ hγ4 hk
    by_cases h0 : (γ \ δ).card = 0
    · exact ih γ hγ hγ4 (by omega)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
    have hdd : (δ \ γ).card = (γ \ δ).card := by
      have h1 : (δ \ γ).card + (δ ∩ γ).card = 4 := by rw [Finset.card_sdiff_add_card_inter, hδ]
      have h2 : (γ \ δ).card + (γ ∩ δ).card = 4 := by rw [Finset.card_sdiff_add_card_inter, hγ4]
      rw [Finset.inter_comm] at h1
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < (δ \ γ).card by omega)
    rw [Finset.mem_sdiff] at hp hq
    have hadj : Adj3 γ (insert q (γ.erase p)) := ⟨p, hp.1, q, hq.2, rfl⟩
    refine ih _ (hT γ hγ _ hadj) (by rw [Adj3.card hadj, hγ4]) ?_
    have hsub : insert q (γ.erase p) \ δ ⊆ (γ \ δ).erase p := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      rcases Finset.mem_insert.mp hz.1 with rfl | hz'
      · exact absurd hq.1 hz.2
      · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hz',
          Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz', hz.2⟩⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hp)] at h1
    omega

theorem eq_singleton_or_univ (hn : 9 ≤ n) (hS4 : ∀ γ ∈ S, γ.card = 4) (hS : IsBlock4 S)
    {α : Finset (Fin n)} (hα : α ∈ S) :
    S = {α} ∨ ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ S := by
  by_cases h : ∀ β ∈ S, β = α
  · left
    ext β
    rw [Set.mem_singleton_iff]
    exact ⟨h β, fun e => e ▸ hα⟩
  · right
    push Not at h
    obtain ⟨β, hβ, hne⟩ := h
    obtain ⟨γ, hγ, γ', hγ', hadj⟩ :=
      exists_adj hn hS (hS4 α hα) (hS4 β hβ) hα hβ (Ne.symm hne)
    set T : Set (Finset (Fin n)) := {δ | δ ∈ S ∧ ∃ δ' ∈ S, Adj3 δ δ'} with hTdef
    have hT : ∀ δ ∈ T, ∀ ε, Adj3 δ ε → ε ∈ T := by
      rintro δ ⟨hδ, δ', hδ', hδδ'⟩ ε hε
      have hεS := adj_mem (by omega) hS (hS4 δ hδ) hδ hδ' hδδ' hε
      exact ⟨hεS, δ, hδ, Adj3.symm hε⟩
    intro δ hδ
    exact (mem_of_closed hT ⟨hγ, γ', hγ', hadj⟩ (hS4 γ hγ) hδ).1

end Block4

end CFSG.ClassicalInvolution.Q3.AE
