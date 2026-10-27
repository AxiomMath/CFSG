module

public import CFSG.CGT.Timmesfeld75.Sec4OneCaseA2
public import CFSG.CGT.Timmesfeld75.Sec4OneCaseB

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G}

@[expose] def sec4N (T T₁ T₂ : Subgroup G) : Subgroup G :=
  normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T

@[expose] def sec4Y (T T₁ T₂ : Subgroup G) : Subgroup G := T ⊔ T₁ ⊔ T₂

theorem normIn_le_sec4N_left : normIn T T₁ ≤ sec4N T T₁ T₂ := le_sup_of_le_left le_sup_left

theorem normIn_le_sec4N_mid : normIn T₁ T ≤ sec4N T T₁ T₂ := le_sup_of_le_left le_sup_right

theorem normIn_le_sec4N_right : normIn T₂ T ≤ sec4N T T₁ T₂ := le_sup_right

theorem left_le_sec4Y : T ≤ sec4Y T T₁ T₂ := le_sup_of_le_left le_sup_left

theorem mid_le_sec4Y : T₁ ≤ sec4Y T T₁ T₂ := le_sup_of_le_left le_sup_right

theorem right_le_sec4Y : T₂ ≤ sec4Y T T₁ T₂ := le_sup_right

theorem sec4N_le_sec4Y : sec4N T T₁ T₂ ≤ sec4Y T T₁ T₂ :=
  sup_le (sup_le ((normIn_le _ _).trans left_le_sec4Y) ((normIn_le _ _).trans mid_le_sec4Y))
    ((normIn_le _ _).trans right_le_sec4Y)

theorem sec4N_le_normalizer_left : sec4N T T₁ T₂ ≤ Subgroup.normalizer (T : Set G) :=
  sup_le (sup_le ((normIn_le _ _).trans Subgroup.le_normalizer) inf_le_right) inf_le_right

theorem inf_sec4N_mid_eq : T₁ ⊓ sec4N T T₁ T₂ = normIn T₁ T := by
  apply le_antisymm
  · intro x hx
    exact mem_normIn.2 ⟨hx.1, sec4N_le_normalizer_left hx.2⟩
  · intro x hx
    exact ⟨normIn_le _ _ hx, normIn_le_sec4N_mid hx⟩

end Setup

section Basic

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.mem_normalizer_normIn (h : Sec4Hyp T T₁ a T₂) :
    a ∈ Subgroup.normalizer (normIn T₁ T : Set G) := by
  by_contra hA
  exact h.false_of_not_normalizer hA

theorem Sec4Hyp.isElemAbelian_sec4N (h : Sec4Hyp T T₁ a T₂) :
    IsElemAbelian 2 (sec4N T T₁ T₂) :=
  h.isElemAbelian_normIn h.mem_normalizer_normIn

theorem Sec4Hyp.normal_sec4N (h : Sec4Hyp T T₁ a T₂) :
    ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal :=
  h.normal_normIn h.mem_normalizer_normIn

theorem Sec4Hyp.sec4Y_le_normalizer (h : Sec4Hyp T T₁ a T₂) :
    sec4Y T T₁ T₂ ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer sec4N_le_sec4Y).1 h.normal_sec4N

theorem Sec4Hyp.sec4N_le_normalizer_mid (h : Sec4Hyp T T₁ a T₂) :
    sec4N T T₁ T₂ ≤ Subgroup.normalizer (T₁ : Set G) := by
  have h2 : normIn T₂ T ≤ Subgroup.normalizer (T₁ : Set G) := by
    rw [h.normIn₂_eq h.mem_normalizer_normIn]
    exact inf_le_right
  exact sup_le (sup_le inf_le_right ((normIn_le _ _).trans Subgroup.le_normalizer)) h2

theorem Sec4Hyp.inf_sec4N_eq (h : Sec4Hyp T T₁ a T₂) :
    T ⊓ sec4N T T₁ T₂ = normIn T T₁ := by
  apply le_antisymm
  · intro x hx
    exact mem_normIn.2 ⟨hx.1, h.sec4N_le_normalizer_mid hx.2⟩
  · intro x hx
    exact ⟨normIn_le _ _ hx, normIn_le_sec4N_left hx⟩

theorem Sec4Hyp.isPGroup_sec4N (h : Sec4Hyp T T₁ a T₂) : IsPGroup 2 (sec4N T T₁ T₂) :=
  isPGroup_two_of_isElemAbelian h.isElemAbelian_sec4N

omit [Finite G] in
theorem Sec4Hyp.exists_mem_sec4Y_conj₁ (h : Sec4Hyp T T₁ a T₂) :
    ∃ x ∈ sec4Y T T₁ T₂, T₁ = conjSubgroup x T := by
  obtain ⟨x, hx, hx'⟩ := h.sec3.conj
  exact ⟨x, sup_le (left_le_sec4Y (T₂ := T₂)) mid_le_sec4Y hx, hx'⟩

theorem Sec4Hyp.exists_mem_sec4Y_conj₂ (h : Sec4Hyp T T₁ a T₂) :
    ∃ x ∈ sec4Y T T₁ T₂, T₂ = conjSubgroup x T := by
  have hS : Sec3 T T₂ := sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj h.ne_left
    h.normIn_ne_bot
  obtain ⟨x, hx, hx'⟩ := hS.conj
  exact ⟨x, sup_le (left_le_sec4Y (T₁ := T₁)) right_le_sec4Y hx, hx'⟩

theorem Sec4Hyp.normIn_conj_of_normalizer (h : Sec4Hyp T T₁ a T₂) {g : G}
    (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hne : conjSubgroup g T ≠ T) :
    normIn T (conjSubgroup g T) = normIn T T₁ ∧
      normIn (conjSubgroup g T) T = conjSubgroup g (normIn T T₁) := by
  have hNg : conjSubgroup g (sec4N T T₁ T₂) = sec4N T T₁ T₂ :=
    mem_normalizer_iff_conjSubgroup_eq.1 hg
  have hNTg : sec4N T T₁ T₂ ≤ Subgroup.normalizer (conjSubgroup g T : Set G) := by
    intro x hx
    rw [mem_normalizer_conjSubgroup_iff]
    apply sec4N_le_normalizer_left
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) x).1 hx
    simpa using this
  have hLle : normIn T T₁ ≤ normIn T (conjSubgroup g T) := by
    intro x hx
    exact mem_normIn.2 ⟨normIn_le _ _ hx, hNTg (normIn_le_sec4N_left hx)⟩
  have hcard : Nat.card (normIn T (conjSubgroup g T)) ≤ Nat.card (normIn T T₁) :=
    h.pair.card_normIn_le ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne
  have hL : normIn T (conjSubgroup g T) = normIn T T₁ :=
    (Subgroup.eq_of_le_of_card_ge hLle hcard).symm
  refine ⟨hL, ?_⟩
  have hLg : conjSubgroup g (normIn T T₁) ≤ normIn (conjSubgroup g T) T := by
    intro x hx
    have hxT : x ∈ conjSubgroup g T :=
      conjSubgroup_mono (normIn_le T T₁) hx
    have hxN : x ∈ sec4N T T₁ T₂ := by
      rw [← hNg]
      exact conjSubgroup_mono normIn_le_sec4N_left hx
    exact mem_normIn.2 ⟨hxT, sec4N_le_normalizer_left hxN⟩
  have hcfg : Cfg T (conjSubgroup g T) :=
    cfg_of_conj_conj h.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne (by
      rw [hL]
      exact h.sec3.cfg.ne)
  have hcard' := hcfg.card_normIn_eq ⟨g, rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hLg ?_).symm
  rw [card_conjSubgroup, ← hcard', hL]

theorem Sec4Hyp.sec3_conj_of_normalizer (h : Sec4Hyp T T₁ a T₂) {g : G}
    (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hne : conjSubgroup g T ≠ T) :
    Sec3 T (conjSubgroup g T) :=
  sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne (by
    rw [(h.normIn_conj_of_normalizer hg hne).1]
    exact h.sec3.cfg.ne)

theorem Sec4Hyp.cfgM_conj_le_sec4N (h : Sec4Hyp T T₁ a T₂) {g : G}
    (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hne : conjSubgroup g T ≠ T) :
    cfgM T (conjSubgroup g T) ≤ sec4N T T₁ T₂ := by
  obtain ⟨h1, h2⟩ := h.normIn_conj_of_normalizer hg hne
  have hNg : conjSubgroup g (sec4N T T₁ T₂) = sec4N T T₁ T₂ :=
    mem_normalizer_iff_conjSubgroup_eq.1 hg
  rw [cfgM, h1, h2]
  refine sup_le normIn_le_sec4N_left ?_
  rw [← hNg]
  exact conjSubgroup_mono normIn_le_sec4N_left

end Basic

section Core

variable {G : Type} [Group G] [Finite G]

theorem not_commutator_mem_of_odd {T T' N : Subgroup G} (hT : IsWC T) (hT' : IsWC T')
    (hN : IsElemAbelian 2 N) (hS : Sec3 T T') (hM : cfgM T T' ≤ N) (hne : T' ≠ T) {t c : G}
    (ht : t ∈ T) (htN : t ∉ N) (hc : c ∈ T') (hcN : c ∉ N) : (c * t)⁻¹ * (t * c) ∉ N := by
  intro hmem
  have hcc : c * c = 1 := elemAbelian_mul_self hT'.1 hc
  have htt : t * t = 1 := elemAbelian_mul_self hT.1 ht
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc1 : c ≠ 1 := fun h1 => hcN (h1 ▸ N.one_mem)
  by_cases hcomm : c * t = t * c
  ·
    have htN' : t ∈ Subgroup.normalizer (T' : Set G) :=
      hT'.centralizer_le_normalizer hc hc1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
    exact htN (hM (Cfg.normIn_le_cfgM_left T T' (mem_normIn.2 ⟨ht, htN'⟩)))
  ·
    have hsq : (c * t)⁻¹ * (t * c) = (t * c) ^ 2 := by
      rw [mul_inv_rev, hci, hti, pow_two]
    have hne1 : (t * c) ^ 2 ≠ 1 := by
      intro h1
      apply hcomm
      have h2 : (t * c) * (t * c) = 1 := by rwa [pow_two] at h1
      have h3 : t * c = (t * c)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [mul_inv_rev, hci, hti] at h3
      exact h3.symm
    have h4 : (t * c) ^ 4 = 1 := by
      have h1 := hN.2 _ hmem
      rw [hsq] at h1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact h1
    have hord : orderOf (t * c) = 4 := by
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t * c) (by simpa using hne1)
        (by simpa using h4)
      simpa using this
    obtain ⟨y, hyX, hy⟩ := hS.conj
    have hodd : Odd (orderOf (t * c)) := by
      refine hS.odd_orderOf_mul (x := 1) (y := y) (Subgroup.one_mem _) hyX ?_
        (by rw [conjSubgroup_one]; exact ht) ?_ ?_ ?_
      · rw [conjSubgroup_one, ← hy]
        exact hne.symm
      · exact fun htM => htN (hM htM)
      · rw [← hy]
        exact hc
      · exact fun hcM => hcN (hM hcM)
    rw [hord] at hodd
    exact absurd hodd (by decide)

theorem Sec4Hyp.not_comm_mod_sec4N {T T₁ T₂ : Subgroup G} {a : G} (h : Sec4Hyp T T₁ a T₂)
    {g : G} (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hne : conjSubgroup g T ≠ T) {t : G} (ht : t ∈ T) (htN : t ∉ sec4N T T₁ T₂) {c : G}
    (hc : c ∈ conjSubgroup g T) (hcN : c ∉ sec4N T T₁ T₂) :
    (c * t)⁻¹ * (t * c) ∉ sec4N T T₁ T₂ :=
  not_commutator_mem_of_odd h.pair.wc (h.pair.wc.conj g) h.isElemAbelian_sec4N
    (h.sec3_conj_of_normalizer hg hne) (h.cfgM_conj_le_sec4N hg hne) hne ht htN hc hcN

end Core

end CFSG.CGT.Timmesfeld75
