module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Cycle
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Equiv Equiv.Perm Subgroup

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def orb (T : Subgroup (Perm Ω)) (x : Ω) : Set Ω := {y | ∃ t ∈ T, t x = y}

section OrbitBasic

variable {T : Subgroup (Perm Ω)}

theorem mem_orb_self (x : Ω) : x ∈ orb T x := ⟨1, T.one_mem, rfl⟩

theorem orb_trans {x y w : Ω} (hy : y ∈ orb T x) (hw : w ∈ orb T y) : w ∈ orb T x := by
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨t * s, T.mul_mem ht hs, rfl⟩

theorem orb_symm {x y : Ω} (hy : y ∈ orb T x) : x ∈ orb T y := by
  obtain ⟨s, hs, rfl⟩ := hy
  exact ⟨s⁻¹, T.inv_mem hs, by simp⟩

theorem smul_mem_orb {t : Perm Ω} (ht : t ∈ T) {x y : Ω} (hy : y ∈ orb T x) : t y ∈ orb T x := by
  obtain ⟨s, hs, rfl⟩ := hy
  exact ⟨t * s, T.mul_mem ht hs, rfl⟩

theorem card_orb_dvd (T : Subgroup (Perm Ω)) (x : Ω) : Nat.card (orb T x) ∣ Nat.card T := by
  have hset : MulAction.orbit T x = orb T x := by
    ext w
    simp [MulAction.mem_orbit_iff, orb, Subgroup.smul_def]
  rw [← hset, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

end OrbitBasic

structure OrbitSetting (p : ℕ) (z : Perm Ω) (T : Subgroup (Perm Ω)) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  order : orderOf z = p
  card_lt : Fintype.card Ω < 2 * p
  two_group : IsPGroup 2 T
  comm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s
  sq : ∀ t ∈ T, t * t = 1
  inv : ∀ t, t ∈ T ↔ z * t * z⁻¹ ∈ T
  min : ∀ T₁ : Subgroup (Perm Ω), T₁ ≤ T → (∀ t, t ∈ T₁ ↔ z * t * z⁻¹ ∈ T₁) →
    T₁ = ⊥ ∨ T₁ = T

namespace OrbitSetting

variable {p : ℕ} {z : Perm Ω} {T : Subgroup (Perm Ω)} (h : OrbitSetting p z T)
include h

theorem cycle : z.IsCycle := isCycle_of_order h.prime h.order h.card_lt

theorem card_support : z.support.card = p := card_support_eq h.prime h.order h.card_lt

theorem p_ne_two : p ≠ 2 := by
  have := h.five_le
  omega

theorem conj_pow_mem (i : ℕ) {t : Perm Ω} (ht : t ∈ T) : (z ^ i) * t * (z ^ i)⁻¹ ∈ T := by
  induction i with
  | zero => simpa using ht
  | succ i ih =>
    have h1 := (h.inv _).1 ih
    have e : z * ((z ^ i) * t * (z ^ i)⁻¹) * z⁻¹ = (z ^ (i + 1)) * t * (z ^ (i + 1))⁻¹ := by
      rw [pow_succ' z i]
      group
    rwa [e] at h1

theorem moved_all (hmove : ∃ x, z x ≠ x ∧ ∃ t ∈ T, t x ≠ x) :
    ∀ x, z x ≠ x → ∃ t ∈ T, t x ≠ x := by
  obtain ⟨x₁, hx₁, t₁, ht₁, hne⟩ := hmove
  intro x hx
  obtain ⟨i, hi⟩ := h.cycle.exists_pow_eq hx₁ hx
  refine ⟨(z ^ i) * t₁ * (z ^ i)⁻¹, h.conj_pow_mem i ht₁, ?_⟩
  intro heq
  apply hne
  rw [← hi] at heq
  simp only [Perm.mul_apply, perm_inv_apply_self] at heq
  exact (z ^ i).injective heq

theorem exists_two_in_orbit (hmove : ∀ x, z x ≠ x → ∃ t ∈ T, t x ≠ x) :
    ∃ x y, z x ≠ x ∧ z y ≠ y ∧ y ≠ x ∧ y ∈ orb T x := by
  classical
  by_contra hcon
  push Not at hcon
  choose! g hgT hgne using hmove
  set S := z.support with hS
  have hmem : ∀ x, x ∈ S ↔ z x ≠ x := fun x => Equiv.Perm.mem_support
  have hgo : ∀ x, z x ≠ x → g x x ∈ orb T x := fun x hx => ⟨g x, hgT x hx, rfl⟩
  have hnot : ∀ x ∈ S, g x x ∉ S := by
    intro x hx hgx
    exact hcon x (g x x) ((hmem x).1 hx) ((hmem _).1 hgx) (hgne x ((hmem x).1 hx))
      (hgo x ((hmem x).1 hx)) |>.elim
  have hinj : Set.InjOn (fun x => g x x) (S : Set Ω) := by
    intro x hx y hy hxy
    by_contra hne
    have hx' := (hmem x).1 (Finset.mem_coe.1 hx)
    have hy' := (hmem y).1 (Finset.mem_coe.1 hy)
    apply hcon x y hx' hy' (Ne.symm hne)
    refine ⟨(g y)⁻¹ * g x, T.mul_mem (T.inv_mem (hgT y hy')) (hgT x hx'), ?_⟩
    simp only [Perm.mul_apply]
    have : g x x = g y y := hxy
    rw [this, perm_inv_apply_self]
  have hdisj : Disjoint S (S.image fun x => g x x) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
    exact hnot x hx ha
  have hcard : (S ∪ S.image fun x => g x x).card = 2 * p := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, hS, h.card_support]
    ring
  have := Finset.card_le_univ (S ∪ S.image fun x => g x x)
  have := h.card_lt
  omega

theorem orbit_invariant {x y : Ω} (hx : z x ≠ x) (hy : z y ≠ y) (hne : y ≠ x)
    (hyx : y ∈ orb T x) :
    (∀ w ∈ orb T x, z w ∈ orb T x) ∧ ∀ w, z w ≠ w → w ∈ orb T x := by
  obtain ⟨k, hk⟩ := h.cycle.exists_pow_eq hx hy
  have hk0 : ¬ p ∣ k := by
    intro hdvd
    have h1 : z ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (h.order ▸ hdvd)
    apply hne
    rw [← hk, h1, Perm.one_apply]
  have hcop : Nat.Coprime k (orderOf z) := by
    rw [h.order]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hk0)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hInv : ∀ w ∈ orb T x, (z ^ k) w ∈ orb T x := by
    rintro w ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hyx
    refine ⟨((z ^ k) * t * (z ^ k)⁻¹) * s, T.mul_mem (h.conj_pow_mem k ht) hs, ?_⟩
    have e : (z ^ k)⁻¹ (s x) = x := by rw [hsx, ← hk, perm_inv_apply_self]
    simp only [Perm.mul_apply, e]
  have hIter : ∀ n : ℕ, ∀ w ∈ orb T x, (z ^ (k * n)) w ∈ orb T x := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      have e : (z ^ (k * (n + 1))) w = (z ^ k) ((z ^ (k * n)) w) := by
        rw [show k * (n + 1) = k + k * n by ring, pow_add, Perm.mul_apply]
      rw [e]
      exact hInv _ (ih w hw)
  have hz1 : ∀ w ∈ orb T x, z w ∈ orb T x := by
    intro w hw
    have := hIter m w hw
    rwa [pow_mul, hm] at this
  refine ⟨hz1, fun w hw => ?_⟩
  obtain ⟨i, hi⟩ := h.cycle.exists_pow_eq hx hw
  have hall : ∀ i : ℕ, (z ^ i) x ∈ orb T x := by
    intro i
    induction i with
    | zero => simpa using mem_orb_self x
    | succ i ih =>
      have : (z ^ (i + 1)) x = z ((z ^ i) x) := by rw [pow_succ', Perm.mul_apply]
      rw [this]
      exact hz1 _ ih
  rw [← hi]
  exact hall i

theorem exists_fixed_in_orbit {x : Ω} (hsub : ∀ w, z w ≠ w → w ∈ orb T x) :
    ∃ o ∈ orb T x, z o = o := by
  by_contra hcon
  push Not at hcon
  have hset : orb T x = (z.support : Set Ω) := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_coe.2 (Equiv.Perm.mem_support.2 (hcon w hw))
    · intro hw
      exact hsub w (Equiv.Perm.mem_support.1 (Finset.mem_coe.1 hw))
  have hcard : Nat.card (orb T x) = p := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, h.card_support]
  have hdvd := card_orb_dvd T x
  rw [hcard] at hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h.two_group
  rw [hn] at hdvd
  have h2 : p ∣ 2 := h.prime.dvd_of_dvd_pow hdvd
  have := Nat.le_of_dvd (by norm_num) h2
  have := h.five_le
  omega

theorem stab_dichotomy {x : Ω} (hzx : z x = x) :
    (∀ t ∈ T, t x = x → t = 1) ∨ (∀ t ∈ T, t x = x) := by
  have hzi : z⁻¹ x = x := by rw [Perm.inv_eq_iff_eq]; exact hzx.symm
  set T₁ : Subgroup (Perm Ω) := T ⊓ MulAction.stabilizer (Perm Ω) x with hT₁
  have hmem : ∀ t, t ∈ T₁ ↔ t ∈ T ∧ t x = x := fun t => by
    simp [hT₁, MulAction.mem_stabilizer_iff]
  have hinv : ∀ t, t ∈ T₁ ↔ z * t * z⁻¹ ∈ T₁ := by
    intro t
    rw [hmem, hmem, ← h.inv t]
    simp only [Perm.mul_apply, hzi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2, hzx]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      apply z.injective
      rw [h2, hzx]
  rcases h.min T₁ inf_le_left hinv with hb | ht
  · left
    intro t htT htx
    have : t ∈ T₁ := (hmem t).2 ⟨htT, htx⟩
    rw [hb] at this
    exact Subgroup.mem_bot.1 this
  · right
    intro t htT
    have : t ∈ T₁ := by rw [ht]; exact htT
    exact ((hmem t).1 this).2

theorem free_at_o {x o : Ω} (hsub : ∀ w, z w ≠ w → w ∈ orb T x) (ho : o ∈ orb T x)
    (hzo : z o = o) : ∀ t ∈ T, t o = o → t = 1 := by
  rcases h.stab_dichotomy hzo with hfree | hfix
  · exact hfree
  · exfalso
    have hall : ∀ w ∈ orb T x, w = o := by
      rintro w ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hso⟩ := orb_symm ho
      rw [← hso]
      exact hfix (t * s) (T.mul_mem ht hs)
    have hsub1 : z.support ⊆ {o} := by
      intro w hw
      exact Finset.mem_singleton.2 (hall w (hsub w (Equiv.Perm.mem_support.1 hw)))
    have := Finset.card_le_card hsub1
    rw [h.card_support, Finset.card_singleton] at this
    have := h.five_le
    omega

theorem fixed_outside {o : Ω} (hmove : ∃ w, z w ≠ w ∧ ∃ t ∈ T, t w ≠ w)
    (hsub : ∀ w, z w ≠ w → w ∈ orb T o) : ∀ x, x ∉ orb T o → ∀ t ∈ T, t x = x := by
  intro x hx
  have hzx : z x = x := by
    by_contra hne
    exact hx (hsub x hne)
  rcases h.stab_dichotomy hzx with hfree | hfix
  · exfalso
    have hcomm : ∀ t ∈ T, t * z = z * t := by
      intro t ht
      have hc : z * t * z⁻¹ * t⁻¹ ∈ T := T.mul_mem ((h.inv t).1 ht) (T.inv_mem ht)
      have hnot : t⁻¹ x ∉ orb T o := fun hmem => hx (by
        have := smul_mem_orb ht hmem
        rwa [perm_apply_inv_self] at this)
      have hzf : z (t⁻¹ x) = t⁻¹ x := by
        by_contra hne
        exact hnot (hsub _ hne)
      have hzf' : z⁻¹ (t⁻¹ x) = t⁻¹ x := by
        rw [Perm.inv_eq_iff_eq]
        exact hzf.symm
      have hx1 : (z * t * z⁻¹ * t⁻¹) x = x := by
        simp only [Perm.mul_apply, hzf', perm_apply_inv_self, hzx]
      have h1 := hfree _ hc hx1
      have h2 : z * t * z⁻¹ = t := mul_inv_eq_one.1 h1
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    obtain ⟨w, hw, t, ht, hne⟩ := hmove
    exact hne (fixes_of_commute h.prime h.p_ne_two h.order h.cycle (hcomm t ht) (h.sq t ht) hw)
  · exact hfix

theorem orbit_structure (hmove : ∃ x, z x ≠ x ∧ ∃ t ∈ T, t x ≠ x) :
    ∃ o : Ω, z o = o ∧ (∀ t ∈ T, t o = o → t = 1) ∧ (∀ x, z x ≠ x → ∃ s ∈ T, s o = x) ∧
      ∀ x, (¬ ∃ s ∈ T, s o = x) → z x = x ∧ ∀ t ∈ T, t x = x := by
  have hall := h.moved_all hmove
  obtain ⟨x, y, hx, hy, hne, hyx⟩ := h.exists_two_in_orbit hall
  obtain ⟨-, hsub⟩ := h.orbit_invariant hx hy hne hyx
  obtain ⟨o, ho, hzo⟩ := h.exists_fixed_in_orbit hsub
  have hfree := h.free_at_o hsub ho hzo
  have hsub' : ∀ w, z w ≠ w → w ∈ orb T o := fun w hw => orb_trans (orb_symm ho) (hsub w hw)
  have hout := h.fixed_outside hmove hsub'
  refine ⟨o, hzo, hfree, fun w hw => hsub' w hw, fun w hw => ?_⟩
  have hw' : w ∉ orb T o := hw
  refine ⟨?_, hout w hw'⟩
  by_contra hne'
  exact hw' (hsub' w hne')

end OrbitSetting

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
