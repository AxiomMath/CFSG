module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem i1810_card_sylow_eq_one_of_le_center {H : Type*} [Group H] [Finite H]
    [hperf : Group.IsPerfect H] {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hP : (P : Subgroup H) ≤ Subgroup.center H) : Nat.card P = 1 := by
  have hPN : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_center_iff.1 (hP hx) g).symm
  obtain ⟨K, hKn, -, hidx, -, -, -, -, -, -, hab⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPN
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h : (QuotientGroup.mk' K) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab _ _
    exact (QuotientGroup.eq_one_iff _).1 h
  rw [← hidx, hK, Subgroup.index_top]

theorem i1810_exists_derivedSeries_succ_eq (H : Type*) [Group H] [Finite H] :
    ∃ n, derivedSeries H (n + 1) = derivedSeries H n := by
  by_contra h
  push Not at h
  have key : ∀ n, n + Nat.card (derivedSeries H n) ≤ Nat.card H := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : derivedSeries H (n + 1) ≤ derivedSeries H n := by
        rw [derivedSeries_succ]
        exact Subgroup.commutator_le_left _ _
      have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h n))
      omega
  have := key (Nat.card H + 1)
  omega

theorem i1810_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P N : Subgroup G} [N.Normal] (hP : IsPGroup p P) (hN : ¬ p ∣ N.index) : P ≤ N := by
  have himage : IsPGroup p (P.map (QuotientGroup.mk' N)) := hP.map _
  obtain ⟨k, hk⟩ := himage.exists_card_eq
  have hdvd : Nat.card (P.map (QuotientGroup.mk' N)) ∣ N.index := by
    rw [Subgroup.index]
    exact Subgroup.card_subgroup_dvd_card _
  cases k with
  | zero =>
    rw [pow_zero] at hk
    have h1 := Subgroup.card_eq_one.1 hk
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  | succ k => exact absurd ((dvd_pow_self p k.succ_ne_zero).trans (hk ▸ hdvd)) hN

theorem i1810_card_comap_mk {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (K : Subgroup (G ⧸ N)) :
    Nat.card (K.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card K := by
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index K
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective N)] at h1
  have hne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (K.comap (QuotientGroup.mk' N)) * K.index =
      (Nat.card N * Nat.card K) * K.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h4

theorem i1810_sup_normal_of_conj {G : Type*} [Group G] {H N : Subgroup G} [hN : N.Normal]
    (h : ∀ g : G, ∀ x ∈ H, g * x * g⁻¹ ∈ H ⊔ N) : (H ⊔ N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : H ⊔ N ≤ (H ⊔ N).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun m hm => ?_)
    · rw [Subgroup.mem_comap]
      exact h g x hx
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (hN.conj_mem m hm g)
  exact hle hn

theorem i1810_map_normal_of_characteristic {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (K : Subgroup N) [hK : K.Characteristic] : (K.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have hmap : K.map (MulAut.conjNormal g : MulAut N).toMonoidHom = K :=
    Subgroup.characteristic_iff_map_eq.1 hK _
  have hy' : (MulAut.conjNormal g : MulAut N) y ∈ K := by
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  refine ⟨_, hy', ?_⟩
  simp [MulAut.conjNormal_apply]

end CFSG.HardMathSupport.Solomon.Coordinator
