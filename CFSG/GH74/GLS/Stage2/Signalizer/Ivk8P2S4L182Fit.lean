module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

open Subgroup CFSG CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Norm

variable {G : Type} [Group G]

theorem conj_mem_map_subtype {M : Subgroup G} (K : Subgroup ↥M) [K.Normal] {m : G} (hm : m ∈ M)
    {y : G} (hy : y ∈ K.map M.subtype) : m * y * m⁻¹ ∈ K.map M.subtype := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨m, hm⟩ * y' * ⟨m, hm⟩⁻¹, Normal.conj_mem ‹K.Normal› y' hy' _, rfl⟩

theorem Fm_conj_mem (M : Subgroup G) {m : G} (hm : m ∈ M) {y : G} (hy : y ∈ Fm M) :
    m * y * m⁻¹ ∈ Fm M :=
  conj_mem_map_subtype (fittingSubgroup ↥M) hm hy

theorem Op_conj_mem (r : ℕ) (M : Subgroup G) {m : G} (hm : m ∈ M) {y : G} (hy : y ∈ Op r M) :
    m * y * m⁻¹ ∈ Op r M :=
  conj_mem_map_subtype (pCore r ↥M) hm hy

end Norm

section Cores

variable {G : Type} [Group G] [Finite G]

theorem Op_le_Fm (r : ℕ) [Fact r.Prime] (M : Subgroup G) : Op r M ≤ Fm M :=
  Subgroup.map_mono (pCore_le_fitting ↥M r)

omit [Finite G] in
theorem isPGroup_Op (r : ℕ) [Fact r.Prime] (M : Subgroup G) : IsPGroup r ↥(Op r M) :=
  (pCore_isPGroup (G := ↥M) (p := r)).map M.subtype

theorem odd_card_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {N : Subgroup G}
    (hN : IsPGroup p ↥N) : Odd (Nat.card ↥N) := by
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn]
  exact (hp.out.odd_of_ne_two hp2).pow

omit [Finite G] in
theorem le_pPrimeCoreOf_of_odd {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop' : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

omit [Finite G] in
theorem op_commute_of_ne {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) (M : Subgroup G)
    {y e : G} (hy : y ∈ Op q M) (he : e ∈ Op p M) : y * e = e * y := by
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨e', he', rfl⟩ := he
  have hcomm := (CFSG.LocalCores.distinct_prime_cores_commute (G := ↥M) hq hp hqp).2
  have hmem : ⁅y', e'⁆ ∈ ⁅pCore q ↥M, pCore p ↥M⁆ := Subgroup.commutator_mem_commutator hy' he'
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem Fm_isNilpotent (M : Subgroup G) : Group.IsNilpotent ↥(Fm M) :=
  Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)

theorem fm_centralized_of_op {M X : Subgroup G}
    (h : ∀ r : ℕ, r.Prime → ∀ x ∈ X, ∀ y ∈ Op r M, x * y * x⁻¹ = y) :
    ∀ x ∈ X, ∀ y ∈ Fm M, x * y * x⁻¹ = y := by
  have hle : Fm M ≤ centralizer (X : Set G) := by
    change (fittingSubgroup ↥M).map M.subtype ≤ _
    rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine iSup_le fun r => ?_
    have hr : (r.1.1).Prime := Nat.prime_of_mem_primeFactors r.1.2
    intro y hy x hx
    exact mul_inv_eq_iff_eq_mul.1 (h _ hr x hx y hy)
  intro x hx y hy
  exact mul_inv_eq_iff_eq_mul.2 (hle hy x hx)

end Cores

section Perfect

variable {G : Type} [Group G]

theorem Em_perfect (H : Subgroup G) [Finite G] : ⁅Em H, Em H⁆ = Em H := by
  show ⁅(layer ↥H).map H.subtype, (layer ↥H).map H.subtype⁆ = (layer ↥H).map H.subtype
  rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]

theorem layer_eq_top_of_Em_eq {X : Subgroup G} (h : Em X = X) : layer ↥X = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  exact h

theorem fm_inf_central [Finite G] {M X : Subgroup G} (hXM : X ≤ M) (hXE : Em X = X) {y : G}
    (hyX : y ∈ X) (hyF : y ∈ Fm M) {x : G} (hx : x ∈ X) : y * x = x * y := by
  let N : Subgroup ↥X := (Fm M).subgroupOf X
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using Fm_conj_mem M (hXM g.2) (Subgroup.mem_subgroupOf.1 hn)⟩
  have : Group.IsNilpotent ↥(Fm M) := Fm_isNilpotent M
  let φ : ↥N →* ↥(Fm M) :=
    { toFun := fun n => ⟨(n.1 : G), Subgroup.mem_subgroupOf.1 n.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun t : ↥(Fm M) => (t : G)) hab))
  have hnil : Group.IsNilpotent ↥N :=
    Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hφ).symm
  have hNF : N ≤ fittingSubgroup ↥X := CFSG.LocalCores.fitting_characteristic.2.2 N hN hnil
  have hcomm := CFSG.LocalCores.fitting_layer_commute (G := ↥X)
  rw [layer_eq_top_of_Em_eq hXE] at hcomm
  have hmem : (⟨y, hyX⟩ : ↥X) ∈ fittingSubgroup ↥X := hNF (Subgroup.mem_subgroupOf.2 hyF)
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hmem
  have := Subgroup.mem_centralizer_iff.1 hcen ⟨x, hx⟩ trivial
  exact (congrArg Subtype.val this).symm

end Perfect

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182
