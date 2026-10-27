module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.IsPerfect
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.GroupTheory.PermSixSylowThree

variable {G : Type*} [Group G] {H Q : Subgroup G}

open scoped Pointwise

private def cycA : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def cycB : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private def p0Set : Finset (Equiv.Perm (Fin 6)) :=
  {1, cycA, cycA ^ 2, cycB, cycB ^ 2, cycA * cycB, cycA * cycB ^ 2, cycA ^ 2 * cycB,
    cycA ^ 2 * cycB ^ 2}

open scoped CFSG.Decide.Bounded in
private theorem p0_mul : ∀ a ∈ p0Set, ∀ b ∈ p0Set, a * b ∈ p0Set := by decide +kernel

private theorem p0_one : (1 : Equiv.Perm (Fin 6)) ∈ p0Set := by decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem p0_inv : ∀ a ∈ p0Set, a⁻¹ ∈ p0Set := by decide +kernel

private theorem p0_set_card : p0Set.card = 9 := by decide +kernel

private def p0 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := ↑p0Set
  mul_mem' := fun ha hb => p0_mul _ ha _ hb
  one_mem' := p0_one
  inv_mem' := fun ha => p0_inv _ ha

private theorem p0_card : Nat.card p0 = 9 := by
  change Nat.card ↥p0Set = 9
  rw [Nat.card_eq_finsetCard]
  exact p0_set_card

private theorem card_permFinSix : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_fin]
  decide

private theorem p0_isPGroup : IsPGroup 3 p0 :=
  IsPGroup.of_card (n := 2) (by rw [p0_card]; norm_num)

private theorem p0_index : p0.index = 80 := by
  have h := p0.index_mul_card
  rw [p0_card, card_permFinSix] at h
  omega

private theorem p0_existsSylow :
    ∃ P : Sylow 3 (Equiv.Perm (Fin 6)), (P : Subgroup (Equiv.Perm (Fin 6))) = p0 := by
  have hprime3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨p0_isPGroup.toSylow (by rw [p0_index]; norm_num), ?_⟩
  simp

open scoped CFSG.Decide.Bounded in
private theorem sign_of_commute_cycA_cycB :
    ∀ π : Equiv.Perm (Fin 6), π * cycA = cycA * π → π * cycB = cycB * π →
      Equiv.Perm.sign π = 1 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem commute_or_inv_of_normalizes_p0 :
    ∀ π : Equiv.Perm (Fin 6), Equiv.Perm.sign π = 1 →
      π * cycA * π⁻¹ ∈ p0Set → π * cycB * π⁻¹ ∈ p0Set →
      π ^ 2 * cycA = cycA * π ^ 2 → π ^ 2 * cycB = cycB * π ^ 2 →
      (∀ p ∈ p0Set, π * p = p * π) ∨ ∀ p ∈ p0Set, π * p * π⁻¹ = p⁻¹ := by
  decide +kernel

private theorem map_commutator_eq_alternating (e : ↥H ≃* Equiv.Perm (Fin 6)) :
    (commutator ↥H).map e.toMonoidHom = alternatingGroup (Fin 6) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 6))

private theorem mem_commutator_iff_sign (e : ↥H ≃* Equiv.Perm (Fin 6)) {x : G} (hx : x ∈ H) :
    x ∈ ⁅H, H⁆ ↔ Equiv.Perm.sign (e ⟨x, hx⟩) = 1 := by
  have hx' : (⟨x, hx⟩ : ↥H) ∈ commutator ↥H ↔
      e ⟨x, hx⟩ ∈ alternatingGroup (Fin 6) := by
    rw [← map_commutator_eq_alternating e]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  have hx'' : (⟨x, hx⟩ : ↥H) ∈ commutator ↥H ↔
      Equiv.Perm.sign (e ⟨x, hx⟩) = 1 := by
    rw [hx', Equiv.Perm.mem_alternatingGroup]
  have hsub : x ∈ (commutator ↥H).map H.subtype ↔
      (⟨x, hx⟩ : ↥H) ∈ commutator ↥H := by
    simpa using (Subgroup.mem_map_iff_mem H.subtype_injective
      (x := (⟨x, hx⟩ : ↥H)))
  rw [← Subgroup.map_subtype_commutator]
  exact hsub.trans hx''

private theorem cycA_mem : cycA ∈ p0Set := by decide +kernel

private theorem cycB_mem : cycB ∈ p0Set := by decide +kernel

private theorem exists_conj_p0_eq (e : ↥H ≃* Equiv.Perm (Fin 6)) (hQH : Q ≤ H)
    (hQ : Nat.card Q = 9) :
    ∃ σ : Equiv.Perm (Fin 6),
      MulAut.conj σ • p0 = (Q.subgroupOf H).map e.toMonoidHom := by
  let Q₁ : Subgroup (Equiv.Perm (Fin 6)) := (Q.subgroupOf H).map e.toMonoidHom
  have hQ1card : Nat.card Q₁ = 9 := by
    calc Nat.card Q₁ = Nat.card ↥(Q.subgroupOf H) :=
          Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
      _ = Nat.card ↥Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
      _ = 9 := hQ
  have hQ1index : Q₁.index = 80 := by
    have h := Q₁.index_mul_card
    rw [hQ1card, card_permFinSix] at h
    omega
  have hQ1isP : IsPGroup 3 Q₁ :=
    IsPGroup.of_card (n := 2) (by rw [hQ1card]; norm_num)
  have hprime3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q₁syl : Sylow 3 (Equiv.Perm (Fin 6)) :=
    hQ1isP.toSylow (by rw [hQ1index]; norm_num)
  obtain ⟨P₀syl, hP₀syl⟩ := p0_existsSylow
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) P₀syl Q₁syl
  refine ⟨σ, ?_⟩
  have hσ' : (MulAut.conj σ) • p0 = Q₁ := by
    have h := congrArg (fun S : Sylow 3 (Equiv.Perm (Fin 6)) =>
      (S : Subgroup (Equiv.Perm (Fin 6)))) hσ
    rw [Sylow.coe_subgroup_smul, hP₀syl] at h
    simpa [Q₁syl] using h
  simpa [Q₁] using hσ'

private theorem mem_p0_conj_of_mem {σ : Equiv.Perm (Fin 6)}
    {S : Subgroup (Equiv.Perm (Fin 6))} (hσ : (MulAut.conj σ) • p0 = S)
    {q : Equiv.Perm (Fin 6)} (hq : q ∈ S) : σ⁻¹ * q * σ ∈ p0 := by
  have hq' : q ∈ (MulAut.conj σ) • p0 := hσ.symm ▸ hq
  have h := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
    (a := MulAut.conj σ) (S := p0) (x := q)).mp hq'
  simpa [MulAut.smul_def, MulAut.conj_symm_apply] using h

private theorem mem_conj_p0_of_mem {σ : Equiv.Perm (Fin 6)}
    {S : Subgroup (Equiv.Perm (Fin 6))} (hσ : (MulAut.conj σ) • p0 = S)
    {p : Equiv.Perm (Fin 6)} (hp : p ∈ p0) : σ * p * σ⁻¹ ∈ S := by
  have h : σ * p * σ⁻¹ ∈ (MulAut.conj σ) • p0 := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using
      (Subgroup.smul_mem_pointwise_smul p (MulAut.conj σ) p0 hp)
  rwa [hσ] at h

theorem mem_commutator_of_commute (e : ↥H ≃* Equiv.Perm (Fin 6)) (hQH : Q ≤ H)
    (hQ : Nat.card Q = 9) {x : G} (hx : x ∈ H) (hxQ : ∀ y ∈ Q, x * y = y * x) :
    x ∈ ⁅H, H⁆ := by
  obtain ⟨σ, hσ⟩ := exists_conj_p0_eq (H := H) (Q := Q) e hQH hQ
  let Q₁ : Subgroup (Equiv.Perm (Fin 6)) := (Q.subgroupOf H).map e.toMonoidHom
  let x' : Equiv.Perm (Fin 6) := e ⟨x, hx⟩
  let π : Equiv.Perm (Fin 6) := σ⁻¹ * x' * σ
  have hσQ : (MulAut.conj σ) • p0 = Q₁ := by simpa [Q₁] using hσ
  have hx'cent : ∀ q ∈ Q₁, x' * q = q * x' := by
    intro q hq
    change q ∈ (Q.subgroupOf H).map e.toMonoidHom at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    have hcommH : (⟨x, hx⟩ : ↥H) * y = y * ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using hxQ (y : G) hyQ
    calc
      x' * e y = e ((⟨x, hx⟩ : ↥H) * y) := by
        dsimp [x']
        rw [← map_mul]
      _ = e (y * ⟨x, hx⟩) := by rw [hcommH]
      _ = e y * x' := by
        dsimp [x']
        rw [← map_mul]
  have hπcent : ∀ p ∈ p0, π * p = p * π := by
    intro p hp
    have hq : σ * p * σ⁻¹ ∈ Q₁ := mem_conj_p0_of_mem hσQ hp
    have hconj : x' * (σ * p * σ⁻¹) = (σ * p * σ⁻¹) * x' := hx'cent _ hq
    calc
      π * p = σ⁻¹ * (x' * (σ * p * σ⁻¹)) * σ := by
        dsimp [π]
        group
      _ = σ⁻¹ * ((σ * p * σ⁻¹) * x') * σ := by rw [hconj]
      _ = p * π := by
        dsimp [π]
        group
  have hsignπ : Equiv.Perm.sign π = 1 :=
    sign_of_commute_cycA_cycB π (hπcent cycA cycA_mem) (hπcent cycB cycB_mem)
  have hsignx' : Equiv.Perm.sign x' = 1 := by
    have hconj : Equiv.Perm.sign π = Equiv.Perm.sign x' := by
      dsimp [π]
      calc
        Equiv.Perm.sign (σ⁻¹ * x' * σ) =
            Equiv.Perm.sign σ⁻¹ * Equiv.Perm.sign x' * Equiv.Perm.sign σ := by
          rw [map_mul, map_mul]
        _ = Equiv.Perm.sign x' := by
          rw [mul_assoc, mul_comm (Equiv.Perm.sign x') (Equiv.Perm.sign σ),
            ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rwa [hconj] at hsignπ
  exact (mem_commutator_iff_sign e hx).mpr hsignx'

theorem commute_or_inv_of_sq_commute (e : ↥H ≃* Equiv.Perm (Fin 6)) (hQH : Q ≤ H)
    (hQ : Nat.card Q = 9) {n : G} (hn : n ∈ ⁅H, H⁆) (hnQ : ∀ y ∈ Q, n * y * n⁻¹ ∈ Q)
    (hn2 : ∀ y ∈ Q, n ^ 2 * y = y * n ^ 2) :
    (∀ y ∈ Q, n * y = y * n) ∨ ∀ y ∈ Q, n * y * n⁻¹ = y⁻¹ := by
  have hnH : n ∈ H := Subgroup.commutator_le_self H hn
  obtain ⟨σ, hσ⟩ := exists_conj_p0_eq (H := H) (Q := Q) e hQH hQ
  let Q₁ : Subgroup (Equiv.Perm (Fin 6)) := (Q.subgroupOf H).map e.toMonoidHom
  let n' : Equiv.Perm (Fin 6) := e ⟨n, hnH⟩
  let π : Equiv.Perm (Fin 6) := σ⁻¹ * n' * σ
  have hσQ : (MulAut.conj σ) • p0 = Q₁ := by simpa [Q₁] using hσ
  have hn'norm : ∀ q ∈ Q₁, n' * q * n'⁻¹ ∈ Q₁ := by
    intro q hq
    change q ∈ (Q.subgroupOf H).map e.toMonoidHom at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    have hmem : n * (y : G) * n⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hnH y.2) (H.inv_mem hnH)
    have heq : n' * e y * n'⁻¹ = e ⟨n * (y : G) * n⁻¹, hmem⟩ := by
      dsimp [n']
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    change n' * e y * n'⁻¹ ∈ (Q.subgroupOf H).map e.toMonoidHom
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨⟨n * (y : G) * n⁻¹, hmem⟩,
      Subgroup.mem_subgroupOf.mpr (hnQ (y : G) hyQ), rfl⟩
  have hn'2cent : ∀ q ∈ Q₁, n' ^ 2 * q = q * n' ^ 2 := by
    intro q hq
    change q ∈ (Q.subgroupOf H).map e.toMonoidHom at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    let a : ↥H := ⟨n, hnH⟩
    have hcommH : a ^ 2 * y = y * a ^ 2 := by
      apply Subtype.ext
      simpa [a, sq] using hn2 (y : G) hyQ
    have hn'2 : n' ^ 2 = e (a ^ 2) := by
      dsimp [n', a]
      rw [← map_pow]
      rfl
    calc
      n' ^ 2 * e y = e (a ^ 2 * y) := by rw [hn'2, ← map_mul]
      _ = e (y * a ^ 2) := by rw [hcommH]
      _ = e y * n' ^ 2 := by rw [hn'2, ← map_mul]
  have hπnorm : ∀ p ∈ p0, π * p * π⁻¹ ∈ p0 := by
    intro p hp
    have hq : σ * p * σ⁻¹ ∈ Q₁ := mem_conj_p0_of_mem hσQ hp
    have hconj : n' * (σ * p * σ⁻¹) * n'⁻¹ ∈ Q₁ := hn'norm _ hq
    have heq : π * p * π⁻¹ = σ⁻¹ * (n' * (σ * p * σ⁻¹) * n'⁻¹) * σ := by
      dsimp [π]
      group
    rw [heq]
    exact mem_p0_conj_of_mem hσQ hconj
  have hπ2cent : ∀ p ∈ p0, π ^ 2 * p = p * π ^ 2 := by
    intro p hp
    have hq : σ * p * σ⁻¹ ∈ Q₁ := mem_conj_p0_of_mem hσQ hp
    have hconj : n' ^ 2 * (σ * p * σ⁻¹) = (σ * p * σ⁻¹) * n' ^ 2 :=
      hn'2cent _ hq
    have hπ2 : π ^ 2 = σ⁻¹ * n' ^ 2 * σ := by
      dsimp [π]
      calc
        (σ⁻¹ * n' * σ) ^ 2 = (σ⁻¹ * n' * σ) * (σ⁻¹ * n' * σ) := by rw [pow_two]
        _ = σ⁻¹ * n' * (σ * σ⁻¹) * n' * σ := by simp only [mul_assoc]
        _ = σ⁻¹ * n' * n' * σ := by rw [mul_inv_cancel, mul_one]
        _ = σ⁻¹ * n' ^ 2 * σ := by rw [pow_two]; simp only [mul_assoc]
    rw [hπ2]
    calc
      σ⁻¹ * n' ^ 2 * σ * p = σ⁻¹ * (n' ^ 2 * (σ * p * σ⁻¹)) * σ := by group
      _ = σ⁻¹ * ((σ * p * σ⁻¹) * n' ^ 2) * σ := by rw [hconj]
      _ = p * (σ⁻¹ * n' ^ 2 * σ) := by group
  have hsign_n' : Equiv.Perm.sign n' = 1 := (mem_commutator_iff_sign e hnH).mp hn
  have hsignπ : Equiv.Perm.sign π = 1 := by
    dsimp [π]
    calc
      Equiv.Perm.sign (σ⁻¹ * n' * σ) =
          Equiv.Perm.sign σ⁻¹ * Equiv.Perm.sign n' * Equiv.Perm.sign σ := by
        rw [map_mul, map_mul]
      _ = 1 := by
        rw [hsign_n']
        simp only [mul_one]
        rw [← map_mul, inv_mul_cancel, map_one]
  have hfin := commute_or_inv_of_normalizes_p0 π hsignπ
    (by simpa [p0] using hπnorm cycA cycA_mem)
    (by simpa [p0] using hπnorm cycB cycB_mem)
    (by simpa using hπ2cent cycA cycA_mem)
    (by simpa using hπ2cent cycB cycB_mem)
  rcases hfin with hcent | hinv
  · left
    intro y hy
    have hyH : y ∈ H := hQH hy
    let yH : ↥H := ⟨y, hyH⟩
    have hq : e yH ∈ Q₁ :=
      Subgroup.mem_map.mpr ⟨yH, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hp : σ⁻¹ * e yH * σ ∈ p0 := mem_p0_conj_of_mem hσQ hq
    have hpSet : σ⁻¹ * e yH * σ ∈ p0Set := by simpa [p0] using hp
    have hcommπ := hcent (σ⁻¹ * e yH * σ) hpSet
    have hn'comm : n' * e yH = e yH * n' := by
      dsimp [π] at hcommπ
      calc
        n' * e yH = σ * (σ⁻¹ * n' * σ * (σ⁻¹ * e yH * σ)) * σ⁻¹ := by group
        _ = σ * ((σ⁻¹ * e yH * σ) * (σ⁻¹ * n' * σ)) * σ⁻¹ := by rw [hcommπ]
        _ = e yH * n' := by group
    have hsub : (⟨n, hnH⟩ : ↥H) * yH = yH * ⟨n, hnH⟩ := by
      apply e.injective
      simpa [n', map_mul] using hn'comm
    exact congrArg (fun z : ↥H => (z : G)) hsub
  · right
    intro y hy
    have hyH : y ∈ H := hQH hy
    let yH : ↥H := ⟨y, hyH⟩
    have hq : e yH ∈ Q₁ :=
      Subgroup.mem_map.mpr ⟨yH, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hp : σ⁻¹ * e yH * σ ∈ p0 := mem_p0_conj_of_mem hσQ hq
    have hpSet : σ⁻¹ * e yH * σ ∈ p0Set := by simpa [p0] using hp
    have hinvπ := hinv (σ⁻¹ * e yH * σ) hpSet
    have hn'inv : n' * e yH * n'⁻¹ = (e yH)⁻¹ := by
      dsimp [π] at hinvπ
      calc
        n' * e yH * n'⁻¹ =
            σ * ((σ⁻¹ * n' * σ) * (σ⁻¹ * e yH * σ) * (σ⁻¹ * n' * σ)⁻¹) * σ⁻¹ := by
          group
        _ = σ * (σ⁻¹ * e yH * σ)⁻¹ * σ⁻¹ := by rw [hinvπ]
        _ = (e yH)⁻¹ := by group
    have hsub : (⟨n, hnH⟩ : ↥H) * yH * (⟨n, hnH⟩ : ↥H)⁻¹ = yH⁻¹ := by
      apply e.injective
      simpa [n', map_mul, map_inv] using hn'inv
    exact congrArg (fun z : ↥H => (z : G)) hsub

theorem mul_mem_commutator_iff (e : ↥H ≃* Equiv.Perm (Fin 6)) {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : x * y ∈ ⁅H, H⁆ ↔ (x ∈ ⁅H, H⁆ ↔ y ∈ ⁅H, H⁆) := by
  have hxyH : x * y ∈ H := H.mul_mem hx hy
  have hlog : Equiv.Perm.sign (e ⟨x * y, hxyH⟩) =
      Equiv.Perm.sign (e ⟨x, hx⟩) * Equiv.Perm.sign (e ⟨y, hy⟩) := by
    rw [show (⟨x * y, hxyH⟩ : ↥H) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
    exact map_mul (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ) _ _
  rw [mem_commutator_iff_sign e hxyH, mem_commutator_iff_sign e hx,
    mem_commutator_iff_sign e hy, hlog]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e ⟨x, hx⟩)) with hx1 | hx1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (e ⟨y, hy⟩)) with hy1 | hy1 <;>
      simp [hx1, hy1]

theorem card_commutator (e : ↥H ≃* Equiv.Perm (Fin 6)) : Nat.card ↥⁅H, H⁆ = 360 := by
  have h1 : Nat.card ↥⁅H, H⁆ = Nat.card (commutator ↥H) := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.card_map_of_injective H.subtype_injective
  have h2 : Nat.card (commutator ↥H) = Nat.card ↥(alternatingGroup (Fin 6)) := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_commutator_eq_alternating e]
  rw [h1, h2, nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem commutator_commutator_eq (e : ↥H ≃* Equiv.Perm (Fin 6)) :
    ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆ := by
  let K : Subgroup ↥H := commutator ↥H
  have hmap : K.map e.toMonoidHom = alternatingGroup (Fin 6) := map_commutator_eq_alternating e
  let eK : K ≃* ↥(alternatingGroup (Fin 6)) :=
    (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let HK : K ≃* ↥⁅H, H⁆ :=
    (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  let F : ↥⁅H, H⁆ ≃* ↥(alternatingGroup (Fin 6)) := HK.symm.trans eK
  have hperfA : Group.IsPerfect ↥(alternatingGroup (Fin 6)) := by
    rw [Subgroup.isPerfect_iff]
    exact commutator_alternatingGroup_eq_self (by simp : 5 ≤ Nat.card (Fin 6))
  have hperfAinst := hperfA
  have hperfH' : Group.IsPerfect ↥⁅H, H⁆ :=
    Group.IsPerfect.ofSurjective (f := F.symm.toMonoidHom) F.symm.surjective
  exact Subgroup.isPerfect_iff.mp hperfH'

end CFSG.GroupTheory.PermSixSylowThree

end
