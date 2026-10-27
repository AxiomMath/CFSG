module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm

private abbrev pairEmbedding {m : ℕ} (i j : Fin m) (hij : i ≠ j) : Fin 2 ↪ Fin m where
  toFun k := if k = 0 then i else j
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

@[simp]
private theorem pairEmbedding_zero {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    pairEmbedding i j hij (0 : Fin 2) = i := rfl

@[simp]
private theorem pairEmbedding_one {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    pairEmbedding i j hij (1 : Fin 2) = j := rfl

private noncomputable abbrev pairPermHom {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Equiv.Perm (Fin 2) →* Equiv.Perm (Fin m) :=
  Equiv.Perm.viaEmbeddingHom (pairEmbedding i j hij)

private theorem pairPermHom_apply_pair {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (u : Equiv.Perm (Fin 2)) (k : Fin 2) :
    pairPermHom i j hij u (pairEmbedding i j hij k) = pairEmbedding i j hij (u k) := by
  rw [pairPermHom, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]

private theorem pairPermHom_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    pairPermHom i j hij (Equiv.swap (0 : Fin 2) 1) = Equiv.swap i j := by
  ext x
  by_cases hx : x ∈ Set.range (pairEmbedding i j hij)
  · obtain ⟨k, rfl⟩ := hx
    rw [pairPermHom_apply_pair]
    fin_cases k <;> simp
  · have hxi : x ≠ i := by
      intro h
      exact hx ⟨0, by rw [pairEmbedding_zero, h]⟩
    have hxj : x ≠ j := by
      intro h
      exact hx ⟨1, by rw [pairEmbedding_one, h]⟩
    rw [pairPermHom, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ x hx,
      Equiv.swap_apply_of_ne_of_ne hxi hxj]

private theorem pairPermHom_apply_of_ne {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (u : Equiv.Perm (Fin 2)) {x : Fin m} (hxi : x ≠ i) (hxj : x ≠ j) :
    pairPermHom i j hij u x = x := by
  have hx : x ∉ Set.range (pairEmbedding i j hij) := by
    rintro ⟨k, hk⟩
    fin_cases k
    · exact hxi hk.symm
    · exact hxj hk.symm
  rw [pairPermHom, Equiv.Perm.viaEmbeddingHom_apply,
    Equiv.Perm.viaEmbedding_apply_of_notMem _ _ x hx]

private theorem complementPermHom_fixes_left {m : ℕ} (i j : Fin m)
    (σ : Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) :
    Equiv.Perm.ofSubtype σ i = i :=
  Equiv.Perm.ofSubtype_apply_of_not_mem σ (by simp)

private theorem complementPermHom_fixes_right {m : ℕ} (i j : Fin m)
    (σ : Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) :
    Equiv.Perm.ofSubtype σ j = j :=
  Equiv.Perm.ofSubtype_apply_of_not_mem σ (by simp)

private theorem commute_ofSubtype_swap {m : ℕ} (i j : Fin m)
    (σ : Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) :
    Commute (Equiv.Perm.ofSubtype σ) (Equiv.swap i j) := by
  show Equiv.Perm.ofSubtype σ * Equiv.swap i j = Equiv.swap i j * Equiv.Perm.ofSubtype σ
  rw [Equiv.mul_swap_eq_swap_mul, complementPermHom_fixes_left,
    complementPermHom_fixes_right]

private theorem commute_pairPermHom_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (u : Equiv.Perm (Fin 2)) :
    Commute (pairPermHom i j hij u) (Equiv.swap i j) := by
  have hcomm : u * Equiv.swap (0 : Fin 2) 1 = Equiv.swap (0 : Fin 2) 1 * u :=
    (Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (by simp)).is_comm.comm u _
  rw [← pairPermHom_swap i j hij]
  change pairPermHom i j hij u * pairPermHom i j hij (Equiv.swap (0 : Fin 2) 1) =
    pairPermHom i j hij (Equiv.swap (0 : Fin 2) 1) * pairPermHom i j hij u
  rw [← map_mul, ← map_mul]
  exact congrArg (pairPermHom i j hij) hcomm

private theorem commute_ofSubtype_pairPermHom {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (σ : Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) (u : Equiv.Perm (Fin 2)) :
    Commute (Equiv.Perm.ofSubtype σ) (pairPermHom i j hij u) := by
  apply Equiv.Perm.Disjoint.commute
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro x hx
  rw [Equiv.Perm.notMem_support]
  have hxi : x ≠ i := by
    intro h
    rw [h] at hx
    exact (Equiv.Perm.mem_support.mp hx) (complementPermHom_fixes_left i j σ)
  have hxj : x ≠ j := by
    intro h
    rw [h] at hx
    exact (Equiv.Perm.mem_support.mp hx) (complementPermHom_fixes_right i j σ)
  exact pairPermHom_apply_of_ne i j hij u hxi hxj

private noncomputable def centralizerSwapHom {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Equiv.Perm (Fin 2) × Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j} →*
      ↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin m)))) where
  toFun p :=
    ⟨pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm₁ : Commute (pairPermHom i j hij p.1) (Equiv.swap i j) :=
        commute_pairPermHom_swap i j hij p.1
      have hcomm₂ : Commute (Equiv.Perm.ofSubtype p.2) (Equiv.swap i j) :=
        commute_ofSubtype_swap i j p.2
      calc
        (pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2) * Equiv.swap i j
            = pairPermHom i j hij p.1 *
                (Equiv.Perm.ofSubtype p.2 * Equiv.swap i j) := by group
        _ = pairPermHom i j hij p.1 *
                (Equiv.swap i j * Equiv.Perm.ofSubtype p.2) := by rw [hcomm₂.eq]
        _ = (pairPermHom i j hij p.1 * Equiv.swap i j) *
                Equiv.Perm.ofSubtype p.2 := by group
        _ = (Equiv.swap i j * pairPermHom i j hij p.1) *
                Equiv.Perm.ofSubtype p.2 := by rw [hcomm₁.eq]
        _ = Equiv.swap i j *
                (pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2) := by group⟩
  map_one' := by
    apply Subtype.ext
    simp [pairPermHom]
  map_mul' := by
    intro p q
    apply Subtype.ext
    change pairPermHom i j hij (p.1 * q.1) * Equiv.Perm.ofSubtype (p.2 * q.2) =
      (pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2) *
        (pairPermHom i j hij q.1 * Equiv.Perm.ofSubtype q.2)
    rw [map_mul, map_mul]
    have hcomm : Commute (Equiv.Perm.ofSubtype p.2) (pairPermHom i j hij q.1) :=
      commute_ofSubtype_pairPermHom i j hij p.2 q.1
    calc
      (pairPermHom i j hij p.1 * pairPermHom i j hij q.1) *
          (Equiv.Perm.ofSubtype p.2 * Equiv.Perm.ofSubtype q.2)
          = pairPermHom i j hij p.1 *
              (pairPermHom i j hij q.1 * Equiv.Perm.ofSubtype p.2) *
                Equiv.Perm.ofSubtype q.2 := by group
      _ = pairPermHom i j hij p.1 *
              (Equiv.Perm.ofSubtype p.2 * pairPermHom i j hij q.1) *
                Equiv.Perm.ofSubtype q.2 := by rw [hcomm.eq]
      _ = (pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2) *
              (pairPermHom i j hij q.1 * Equiv.Perm.ofSubtype q.2) := by group

private theorem centralizerSwapHom_injective {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Function.Injective (centralizerSwapHom i j hij) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have hprod : pairPermHom i j hij p.1 * Equiv.Perm.ofSubtype p.2 = 1 :=
    congrArg Subtype.val hp
  have h0 : p.1 0 = 0 := by
    have h := congrArg (fun f : Equiv.Perm (Fin m) => f i) hprod
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, complementPermHom_fixes_left] at h
    have h' : pairEmbedding i j hij (p.1 0) = pairEmbedding i j hij 0 := by
      rw [← pairPermHom_apply_pair i j hij p.1 0, pairEmbedding_zero]
      exact h
    exact (pairEmbedding i j hij).injective h'
  have h1 : p.1 1 = 1 := by
    have h := congrArg (fun f : Equiv.Perm (Fin m) => f j) hprod
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, complementPermHom_fixes_right] at h
    have h' : pairEmbedding i j hij (p.1 1) = pairEmbedding i j hij 1 := by
      rw [← pairPermHom_apply_pair i j hij p.1 1, pairEmbedding_one]
      exact h
    exact (pairEmbedding i j hij).injective h'
  have hu : p.1 = 1 := by
    ext k
    fin_cases k <;> simp [h0, h1]
  have hσ : p.2 = 1 := by
    have hof : Equiv.Perm.ofSubtype p.2 = 1 := by
      rw [hu, map_one, one_mul] at hprod
      exact hprod
    exact Equiv.Perm.ofSubtype_injective (by
      rw [map_one]
      exact hof)
  exact Prod.ext hu hσ

private theorem nat_card_centralizerSwapHom_domain {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Nat.card (Equiv.Perm (Fin 2) × Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) =
      2 * (m - 2).factorial := by
  have hcomp : Nat.card {x : Fin m // x ≠ i ∧ x ≠ j} = m - 2 := by
    classical
    have hcard : Fintype.card {x : Fin m // x ≠ i ∧ x ≠ j} = m - 2 := by
      have hcompl : Fintype.card {x : Fin m // x ≠ i ∧ x ≠ j} =
          Fintype.card (Fin m) - Fintype.card {x : Fin m // x = i ∨ x = j} := by
        simpa only [not_or] using
          (Fintype.card_subtype_compl (α := Fin m) (p := fun x => x = i ∨ x = j))
      rw [hcompl, Fintype.card_fin, Fintype.card_subtype_eq_or_eq_of_ne hij]
    rw [Nat.card_eq_fintype_card, hcard]
  rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, hcomp]
  norm_num

theorem nonempty_centralizer_swap_mulEquiv {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Nonempty (↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin m)))) ≃*
      (Equiv.Perm (Fin 2) × Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j})) := by
  classical
  let φ := centralizerSwapHom i j hij
  have hinj : Function.Injective φ := centralizerSwapHom_injective i j hij
  have hcard :
      Nat.card (Equiv.Perm (Fin 2) × Equiv.Perm {x : Fin m // x ≠ i ∧ x ≠ j}) =
        Nat.card ↥(Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin m)))) := by
    rw [nat_card_centralizerSwapHom_domain hij]
    have hcyc : (Equiv.swap i j).cycleType = {2} := by
      rw [(Equiv.Perm.isCycle_swap hij).cycleType, Equiv.Perm.card_support_swap hij]
    rw [Equiv.Perm.nat_card_centralizer, hcyc]
    simp [Nat.mul_comm]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end CFSG.GroupTheory
