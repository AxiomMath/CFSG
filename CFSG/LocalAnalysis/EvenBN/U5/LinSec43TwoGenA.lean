module

public import CFSG.Open.LocalVocabulary
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinT43

open Subgroup Matrix
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem card_le_range_mul [Finite G] {H N : Subgroup G} {T : Type*} (ρ : H → T)
    (hρ : ∀ a b : H, ρ a = ρ b → (a : G)⁻¹ * (b : G) ∈ N) :
    Nat.card H ≤ Nat.card (Set.range ρ) * Nat.card N := by
  have hsurj : ∀ t : Set.range ρ, ∃ c : H, ρ c = t.1 := fun t => Set.mem_range.mp t.2
  choose rep hrep using hsurj
  let s : H → Set.range ρ := fun a => ⟨ρ a, Set.mem_range_self a⟩
  let Φ : H → Set.range ρ × N := fun a =>
    (s a, ⟨((rep (s a) : H) : G)⁻¹ * (a : G), hρ (rep (s a)) a (hrep (s a))⟩)
  have hΦ : Function.Injective Φ := by
    intro a b hab
    have h1 : s a = s b := congrArg Prod.fst hab
    have h2 : ((rep (s a) : H) : G)⁻¹ * (a : G) = ((rep (s b) : H) : G)⁻¹ * (b : G) :=
      congrArg (fun p : Set.range ρ × N => ((p.2 : N) : G)) hab
    rw [congrArg rep h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  calc Nat.card H ≤ Nat.card (Set.range ρ × N) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (Set.range ρ) * Nat.card N := Nat.card_prod _ _

theorem card_ker_mulVec_le {k : Type*} [Field k] [Finite k] (M : Matrix (Fin 2) (Fin 2) k)
    (hM : M ≠ 0) : Nat.card {v : Fin 2 → k // M *ᵥ v = 0} ≤ Nat.card k := by
  classical
  set K : Submodule k (Fin 2 → k) := LinearMap.ker (Matrix.mulVecLin M) with hKdef
  have hmem : ∀ v : Fin 2 → k, v ∈ K ↔ M *ᵥ v = 0 := fun v => by
    rw [hKdef, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hK : K ≠ ⊤ := by
    intro htop
    apply hM
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.zero_mulVec]
    have hall : (Pi.single j (1 : k) : Fin 2 → k) ∈ K := by
      rw [htop]
      exact Submodule.mem_top
    exact (hmem _).1 hall
  have hlt : Module.finrank k K < Module.finrank k (Fin 2 → k) := Submodule.finrank_lt hK
  have hfin : Module.finrank k (Fin 2 → k) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hle : Module.finrank k K ≤ 1 := by omega
  have hcard : Nat.card K = Nat.card k ^ Module.finrank k K := Module.natCard_eq_pow_finrank
  have hequiv : Nat.card {v : Fin 2 → k // M *ᵥ v = 0} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => (hmem v).symm)
  have hpos : 0 < Nat.card k := Nat.card_pos
  rw [hequiv, hcard]
  calc Nat.card k ^ Module.finrank k K ≤ Nat.card k ^ 1 := Nat.pow_le_pow_right hpos hle
    _ = Nat.card k := pow_one _

theorem card_inf_centralizer_le_of_isNaturalModule [Finite G] {k : Type*} [Field k] [Finite k]
    {R : Subgroup G} {φ : R ≃* SL(2, k)} {θ : (Fin 2 → k) → G}
    (hθ : CFSG.Timmesfeld.ARS.IsNaturalModule φ θ) {A : Subgroup G}
    (hA : Set.range θ = (A : Set G)) {y : G} (hy : y ∈ R) (hy1 : y ≠ 1) :
    Nat.card (A ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ Nat.card k := by
  set M : Matrix (Fin 2) (Fin 2) k := (φ ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) k) with hMdef
  have hM1 : M - 1 ≠ 0 := by
    intro h
    have hM : M = 1 := sub_eq_zero.mp h
    have hφ1 : φ ⟨y, hy⟩ = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact congrFun (congrFun hM i) j
    have hy' : (⟨y, hy⟩ : R) = 1 := φ.injective (hφ1.trans (map_one φ).symm)
    exact hy1 (congrArg Subtype.val hy')
  have hθA : ∀ a : (A ⊓ centralizer ({y} : Set G) : Subgroup G), ∃ v : Fin 2 → k,
      θ v = (a : G) := by
    intro a
    have ha : (a : G) ∈ Set.range θ := by
      rw [hA]
      exact (Subgroup.mem_inf.mp a.2).1
    exact Set.mem_range.mp ha
  choose vOf hvOf using hθA
  have hfix : ∀ a : (A ⊓ centralizer ({y} : Set G) : Subgroup G), M *ᵥ vOf a = vOf a := by
    intro a
    have hcomm : (a : G) * y = y * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp a.2).2
    have key : θ (M *ᵥ vOf a) = (a : G) := by
      have h := hθ.map_mulVec ⟨y, hy⟩ (vOf a)
      rw [hvOf a] at h
      rw [hMdef, h]
      show y * (a : G) * y⁻¹ = (a : G)
      rw [hcomm.symm]
      simp
    apply hθ.injective
    exact key.trans (hvOf a).symm
  let f : (A ⊓ centralizer ({y} : Set G) : Subgroup G) → {v : Fin 2 → k // (M - 1) *ᵥ v = 0} :=
    fun a => ⟨vOf a, by rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]; exact hfix a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hv : vOf a = vOf b := congrArg Subtype.val hab
    exact Subtype.ext ((hvOf a).symm.trans ((congrArg θ hv).trans (hvOf b)))
  calc Nat.card (A ⊓ centralizer ({y} : Set G) : Subgroup G)
      ≤ Nat.card {v : Fin 2 → k // (M - 1) *ᵥ v = 0} := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card k := card_ker_mulVec_le (M - 1) hM1

end LinT43

end CFSG.LocalAnalysis.EvenBN.U5
