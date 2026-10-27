module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem index_inf_centralizer_le_card_commutator [Finite G] {L V : Subgroup G} {y : G}
    (hy : y ∈ V) :
    ((L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G).subgroupOf L).index ≤
      Nat.card ↥(⁅V, L⁆ : Subgroup G) := by
  set Y' := (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G).subgroupOf L with hY'
  have hmem : ∀ l : L, (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈ (⁅V, L⁆ : Subgroup G) := fun l => by
    have e : (l : G) * y * (l : G)⁻¹ * y⁻¹ = (y * (l : G) * y⁻¹ * (l : G)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy l.2)
  let F : L ⧸ Y' → ↥(⁅V, L⁆ : Subgroup G) :=
    Quotient.lift (fun l : L => (⟨(l : G) * y * (l : G)⁻¹ * y⁻¹, hmem l⟩ : ↥(⁅V, L⁆ : Subgroup G)))
      (fun a b hab => by
        have hab' : (a : L)⁻¹ * b ∈ Y' := QuotientGroup.leftRel_apply.mp hab
        have h1 : ((a : G)⁻¹ * (b : G)) ∈ Subgroup.centralizer ({y} : Set G) := hab'.2
        rw [Subgroup.mem_centralizer_singleton_iff] at h1
        apply Subtype.ext
        show (a : G) * y * (a : G)⁻¹ * y⁻¹ = (b : G) * y * (b : G)⁻¹ * y⁻¹
        have h2 : (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ := by
          have : (a : G)⁻¹ * (b : G) * y = y * ((a : G)⁻¹ * (b : G)) := h1
          calc (a : G) * y * (a : G)⁻¹ = (a : G) * (y * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by
                group
            _ = (a : G) * ((a : G)⁻¹ * (b : G) * y) * (b : G)⁻¹ := by rw [this]
            _ = (b : G) * y * (b : G)⁻¹ := by group
        rw [h2])
  have hF : Function.Injective F := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | _ a =>
    induction q using Quotient.inductionOn with
    | _ b =>
    have h1 : (a : G) * y * (a : G)⁻¹ * y⁻¹ = (b : G) * y * (b : G)⁻¹ * y⁻¹ :=
      congrArg Subtype.val hpq
    have h2 : (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ := mul_right_cancel h1
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    rw [hY', Subgroup.mem_subgroupOf]
    refine ⟨(a⁻¹ * b).2, ?_⟩
    change ((a⁻¹ * b : L) : G) ∈ Subgroup.centralizer ({y} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (a : G)⁻¹ * (b : G) * y = y * ((a : G)⁻¹ * (b : G))
    calc (a : G)⁻¹ * (b : G) * y = (a : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) := by group
      _ = (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (b : G) := by rw [h2]
      _ = y * ((a : G)⁻¹ * (b : G)) := by group
  have := Nat.card_le_card_of_injective F hF
  rw [hY']
  exact this

theorem three_dvd_card_inf_centralizer_of_orbit_bound [Finite G] {L V : Subgroup G} {y : G}
    (hy : y ∈ V) {n : ℕ} (hn : Nat.card ↥(⁅V, L⁆ : Subgroup G) ≤ n)
    (hb : ∀ Y : Subgroup G, Y ≤ L → ¬ 3 ∣ Nat.card Y → n * Nat.card Y < Nat.card L) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  by_contra h3
  set Y : Subgroup G := L ⊓ Subgroup.centralizer ({y} : Set G) with hY
  have hlt := hb Y inf_le_left h3
  have hidx := (index_inf_centralizer_le_card_commutator (L := L) hy).trans hn
  have hcard := Subgroup.index_mul_card (Y.subgroupOf L)
  have hY' : Nat.card (Y.subgroupOf L) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ≤ L)).toEquiv
  rw [hY'] at hcard
  have : (Y.subgroupOf L).index * Nat.card Y ≤ n * Nat.card Y := Nat.mul_le_mul_right _ hidx
  omega


theorem mul_card_lt_card_of_surjective {A Γ : Type*} [Group A] [Finite A] [Group Γ]
    (F : A →* Γ) (hF : Function.Surjective F) {c n : ℕ}
    (hc : ∀ H : Subgroup Γ, ¬ 3 ∣ Nat.card H → Nat.card H ≤ c) (hlt : n * c < Nat.card Γ)
    (Y : Subgroup A) (hY : ¬ 3 ∣ Nat.card Y) : n * Nat.card Y < Nat.card A := by
  have hA : Nat.card F.ker * Nat.card F.range = Nat.card A := Subgroup.card_ker_mul_card_range F
  have hrange : Nat.card F.range = Nat.card Γ := by
    rw [F.range_eq_top_of_surjective hF, Subgroup.card_top]
  have hYle : Nat.card Y ≤ Nat.card F.ker * Nat.card (Y.map F) := by
    have h1 : Nat.card (F.comp Y.subtype).ker * Nat.card (F.comp Y.subtype).range = Nat.card Y :=
      Subgroup.card_ker_mul_card_range (F.comp Y.subtype)
    have h2 : (F.comp Y.subtype).range = Y.map F := by
      ext z; simp [MonoidHom.mem_range, Subgroup.mem_map]
    have h3 : Nat.card (F.comp Y.subtype).ker ≤ Nat.card F.ker := by
      have hinj : Function.Injective
          (fun x : (F.comp Y.subtype).ker => (⟨(x : Y).1, x.2⟩ : F.ker)) := by
        intro a b hab
        have : (((a : (F.comp Y.subtype).ker) : Y) : A) = (((b : (F.comp Y.subtype).ker) : Y) : A) :=
          congrArg (fun z : F.ker => (z : A)) hab
        exact Subtype.ext (Subtype.ext this)
      exact Nat.card_le_card_of_injective _ hinj
    rw [h2] at h1
    rw [← h1]
    exact Nat.mul_le_mul_right _ h3
  have hFY : ¬ 3 ∣ Nat.card (Y.map F) := fun h =>
    hY (h.trans (Subgroup.card_map_dvd Y F))
  have hFYc := hc _ hFY
  have hker : 0 < Nat.card F.ker := Nat.card_pos
  rw [hrange] at hA
  calc n * Nat.card Y ≤ n * (Nat.card F.ker * Nat.card (Y.map F)) := Nat.mul_le_mul_left _ hYle
    _ ≤ n * (Nat.card F.ker * c) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hFYc)
    _ = Nat.card F.ker * (n * c) := by ring
    _ < Nat.card F.ker * Nat.card Γ := Nat.mul_lt_mul_of_pos_left hlt hker
    _ = Nat.card A := hA

theorem three_dvd_card_inf_centralizer_of_quotient_bound [Finite G] {L V : Subgroup G} {y : G}
    (hy : y ∈ V) {Γ : Type*} [Group Γ] (F : ↥L →* Γ) (hF : Function.Surjective F) {c n : ℕ}
    (hn : Nat.card ↥(⁅V, L⁆ : Subgroup G) ≤ n)
    (hc : ∀ H : Subgroup Γ, ¬ 3 ∣ Nat.card H → Nat.card H ≤ c) (hlt : n * c < Nat.card Γ) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  refine three_dvd_card_inf_centralizer_of_orbit_bound hy hn fun Y hYL hY3 => ?_
  have h := mul_card_lt_card_of_surjective F hF hc hlt (Y.subgroupOf L)
    (by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv])
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv] at h

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
