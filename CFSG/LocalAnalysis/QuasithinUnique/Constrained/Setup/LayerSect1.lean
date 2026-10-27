module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddModule
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

theorem exists_good_perfect [Finite V] (ρ : X →* (V ≃ₗ[k] V)) (L : Subgroup X)
    (hperf : Group.IsPerfect ↥L) (h : ¬ (⊤ : Submodule k V) ≤ fixSub ρ L) :
    ∃ I : Submodule k V, IsGoodModule ρ L I := by
  obtain ⟨I, hI1, hI2, hmin⟩ := exists_minimal_noncentral ρ L h
  have hcI : Offender.IsInvariant ρ L (commSub ρ L I) := isInvariant_commSub hI1
  have hle : commSub ρ L I ≤ I := commSub_le_of_isInvariant hI1
  have hc : commSub ρ L I = I := by
    by_cases hf : commSub ρ L I ≤ fixSub ρ L
    · exfalso
      apply hI2
      intro u hu l hl
      let f : ↥L →* Multiplicative V :=
        { toFun := fun l => Multiplicative.ofAdd (ρ l u - u)
          map_one' := by simp
          map_mul' := fun a b => by
            have h1 : ρ (a : X) (ρ (b : X) u - u) = ρ (b : X) u - u :=
              hf (mem_commSub_of b.2 hu) a a.2
            show Multiplicative.ofAdd (ρ ((a : X) * (b : X)) u - u) =
              Multiplicative.ofAdd (ρ (a : X) u - u) * Multiplicative.ofAdd (ρ (b : X) u - u)
            rw [← ofAdd_add, ρ_mul_apply]
            congr 1
            rw [map_sub] at h1
            calc ρ (a : X) (ρ (b : X) u) - u
                = (ρ (a : X) (ρ (b : X) u) - ρ (a : X) u) + (ρ (a : X) u - u) := by abel
              _ = (ρ (b : X) u - u) + (ρ (a : X) u - u) := by rw [h1]
              _ = (ρ (a : X) u - u) + (ρ (b : X) u - u) := add_comm _ _ }
      have hker : (⊤ : Subgroup ↥L) ≤ f.ker := by
        rw [← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
      have h1 : f ⟨l, hl⟩ = 1 := hker (Subgroup.mem_top _)
      have h2 : ρ l u - u = 0 := by
        have := congrArg Multiplicative.toAdd h1
        simpa [f] using this
      exact sub_eq_zero.1 h2
    · exact hmin _ hcI hle hf
  refine ⟨I, hI1, hc, hI2, fun U hU hlo hhi => ?_⟩
  by_cases hUf : U ≤ fixSub ρ L
  · left
    exact le_antisymm (le_inf hhi hUf) hlo
  · right
    exact hmin U hU hhi hUf

theorem natCard_quotient_le_weight [Finite V] {B : Type*} [Group B]
    (ρ : B →* (V ≃ₗ[k] V)) (Z : Submodule k V) (hZ : ∀ x, ∀ z ∈ Z, ρ x z ∈ Z)
    (h : Nat.card V ≤ weight ρ ⊤) :
    Nat.card (V ⧸ Z) ≤ weight (quotHom ρ Z hZ) ⊤ := by
  unfold weight at h ⊢
  set π := quotHom ρ Z hZ with hπ
  have hmap : (fixSub ρ ⊤).map Z.mkQ ≤ fixSub π ⊤ := by
    rintro _ ⟨u, hu, rfl⟩ b _
    rw [quotHom_mkQ, hu b (Subgroup.mem_top b)]
  have h1 : Nat.card ↥((fixSub ρ ⊤).map Z.mkQ) ≤ Nat.card ↥(fixSub π ⊤) :=
    Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hmap)
  have h2 : Nat.card ↥(fixSub ρ ⊤ ⊓ Z) ≤ Nat.card ↥Z :=
    Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le inf_le_right)
  have h3 := natCard_map_mkQ_mul_natCard_inf Z (fixSub ρ ⊤)
  have h4 := Submodule.card_eq_card_quotient_mul_card Z
  have hfix : Nat.card ↥(fixSub ρ ⊤) ≤ Nat.card ↥(fixSub π ⊤) * Nat.card ↥Z := by
    rw [← h3]
    exact Nat.mul_le_mul h1 h2
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have h5 : Nat.card ↥(⊤ : Subgroup B) * Nat.card ↥(fixSub ρ ⊤) ≤
      Nat.card ↥(⊤ : Subgroup B) * (Nat.card ↥(fixSub π ⊤) * Nat.card ↥Z) :=
    Nat.mul_le_mul_left _ hfix
  have h6 : Nat.card (V ⧸ Z) * Nat.card ↥Z ≤
      (Nat.card ↥(⊤ : Subgroup B) * Nat.card ↥(fixSub π ⊤)) * Nat.card ↥Z := by
    calc Nat.card (V ⧸ Z) * Nat.card ↥Z = Nat.card V := (mul_comm _ _).trans h4.symm
      _ ≤ Nat.card ↥(⊤ : Subgroup B) * Nat.card ↥(fixSub ρ ⊤) := h
      _ ≤ Nat.card ↥(⊤ : Subgroup B) * (Nat.card ↥(fixSub π ⊤) * Nat.card ↥Z) := h5
      _ = (Nat.card ↥(⊤ : Subgroup B) * Nat.card ↥(fixSub π ⊤)) * Nat.card ↥Z := by ring
  exact Nat.le_of_mul_le_mul_right h6 hZpos

theorem commutator_normal_in_left {L A : Subgroup X}
    (hAL : A ≤ Subgroup.normalizer (L : Set X)) : (⁅L, A⁆.subgroupOf L).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (commutator_le_left hAL)]
  intro d l hd hl
  induction hd using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, a, ha, rfl⟩ := hy
    have e : l * ⁅x, a⁆ * l⁻¹ = ⁅l * x, a⁆ * ⁅l, a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (L.mul_mem hl hx) ha)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hl ha))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem comm_eq_of_quasisimple {L A : Subgroup X} (hL : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set X)) (hne : ⁅L, A⁆ ≠ ⊥) : ⁅L, A⁆ = L := by
  have hN := commutator_normal_in_left hAL
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with htop | hcen
  · apply le_antisymm (commutator_le_left hAL)
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ ⁅L, A⁆.subgroupOf L := by rw [htop]; trivial
    exact this
  · exfalso
    apply hne
    apply CFSG.LocalCores.perfect_double_commutator hL.1
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd l hl
    have hc := hcen (show (⟨d, commutator_le_left hAL hd⟩ : ↥L) ∈ ⁅L, A⁆.subgroupOf L from hd)
    rw [Subgroup.mem_center_iff] at hc
    have := hc ⟨l, hl⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val this).symm

theorem noPQuotient_centralPChief_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) {p : ℕ} (hp : p.Prime) : NoPQuotient p Q ∧ CentralPChief p Q := by
  have hq : ∀ i : Fin 1, CFSG.IsQuasisimple (⊤ : Subgroup Q) := fun _ =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
  obtain ⟨-, h2, -, h4, -⟩ := quasisimple_product (fun _ : Fin 1 => (⊤ : Subgroup Q)) hq
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (iSup_const)
  exact ⟨h2 p hp, h4 p hp⟩

end CFSG.QuasithinUnique.Setup.Layer
