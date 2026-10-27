module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open
open CFSG.RankThree.Classical (spEnd)
open scoped commutatorElement

private theorem isSolvable_of_card {G : Type*} [Group G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

private theorem isSolvable_sup {G : Type*} [Group G] {P Q : Subgroup G}
    (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) [Group.IsSolvable P] [Group.IsSolvable Q] :
    Group.IsSolvable ↥(P ⊔ Q) := by
  have hf := MonoidHom.noncommCoprod_range P.subtype Q.subtype fun a b => hc a a.2 b b.2
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hf
  rw [← hf]
  exact Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)

private theorem commutator_le_self {G : Type*} [Group G] (P : Subgroup G) : ⁅P, P⁆ ≤ P :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)

private theorem commutator_normal_sup {G : Type*} [Group G] {P Q : Subgroup G}
    (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) : (⁅P, P⁆.subgroupOf (P ⊔ Q)).Normal := by
  refine ⟨fun k hk x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  obtain ⟨a, ha, b, hb, hx⟩ := CatB.U4Sp8.exists_mul_of_mem_sup hc x.2
  have hkb : (k : G) * b = b * k := hc k (commutator_le_self P hk) b hb
  have e : ((x * k * x⁻¹ : ↥(P ⊔ Q)) : G) = ⁅a, (k : G)⁆ * k := by
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx,
      mul_assoc a b, ← hkb]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator ha (commutator_le_self P hk)) hk

private theorem glaPLayer_eq_bot {G : Type} [Group G] [Finite G] {X : Subgroup G}
    [Group.IsSolvable X] : GLAPLayer 3 X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun L hL g hg => ?_)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val
    (CFSG.HardMathSupport.Solomon.Coordinator.hom_eq_one_of_solvable Nat.prime_three hL
      (MonoidHom.id X) g hg)

private theorem card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem exists_ne_comm_of_card {T : Type*} [Group T] [IsSimpleGroup T]
    (h : Nat.card T = 360) : ∃ a b : T, a * b ≠ b * a := by
  by_contra hcon
  letI : CommGroup T :=
    { (inferInstance : Group T) with
      mul_comm := fun a b => by_contra fun hab => hcon ⟨a, b, hab⟩ }
  have hp := (CommGroup.is_simple_iff_prime_card (α := T)).1 inferInstance
  rw [h] at hp
  norm_num at hp

section Layer

variable {s : StatedSp 3 (ZMod 2)} {s₀ m : ℕ} {A₀ A₁ : Subgroup (StatedSp 3 (ZMod 2))}

private theorem isSolvable_fixed (hc : Sp6Class s s₀ m A₀ A₁) (hs : s₀ ≤ 1) :
    Group.IsSolvable ↥A₀ := by
  rcases hc.fixed with ⟨-, rfl⟩ | ⟨h1, ⟨e⟩⟩
  · exact isSolvable_of_card (a := 0) (b := 0) (by rw [Subgroup.card_bot]; norm_num)
  · obtain rfl : s₀ = 1 := by omega
    refine isSolvable_of_card (a := 1) (b := 1) ?_
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
    norm_num

private theorem isSolvable_unitary (hc : Sp6Class s s₀ m A₀ A₁) : Group.IsSolvable ↥A₁ := by
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e⟩⟩ := hc.unitary
  have hcard := (CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hdim hc.one_le).1
  rw [← Nat.card_congr e.toEquiv] at hcard
  have h1 := hc.one_le
  have h3 : m ≤ 3 := by have := hc.sum_eq; omega
  interval_cases m
  · refine isSolvable_of_card (a := 0) (b := 1) ?_
    norm_num [Finset.Icc_self] at hcard
    exact_mod_cast hcard
  · refine isSolvable_of_card (a := 1) (b := 2) ?_
    norm_num [Finset.prod_Icc_succ_top] at hcard
    exact_mod_cast hcard
  · refine isSolvable_of_card (a := 3) (b := 4) ?_
    norm_num [Finset.prod_Icc_succ_top] at hcard
    exact_mod_cast hcard

theorem Sp6Class.layer (hc : Sp6Class s s₀ m A₀ A₁) :
    (m = 1 → (⁅A₀, A₀⁆.subgroupOf (Subgroup.centralizer {s})).Normal ∧
        Nonempty (↥⁅A₀, A₀⁆ ≃* alternatingGroup (Fin 6)) ∧
        ⁅A₀, A₀⁆ ≤ GLAPLayer 3 (Subgroup.centralizer {s})) ∧
      (2 ≤ m → Group.IsSolvable ↥(Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2)))) ∧
        GLAPLayer 3 (Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2)))) = ⊥) := by
  have hsum := hc.sum_eq
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  ·
    obtain rfl : s₀ = 2 := by omega
    obtain ⟨-, ⟨e₀⟩⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨eS⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := ZMod 2) (ZMod.card 2)
    obtain ⟨eA⟩ :=
      CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating (e₀.trans eS)
    have hn := commutator_normal_sup hc.commute
    rw [← hc.centralizer_eq] at hn
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup ↥⁅A₀, A₀⁆ := eA.isSimpleGroup
    have hcard : Nat.card ↥⁅A₀, A₀⁆ = 360 := (Nat.card_congr eA.toEquiv).trans card_alt_six
    refine ⟨hn, ⟨eA⟩, ?_⟩
    refine CFSG.HardMathSupport.Solomon.Coordinator.le_glaPLayer_of_normal_simple Nat.prime_three
      ?_ hn (exists_ne_comm_of_card hcard) (by rw [hcard]; norm_num)
    rw [hc.centralizer_eq]
    exact (commutator_le_self A₀).trans le_sup_left
  ·
    have hsol : Group.IsSolvable ↥(Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2)))) := by
      rw [hc.centralizer_eq]
      haveI := isSolvable_fixed hc (by omega)
      haveI := isSolvable_unitary hc
      exact isSolvable_sup hc.commute
    exact ⟨hsol, glaPLayer_eq_bot⟩

end Layer

theorem finrank_ker_le_two_of_layer_eq_bot_sp6 {s : StatedSp 3 (ZMod 2)} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1)
    (hL : GLAPLayer 3 (Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2)))) = ⊥) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd s - 1)) ≤ 2 := by
  obtain ⟨s₀, m, A₀, A₁, hc⟩ := exists_sp6Class hs3 hs1
  have hsum := hc.sum_eq
  have h1 := hc.one_le
  have hm : m ≠ 1 := by
    intro hm
    obtain ⟨-, ⟨e⟩, hle⟩ := hc.layer.1 hm
    rw [hL, le_bot_iff] at hle
    have h := Nat.card_congr e.toEquiv
    rw [hle, Subgroup.card_bot, card_alt_six] at h
    omega
  rw [hc.finrank_fixed]
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
