module

public import CFSG.Quasithin.Background.A1bKrullSchmidt
public import CFSG.GroupTheory.PCore.Construction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import all CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.GroupTheory.SylowInfNormal

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Quasithin
open scoped commutatorElement

theorem isIndecomposableGroup_of_isSimpleGroup (Y : Type*) [Group Y] [IsSimpleGroup Y] :
    IsIndecomposableGroup Y := by
  refine And.intro (inferInstance : Nontrivial Y) ?_
  intro B C hB _ hBC _
  rcases hB.eq_bot_or_eq_top with h | h
  · exact Or.inl h
  · rw [h, top_inf_eq] at hBC
    exact Or.inr hBC

private theorem exists_three_distinct {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 3 ≤ Nat.card α) : ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) (n := 3)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hα)
  rw [Finset.card_eq_three] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  exact ⟨a, b, c, hab, hac, hbc⟩

theorem isIndecomposableGroup_perm {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 5 ≤ Nat.card α) : IsIndecomposableGroup (Equiv.Perm α) := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := exists_three_distinct (α := α) (by omega)
  have hntPerm : Nontrivial (Equiv.Perm α) :=
    ⟨Equiv.swap a b, 1, fun h => hab (by
      simpa [Equiv.swap_apply_left] using congrArg (fun σ : Equiv.Perm α => σ a) h.symm)⟩
  refine And.intro hntPerm ?_
  intro B C hB hC hBC _
  by_contra hcon
  push Not at hcon
  have hB' : alternatingGroup α ≤ B :=
    Equiv.Perm.alternatingGroup_le_of_normal (N := B) hα ((nontrivial_iff_ne_bot B).2 hcon.1)
  have hC' : alternatingGroup α ≤ C :=
    Equiv.Perm.alternatingGroup_le_of_normal (N := C) hα ((nontrivial_iff_ne_bot C).2 hcon.2)
  have hmem : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup α := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc, Int.units_mul_self]
  have hone : Equiv.swap a b * Equiv.swap b c = 1 := by
    rw [← Subgroup.mem_bot, ← hBC]
    exact ⟨hB' hmem, hC' hmem⟩
  have h2 : (Equiv.swap a b * Equiv.swap b c) a = a := by rw [hone]; rfl
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac,
    Equiv.swap_apply_left] at h2
  exact hab h2.symm

private theorem inf_sylow_eq_bot_of_normal {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pCore 2 Y = ⊥) (T : Sylow 2 Y) {X : Subgroup Y}
    (hXT : (X ⊓ (T : Subgroup Y)).Normal) : X ⊓ (T : Subgroup Y) = ⊥ := by
  have hle : X ⊓ (T : Subgroup Y) ≤ CFSG.pCore 2 Y := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (X ⊓ (T : Subgroup Y)) (le_iSup_of_le hXT
      (le_iSup_of_le ((T.isPGroup').to_le inf_le_right) le_rfl))
  rw [hO] at hle
  exact le_bot_iff.mp hle

private theorem not_two_dvd_card_of_inf_sylow_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (T : Sylow 2 Y) {X : Subgroup Y} (hX : X.Normal)
    (hXT : X ⊓ (T : Subgroup Y) = ⊥) : ¬ 2 ∣ Nat.card X := by
  have hTY : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup Y) (⊤ : Subgroup Y) := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    have hcoeeq : (↑(T.subtype le_top) : Subgroup ↥(⊤ : Subgroup Y)) =
        (T : Subgroup Y).subgroupOf ⊤ := Sylow.coe_subtype T le_top
    rw [← hcoeeq]
    exact (T.subtype le_top).not_dvd_index
  have hXsyl := CFSG.isSylowTwoOf_inf_of_normal (S := (T : Subgroup Y))
    (X := (⊤ : Subgroup Y)) hTY le_top (Subgroup.normalizer_eq_top_iff.mpr hX).ge
  have h3 := hXsyl.2.2
  rw [hXT, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h3
  exact h3

private theorem eq_bot_of_compl_of_normal {Y : Type*} [Group Y] [Finite Y]
    (hgen : closure {y : Y | ∃ k : ℕ, orderOf y = 2 ^ k} = ⊤) (T : Sylow 2 Y)
    {X W : Subgroup Y} (hX : X.Normal) (hXW : X ⊓ W = ⊥) (hsup : X ⊔ W = ⊤)
    (hXT : X ⊓ (T : Subgroup Y) = ⊥) (hcomm : ∀ x ∈ X, ∀ w ∈ W, x * w = w * x) :
    X = ⊥ := by
  have hodd : ¬ 2 ∣ Nat.card X := not_two_dvd_card_of_inf_sylow_eq_bot T hX hXT
  have hmemW : ∀ y : Y, (∃ k : ℕ, orderOf y = 2 ^ k) → y ∈ W := by
    intro y hy
    obtain ⟨k, hk⟩ := hy
    have hy' : y ∈ (X ⊔ W : Subgroup Y) := by rw [hsup]; exact Subgroup.mem_top y
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hy'
    obtain ⟨x, hx, w, hw, rfl⟩ := Set.mem_mul.mp hy'
    have hcw : Commute x w := hcomm x hx w hw
    have h1 : (x * w) ^ (2 ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
    rw [hcw.mul_pow (2 ^ k)] at h1
    have hx2 : x ^ (2 ^ k) = 1 := by
      have hxW : x ^ (2 ^ k) ∈ W := by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact W.inv_mem (W.pow_mem hw _)
      have hxX : x ^ (2 ^ k) ∈ X := X.pow_mem hx _
      have hmem : x ^ (2 ^ k) ∈ X ⊓ W := ⟨hxX, hxW⟩
      rwa [hXW, Subgroup.mem_bot] at hmem
    have hdx : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hdc : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
    have hcop : Nat.Coprime (Nat.card X) (2 ^ k) :=
      Nat.prime_two.coprime_pow_of_not_dvd hodd
    have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdc hdx
    rw [orderOf_eq_one_iff.mp hone, one_mul]
    exact hw
  have hWtop : W = ⊤ := by
    rw [← top_le_iff, ← hgen]
    exact (Subgroup.closure_le W).mpr hmemW
  rw [hWtop, inf_top_eq] at hXW
  exact hXW

private theorem normal_inf_sylow_of_le_normalizer {Y : Type*} [Group Y]
    {B C : Subgroup Y} (T : Sylow 2 Y)
    (hCle : C ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hcom : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) (hsup : B ⊔ C = ⊤) :
    (C ⊓ (T : Subgroup Y)).Normal := by
  have hcommbot : ⁅B, C⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcom b hb c hc).symm
  have hnormB : B ≤ Subgroup.normalizer ((C ⊓ (T : Subgroup Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    calc ⁅B, C ⊓ (T : Subgroup Y)⁆ ≤ ⁅B, C⁆ := Subgroup.commutator_mono le_rfl inf_le_left
      _ = ⊥ := hcommbot
      _ ≤ C ⊓ (T : Subgroup Y) := bot_le
  have hnormC : C ≤ Subgroup.normalizer ((C ⊓ (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    (le_inf C.le_normalizer hCle).trans Subgroup.inf_normalizer_le_normalizer_inf
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hsup]
  exact sup_le hnormB hnormC

private theorem normal_inf_sylow_of_normal {Y : Type*} [Group Y]
    {B C : Subgroup Y} (T : Sylow 2 Y) (hB : B.Normal)
    (hcom : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hsup : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ⊔ C = ⊤) :
    (B ⊓ (T : Subgroup Y)).Normal := by
  have hNB : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (B : Set Y) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact Subgroup.commutator_le_right (Subgroup.normalizer ((T : Subgroup Y) : Set Y)) B
  have hnormN : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer ((B ⊓ (T : Subgroup Y) : Subgroup Y) : Set Y) :=
    (le_inf hNB le_rfl).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hnormC : C ≤ Subgroup.normalizer ((B ⊓ (T : Subgroup Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    have hcommbot : ⁅C, B⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcom b hb c hc
    calc ⁅C, B ⊓ (T : Subgroup Y)⁆ ≤ ⁅C, B⁆ := Subgroup.commutator_mono le_rfl inf_le_left
      _ = ⊥ := hcommbot
      _ ≤ B ⊓ (T : Subgroup Y) := bot_le
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hsup]
  exact sup_le hnormN hnormC

theorem isIndecomposableGroup_of_isCoatom_normalizer {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pCore 2 Y = ⊥) (hgen : closure {y : Y | ∃ k : ℕ, orderOf y = 2 ^ k} = ⊤)
    (T : Sylow 2 Y) (hT : IsCoatom (normalizer ((T : Subgroup Y) : Set Y))) :
    IsIndecomposableGroup Y := by
  have hnt : Nontrivial Y := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    refine hT.1 (top_le_iff.mp fun y _ => ?_)
    rw [Subsingleton.elim y 1]
    exact Subgroup.one_mem _
  refine And.intro hnt ?_
  intro B C hB hC hBC hsup
  have hcommbot : ⁅B, C⁆ = ⊥ := by
    have hle : ⁅B, C⁆ ≤ B ⊓ C := Subgroup.commutator_le_inf B C
    rw [hBC] at hle
    exact le_bot_iff.mp hle
  have hBcent : B ≤ Subgroup.centralizer (C : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
  have hBcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := by
    intro b hb c hc
    exact (Subgroup.mem_centralizer_iff.mp (hBcent hb) c hc).symm
  rcases (IsCoatom.le_iff hT).mp (le_sup_left : normalizer ((T : Subgroup Y) : Set Y) ≤
      normalizer ((T : Subgroup Y) : Set Y) ⊔ C) with htop | hN
  · have hBT : B ⊓ (T : Subgroup Y) = ⊥ :=
      inf_sylow_eq_bot_of_normal hO T (normal_inf_sylow_of_normal T hB hBcomm htop)
    exact Or.inl (eq_bot_of_compl_of_normal (X := B) (W := C) hgen T hB hBC hsup hBT hBcomm)
  · have hCle : C ≤ normalizer ((T : Subgroup Y) : Set Y) := hN ▸ le_sup_right
    have hCT : C ⊓ (T : Subgroup Y) = ⊥ :=
      inf_sylow_eq_bot_of_normal hO T (normal_inf_sylow_of_le_normalizer T hCle hBcomm hsup)
    have hcommCB : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c :=
      fun c hc b hb => (hBcomm b hb c hc).symm
    exact Or.inr (eq_bot_of_compl_of_normal (X := C) (W := B) hgen T hC
      ((inf_comm C B).trans hBC) ((sup_comm C B).trans hsup) hCT hcommCB)

theorem center_quotient_center_eq_bot_of_coprime {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hZ : Nat.Coprime (Nat.card (center Y)) p)
    (hgen : closure {y : Y | ∃ k : ℕ, orderOf y = p ^ k} = ⊤) : center (Y ⧸ center Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (N := center Y) x
  have hx₀' : (x₀ : Y ⧸ center Y) = x := by simpa [QuotientGroup.mk'_apply] using hx₀
  rw [← hx₀'] at hx ⊢
  rw [QuotientGroup.eq_one_iff]
  rw [Subgroup.mem_center_iff]
  intro y
  have hcent : ∀ t : Y, (∃ k : ℕ, orderOf t = p ^ k) → t * x₀ = x₀ * t := by
    intro t ht
    have hmem : ⁅t, x₀⁆ ∈ center Y := by
      have heq : ((t * x₀ : Y) : Y ⧸ center Y) = ((x₀ * t : Y) : Y ⧸ center Y) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact Subgroup.mem_center_iff.mp hx (t : Y ⧸ center Y)
      have h1 : (((t * x₀) * (x₀ * t)⁻¹ : Y) : Y ⧸ center Y) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
      have h2 : (t * x₀) * (x₀ * t)⁻¹ = ⁅t, x₀⁆ := by
        rw [commutatorElement_def]; group
      rw [h2] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := ht
    have hcomm : Commute t ⁅t, x₀⁆ := Subgroup.mem_center_iff.mp hmem t
    have hpk : ⁅t, x₀⁆ ^ (p ^ k) = 1 := by
      rw [hcomm.commutatorElement_pow_left (p ^ k), ← hk, pow_orderOf_eq_one,
        commutatorElement_one_left]
    have hdvd1 : orderOf ⁅t, x₀⁆ ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hpk
    have hdvd2 : orderOf ⁅t, x₀⁆ ∣ Nat.card (center Y) :=
      Subgroup.orderOf_dvd_natCard (center Y) hmem
    have hcop : Nat.Coprime (Nat.card (center Y)) (p ^ k) := hZ.pow_right k
    have hone : orderOf ⁅t, x₀⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
    exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp hone)
  have hcent' : Subgroup.centralizer ({x₀} : Set Y) = ⊤ := by
    rw [← top_le_iff, ← hgen]
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    simpa only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] using hcent t ht
  have hy : y ∈ Subgroup.centralizer ({x₀} : Set Y) := by rw [hcent']; exact Subgroup.mem_top y
  rwa [Subgroup.mem_centralizer_singleton_iff] at hy

end CFSG.GroupTheory
