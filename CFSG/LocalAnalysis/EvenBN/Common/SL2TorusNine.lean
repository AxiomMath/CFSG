module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive
public import CFSG.LocalAnalysis.EvenBN.Common.ProdFactors
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup CFSG.SL2MinimalFaithful
open scoped MatrixGroups

section Centralizer

variable {k : Type*} [Field k] [CharP k 2]

theorem centralizer_eq_upperSL_of_mem [Finite k] {u : SL(2, k)} (hu : u ∈ upperSL k)
    (hu1 : u ≠ 1) : centralizer ({u} : Set SL(2, k)) = upperSL k := by
  obtain ⟨β, rfl⟩ := mem_upperSL_iff.1 hu
  have hβ : β ≠ 0 := fun h => hu1 (by rw [h, unipotent_zero])
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext x
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_mkSL x
    have h00 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) hx
    have h01 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) hx
    simp [coe_mkSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    have hc : c = 0 := h00.resolve_left hβ
    have had : a = d := by
      have : (a - d) * β = 0 := by linear_combination h01
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hβ)
    have ha : a = 1 := by
      have : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2 + a * had + b * hc
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
    have hd : d = 1 := by rw [← had, ha]
    refine mem_upperSL_iff.2 ⟨b, eq_of_coe_eq ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_mkSL, coe_unipotent, ha, hc, hd]
  · intro hx
    obtain ⟨γ, rfl⟩ := mem_upperSL_iff.1 hx
    rw [← unipotent_add, ← unipotent_add, add_comm]

theorem centralizer_eq_of_mem_of_card [Finite k] {W : Subgroup SL(2, k)}
    (hW : Nat.card W = Nat.card k) {w : SL(2, k)} (hw : w ∈ W) (hw1 : w ≠ 1) :
    centralizer ({w} : Set SL(2, k)) = W := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two
    (by rw [Nat.card_eq_fintype_card, hn]) hW
  have hWeq : (upperSL k).map (MulAut.conj g).toMonoidHom = W := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      exact hg t.toAdd
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_upperSL, hW]
  rw [← hWeq] at hw ⊢
  obtain ⟨u, hu, rfl⟩ := hw
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hw1 (map_one _)
  rw [← centralizer_eq_upperSL_of_mem hu hu1, map_equiv_centralizer, Set.image_singleton]
  rfl

theorem centralizer_eq_of_mem_of_mulEquiv [Finite k] {X : Type*} [Group X] (ψ : X ≃* SL(2, k))
    {S : Subgroup X} (hS : Nat.card S = Nat.card k) {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) :
    centralizer ({s} : Set X) = S := by
  apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rw [map_equiv_centralizer, Set.image_singleton]
  exact centralizer_eq_of_mem_of_card (by rw [card_map_of_injective ψ.injective, hS])
    ⟨s, hs, rfl⟩ (by simpa using hs1)

theorem inf_centralizer_eq_of_mem_of_card [Finite k] {G : Type*} [Group G] {X S : Subgroup G}
    (ψ : X ≃* SL(2, k)) (hSX : S ≤ X) (hS : Nat.card S = Nat.card k) {s : G} (hs : s ∈ S)
    (hs1 : s ≠ 1) : X ⊓ centralizer ({s} : Set G) = S := by
  have hS' : Nat.card (S.subgroupOf X) = Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv, hS]
  have key := centralizer_eq_of_mem_of_mulEquiv ψ hS' (s := ⟨s, hSX hs⟩) hs
    (fun h => hs1 (congrArg Subtype.val h))
  ext x
  rw [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxX, hxs⟩
    have hx : (⟨x, hxX⟩ : X) ∈ centralizer ({⟨s, hSX hs⟩} : Set X) :=
      mem_centralizer_singleton_iff.2 (Subtype.ext hxs)
    rw [key] at hx
    exact hx
  · intro hx
    have hx' : (⟨x, hSX hx⟩ : X) ∈ centralizer ({⟨s, hSX hs⟩} : Set X) := by
      rw [key]
      exact hx
    exact ⟨hSX hx, congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx')⟩

theorem eq_of_mem_of_card [Finite k] {G : Type*} [Group G] {X S S' : Subgroup G}
    (ψ : X ≃* SL(2, k)) (hSX : S ≤ X) (hS'X : S' ≤ X) (hS : Nat.card S = Nat.card k)
    (hS' : Nat.card S' = Nat.card k) {s : G} (hs : s ∈ S) (hs' : s ∈ S') (hs1 : s ≠ 1) :
    S = S' :=
  (inf_centralizer_eq_of_mem_of_card ψ hSX hS hs hs1).symm.trans
    (inf_centralizer_eq_of_mem_of_card ψ hS'X hS' hs' hs1)

end Centralizer

section ProdFactor

variable {G : Type*} [Group G]

theorem map_conj_le_of_le_of_mem_normalizer {M H : Subgroup G} (hHM : H ≤ M) {g : G}
    (hg : g ∈ normalizer (M : Set G)) : H.map (MulAut.conj g).toMonoidHom ≤ M := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 hg x).1 (hHM hx)

theorem le_normalizer_map_conj_of_mem_normalizer {M H : Subgroup G}
    (hMH : M ≤ normalizer (H : Set G)) {g : G} (hg : g ∈ normalizer (M : Set G)) :
    M ≤ normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ y ∈ H.map (MulAut.conj g).toMonoidHom,
      m * y * m⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by
    rintro m hm _ ⟨x, hx, rfl⟩
    have hm' : g⁻¹ * m * g ∈ M := by
      have := (mem_normalizer_iff.1 (inv_mem hg) m).1 hm
      rwa [inv_inv] at this
    refine ⟨(g⁻¹ * m * g) * x * (g⁻¹ * m * g)⁻¹, (mem_normalizer_iff.1 (hMH hm') x).1 hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  intro m hm
  exact mem_normalizer_of_conj_mem (key m hm) (key m⁻¹ (inv_mem hm))

variable {M : Subgroup G} {S : Type*} [Group S] (ψ : M ≃* S × S)

theorem prodFactorOne_ne_bot [Nontrivial S] : prodFactorOne ψ ≠ ⊥ := by
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  intro h
  have h1 := symm_inl_mem_prodFactorOne ψ s
  rw [h, mem_bot] at h1
  have h2 : ψ.symm (s, 1) = 1 := Subtype.ext h1
  rw [MulEquiv.symm_apply_eq, map_one] at h2
  exact hs (congrArg Prod.fst h2)

theorem prodFactorTwo_ne_bot [Nontrivial S] : prodFactorTwo ψ ≠ ⊥ := by
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  intro h
  have h1 := symm_inr_mem_prodFactorTwo ψ s
  rw [h, mem_bot] at h1
  have h2 : ψ.symm (1, s) = 1 := Subtype.ext h1
  rw [MulEquiv.symm_apply_eq, map_one] at h2
  exact hs (congrArg Prod.snd h2)

theorem not_prodFactorTwo_le_prodFactorOne [Nontrivial S] :
    ¬ prodFactorTwo ψ ≤ prodFactorOne ψ := fun h =>
  prodFactorTwo_ne_bot ψ (by rw [← prodFactorOne_inf_prodFactorTwo ψ, inf_eq_right.2 h])

theorem not_prodFactorOne_le_prodFactorTwo [Nontrivial S] :
    ¬ prodFactorOne ψ ≤ prodFactorTwo ψ := fun h =>
  prodFactorOne_ne_bot ψ (by rw [← prodFactorOne_inf_prodFactorTwo ψ, inf_eq_left.2 h])

end ProdFactor

section ProdFactorSL

variable {k : Type*} [Field k] [CharP k 2] {G : Type*} [Group G]

theorem eq_prodFactor_of_le_normalizer (h4 : 4 ≤ Nat.card k) {M : Subgroup G}
    (ψ : M ≃* SL(2, k) × SL(2, k)) {H : Subgroup G} (hHM : H ≤ M)
    (hMH : M ≤ normalizer (H : Set G)) :
    H = ⊥ ∨ H = prodFactorOne ψ ∨ H = prodFactorTwo ψ ∨ H = M := by
  have hN : (H.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hHM).2 hMH
  have hmem : ∀ x : G, x ∈ H ↔ ∃ hx : x ∈ M, (⟨x, hx⟩ : M) ∈ H.subgroupOf M :=
    fun x => ⟨fun h => ⟨hHM h, h⟩, fun ⟨_, h⟩ => h⟩
  rcases normal_eq_of_mulEquiv_sl2_prod h4 ψ hN with h | h | h | h
  · left
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxM, hx'⟩ := (hmem x).1 hx
    rw [h, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')
  · right; left
    ext x
    rw [hmem, h, mem_prodFactorOne_iff]
    simp [mem_prod]
  · right; right; left
    ext x
    rw [hmem, h, mem_prodFactorTwo_iff]
    simp [mem_prod]
  · right; right; right
    exact le_antisymm hHM (subgroupOf_eq_top.1 h)

theorem conj_prodFactor_eq_or_swap [Finite k] (h4 : 4 ≤ Nat.card k) {M : Subgroup G}
    (ψ : M ≃* SL(2, k) × SL(2, k)) {g : G} (hg : g ∈ normalizer (M : Set G)) :
    ((prodFactorOne ψ).map (MulAut.conj g).toMonoidHom = prodFactorOne ψ ∧
      (prodFactorTwo ψ).map (MulAut.conj g).toMonoidHom = prodFactorTwo ψ) ∨
    ((prodFactorOne ψ).map (MulAut.conj g).toMonoidHom = prodFactorTwo ψ ∧
      (prodFactorTwo ψ).map (MulAut.conj g).toMonoidHom = prodFactorOne ψ) := by
  have := (sl2_isSimpleGroup_of_charTwo h4).toNontrivial
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcase : ∀ {H H' : Subgroup G}, (H = prodFactorOne ψ ∧ H' = prodFactorTwo ψ) ∨
      (H = prodFactorTwo ψ ∧ H' = prodFactorOne ψ) →
      H.map (MulAut.conj g).toMonoidHom = prodFactorOne ψ ∨
        H.map (MulAut.conj g).toMonoidHom = prodFactorTwo ψ := by
    intro H H' hHH'
    have hHM : H ≤ M := by
      rcases hHH' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact prodFactorOne_le ψ
      · exact prodFactorTwo_le ψ
    have hH'M : H' ≤ M := by
      rcases hHH' with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact prodFactorTwo_le ψ
      · exact prodFactorOne_le ψ
    have hMH : M ≤ normalizer (H : Set G) := by
      rcases hHH' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact le_normalizer_prodFactorOne ψ
      · exact le_normalizer_prodFactorTwo ψ
    have hne : H ≠ ⊥ := by
      rcases hHH' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact prodFactorOne_ne_bot ψ
      · exact prodFactorTwo_ne_bot ψ
    have hnle : ¬ H' ≤ H := by
      rcases hHH' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact not_prodFactorTwo_le_prodFactorOne ψ
      · exact not_prodFactorOne_le_prodFactorTwo ψ
    rcases eq_prodFactor_of_le_normalizer h4 ψ (map_conj_le_of_le_of_mem_normalizer hHM hg)
      (le_normalizer_map_conj_of_mem_normalizer hMH hg) with h | h | h | h
    · exact absurd ((map_eq_bot_iff_of_injective _ hinj).1 h) hne
    · exact Or.inl h
    · exact Or.inr h
    · refine absurd ?_ hnle
      have h' := map_conj_le_of_le_of_mem_normalizer hH'M hg
      rw [← h] at h'
      exact (map_le_map_iff_of_injective hinj).1 h'
  have hne : prodFactorOne ψ ≠ prodFactorTwo ψ := fun h =>
    not_prodFactorTwo_le_prodFactorOne ψ h.ge
  rcases hcase (Or.inl ⟨rfl, rfl⟩) with h1 | h1 <;>
    rcases hcase (Or.inr ⟨rfl, rfl⟩) with h2 | h2
  · exact absurd (map_injective hinj (h1.trans h2.symm)) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (map_injective hinj (h1.trans h2.symm)) hne

end ProdFactorSL

end CFSG.LocalAnalysis.EvenBN.Common
