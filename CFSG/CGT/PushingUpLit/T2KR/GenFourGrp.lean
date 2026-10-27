module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]


theorem relIndex_pos_of_finite [Finite G] (A C : Subgroup G) : 0 < A.relIndex C :=
  Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card A C) Nat.card_pos

theorem exists_finset_closure_sup_eq_of_relIndex_le [Finite G] {Z : Subgroup G} :
    ∀ (j : ℕ) (Y : Subgroup G), Y ≤ Z → Y.relIndex Z ≤ 2 ^ j →
      ∃ t : Finset G, t.card ≤ j ∧ (↑t : Set G) ⊆ (Z : Set G) ∧
        Subgroup.closure (t : Set G) ⊔ Y = Z := by
  classical
  intro j
  induction j with
  | zero =>
    intro Y hYZ hrel
    have hpos := relIndex_pos_of_finite Y Z
    have h1 : Y.relIndex Z = 1 := by simp at hrel; omega
    have hZY : Z ≤ Y := Subgroup.relIndex_eq_one.1 h1
    refine ⟨∅, by simp, by simp, ?_⟩
    simp [le_antisymm hYZ hZY]
  | succ j ih =>
    intro Y hYZ hrel
    by_cases hZY : Z ≤ Y
    · refine ⟨∅, by simp, by simp, ?_⟩
      simp [le_antisymm hYZ hZY]
    · obtain ⟨x, hxZ, hxY⟩ := Set.not_subset.1 hZY
      set Y' : Subgroup G := Y ⊔ Subgroup.zpowers x with hY'
      have hYY' : Y ≤ Y' := le_sup_left
      have hxY' : x ∈ Y' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      have hY'Z : Y' ≤ Z := sup_le hYZ ((Subgroup.zpowers_le).2 hxZ)
      have hmul : Y.relIndex Y' * Y'.relIndex Z = Y.relIndex Z :=
        Subgroup.relIndex_mul_relIndex Y Y' Z hYY' hY'Z
      have hne : Y.relIndex Y' ≠ 1 := fun h =>
        hxY ((Subgroup.relIndex_eq_one.1 h) hxY')
      have hpos := relIndex_pos_of_finite Y Y'
      have h2 : 2 ≤ Y.relIndex Y' := by omega
      have hle : Y'.relIndex Z ≤ 2 ^ j := by
        have h3 : Y.relIndex Y' * Y'.relIndex Z ≤ 2 ^ (j + 1) := hmul ▸ hrel
        rw [pow_succ] at h3
        nlinarith
      obtain ⟨t', ht'c, ht'Z, ht'⟩ := ih Y' hY'Z hle
      have hins : ((insert x t' : Finset G) : Set G) ⊆ (Z : Set G) := by
        intro y hy
        rw [Finset.coe_insert] at hy
        rcases hy with rfl | hy
        · exact hxZ
        · exact ht'Z hy
      refine ⟨insert x t', ?_, hins, ?_⟩
      · calc (insert x t').card ≤ t'.card + 1 := Finset.card_insert_le _ _
          _ ≤ j + 1 := by omega
      · apply le_antisymm
        · exact sup_le ((Subgroup.closure_le Z).2 hins) hYZ
        · rw [← ht']
          have hx : Subgroup.zpowers x ≤ Subgroup.closure ((insert x t' : Finset G) : Set G) :=
            (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
          have ht'c : Subgroup.closure (t' : Set G) ≤
              Subgroup.closure ((insert x t' : Finset G) : Set G) :=
            Subgroup.closure_mono (by intro y hy; rw [Finset.coe_insert]; exact Or.inr hy)
          calc Subgroup.closure (t' : Set G) ⊔ (Y ⊔ Subgroup.zpowers x)
              ≤ Subgroup.closure ((insert x t' : Finset G) : Set G) ⊔ Y := by
                refine sup_le (le_trans ht'c le_sup_left)
                  (sup_le le_sup_right (le_trans hx le_sup_left))
            _ = _ := rfl

theorem exists_le_proper_commutator [Finite G] {S Y : Subgroup G} (hS : IsPGroup 2 S)
    (hYS : Y ≤ S) (hne : Y ≠ S) :
    ∃ K : Subgroup G, Y ≤ K ∧ K ≤ S ∧ K ≠ S ∧ ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  set Y' : Subgroup S := Y.subgroupOf S with hY'
  have hY'ne : Y' ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hYS fun x hx => ?_
    have : (⟨x, hx⟩ : S) ∈ Y' := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨K', hK'coatom, hYK'⟩ := (eq_top_or_exists_le_coatom Y').resolve_left hY'ne
  have hidx : K'.index = 2 := (hS.isCoatom_iff_index_eq_prime).1 hK'coatom
  have hK'n : K'.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcomm : ∀ x y : S, ⁅x, y⁆ ∈ K' := by
    intro x y
    by_cases hx : x ∈ K'
    · have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact K'.mul_mem hx (hK'n.conj_mem _ (K'.inv_mem hx) y)
    · by_cases hy : y ∈ K'
      · have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact K'.mul_mem (hK'n.conj_mem _ hy x) (K'.inv_mem hy)
      · have hxy : x * y ∈ K' := (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hx hy)
        have hyx : y * x ∈ K' := (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hy hx)
        have e : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by simp only [commutatorElement_def]; group
        rw [e]
        exact K'.mul_mem hxy (K'.inv_mem hyx)
  refine ⟨K'.map S.subtype, ?_, Subgroup.map_subtype_le K', ?_, ?_⟩
  · intro y hy
    exact ⟨⟨y, hYS hy⟩, hYK' (show (⟨y, hYS hy⟩ : S) ∈ Y' from hy), rfl⟩
  · intro h
    apply hK'coatom.1
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ K'.map S.subtype := by rw [h]; exact x.2
    obtain ⟨k, hk, hkx⟩ := hx
    have : k = x := Subtype.ext hkx
    exact this ▸ hk
  · intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : S), ⟨y, hy⟩⁆, hcomm _ _, rfl⟩

theorem closure_union_eq [Finite G] {S W : Subgroup G} (hS : IsPGroup 2 S) (hWS : W ≤ S)
    {s w : Finset G} (hsS : (↑s : Set G) ⊆ (S : Set G)) (hwS : (↑w : Set G) ⊆ (S : Set G))
    (hSs : S ≤ Subgroup.closure (s : Set G) ⊔ W)
    (hWw : W ≤ Subgroup.closure (w : Set G) ⊔ ⁅W, S⁆) :
    Subgroup.closure ((s : Set G) ∪ (w : Set G)) = S := by
  set Y := Subgroup.closure ((s : Set G) ∪ (w : Set G)) with hY
  have hYS : Y ≤ S := (Subgroup.closure_le S).2 (Set.union_subset hsS hwS)
  by_contra hne
  obtain ⟨K, hYK, hKS, hKne, hcomm⟩ := exists_le_proper_commutator hS hYS hne
  have hsK : Subgroup.closure (s : Set G) ≤ K :=
    le_trans (Subgroup.closure_mono Set.subset_union_left) hYK
  have hwK : Subgroup.closure (w : Set G) ≤ K :=
    le_trans (Subgroup.closure_mono Set.subset_union_right) hYK
  have hWSK : ⁅W, S⁆ ≤ K := (Subgroup.commutator_le).2 fun x hx y hy => hcomm x (hWS hx) y hy
  have hWK : W ≤ K := hWw.trans (sup_le hwK hWSK)
  have hSK : S ≤ K := hSs.trans (sup_le hsK hWK)
  exact hKne (le_antisymm hKS hSK)

theorem exists_two_generators_mod_commutator [Finite G] {S W : Subgroup G}
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWn : ∀ x ∈ S, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    {s : G} (hsS : s ∈ S) (hfix : Nat.card {w : G // w ∈ W ∧ s * w = w * s} ≤ 4) :
    ∃ w : Finset G, w.card ≤ 2 ∧ (↑w : Set G) ⊆ (W : Set G) ∧
      W ≤ Subgroup.closure (w : Set G) ⊔ ⁅W, S⁆ := by
  classical
  let _ : CommGroup W := { (inferInstance : Group ↥W) with
    mul_comm := fun a b => Subtype.ext (hWc _ a.2 _ b.2) }
  let c : ↥W →* ↥W :=
    { toFun := fun a => ⟨s * (a : G) * s⁻¹, hWn s hsS a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  let δ : ↥W →* ↥W := MonoidHom.mk' (fun a => a * (c a)⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hδ : ∀ a : ↥W, ((δ a : ↥W) : G) = ⁅(a : G), s⁆ := by
    intro a
    show (a : G) * (s * (a : G) * s⁻¹)⁻¹ = _
    simp only [commutatorElement_def]
    group
  have hker : ∀ a : ↥W, a ∈ δ.ker ↔ s * (a : G) = (a : G) * s := by
    intro a
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hδ, Subgroup.coe_one,
      commutatorElement_eq_one_iff_mul_comm]
    exact eq_comm
  have hkerc : Nat.card ↥δ.ker = Nat.card {w : G // w ∈ W ∧ s * w = w * s} := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), a.1.2, (hker a.1).1 a.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, (hker ⟨w.1, w.2.1⟩).2 w.2.2⟩
        left_inv := fun a => rfl
        right_inv := fun w => rfl }
  have hidx : δ.range.index = Nat.card ↥δ.ker := by
    have h1 : δ.ker.index = Nat.card δ.range := Subgroup.index_ker δ
    have h2 := Subgroup.card_mul_index δ.ker
    have h3 := Subgroup.card_mul_index δ.range
    rw [h1] at h2
    have hpos : 0 < Nat.card δ.range := Nat.card_pos
    have : Nat.card δ.range * δ.range.index = Nat.card δ.range * Nat.card δ.ker := by
      rw [h3, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  set I : Subgroup G := δ.range.map W.subtype with hI
  have hIW : I ≤ W := Subgroup.map_subtype_le _
  have hIrel : I.relIndex W ≤ 2 ^ 2 := by
    have : I.relIndex W = δ.range.index := by
      show ((δ.range.map W.subtype).comap W.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    rw [this, hidx, hkerc]
    exact hfix
  obtain ⟨w, hwc, hwW, hw⟩ := exists_finset_closure_sup_eq_of_relIndex_le 2 I hIW hIrel
  refine ⟨w, hwc, hwW, ?_⟩
  have hIc : I ≤ ⁅W, S⁆ := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    show ((δ a : ↥W) : G) ∈ ⁅W, S⁆
    rw [hδ]
    exact Subgroup.commutator_mem_commutator a.2 hsS
  calc W = Subgroup.closure (w : Set G) ⊔ I := hw.symm
    _ ≤ Subgroup.closure (w : Set G) ⊔ ⁅W, S⁆ := sup_le_sup_left hIc _

theorem closure_pair_sup_ker {A K : Type*} [Group A] [Group K] [Finite K] (f : A →* K)
    (hcard : Nat.card f.range ≤ 4) {n m : A} (hn : f n ≠ 1) (hm : f m ≠ 1) (hnm : f n ≠ f m) :
    Subgroup.closure ({n, m} : Set A) ⊔ f.ker = ⊤ := by
  classical
  set C : Subgroup K := Subgroup.closure ({f n, f m} : Set K) with hC
  have hmem1 : f n ∈ C := Subgroup.subset_closure (by simp)
  have hmem2 : f m ∈ C := Subgroup.subset_closure (by simp)
  have hCR : C ≤ f.range := (Subgroup.closure_le _).2 (by
    rintro _ (rfl | rfl)
    exacts [⟨n, rfl⟩, ⟨m, rfl⟩])
  have h3 : 3 ≤ Nat.card C := by
    let g : Fin 3 → C := ![1, ⟨f n, hmem1⟩, ⟨f m, hmem2⟩]
    have hg : Function.Injective g := by
      intro i j hij
      have h1n : (1 : K) ≠ f n := fun h => hn h.symm
      have h1m : (1 : K) ≠ f m := fun h => hm h.symm
      have hmn : f m ≠ f n := fun h => hnm h.symm
      fin_cases i <;> fin_cases j <;> simp_all [g, Subtype.ext_iff]
    simpa using Nat.card_le_card_of_injective g hg
  have hdvd : Nat.card C ∣ Nat.card f.range := Subgroup.card_dvd_of_le hCR
  have hCeq : C = f.range := by
    refine Subgroup.eq_of_le_of_card_ge hCR ?_
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    obtain ⟨k, hk⟩ := hdvd
    have : k = 1 := by
      rcases k with _ | _ | k
      · omega
      · rfl
      · nlinarith
    subst this
    omega
  rw [eq_top_iff]
  intro a _
  have hfa : f a ∈ C := hCeq ▸ ⟨a, rfl⟩
  have hmap : C = (Subgroup.closure ({n, m} : Set A)).map f := by
    rw [hC, MonoidHom.map_closure, Set.image_pair]
  rw [hmap] at hfa
  obtain ⟨z, hz, hza⟩ := hfa
  have hker : z⁻¹ * a ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hza, inv_mul_cancel]
  have : a = z * (z⁻¹ * a) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hz hker

theorem le_closure_pair_sup_map_ker {N : Subgroup G} {K : Type*} [Group K] [Finite K]
    (f : ↥N →* K) (hcard : Nat.card f.range ≤ 4) {n m : G} (hn : n ∈ N) (hm : m ∈ N)
    (hn1 : f ⟨n, hn⟩ ≠ 1) (hm1 : f ⟨m, hm⟩ ≠ 1) (hnm : f ⟨n, hn⟩ ≠ f ⟨m, hm⟩) :
    N ≤ Subgroup.closure ({n, m} : Set G) ⊔ f.ker.map N.subtype := by
  have h := closure_pair_sup_ker f hcard hn1 hm1 hnm
  intro y hy
  have h1 : (⟨y, hy⟩ : N) ∈ Subgroup.closure ({⟨n, hn⟩, ⟨m, hm⟩} : Set N) ⊔ f.ker :=
    h ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem N.subtype h1
  rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair] at h2
  exact h2

theorem inv_mul_mem_of_relIndex_two {S N : Subgroup G} (hN : N.relIndex S = 2) {a b : G}
    (haS : a ∈ S) (hbS : b ∈ S) (haN : a ∉ N) (hbN : b ∉ N) : a⁻¹ * b ∈ N := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := N.subgroupOf S) hN
    (a := (⟨a, haS⟩ : S)⁻¹) (b := ⟨b, hbS⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haN hbN)
  exact Subgroup.mem_subgroupOf.1 key

end CFSG.CGT.PushingUpLit.T2KR
