module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)

section Gen

variable {F : Type} [Field F] {n : ℕ}

theorem single_apply_eq_zero_of_mem_planeCoords {N : Finset (Fin n)} {a' b' a b : Fin n ⊕ Fin n}
    (ha' : a' ∈ planeCoords N) (hb' : b' ∈ planeCoords N)
    (hab : ¬(a ∈ planeCoords N ∧ b ∈ planeCoords N)) :
    (Matrix.single a' b' (1 : F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b = 0 := by
  rw [Matrix.single_apply]
  split_ifs with h
  · exact absurd ⟨h.1 ▸ ha', h.2 ▸ hb'⟩ hab
  · rfl

theorem elt_difference_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ N)
    (hj : j ∈ N) (c : F) : elt (.difference i j hij) c ∈ spBlock F N := by
  intro a b hab
  have hi' : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj' : (Sum.inl j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  have hi'' : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj'' : (Sum.inr j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  rw [mat_elt]
  simp only [E, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    single_apply_eq_zero_of_mem_planeCoords hi' hj' hab,
    single_apply_eq_zero_of_mem_planeCoords hj'' hi'' hab, sub_zero, smul_zero, add_zero]

theorem elt_positiveLong_mem_spBlock {N : Finset (Fin n)} {i : Fin n} (hi : i ∈ N) (c : F) :
    elt (.positiveLong i) c ∈ spBlock F N := by
  intro a b hab
  have hi' : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hi'' : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  rw [mat_elt]
  simp only [E, Matrix.add_apply, Matrix.smul_apply,
    single_apply_eq_zero_of_mem_planeCoords hi' hi'' hab, smul_zero, add_zero]

theorem elt_negativeLong_mem_spBlock {N : Finset (Fin n)} {i : Fin n} (hi : i ∈ N) (c : F) :
    elt (.negativeLong i) c ∈ spBlock F N := by
  intro a b hab
  have hi' : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hi'' : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  rw [mat_elt]
  simp only [E, Matrix.add_apply, Matrix.smul_apply,
    single_apply_eq_zero_of_mem_planeCoords hi'' hi' hab, smul_zero, add_zero]

theorem spEmbed_elt_positiveLong {m : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (a : Fin m) (c : F) :
    spEmbed σ hσ (elt (.positiveLong a) c) = elt (.positiveLong (σ a)) c := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_elt, mat_elt]
  have e : (1 + c • E F (.positiveLong a) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) - 1 =
      c • E F (.positiveLong a) := add_sub_cancel_left _ _
  rw [spEmbedMat, e]
  simp only [E, Matrix.mul_smul, Matrix.smul_mul, spIncl_mul_single_mul_transpose, Sum.map_inl,
    Sum.map_inr]

theorem spEmbed_elt_negativeLong {m : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (a : Fin m) (c : F) :
    spEmbed σ hσ (elt (.negativeLong a) c) = elt (.negativeLong (σ a)) c := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_elt, mat_elt]
  have e : (1 + c • E F (.negativeLong a) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) - 1 =
      c • E F (.negativeLong a) := add_sub_cancel_left _ _
  rw [spEmbedMat, e]
  simp only [E, Matrix.mul_smul, Matrix.smul_mul, spIncl_mul_single_mul_transpose, Sum.map_inl,
    Sum.map_inr]

theorem eq_top_of_adjacent_of_long_statedSp (H : Subgroup (StatedSp n F)) (r : Fin n)
    (hadj : ∀ (i j : Fin n) (hij : i ≠ j) (c : F), i.val + 1 = j.val ∨ j.val + 1 = i.val →
      elt (.difference i j hij) c ∈ H)
    (hpos : ∀ c : F, elt (.positiveLong r) c ∈ H)
    (hneg : ∀ c : F, elt (.negativeLong r) c ∈ H) : H = ⊤ := by
  have htop : H.comap (equivStatedSp n F).toMonoidHom = ⊤ := by
    refine TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long _ r ?_ ?_ ?_
    · intro i j hij c hadj'
      have key : equivStatedSp n F (TauCeti.GLSymplecticFin.differenceShortRootUnit hij c) =
          elt (.difference i j hij) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_difference,
          TauCeti.GLSymplecticFin.differenceShortRootHom_apply, toAdd_ofAdd]
      change equivStatedSp n F _ ∈ H
      rw [key]
      exact hadj i j hij c hadj'
    · intro c
      have key : equivStatedSp n F
          (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit r c) =
            elt (.positiveLong r) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
          TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp n F _ ∈ H
      rw [key]
      exact hpos c
    · intro c
      have key : equivStatedSp n F
          (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit r c) =
            elt (.negativeLong r) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
          TauCeti.GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp n F _ ∈ H
      rw [key]
      exact hneg c
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp n F).surjective x
  have hy : y ∈ H.comap (equivStatedSp n F).toMonoidHom := by
    rw [htop]
    exact mem_top y
  exact hy

theorem exists_ne_ne_of_three_le (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  classical
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset (Fin n)), k ∉ ({i, j} : Finset (Fin n)) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      have h := Finset.card_insert_le i ({j} : Finset (Fin n))
      rw [Finset.card_singleton] at h
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩

theorem mem_compl_singleton_iff' {p k : Fin n} : p ∈ ({k}ᶜ : Finset (Fin n)) ↔ p ≠ k := by
  simp

theorem mem_compl_pair_iff' {p k l : Fin n} :
    p ∈ ({k, l}ᶜ : Finset (Fin n)) ↔ p ≠ k ∧ p ≠ l := by
  simp

theorem iSup_spBlock_compl_singleton_eq_top (hn : 3 ≤ n) :
    ⨆ k : Fin n, spBlock F ({k}ᶜ : Finset (Fin n)) = ⊤ := by
  refine eq_top_of_adjacent_of_long_statedSp _ ⟨0, by omega⟩ (fun i j hij c _ => ?_)
    (fun c => ?_) (fun c => ?_)
  · obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hn i j
    exact mem_iSup_of_mem k (elt_difference_mem_spBlock hij
      (mem_compl_singleton_iff'.2 (Ne.symm hki)) (mem_compl_singleton_iff'.2 (Ne.symm hkj)) c)
  · refine mem_iSup_of_mem ⟨1, by omega⟩ (elt_positiveLong_mem_spBlock
      (mem_compl_singleton_iff'.2 fun h => ?_) c)
    have := congrArg Fin.val h
    simp at this
  · refine mem_iSup_of_mem ⟨1, by omega⟩ (elt_negativeLong_mem_spBlock
      (mem_compl_singleton_iff'.2 fun h => ?_) c)
    have := congrArg Fin.val h
    simp at this

theorem exists_perm_first_last {m : ℕ} (hm : 3 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    ∃ π : Equiv.Perm (Fin m), π ⟨0, by omega⟩ = a ∧ π ⟨m - 1, by omega⟩ = b := by
  set z : Fin m := ⟨0, by omega⟩ with hz
  set w : Fin m := ⟨m - 1, by omega⟩ with hw
  have hzw : z ≠ w := fun h => by
    have := congrArg Fin.val h
    simp only [hz, hw] at this
    omega
  set b' := Equiv.swap z a b with hb'def
  have hb' : b' ≠ z := by
    intro h
    have h2 := congrArg (Equiv.swap z a) h
    rw [hb'def, Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact hab h2.symm
  refine ⟨Equiv.swap z a * Equiv.swap w b', ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzw (Ne.symm hb'),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hb'def, Equiv.swap_apply_self]

theorem spBlock_compl_singleton_le_sup (hn : 4 ≤ n) {k l m : Fin n} (hkl : k ≠ l) (hkm : k ≠ m)
    (hlm : l ≠ m) :
    spBlock F ({k}ᶜ : Finset (Fin n)) ≤
      spBlock F ({k, l}ᶜ : Finset (Fin n)) ⊔ spBlock F ({k, m}ᶜ : Finset (Fin n)) := by
  classical
  set N : Finset (Fin n) := {k}ᶜ with hN
  have hcard : N.card = n - 1 := by
    rw [hN, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hN3 : 3 ≤ N.card := by omega
  have hrange := range_planeEnum N
  obtain ⟨a, ha⟩ : ∃ a, planeEnum N a = l := by
    have : l ∈ Set.range (planeEnum N) := by
      rw [hrange]
      exact mem_compl_singleton_iff'.2 (Ne.symm hkl)
    exact this
  obtain ⟨b, hb⟩ : ∃ b, planeEnum N b = m := by
    have : m ∈ Set.range (planeEnum N) := by
      rw [hrange]
      exact mem_compl_singleton_iff'.2 (Ne.symm hkm)
    exact this
  have hab : a ≠ b := fun h => hlm (by rw [← ha, ← hb, h])
  obtain ⟨π, hπ0, hπl⟩ := exists_perm_first_last hN3 hab
  set σ : Fin N.card → Fin n := planeEnum N ∘ π with hσ
  have hσinj : Function.Injective σ := (planeEnum_injective N).comp π.injective
  have hσrange : Set.range σ = N := by
    rw [hσ, Set.range_comp, π.range_eq_univ, Set.image_univ, hrange]
  have hσN : ∀ x, σ x ≠ k := fun x h => by
    have hx : σ x ∈ (N : Set (Fin n)) := hσrange ▸ Set.mem_range_self x
    exact mem_compl_singleton_iff'.1 hx h
  have hσz : σ ⟨0, by omega⟩ = l := by simp only [hσ, Function.comp_apply, hπ0, ha]
  have hσw : σ ⟨N.card - 1, by omega⟩ = m := by simp only [hσ, Function.comp_apply, hπl, hb]
  have hblock : spBlock F N = (spEmbed (K := F) σ hσinj).range := by
    rw [range_spEmbed, range_sumMap_eq_planeCoords hσrange, spBlock]
  rw [hblock]
  rintro _ ⟨g, rfl⟩
  set H := spBlock F ({k, l}ᶜ : Finset (Fin n)) ⊔ spBlock F ({k, m}ᶜ : Finset (Fin n)) with hH
  have htop : H.comap (spEmbed (K := F) σ hσinj) = ⊤ := by
    refine eq_top_of_adjacent_of_long_statedSp _ ⟨0, by omega⟩ (fun i j hij c hadj => ?_)
      (fun c => ?_) (fun c => ?_)
    · rw [mem_comap, spEmbed_elt_difference]
      by_cases hz : i.val = 0 ∨ j.val = 0
      ·
        have hiw : σ i ≠ m := fun h => by
          have := congrArg Fin.val (hσinj (h.trans hσw.symm))
          simp only at this
          omega
        have hjw : σ j ≠ m := fun h => by
          have := congrArg Fin.val (hσinj (h.trans hσw.symm))
          simp only at this
          omega
        exact mem_sup_right (elt_difference_mem_spBlock _ (mem_compl_pair_iff'.2 ⟨hσN i, hiw⟩)
          (mem_compl_pair_iff'.2 ⟨hσN j, hjw⟩) c)
      · have hiz : σ i ≠ l := fun h => by
          have := congrArg Fin.val (hσinj (h.trans hσz.symm))
          simp only at this
          omega
        have hjz : σ j ≠ l := fun h => by
          have := congrArg Fin.val (hσinj (h.trans hσz.symm))
          simp only at this
          omega
        exact mem_sup_left (elt_difference_mem_spBlock _ (mem_compl_pair_iff'.2 ⟨hσN i, hiz⟩)
          (mem_compl_pair_iff'.2 ⟨hσN j, hjz⟩) c)
    · rw [mem_comap, spEmbed_elt_positiveLong, hσz]
      exact mem_sup_right (elt_positiveLong_mem_spBlock (mem_compl_pair_iff'.2 ⟨Ne.symm hkl, hlm⟩) c)
    · rw [mem_comap, spEmbed_elt_negativeLong, hσz]
      exact mem_sup_right (elt_negativeLong_mem_spBlock (mem_compl_pair_iff'.2 ⟨Ne.symm hkl, hlm⟩) c)
  have hg : g ∈ H.comap (spEmbed (K := F) σ hσinj) := by
    rw [htop]
    exact mem_top g
  exact hg

end Gen

end CFSG.SeitzReduction.SymplecticPilot
