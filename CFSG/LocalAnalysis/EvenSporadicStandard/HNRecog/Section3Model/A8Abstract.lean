module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

private noncomputable def botProdTopEquiv (A : Type*) [Group A] :
    (⊥ : Subgroup (Elem2 2)).prod (⊤ : Subgroup A) ≃* A where
  toFun x := (x : Elem2 2 × A).2
  invFun a := ⟨(1, a), by simp [Subgroup.mem_prod]⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp x.2).1).symm rfl
  right_inv a := rfl
  map_mul' x y := rfl

theorem nonempty_mulEquiv_A8_derivedOf {H : Type} [Group H] {b : H}
    (h : IsShapeTwoTwoTimesA8 ↥(Gx b)) :
    Nonempty (alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gx b))) := by
  obtain ⟨e⟩ := h
  have hmap1 : (commutator ↥(Gx b)).map e.toMonoidHom =
      commutator (Elem2 2 × alternatingGroup (Fin 8)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hcomm_eq : commutator (Elem2 2 × alternatingGroup (Fin 8)) =
      (⊥ : Subgroup (Elem2 2)).prod (⊤ : Subgroup (alternatingGroup (Fin 8))) := by
    have h2 : (⁅(⊤ : Subgroup (Elem2 2)), ⊤⁆ : Subgroup (Elem2 2)) = ⊥ :=
      commutator_eq_bot (Elem2 2)
    have h3 : (⁅(⊤ : Subgroup (alternatingGroup (Fin 8))), ⊤⁆ :
        Subgroup (alternatingGroup (Fin 8))) = ⊤ :=
      commutator_alternatingGroup_eq_top (α := Fin 8) (by simp)
    rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, h2, h3]
  let f1 : alternatingGroup (Fin 8) ≃*
      ↥(commutator (Elem2 2 × alternatingGroup (Fin 8))) :=
    ((MulEquiv.subgroupCongr hcomm_eq).trans
      (botProdTopEquiv (alternatingGroup (Fin 8)))).symm
  let f2 : ↥(commutator (Elem2 2 × alternatingGroup (Fin 8))) ≃*
      ↥(commutator ↥(Gx b)) :=
    ((Subgroup.equivMapOfInjective (commutator ↥(Gx b)) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap1)).symm
  let f3 : ↥(commutator ↥(Gx b)) ≃* ↥(derivedOf (Gx b)) :=
    Subgroup.equivMapOfInjective (commutator ↥(Gx b)) (Gx b).subtype (Gx b).subtype_injective
  exact ⟨f1.trans (f2.trans f3)⟩

theorem exists_cycleType_two_four :
    ∃ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · show (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7 :
        Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}
    have hre : (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7 :
        Equiv.Perm (Fin 8)) =
        (Equiv.swap 0 1 * Equiv.swap 2 3) * (Equiv.swap 4 5 * Equiv.swap 6 7) := by
      group
    have hdisj : Equiv.Perm.Disjoint
        (Equiv.swap (0 : Fin 8) 1 * Equiv.swap (2 : Fin 8) 3)
        (Equiv.swap (4 : Fin 8) 5 * Equiv.swap (6 : Fin 8) 7) := by
      apply Equiv.Perm.Disjoint.mul_left
      · apply Equiv.Perm.Disjoint.mul_right
        · exact Equiv.Perm.disjoint_swap_swap (by decide : ([0, 1, 4, 5] : List (Fin 8)).Nodup)
        · exact Equiv.Perm.disjoint_swap_swap (by decide : ([0, 1, 6, 7] : List (Fin 8)).Nodup)
      · apply Equiv.Perm.Disjoint.mul_right
        · exact Equiv.Perm.disjoint_swap_swap (by decide : ([2, 3, 4, 5] : List (Fin 8)).Nodup)
        · exact Equiv.Perm.disjoint_swap_swap (by decide : ([2, 3, 6, 7] : List (Fin 8)).Nodup)
    rw [hre, Equiv.Perm.Disjoint.cycleType_mul hdisj,
      Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide : ([0, 1, 2, 3] : List (Fin 8)).Nodup),
      Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide : ([4, 5, 6, 7] : List (Fin 8)).Nodup)]
    rfl

private theorem card_centralizer_A8_of_ncard {t : alternatingGroup (Fin 8)} {k c : ℕ}
    (hk : (conjugatesOf t).ncard = k) (hkc : k * c = 20160) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 8)))) = c := by
  have hidx : (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 8)))).index = k := by
    rw [Subgroup.index_centralizer_eq_ncard, hk]
  have hmul := Subgroup.card_mul_index
    (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 8))))
  rw [hidx] at hmul
  have hA8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [hA8] at hmul
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkc
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hk0 (hmul.trans (hkc.symm.trans (Nat.mul_comm k c)))

private theorem conjugatesOf_A8_two_four {t : alternatingGroup (Fin 8)}
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) :
    (conjugatesOf t : Set (alternatingGroup (Fin 8))) =
      {s : alternatingGroup (Fin 8) | (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}} := by
  ext s
  constructor
  · intro hs
    change IsConj t s at hs
    rw [isConj_iff] at hs
    obtain ⟨c, hc⟩ := hs
    have hperm : IsConj (t : Equiv.Perm (Fin 8)) (s : Equiv.Perm (Fin 8)) := by
      rw [isConj_iff]
      exact ⟨(c : Equiv.Perm (Fin 8)), by simpa using congrArg Subtype.val hc⟩
    exact (Equiv.Perm.isConj_iff_cycleType_eq.mp hperm).symm.trans ht
  · intro hs
    change IsConj t s
    exact isConj_of_cycleType_two_two_two_two ht hs

private theorem conjugatesOf_A8_two_two {t : alternatingGroup (Fin 8)}
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2}) :
    (conjugatesOf t : Set (alternatingGroup (Fin 8))) =
      {s : alternatingGroup (Fin 8) | (s : Equiv.Perm (Fin 8)).cycleType = {2, 2}} := by
  ext s
  constructor
  · intro hs
    change IsConj t s at hs
    rw [isConj_iff] at hs
    obtain ⟨c, hc⟩ := hs
    have hperm : IsConj (t : Equiv.Perm (Fin 8)) (s : Equiv.Perm (Fin 8)) := by
      rw [isConj_iff]
      exact ⟨(c : Equiv.Perm (Fin 8)), by simpa using congrArg Subtype.val hc⟩
    exact (Equiv.Perm.isConj_iff_cycleType_eq.mp hperm).symm.trans ht
  · intro hs
    change IsConj t s
    exact isConj_of_cycleType_two_two ht hs

theorem card_centralizer_A8_two_four {t : alternatingGroup (Fin 8)}
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 8)))) = 192 := by
  refine card_centralizer_A8_of_ncard (k := 105) ?_ (by norm_num)
  rw [conjugatesOf_A8_two_four ht, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    AlternatingGroup.card_of_cycleType, if_pos (by decide)]
  norm_num

theorem ncard_conjugatesOf_A8_two_two {t : alternatingGroup (Fin 8)}
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2}) : (conjugatesOf t).ncard = 210 := by
  rw [conjugatesOf_A8_two_two ht, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    AlternatingGroup.card_of_cycleType, if_pos (by decide)]
  norm_num

theorem card_centralizer_A8_two_two {t : alternatingGroup (Fin 8)}
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2}) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 8)))) = 96 :=
  card_centralizer_A8_of_ncard (k := 210) (ncard_conjugatesOf_A8_two_two ht) (by norm_num)

theorem card_centralizer_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    Nat.card ↥(Subgroup.centralizer ({e x} : Set B)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set A)) := by
  have hmap : (Subgroup.centralizer ({x} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set B) := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      change e w * e x = e x * e w
      rw [← map_mul, ← map_mul, hw]
    · intro hy
      rw [Subgroup.mem_map]
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hy
  rw [← hmap]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective
    (Subgroup.centralizer ({x} : Set A)) e.toMonoidHom e.injective).toEquiv).symm

theorem isConj_of_card_centralizer_192 {Γ β : Type*} [Group Γ]
    (φ : alternatingGroup (Fin 8) ≃* Γ) {F : Γ → β} (hF : Function.Injective F) {T : Set β}
    (hT : T.Finite) (hT105 : T.ncard ≤ 105) {u₀ : Γ} (hu₀2 : u₀ * u₀ = 1) (hu₀1 : u₀ ≠ 1)
    (hu₀T : ∀ g : Γ, F (g * u₀ * g⁻¹) ∈ T) {u : Γ} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hc : Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 192) : IsConj u₀ u := by
  have hsq : ∀ {v : Γ}, v * v = 1 → (φ.symm v) ^ 2 = 1 := fun {v} hv => by
    rw [pow_two, ← map_mul, hv, map_one]
  have hne : ∀ {v : Γ}, v ≠ 1 → φ.symm v ≠ 1 := fun {v} hv h1 => hv (by
    simpa using congrArg φ h1)
  have ht₀ : ((φ.symm u₀ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType =
      {2, 2, 2, 2} := by
    rcases cycleType_eq_of_sq_eq_one (hsq hu₀2) (hne hu₀1) with h | h
    · exfalso
      have hinj : Set.InjOn (fun s => F (φ s)) (conjugatesOf (φ.symm u₀)) :=
        fun x _ y _ hxy => φ.injective (hF hxy)
      have hmaps : ∀ s ∈ conjugatesOf (φ.symm u₀), F (φ s) ∈ T := by
        intro s hs
        change IsConj (φ.symm u₀) s at hs
        obtain ⟨g, hg⟩ := isConj_iff.mp hs
        rw [← hg, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact hu₀T (φ g)
      have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj hT
      rw [ncard_conjugatesOf_A8_two_two h] at hle
      omega
    · exact h
  have ht : ((φ.symm u : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType =
      {2, 2, 2, 2} := by
    rcases cycleType_eq_of_sq_eq_one (hsq hu2) (hne hu1) with h | h
    · exfalso
      have h96 := card_centralizer_A8_two_two h
      rw [card_centralizer_eq_of_mulEquiv φ.symm u, hc] at h96
      omega
    · exact h
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_cycleType_two_two_two_two ht ht₀)
  have h1 := congrArg φ hg
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  exact (isConj_iff.mpr ⟨φ g, h1⟩).symm

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
