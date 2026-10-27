module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Golay

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint

abbrev Cocode : Type := Word ⧸ golayCode

@[expose] def coMk : Word →ₗ[ZMod 2] Cocode := golayCode.mkQ

theorem coMk_eq_zero {v : Word} : coMk v = 0 ↔ v ∈ golayCode :=
  Submodule.Quotient.mk_eq_zero golayCode

theorem coMk_eq_coMk {v w : Word} : coMk v = coMk w ↔ v - w ∈ golayCode :=
  Submodule.Quotient.eq golayCode

theorem coMk_surjective : Function.Surjective coMk := Submodule.mkQ_surjective golayCode

@[expose] def pt (i : Fin 23) : Cocode := coMk (Pi.single i 1)

theorem natCard_cocode : Nat.card Cocode = 2 ^ 11 := by
  have h := Submodule.card_eq_card_quotient_mul_card golayCode
  rw [natCard_golayCode, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  have : 2 ^ 12 * 2 ^ 11 = 2 ^ 12 * Nat.card Cocode := by
    rw [← pow_add, h]
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm

@[expose] def ind (s : Finset (Fin 23)) : Word := fun i => if i ∈ s then 1 else 0

theorem ind_apply (s : Finset (Fin 23)) (i : Fin 23) : ind s i = if i ∈ s then 1 else 0 := rfl

theorem ind_singleton (i : Fin 23) : ind {i} = Pi.single i 1 := by
  ext j
  simp [ind, Pi.single_apply]

theorem ind_empty : ind ∅ = 0 := by
  ext j
  simp [ind]

theorem ind_eq_sum (s : Finset (Fin 23)) : ind s = ∑ i ∈ s, Pi.single i 1 := by
  ext j
  simp [ind, Finset.sum_apply, Pi.single_apply]

theorem ind_injective : Function.Injective ind := by
  intro s t h
  ext i
  have := congrFun h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [ind]

theorem hammingNorm_ind (s : Finset (Fin 23)) : hammingNorm (ind s) = s.card := by
  simp [hammingNorm, ind]

theorem hammingNorm_add_le (v w : Word) :
    hammingNorm (v + w) ≤ hammingNorm v + hammingNorm w := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_cases h : v i = 0
  · exact Or.inr fun hw => hi (by rw [h, hw, add_zero])
  · exact Or.inl h

theorem word_sub_eq_add (v w : Word) : v - w = v + w := by
  ext i
  exact CharTwo.sub_eq_add _ _

theorem eq_of_ind_add_mem {s t : Finset (Fin 23)} (hs : s.card ≤ 3) (ht : t.card ≤ 3)
    (h : ind s + ind t ∈ golayCode) : s = t := by
  by_contra hne
  have h0 : ind s + ind t ≠ 0 := by
    intro h0
    apply hne
    apply ind_injective
    ext i
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ (congrFun h0 i)
  have h7 := le_hammingNorm_of_mem_golayCode _ h h0
  have := hammingNorm_add_le (ind s) (ind t)
  rw [hammingNorm_ind, hammingNorm_ind] at this
  omega

theorem pt_eq_pt_iff {i j : Fin 23} : pt i = pt j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h' := coMk_eq_coMk.1 h
  rw [word_sub_eq_add, ← ind_singleton, ← ind_singleton] at h'
  simpa using eq_of_ind_add_mem (by simp) (by simp) h'

theorem pt_injective : Function.Injective pt := fun _ _ h => pt_eq_pt_iff.1 h

theorem pt_ne_zero (i : Fin 23) : pt i ≠ 0 := by
  intro h
  have h' := coMk_eq_zero.1 h
  rw [← ind_singleton, ← add_zero (ind {i}), ← ind_empty] at h'
  simpa using eq_of_ind_add_mem (by simp) (by simp) h'

theorem coMk_ind_injective :
    Function.Injective fun s : {s : Finset (Fin 23) // s.card ≤ 3} => coMk (ind s.1) := by
  intro s t h
  have h' := coMk_eq_coMk.1 h
  rw [word_sub_eq_add] at h'
  exact Subtype.ext (eq_of_ind_add_mem s.2 t.2 h')

theorem natCard_card_le_three : Nat.card {s : Finset (Fin 23) // s.card ≤ 3} = 2 ^ 11 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range 4) ?_]
  · have : ∀ k ∈ Finset.range 4,
        ({s ∈ ({s | s.card ≤ 3} : Finset (Finset (Fin 23))) | s.card = k}).card =
          Nat.choose 23 k := by
      intro k hk
      rw [Finset.mem_range] at hk
      have := Finset.card_powersetCard k (Finset.univ : Finset (Fin 23))
      rw [Finset.card_univ, Fintype.card_fin] at this
      rw [← this]
      congr 1
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      omega
    rw [Finset.sum_congr rfl this]
    decide
  · intro s hs
    simp at hs ⊢
    omega

theorem existsUnique_card_le_three (x : Cocode) :
    ∃! s : Finset (Fin 23), s.card ≤ 3 ∧ coMk (ind s) = x := by
  have hb := coMk_ind_injective.bijective_of_nat_card_le
    (by rw [natCard_card_le_three, natCard_cocode])
  obtain ⟨⟨s, hs⟩, hx⟩ := hb.2 x
  refine ⟨s, ⟨hs, hx⟩, ?_⟩
  rintro t ⟨ht, hxt⟩
  exact congrArg Subtype.val
    (coMk_ind_injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) (hxt.trans hx.symm))

theorem exists_card_le_three (x : Cocode) :
    ∃ s : Finset (Fin 23), s.card ≤ 3 ∧ coMk (ind s) = x :=
  (existsUnique_card_le_three x).exists

@[expose] def cocodeEquiv (g : NativeSporadic.Carrier .M23) : Cocode ≃ₗ[ZMod 2] Cocode :=
  Submodule.Quotient.equiv golayCode golayCode (wordRep g)
    (map_permLin_eq (golayCode_mem_permStab (toPerm_mem g)))

@[expose] def cocodeRep : NativeSporadic.Carrier .M23 →* (Cocode ≃ₗ[ZMod 2] Cocode) where
  toFun := cocodeEquiv
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with | _ v => rfl
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with | _ v => rfl

theorem cocodeRep_coMk (g : NativeSporadic.Carrier .M23) (v : Word) :
    cocodeRep g (coMk v) = coMk (wordRep g v) := rfl

theorem wordRep_ind (g : NativeSporadic.Carrier .M23) (s : Finset (Fin 23)) :
    wordRep g (ind s) = ind (s.image (toPerm g)) := by
  ext i
  simp only [wordRep_apply, ind_apply, Finset.mem_image]
  have : (toPerm g)⁻¹ i ∈ s ↔ ∃ a ∈ s, toPerm g a = i := by
    constructor
    · exact fun h => ⟨_, h, Equiv.apply_symm_apply _ _⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  simp only [this]

theorem cocodeRep_ind (g : NativeSporadic.Carrier .M23) (s : Finset (Fin 23)) :
    cocodeRep g (coMk (ind s)) = coMk (ind (s.image (toPerm g))) := by
  rw [cocodeRep_coMk, wordRep_ind]

theorem cocodeRep_pt (g : NativeSporadic.Carrier .M23) (i : Fin 23) :
    cocodeRep g (pt i) = pt (toPerm g i) := by
  rw [pt, cocodeRep_coMk, wordRep_single]
  rfl

theorem cocodeRep_injective : Function.Injective cocodeRep := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply toPerm_injective
  ext i
  have h : pt (toPerm g i) = pt i := by
    rw [← cocodeRep_pt, hg]
    rfl
  exact congrArg Fin.val (pt_injective h)

end CFSG.EvenSporadicStandard.Wong77.Module
