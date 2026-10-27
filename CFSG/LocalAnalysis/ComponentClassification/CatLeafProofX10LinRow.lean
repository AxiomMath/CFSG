module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinDispatch
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_psl_of_lieModel)

theorem isClassicalTag_of_mem_orthTuples {t : StatedLieTag} {m e d f : ℕ}
    (h : (t, m, e) ∈ orthTuples d f) : IsClassicalTag t := by
  rcases h with ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩ <;>
    rw [(Prod.mk.inj h).1] <;> simp [IsClassicalTag]

theorem isClassicalTag_of_mem_graphTuples {t : StatedLieTag} {m e d f : ℕ}
    (h : (t, m, e) ∈ graphTuples d f) : IsClassicalTag t := by
  rcases h with h | ⟨-, h⟩
  · exact isClassicalTag_of_mem_orthTuples h
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]

theorem isClassicalTag_of_mem_linTuples {t : StatedLieTag} {m e n f : ℕ}
    (h : (t, m, e) ∈ linTuples n f) : IsClassicalTag t := by
  rcases h with (⟨k, -, -, -, h⟩ | ⟨-, h⟩) | h | ⟨j, -, h | h⟩
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]
  · exact isClassicalTag_of_mem_graphTuples h
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]

theorem isClassicalTag_of_mem_linUTuples {t : StatedLieTag} {m e n f : ℕ}
    (h : (t, m, e) ∈ linUTuples n f) : IsClassicalTag t := by
  rcases h with (⟨k, -, -, h⟩ | ⟨-, h⟩) | h
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]
  · rw [(Prod.mk.inj h).1]
    simp [IsClassicalTag]
  · exact isClassicalTag_of_mem_graphTuples h

theorem psp_mem_graphTuples {n f' f : ℕ} (h : ((.PSp : StatedLieTag), 2, f) ∈ graphTuples n f') :
    (n = 4 ∧ f' = f) ∨ n = 5 := by
  rcases h with h | ⟨⟨r, hr⟩, h⟩
  · rcases h with ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨h5, -⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩
    all_goals first
      | exact Or.inr h5
      | exact absurd (Prod.mk.inj h).1 (by decide)
  · obtain ⟨h2, h3⟩ := Prod.mk.inj (Prod.mk.inj h).2
    left
    omega

theorem psp_mem_linTuples {n f' f : ℕ} (h : ((.PSp : StatedLieTag), 2, f) ∈ linTuples n f') :
    (n = 4 ∧ f' = f) ∨ n = 5 := by
  rcases h with (⟨k, -, -, -, h⟩ | ⟨-, h⟩) | h | ⟨j, -, h | h⟩
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact psp_mem_graphTuples h
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)

theorem psp_mem_linUTuples {n f' f : ℕ} (h : ((.PSp : StatedLieTag), 2, f) ∈ linUTuples n f') :
    (n = 4 ∧ f' = f) ∨ n = 5 := by
  rcases h with (⟨k, -, -, h⟩ | ⟨-, h⟩) | h
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact psp_mem_graphTuples h

theorem psp_of_mem_graphTuples_five {t : StatedLieTag} {m e f : ℕ}
    (h : (t, m, e) ∈ graphTuples 5 f) : t = .PSp := by
  rcases h with h | ⟨h5, -⟩
  · rcases h with ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h⟩ | ⟨h6, -⟩ | ⟨h7, -, -⟩ | ⟨h8, -, -⟩
    · omega
    · omega
    · exact (Prod.mk.inj h).1
    · omega
    · omega
    · omega
  · exact absurd h5 (by decide)

theorem mem_linTuples_five {t : StatedLieTag} {m e f : ℕ} (h : (t, m, e) ∈ linTuples 5 f) :
    (t = .PSL ∧ 3 ≤ m) ∨ t = .PSU ∨ t = .PSp := by
  rcases h with (⟨k, -, hk3, -, h⟩ | ⟨h5, -⟩) | h | ⟨j, -, h | h⟩
  · obtain ⟨ht, hme⟩ := Prod.mk.inj h
    exact Or.inl ⟨ht, by rw [(Prod.mk.inj hme).1]; exact hk3⟩
  · exact absurd h5 (by decide)
  · exact Or.inr (Or.inr (psp_of_mem_graphTuples_five h))
  · obtain ⟨ht, hme⟩ := Prod.mk.inj h
    exact Or.inl ⟨ht, by rw [(Prod.mk.inj hme).1]; norm_num⟩
  · exact Or.inr (Or.inl (Prod.mk.inj h).1)

theorem mem_linUTuples_five {t : StatedLieTag} {m e f : ℕ} (h : (t, m, e) ∈ linUTuples 5 f) :
    (t = .PSL ∧ 3 ≤ m) ∨ t = .PSU ∨ t = .PSp := by
  rcases h with (⟨k, -, -, h⟩ | ⟨h5, -⟩) | h
  · exact Or.inr (Or.inl (Prod.mk.inj h).1)
  · exact absurd h5 (by decide)
  · exact Or.inr (Or.inr (psp_of_mem_graphTuples_five h))

theorem fixedTwoComponentsQuasisimple_lin {N : Type} [Group N] [Finite N] {τ : StatedLieTag}
    {n p f : ℕ} (hp2 : p ≠ 2) (hτ : τ = .PSL ∨ τ = .PSU) (hadm : StatedLieAdmissible τ n p f)
    (hN : LieModel N τ n p f) : FixedTwoComponentsQuasisimple N := by
  rcases hτ with rfl | rfl
  · have hn : 2 ≤ n := hadm.2.2.1
    have hsc := GH74.statedClassicalModel_of_lieModel (by omega) hN
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · have : IsSimpleGroup N := X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) hN
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hN
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hadm.1.eq_two_or_odd'.resolve_left hp2).pow
      have h2 : Nat.card K ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
      have h3 : Nat.card K ≠ 3 := fun h => hadm.2.2.2.2 (by rw [← hK, h])
      obtain ⟨-, -, a, b, hab⟩ := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
        (Or.inr h2) (Or.inr h3)
      refine fixedTwoComponentsQuasisimple_psl_two ⟨e.symm a, e.symm b, fun h => hab ?_⟩ hp2 hsc
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h
    · exact fixedTwoComponentsQuasisimple_psl hp2 hn3 hsc
  · have hn : 3 ≤ n := hadm.2.2.1
    exact fixedTwoComponentsQuasisimple_psu hp2 (GH74.statedClassicalModel_of_lieModel (by omega)
      hN)

theorem false_of_lin_twoComponent {N : Type} [Group N] [Finite N] {τ : StatedLieTag}
    {n p f' f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hτ : τ = .PSL ∨ τ = .PSU)
    (hadm : StatedLieAdmissible τ n p f') (hN : LieModel N τ n p f') (hf : 1 ≤ f)
    (h5 : 5 ≤ p ^ f) {α : MulAut N} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (fixedSubgroup α)} (hL : IsPComponent 2 L)
    (hX : (LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f ∧ ¬((n = 4 ∧ f' = f) ∨ n = 5)) ∨
      (LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p (2 * f) ∧ n = 5)) : False := by
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_lin hp2 hτ hadm hN α hα2 hα1 L hL
  have hsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hL
    exact h
  have hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := by
    rcases hX with ⟨h, -⟩ | ⟨h, -⟩
    · exact GSThmB.X10Rec.isSimpleGroup_of_lieModel_psp h5 h
    · exact X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) h
  have hZO := GSThmB.X10Rec.center_eq_pPrimeCore hq hs
  have hY : ∀ {t : StatedLieTag} {m e : ℕ}, LieModel (L ⧸ pPrimeCore 2 L) t m p e →
      LieModel (L ⧸ center L) t m p e := fun h =>
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm h
  have hα : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  have hcases : ∃ T : Set (StatedLieTag × ℕ × ℕ), ComponentCases p T L ∧
      (∀ {t m e}, (t, m, e) ∈ T → IsClassicalTag t) ∧
      (∀ {e}, (StatedLieTag.PSp, 2, e) ∈ T → (n = 4 ∧ f' = e) ∨ n = 5) ∧
      (n = 5 → ∀ {t m e}, (t, m, e) ∈ T → (t = .PSL ∧ 3 ≤ m) ∨ t = .PSU ∨ t = .PSp) := by
    rcases hτ with rfl | rfl
    · refine ⟨linTuples n f', psl_component_cases hp hp2 hadm hN hα ⟨hq, hsub⟩,
        isClassicalTag_of_mem_linTuples, psp_mem_linTuples, fun h5' => ?_⟩
      subst h5'
      exact mem_linTuples_five
    · refine ⟨linUTuples n f', psu_component_cases hp2 hadm hN hα ⟨hq, hsub⟩,
        isClassicalTag_of_mem_linUTuples, psp_mem_linUTuples, fun h5' => ?_⟩
      subst h5'
      exact mem_linUTuples_five
  obtain ⟨T, hC, hcl, hpsp, hfive⟩ := hcases
  rcases hC with ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  ·
    exact hz1 (congrArg Subtype.val (X10Sp.eq_one_of_mem_center hZO (z := ⟨z, hzL⟩)
      (mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm) (Subtype.ext hzz)))
  · rcases hX with ⟨hX, hn⟩ | ⟨hX, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := eq_psp4_of_two_lieModels hp hp2 hf (hcl hT) hadm' hm' (hY hX)
      exact hn (hpsp hT)
    · exact false_of_two_lieModels_l2 hp hp2 hf (hfive rfl hT) hadm' hm' (hY hX)

theorem cf81X10RowLin : GSThmB.CF81X10RowLin := by
  intro N _ _ τ n p f' f hp hp2 hτ hadm hN hf h5 α hα2 hα1 L hL
  refine ⟨fun hX => ?_, fun h5' hX => ?_⟩
  · by_contra hn
    exact false_of_lin_twoComponent hp hp2 hτ hadm hN hf h5 hα2 hα1 hL (Or.inl ⟨hX, hn⟩)
  · exact false_of_lin_twoComponent hp hp2 hτ hadm hN hf h5 hα2 hα1 hL (Or.inr ⟨hX, h5'⟩)

end CFSG.ComponentClassification.CatLeafProof.X10Lin
