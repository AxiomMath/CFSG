module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylTwist
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.RankThree.PartOne.S11c.G2Torus

public noncomputable section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne CFSG.RankThree.Classical CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Coordinates

variable {K : Type} [Field K]

abbrev g2tuple (a b : Kˣ) : Fin Tag.G2.rank → Kˣ := ![a, b]

theorem rootChar_g2tuple (a b : Kˣ) (u v : ℤ) :
    rootChar (g2tuple a b) (g2v u v) = a ^ u * b ^ v := by
  change (∏ i : Fin 2, (![a, b] : Fin 2 → Kˣ) i ^ (![u, v] : Fin 2 → ℤ) i) = _
  simp [Fin.prod_univ_two]

theorem g2pair : G2SignPair (g2v 0 1) (g2v 2 3) := Or.inl ⟨rfl, rfl⟩

theorem chi_g2tuple (l : Kˣ) :
    rootChar (g2tuple l⁻¹ l) (g2v 0 1) = l ∧ rootChar (g2tuple l⁻¹ l) (g2v 2 3) = l := by
  rw [rootChar_g2tuple, rootChar_g2tuple]
  constructor
  · simp
  · simp
    group

end Coordinates

section G2


variable {K : Type} [Field K]

theorem g2_conj₁ (l : Kˣ) (A : SL2 K) :
    rootDiagUnit .G2 (g2tuple l⁻¹ l) * rootSL2 .G2 K (g2v 0 1) A *
        (rootDiagUnit .G2 (g2tuple l⁻¹ l))⁻¹ =
      rootSL2 .G2 K (g2v 0 1) (conjSL (diagUnitOne l) A) := by
  rw [rootDiagUnit_conj_rootSL2 _ (g2_pair_isRoot g2pair).1, (chi_g2tuple l).1]

theorem g2_conj₂ (l : Kˣ) (A : SL2 K) :
    rootDiagUnit .G2 (g2tuple l⁻¹ l) * rootSL2 .G2 K (g2v 2 3) A *
        (rootDiagUnit .G2 (g2tuple l⁻¹ l))⁻¹ =
      rootSL2 .G2 K (g2v 2 3) (conjSL (diagUnitOne l) A) := by
  rw [rootDiagUnit_conj_rootSL2 _ (g2_pair_isRoot g2pair).2, (chi_g2tuple l).2]

theorem g2_sq (l : Kˣ) :
    rootDiagUnit .G2 (g2tuple l⁻¹ l) * rootDiagUnit .G2 (g2tuple l⁻¹ l) =
      rootSL2 .G2 K (g2v 0 1) (HSL l) * rootSL2 .G2 K (g2v 2 3) (HSL l) := by
  have hα := (g2_pair_isRoot g2pair).1
  have hβ := (g2_pair_isRoot g2pair).2
  rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v (-3) 2) g2_hm_01,
    rootSL2_HSL_eq_rootDiagUnit hβ (g2v 1 0) g2_hm_23, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext i
  fin_cases i
  · simp
    group
  · show l * l = l ^ (2 : ℤ) * l ^ (0 : ℤ)
    rw [zpow_zero, mul_one, zpow_two]

@[expose] def g2TwistedPairModGL (l : Kˣ) (hl : ∀ p : K, (l : K) ≠ p * p) :
    TwistedPair K (ModGL .G2 K) where
  ρ₁ := rootSL2 .G2 K (g2v 0 1)
  ρ₂ := rootSL2 .G2 K (g2v 2 3)
  g := rootDiagUnit .G2 (g2tuple l⁻¹ l)
  l := l
  comm A B := (g2_pair_commute g2pair A B).eq
  neg := g2_pair_HSL_neg_one g2pair
  inj₁ := rootSL2_injective_of_field _
  inj₂ := rootSL2_injective_of_field _
  conj₁ A := g2_conj₁ l A
  conj₂ A := g2_conj₂ l A
  sq := g2_sq l
  nonsq := hl

theorem rootSL2_mem_adjointGroup' (β : Fin Tag.G2.rank → ℤ) (A : SL2 K) :
    rootSL2 .G2 K β A ∈ adjointGroup .G2 K := by
  rw [rootSL2_apply]
  exact mul_mem (mul_mem (pinnedWeyl_mem_adjointGroup β) (simpleRootSL2_mem_adjointGroup _ A))
    (inv_mem (pinnedWeyl_mem_adjointGroup β))

theorem rootDiagUnit_mem_adjointGroup_G2 (b : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit .G2 b ∈ adjointGroup .G2 K := by
  have h : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t
  exact h (rootDiagUnit_mem_torusGroup_G2 b)

@[expose] def g2TwistedPair (l : Kˣ) (hl : ∀ p : K, (l : K) ≠ p * p) :
    TwistedPair K ↥(adjointGroup .G2 K) :=
  (g2TwistedPairModGL l hl).restrict (adjointGroup .G2 K)
    (fun A => rootSL2_mem_adjointGroup' _ A) (fun A => rootSL2_mem_adjointGroup' _ A)
    (rootDiagUnit_mem_adjointGroup_G2 _)

end G2

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
