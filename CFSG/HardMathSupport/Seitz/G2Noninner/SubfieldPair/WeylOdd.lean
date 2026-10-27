module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.CloseOdd
public import CFSG.RankThree.PartOne.SEITZ6.G2Bruhat

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K]

theorem sign_mul_sign {a b : K} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem weylElement_smul_rootVec_sign (i : Fin (Tag.rank .G2)) {t t' : ℕ}
    (ht : t < 12) (h : reflect .G2 i (rt t) = rt t') :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      weylElement .G2 K i • rootVec .G2 K (rt t) = ε • rootVec .G2 K (rt t') := by
  have hα : IsRoot .G2 (rt t) := isRoot_rt ht
  have hw := weylElt_rootVec (R := K) i (1 : Kˣ) hα
  refine ⟨(-1) ^ stringDown .G2 i (rt t), neg_one_pow_eq_or K _, ?_⟩
  show (weylElt .G2 K i 1 : Module.End K (RootModule .G2 K)) (rootVec .G2 K (rt t)) = _
  rw [hw, h]
  simp

theorem list_prod_weylElement_sign (ω : List (Fin (Tag.rank .G2))) :
    ∃ t ∈ longPos, ∃ ε₁ ε₂ : K, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      (ω.map (weylElement .G2 K)).prod • rootVec .G2 K (rt 7) = ε₁ • rootVec .G2 K (rt t) ∧
      ∀ c : K, (ω.map (weylElement .G2 K)).prod * xp 7 c * ((ω.map (weylElement .G2 K)).prod)⁻¹ =
        xp t (ε₂ * c) := by
  induction ω with
  | nil => exact ⟨7, by simp [longPos], 1, 1, Or.inl rfl, Or.inl rfl, by simp, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨t, ht, ε₁, ε₂, hε₁, hε₂, h1, h2⟩ := ih
    obtain ⟨t', ht', hr⟩ := reflect_long t ht i
    have ht12 : t < 12 := by
      simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
      omega
    obtain ⟨ε, hε, hv⟩ := weylElement_smul_rootVec_sign (K := K) i ht12 hr
    obtain ⟨δ, hδ, hc⟩ := weylElement_conj_xp_sign (K := K) i ht12 hr
    refine ⟨t', ht', ε₁ * ε, δ * ε₂, sign_mul_sign hε₁ hε, sign_mul_sign hδ hε₂, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_smul, h1, smul_smul_comm, hv, smul_smul]
    · intro c
      rw [List.map_cons, List.prod_cons,
        show weylElement .G2 K i * (ω.map (weylElement .G2 K)).prod * xp 7 c *
          (weylElement .G2 K i * (ω.map (weylElement .G2 K)).prod)⁻¹ =
          weylElement .G2 K i * ((ω.map (weylElement .G2 K)).prod * xp 7 c *
            ((ω.map (weylElement .G2 K)).prod)⁻¹) * (weylElement .G2 K i)⁻¹ by group, h2 c, hc,
        mul_assoc]

theorem nrep_stab_X7_sign
    (w : (CFSG.LieType.RootSystem.coxeterMatrix (g2Datum K).isFiniteType).Group) :
    ∃ t ∈ longPos, ∃ ε₁ ε₂ : K, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w • rootVec .G2 K (rt 7) =
        ε₁ • rootVec .G2 K (rt t) ∧
      (∀ c : K, CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w * xp 7 c *
        (CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w)⁻¹ = xp t (ε₂ * c)) := by
  obtain ⟨ω, hω, rfl⟩ :=
    ((CFSG.LieType.RootSystem.coxeterMatrix
      (g2Datum K).isFiniteType).toCoxeterSystem).exists_isReduced w
  rw [CFSG.LieType.Steinberg.nrep_wordProd (g2_isCTGroupDatum K) hω]
  exact list_prod_weylElement_sign ω

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
