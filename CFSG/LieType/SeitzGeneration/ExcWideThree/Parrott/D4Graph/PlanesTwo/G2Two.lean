module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Words
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.SL2Two
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Side
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QuadExt
public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
  CFSG.LieType.HighestRoot CFSG.RankThree.Chevalley


variable {K : Type} [Field K] [Finite K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

variable (K) in
@[expose] noncomputable def fixSubgroupEquivG2Two (h2 : (2 : K) = 0) :
    ↥(fixSubgroup (d4Graph K 1)) ≃* ↥(adjointGroup Tag.G2 K) :=
  (fixSubgroupEquivTwisted K).trans (d4FixedG2Equiv K h2)

theorem coe_fixSubgroupEquivG2Two (h2 : (2 : K) = 0) (y : ↥(fixSubgroup (d4Graph K 1))) :
    ((fixSubgroupEquivG2Two K h2 y : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      d4FixedToG2 K ⟨y.1.1, mem_fixSubgroup_d4Graph_one_iff.1 y.2⟩ :=
  rfl

theorem fixSubgroupEquivG2Two_sl2Two (h2 : (2 : K) = 0) (A : SL2 K) :
    ((fixSubgroupEquivG2Two K h2 (sl2TwoFix A) : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      simpleRootSL2 Tag.G2 K ⟨0, by decide⟩ A := by
  set ρ : SL2 K →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp
    ((fixSubgroupEquivG2Two K h2).toMonoidHom.comp sl2TwoFix)
  have hρ : ρ = simpleRootSL2 Tag.G2 K ⟨0, by decide⟩ := by
    refine eq_simpleRootSL2 _ (fun c => ?_) fun c => ?_
    · show ((fixSubgroupEquivG2Two K h2 (sl2TwoFix (uSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2Two, ← d4FixedToG2_g2OrbitXUnitAll]
      congr 1
      exact Subtype.ext ((congrArg Subtype.val (sl2At_uSL (K := K) ⟨2, by decide⟩ c)).trans
        (xUnit_two_eq_g2OrbitXUnit c))
    · show ((fixSubgroupEquivG2Two K h2 (sl2TwoFix (vSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2Two, ← d4FixedToG2_g2OrbitYUnitAll]
      congr 1
      exact Subtype.ext ((congrArg Subtype.val (sl2At_vSL (K := K) ⟨2, by decide⟩ c)).trans
        (yUnit_two_eq_g2OrbitYUnit c))
  exact DFunLike.congr_fun hρ A

theorem fixSubgroupEquivG2Two_sl2Short (h2 : (2 : K) = 0) (A : SL2 K) :
    ((fixSubgroupEquivG2Two K h2 (sl2ShortFix A) : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      simpleRootSL2 Tag.G2 K ⟨1, by decide⟩ A := by
  set ρ : SL2 K →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp
    ((fixSubgroupEquivG2Two K h2).toMonoidHom.comp sl2ShortFix)
  have hρ : ρ = simpleRootSL2 Tag.G2 K ⟨1, by decide⟩ := by
    refine eq_simpleRootSL2 _ (fun c => ?_) fun c => ?_
    · show ((fixSubgroupEquivG2Two K h2 (sl2ShortFix (uSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2Two, ← d4FixedToG2_g2OrbitXUnitAll]
      congr 1
      refine Subtype.ext ?_
      show ((sl2Short K (uSL c) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = _
      rw [sl2Short_apply, sl2At_uSL, sl2At_uSL, sl2At_uSL]
      exact xUnit_short_eq_g2OrbitXUnit c
    · show ((fixSubgroupEquivG2Two K h2 (sl2ShortFix (vSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2Two, ← d4FixedToG2_g2OrbitYUnitAll]
      congr 1
      refine Subtype.ext ?_
      show ((sl2Short K (vSL c) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = _
      rw [sl2Short_apply, sl2At_vSL, sl2At_vSL, sl2At_vSL]
      exact yUnit_short_eq_g2OrbitYUnit c
  exact DFunLike.congr_fun hρ A

theorem g2_exists_conj_simpleRootSL2_two (hK : Nat.card K = 2) {z : adjointGroup Tag.G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (g : adjointGroup Tag.G2 K) (j : Fin Tag.G2.rank) (A : SL2 K),
      ((g * z * g⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
        simpleRootSL2 Tag.G2 K j A := by
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ :=
    CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.exists_quadratic_frobenius_all K
  have : Finite K₂ := (CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ).1
  obtain ⟨M⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.nonempty_qPlusModel hdeg hσ
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.exists_conj_short_or_long M hdeg hσ h3 hz3 hz1
  rcases hg with hS | hL
  · obtain ⟨g', j, A, h⟩ := g2_exists_conj_of_mem_rootQ (y := g * z * g⁻¹) isRoot_g2δ
      (Subgroup.mem_comap.1 hS)
    refine ⟨g' * g, j, A, ?_⟩
    have e : g' * g * z * (g' * g)⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹ := by group
    rw [e]
    exact h
  · obtain ⟨g', j, A, h⟩ := g2_exists_conj_of_mem_rootQ (y := g * z * g⁻¹)
      (isRoot_single Tag.G2 g2l) (Subgroup.mem_comap.1 hL)
    refine ⟨g' * g, j, A, ?_⟩
    have e : g' * g * z * (g' * g)⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹ := by group
    rw [e]
    exact h

theorem closure_eq_top_short_two (hK : Nat.card K = 2) {A : SL2 K} (hA3 : sl2Short K A ^ 3 = 1)
    (hA1 : sl2Short K A ≠ 1) :
    Subgroup.closure ((Subgroup.centralizer ({sl2Short K A} :
      Set ↥(adjointGroup Tag.D4 K)) : Set ↥(adjointGroup Tag.D4 K)) ∪
        (fixedSubgroup (d4Graph K 1) : Set ↥(adjointGroup Tag.D4 K))) = ⊤ := by
  set M := Subgroup.closure ((Subgroup.centralizer ({sl2Short K A} :
      Set ↥(adjointGroup Tag.D4 K)) : Set ↥(adjointGroup Tag.D4 K)) ∪
        (fixedSubgroup (d4Graph K 1) : Set ↥(adjointGroup Tag.D4 K))) with hM
  have hγ : ∀ g, d4Graph K 1 g = g → g ∈ M := fun g hg => Subgroup.subset_closure (Or.inr hg)
  have hc := fun (i j : Fin Tag.D4.rank) (hi : i ≠ ⟨2, by decide⟩) (hj : j ≠ ⟨2, by decide⟩)
    (hij : i ≠ j) (A B : SL2 K) => sl2At_commute (K := K) hi hj hij A B
  have hcen : ∀ i : Fin Tag.D4.rank, i ≠ ⟨2, by decide⟩ → ∀ B : SL2 K,
      (B = A ∨ B = A⁻¹) → sl2At K i B ∈ M := by
    intro i hi B hB
    have hA : sl2At K i A ∈ M := by
      refine Subgroup.subset_closure (Or.inl ?_)
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, sl2Short_apply]
      have hcomm : ∀ j : Fin Tag.D4.rank, j ≠ ⟨2, by decide⟩ →
          Commute (sl2At K i A) (sl2At K j A) := by
        intro j hj
        by_cases hij : i = j
        · subst hij
          exact Commute.refl _
        · exact hc i j hi hj hij A A
      exact (((hcomm ⟨0, by decide⟩ (by decide)).mul_right
        (hcomm ⟨1, by decide⟩ (by decide))).mul_right (hcomm ⟨3, by decide⟩ (by decide))).eq
    rcases hB with rfl | rfl
    · exact hA
    · rw [map_inv]
      exact M.inv_mem hA
  have huv : ∀ i : Fin Tag.D4.rank, i ≠ ⟨2, by decide⟩ → sl2At K i (uSL 1 * vSL 1) ∈ M := by
    intro i hi
    rcases sl2_sq_eq_one_or hK A with hsq | hA | hA
    · exfalso
      apply hA1
      have h2' : sl2Short K A * sl2Short K A = 1 := by rw [← map_mul, hsq, map_one]
      calc sl2Short K A = sl2Short K A ^ 3 * (sl2Short K A * sl2Short K A)⁻¹ := by group
        _ = 1 := by rw [hA3, h2']; group
    · exact hcen i hi _ (Or.inl hA.symm)
    · refine hcen i hi _ (Or.inr ?_)
      rw [hA, vu_inv hK]
  obtain ⟨e0, e1, -, e3⟩ := sl2At_uv_eq_wordG (K := K)
  obtain ⟨-, -, r2, -, -, -, r8, -⟩ := rt_single
  have hx2 : wordG K [2] ∈ M := by
    refine hγ _ ?_
    have := (d4Graph_one_xPar_two (K := K) 1).1
    simpa [wordG, r2] using this
  have hy2 : wordG K [8] ∈ M := by
    refine hγ _ ?_
    have := (d4Graph_one_xPar_two (K := K) 1).2
    simpa [wordG, r8] using this
  refine eq_top_of_psi hK ?_ ?_ ?_ hx2 hy2
  · rw [← e0]; exact huv _ (by decide)
  · rw [← e1]; exact huv _ (by decide)
  · rw [← e3]; exact huv _ (by decide)

theorem pairGenAt_d4Graph_one_two (hK : Nat.card K = 2) : PairGenAt (d4Graph K 1) := by
  intro x hx3 hx1 hγx
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_two' hK
  set Φ := fixSubgroupEquivG2Two K h2
  set y : ↥(fixSubgroup (d4Graph K 1)) := ⟨x, mem_fixSubgroup.2 hγx⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simp [y, hx3])
  have hy1 : y ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hz3 : Φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hz1 : Φ y ≠ 1 := fun h => hy1 (Φ.injective (h.trans (map_one Φ).symm))
  obtain ⟨g, j, A, hj⟩ := g2_exists_conj_simpleRootSL2_two hK hz3 hz1
  set h := Φ.symm g
  have hΦ : Φ (h * y * h⁻¹) = g * Φ y * g⁻¹ := by simp [h]
  have hhγ : d4Graph K 1 (h : ↥(adjointGroup Tag.D4 K)) = h := mem_fixSubgroup.1 h.2
  refine closure_eq_top_of_conj hhγ ?_
  have hw3 : ((h : ↥(adjointGroup Tag.D4 K)) * x * (h : ↥(adjointGroup Tag.D4 K))⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    group
  have hw1 : (h : ↥(adjointGroup Tag.D4 K)) * x * (h : ↥(adjointGroup Tag.D4 K))⁻¹ ≠ 1 := by
    intro h0
    apply hx1
    calc x = (h : ↥(adjointGroup Tag.D4 K))⁻¹ * ((h : ↥(adjointGroup Tag.D4 K)) * x *
          (h : ↥(adjointGroup Tag.D4 K))⁻¹) * h := by group
      _ = 1 := by rw [h0]; group
  fin_cases j
  · have e : h * y * h⁻¹ = sl2TwoFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2Two_sl2Two]))
    have e' : (h : ↥(adjointGroup Tag.D4 K)) * x * (h : ↥(adjointGroup Tag.D4 K))⁻¹ =
        sl2At K ⟨2, by decide⟩ A := congrArg Subtype.val e
    rw [e']
    exact closure_eq_top_long A
  · have e : h * y * h⁻¹ = sl2ShortFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2Two_sl2Short]))
    have e' : (h : ↥(adjointGroup Tag.D4 K)) * x * (h : ↥(adjointGroup Tag.D4 K))⁻¹ =
        sl2Short K A := congrArg Subtype.val e
    rw [e'] at hw3 hw1 ⊢
    exact closure_eq_top_short_two hK hw3 hw1

theorem pairGenTwoG2_holds : PairGenTwoG2 :=
  fun _ _ _ hK => pairGenAt_d4Graph_one_two hK

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
