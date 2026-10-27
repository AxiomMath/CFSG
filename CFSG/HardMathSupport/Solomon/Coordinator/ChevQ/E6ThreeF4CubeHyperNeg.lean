module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperGen
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.LangLeviAux
import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofCent

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Cubes

theorem mu3_cases {L : Type*} [Field L] {ω : L} (hω : IsPrimitiveRoot ω 3) {r s : L}
    (hr : r ^ 3 = 1) (hs : s ^ 3 = 1) : r = 1 ∨ s = 1 ∨ r * s = 1 ∨ r * s ^ 2 = 1 := by
  obtain ⟨k, hk, rfl⟩ := hω.eq_pow_of_pow_eq_one hr
  obtain ⟨l, hl, rfl⟩ := hω.eq_pow_of_pow_eq_one hs
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  interval_cases k <;> interval_cases l
  · exact Or.inl (pow_zero ω)
  · exact Or.inl (pow_zero ω)
  · exact Or.inl (pow_zero ω)
  · exact Or.inr (Or.inl (pow_zero ω))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h3)))
  · exact Or.inr (Or.inr (Or.inl (by linear_combination h3)))
  · exact Or.inr (Or.inl (pow_zero ω))
  · exact Or.inr (Or.inr (Or.inl (by linear_combination h3)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination (ω ^ 3 + 1) * h3)))

theorem eq_one_of_diag_cube {L : Type*} [Field L] (D : SL(3, L))
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0)
    (hne : ∀ i j : Fin 3, i ≠ j →
      (D : Matrix (Fin 3) (Fin 3) L) i i ≠ (D : Matrix (Fin 3) (Fin 3) L) j j)
    {ζ : L} (h3 : (D : Matrix (Fin 3) (Fin 3) L) ^ 3 = Matrix.scalar (Fin 3) ζ) : ζ = 1 := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (D : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hD i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (D : Matrix (Fin 3) (Fin 3) L) 0 0 * (D : Matrix (Fin 3) (Fin 3) L) 1 1 *
      (D : Matrix (Fin 3) (Fin 3) L) 2 2 = 1 := by
    have h := D.2
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at h
    exact h
  have hcube : ∀ i, (D : Matrix (Fin 3) (Fin 3) L) i i ^ 3 = ζ := by
    intro i
    have h := congrFun (congrFun h3 i) i
    rw [hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Pi.pow_apply] at h
    exact h
  have key : ∀ a b : L, a ≠ b → a ^ 3 = b ^ 3 → a ^ 2 + a * b + b ^ 2 = 0 := by
    intro a b hab h
    have h' : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hab)
  have h01 := key _ _ (hne 0 1 (by decide)) ((hcube 0).trans (hcube 1).symm)
  have h02 := key _ _ (hne 0 2 (by decide)) ((hcube 0).trans (hcube 2).symm)
  have hsum : (D : Matrix (Fin 3) (Fin 3) L) 0 0 + (D : Matrix (Fin 3) (Fin 3) L) 1 1 +
      (D : Matrix (Fin 3) (Fin 3) L) 2 2 = 0 := by
    have h' : ((D : Matrix (Fin 3) (Fin 3) L) 1 1 - (D : Matrix (Fin 3) (Fin 3) L) 2 2) *
        ((D : Matrix (Fin 3) (Fin 3) L) 0 0 + (D : Matrix (Fin 3) (Fin 3) L) 1 1 +
          (D : Matrix (Fin 3) (Fin 3) L) 2 2) = 0 := by linear_combination h01 - h02
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (hne 1 2 (by decide)))
  rw [← hcube 0]
  linear_combination (D : Matrix (Fin 3) (Fin 3) L) 0 0 * h01 -
    (D : Matrix (Fin 3) (Fin 3) L) 0 0 * (D : Matrix (Fin 3) (Fin 3) L) 1 1 * hsum + hdet

private theorem pow_three_eq_one_of_diag {L : Type*} [Field L] {D : SL(3, L)}
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0)
    (hne : ∀ i j : Fin 3, i ≠ j →
      (D : Matrix (Fin 3) (Fin 3) L) i i ≠ (D : Matrix (Fin 3) (Fin 3) L) j j)
    (h3 : D ^ 3 ∈ Subgroup.center (SL(3, L))) : D ^ 3 = 1 := by
  obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h3
  have h := eq_one_of_diag_cube D hD hne (ζ := ζ)
    (by rw [← Matrix.SpecialLinearGroup.coe_pow, ← hζ])
  refine Subtype.ext ?_
  rw [← hζ, h, map_one]
  exact Matrix.SpecialLinearGroup.coe_one.symm

private theorem defect_mul_of_center {G : Type*} [Group G] (Φ : G →* G) {X₁ X₂ : G}
    (h₁ : (Φ X₁)⁻¹ * X₁ ∈ Subgroup.center G) :
    (Φ (X₁ * X₂))⁻¹ * (X₁ * X₂) = (Φ X₁)⁻¹ * X₁ * ((Φ X₂)⁻¹ * X₂) := by
  have hc := Subgroup.mem_center_iff.1 h₁ (Φ X₂)⁻¹
  rw [map_mul, mul_inv_rev]
  calc (Φ X₂)⁻¹ * (Φ X₁)⁻¹ * (X₁ * X₂) = (Φ X₂)⁻¹ * ((Φ X₁)⁻¹ * X₁) * X₂ := by group
    _ = (Φ X₁)⁻¹ * X₁ * (Φ X₂)⁻¹ * X₂ := by rw [hc]
    _ = (Φ X₁)⁻¹ * X₁ * ((Φ X₂)⁻¹ * X₂) := by group

private theorem exists_fixed_of_center_defect {L : Type*} [Field L] {ω : L}
    (hω : IsPrimitiveRoot ω 3) (Φ : SL(3, L) →* SL(3, L)) {X₁ X₂ : SL(3, L)}
    (h₁ : (Φ X₁)⁻¹ * X₁ ∈ Subgroup.center (SL(3, L)))
    (h₂ : (Φ X₂)⁻¹ * X₂ ∈ Subgroup.center (SL(3, L))) :
    Φ X₁ = X₁ ∨ Φ X₂ = X₂ ∨ Φ (X₁ * X₂) = X₁ * X₂ ∨ Φ (X₁ * X₂ * X₂) = X₁ * X₂ * X₂ := by
  obtain ⟨r₁, hr₁, hs₁⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h₁
  obtain ⟨r₂, hr₂, hs₂⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h₂
  have key : ∀ X : SL(3, L), Matrix.scalar (Fin 3) 1 =
      (((Φ X)⁻¹ * X : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) → Φ X = X := by
    intro X h
    refine inv_mul_eq_one.1 (Subtype.ext ?_)
    rw [← h, map_one]
    exact Matrix.SpecialLinearGroup.coe_one.symm
  have h12 := defect_mul_of_center Φ (X₂ := X₂) h₁
  have h122 := defect_mul_of_center Φ (X₁ := X₁ * X₂) (X₂ := X₂)
    (by rw [h12]; exact mul_mem h₁ h₂)
  rcases mu3_cases hω (by simpa using hr₁) (by simpa using hr₂) with h | h | h | h
  · exact Or.inl (key X₁ (h ▸ hs₁))
  · exact Or.inr (Or.inl (key X₂ (h ▸ hs₂)))
  · refine Or.inr (Or.inr (Or.inl (key _ ?_)))
    rw [h12, Matrix.SpecialLinearGroup.coe_mul, ← hs₁, ← hs₂, ← map_mul, h]
  · refine Or.inr (Or.inr (Or.inr (key _ ?_)))
    rw [h122, h12, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hs₁,
      ← hs₂, ← map_mul, ← map_mul, mul_assoc, ← sq, h]

private theorem mem_of_range_eq {G H : Type*} [Group G] [Group H] {ψ : G →* H}
    {S : Subgroup H} (hr : ψ.range = S) (A : G) : ψ A ∈ S := by
  rw [← hr]
  exact ⟨A, rfl⟩

private theorem exists_mem_not_mem_of_card_lt {G : Type*} [Group G] [Finite G]
    {E H : Subgroup G} (h : Nat.card H < Nat.card E) : ∃ a ∈ E, a ∉ H := by
  by_contra hcon
  have hle : E ≤ H := fun a ha => by
    by_contra haH
    exact hcon ⟨a, ha, haH⟩
  exact absurd (Subgroup.card_le_of_le hle) (not_le.2 h)

end Cubes

section LangLevi

open CFSG.Blueprint CFSG.SeitzReduction CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.LieType.AlgebraicGroups

theorem exists_lang_algebraicClosure (τ : Tag) (K : Type) [Field K] [Finite K] (w : WeylGroup τ)
    (hw : w • highRoot τ = highRoot τ) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, ∃ _ : ∀ c, Fr c = c ^ Nat.card K,
      ∃ g : ModGL τ (AlgebraicClosure K), ∃ _ : g ∈ Lθ τ (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g =
          g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  classical
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hcard' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hZ := LangLeviAux.isConnectedAlgebraicSubgroup_parabolicLevi (τ := τ)
    (k := AlgebraicClosure K) (Jθ τ)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ (e := (n : ℕ)) n.pos 1
    (fun g hg => LangLeviAux.frobTwistGL_one_mem_parabolicLevi p (n : ℕ) (Jθ τ) hg)
  have hn : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∈ Lθ τ (AlgebraicClosure K) :=
    canonicalRep_mem_parabolicLevi (mem_parabolicWeylGroup_of_smul_highRoot τ hw)
  obtain ⟨z, hz, hzn⟩ := hlang _ hn
  refine ⟨iterateFrobenius (AlgebraicClosure K) p n, fun c => ?_, z, hz, ?_⟩
  · rw [iterateFrobenius_def, hcard']
  · have h1 : frobTwistGL τ (AlgebraicClosure K) p n 1 z =
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) p n)) z := by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    rw [← hzn, mul_inv_cancel_left]
    exact h1.symm

end LangLevi

section Kills

theorem exists_kills_of_conj {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A)
    {g : ModGL τ (AlgebraicClosure K)} (hg : g ∈ adjointGroup τ (AlgebraicClosure K))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hk : ∀ x ∈ A, ∃ b : Fin τ.rank → (AlgebraicClosure K)ˣ, rootDiagUnit τ b =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∧
        rootChar b α = 1) :
    ∃ β, IsRoot τ β ∧ D.Kills β := by
  classical
  choose! b hb hbα using hk
  have ha : ∀ x : A, ∃ a, rootDiagUnit τ a = diagMap D x :=
    fun x => exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D x.2)
  choose a ha using ha
  set n := D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c : ModGL τ K) * g
    with hn
  have hnG : n ∈ adjointGroup τ (AlgebraicClosure K) := mul_mem (mul_mem (inv_mem D.hg0C)
    (baseChangeGL_mem_adjointGroup _ D.c.2)) hg
  have hconj : ∀ x : A, n * rootDiagUnit τ (b x) * n⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [ha x, hb x x.2, diagMap_apply, hn]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    group
  obtain ⟨w, hw⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family τ
    (AlgebraicClosure K) (fun x : A => a x) (fun x : A => b x) hnG hconj
  refine ⟨w • α, IsRoot.smul hα w, fun x hx => ⟨a ⟨x, hx⟩, ?_, ?_⟩⟩
  · rw [ha, diagMap_apply]
  · rw [(rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).1 (hw ⟨x, hx⟩) α, hbα x hx]

end Kills

section Frames

theorem rootChar_eq_one_of_frame_commute {τ : Tag} {L : Type} [Field L]
    {ψ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsA2Frame ψ σ)
    {c : Fin τ.rank → Lˣ} (hc : ∀ A, rootDiagUnit τ c * ψ A = ψ A * rootDiagUnit τ c)
    {i j : Fin 3} (hij : i ≠ j) : rootChar c (σ i j) = 1 := by
  obtain ⟨ε, hε⟩ := hψ.transv i j hij
  have h1 := rootDiagUnit_conj_pinnedX c (hψ.isRoot i j hij) ((ε : L) * 1)
  rw [← hε, hc, mul_inv_cancel_right, hε] at h1
  have h2 := pinnedX_injective τ L (σ i j) h1
  have hε0 : (ε : L) * 1 ≠ 0 := by
    rw [mul_one]
    exact ε.ne_zero
  refine Units.ext ?_
  rw [Units.val_one]
  exact mul_right_cancel₀ hε0 (h2.symm.trans (one_mul _).symm)

theorem exists_frob_frame {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsA2Frame ψ σ) (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (w : WeylGroup τ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j, i ≠ j → w • σ i j = σ (π j) (π i)) :
    ∃ Φ' : SL(3, L) ≃* SL(3, L), ∀ X, canonicalRep (coxeterSystem τ) L w *
      Units.map (entrywiseHom Fr) (ψ X) * (canonicalRep (coxeterSystem τ) L w)⁻¹ = ψ (Φ' X) := by
  classical
  choose! ε hε using hψ.transv
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      canonicalRep (coxeterSystem τ) L w * pinnedX τ L (σ i j) c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (σ (π j) (π i)) ((b : L) * c) := by
    intro i j hij
    obtain ⟨e, he, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (hψ.isRoot i j hij)
    refine ⟨Units.mkOfMulEqOne e e he, fun c => ?_⟩
    rw [hX c, hπ i j hij, Units.val_mkOfMulEqOne]
  obtain ⟨Φ', hΦ', -⟩ := CFSG.RankThree.PartOne.KE.exists_aut_of_rootData_n (τ := τ) (ν := 3) ψ
    hψ.injective σ ε (fun i j hij t => hε i j hij t) Fr hFr (canonicalRep (coxeterSystem τ) L w)
    (fun i j => (π j, π i)) (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hconj
  exact ⟨Φ', hΦ'⟩

end Frames

section BaseChange

private def conjBC {τ : Tag} {K : Type} [Field K] (g : ModGL τ (AlgebraicClosure K)) :
    adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj g⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)

private theorem conjBC_apply {τ : Tag} {K : Type} [Field K] (g : ModGL τ (AlgebraicClosure K))
    (a : adjointGroup τ K) :
    conjBC g a = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * g := by
  simp only [conjBC, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]

private theorem conjBC_injective {τ : Tag} {K : Type} [Field K]
    (g : ModGL τ (AlgebraicClosure K)) : Function.Injective (conjBC (K := K) g) := by
  intro a b h
  rw [conjBC_apply, conjBC_apply] at h
  exact Subtype.ext (baseChangeGL_injective _ (mul_left_cancel (mul_right_cancel h)))

private theorem conjBC_mem {τ : Tag} {K : Type} [Field K] {g : ModGL τ (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup τ (AlgebraicClosure K)) (a : adjointGroup τ K) :
    conjBC g a ∈ adjointGroup τ (AlgebraicClosure K) := by
  rw [conjBC_apply]
  exact mul_mem (mul_mem (inv_mem hg) (baseChangeGL_mem_adjointGroup _ a.2)) hg

private def killSub {τ : Tag} {K : Type} [Field K] (g : ModGL τ (AlgebraicClosure K))
    (α : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  ((rootCharHom (L := AlgebraicClosure K) α).ker.map
    (rootDiagUnitHom τ (AlgebraicClosure K))).comap (conjBC g)

private theorem mem_killSub {τ : Tag} {K : Type} [Field K] {g : ModGL τ (AlgebraicClosure K)}
    {α : Fin τ.rank → ℤ} {a : adjointGroup τ K} :
    a ∈ killSub g α ↔ ∃ b, rootDiagUnit τ b = conjBC g a ∧ rootChar b α = 1 := by
  simp only [killSub, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.mem_ker]
  exact ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩⟩

private theorem planeDatum {K : Type} [Field K] [Finite K] (hnd : ¬ 3 ∣ Nat.card K)
    {P : Subgroup (adjointGroup Tag.F4 K)} (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPc : Nat.card P = 3 ^ 2) : Nonempty (LangPlaneData Tag.F4 K P) := by
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K hnd P hP3 hPc
  exact ⟨⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩⟩

end BaseChange

section F4Frames

open CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
open CFSG.RankThree.E6 (chainRoot)

private theorem setL_eq_S1set : setL = S1set := by
  have h1 : ∀ i j : Fin 3, i ≠ j → sigmaL i j ∈ f4LongList := by decide +kernel
  have h2 : ∀ r ∈ f4LongList, ∃ i j : Fin 3, i ≠ j ∧ r = sigmaL i j := by decide +kernel
  ext r
  simp only [setL, S1set, Set.mem_setOf_eq]
  exact ⟨fun ⟨i, j, hij, hr⟩ => hr ▸ h1 i j hij, fun hr => h2 r hr⟩

theorem exists_frame_decomp {L : Type} [Field L] [IsAlgClosed L] {ω : Lˣ} (hω : orderOf ω = 3)
    {ψA ψB : SL(3, L) →* ModGL Tag.F4 L} (hrA : ψA.range = X1 L) (hrB : ψB.range = X2 L)
    {m : ModGL Tag.F4 L} (hm : m ∈ adjointGroup Tag.F4 L)
    (hmd : m * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * m) :
    ∃ X Y : SL(3, L), m = ψA X * ψB Y := by
  have hsup := mem_sup_of_commute_bStd hω hm hmd
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hsup
  have hSB : setS = S2set := QuasiF4.S₂_eq_chain.symm.trans QuasiF4.S₂_eq
  rw [range_rhoL, setL_eq_S1set] at hu
  rw [range_rhoS, hSB] at hv
  obtain ⟨X, hX⟩ : u ∈ ψA.range := by
    rw [hrA]
    exact hu
  obtain ⟨Y, hY⟩ : v ∈ ψB.range := by
    rw [hrB]
    exact hv
  exact ⟨X, Y, by rw [hX, hY]⟩

private theorem frames_commute {L : Type} [Field L] {ψA ψB : SL(3, L) →* ModGL Tag.F4 L}
    (hrA : ψA.range = X1 L) (hrB : ψB.range = X2 L) (A B : SL(3, L)) :
    Commute (ψA A) (ψB B) :=
  X1_X2_commute L _ (mem_of_range_eq hrA A) _ (mem_of_range_eq hrB B)

private theorem commute_d_of_mem_sup {L : Type} [Field L] [IsAlgClosed L] {ω : Lˣ}
    (hω : orderOf ω = 3)
    {m : ModGL Tag.F4 L} (hm : m ∈ X1 L ⊔ X2 L) :
    m * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * m := by
  have hSB : setS = S2set := QuasiF4.S₂_eq_chain.symm.trans QuasiF4.S₂_eq
  refine commute_bStd_of_mem_sup hω ?_
  rw [range_rhoL, range_rhoS, setL_eq_S1set, hSB]
  exact hm

private theorem mem_adjointGroup_of_mem_sup {L : Type} [Field L] {m : ModGL Tag.F4 L}
    (hm : m ∈ X1 L ⊔ X2 L) : m ∈ adjointGroup Tag.F4 L := by
  have h1 : X1 L ≤ adjointGroup Tag.F4 L := iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have h2 : X2 L ≤ adjointGroup Tag.F4 L := iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  exact sup_le h1 h2 hm

private theorem rootChar_frame_eq_one_iff {L : Type} [Field L]
    {ρ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (h : IsA2Frame ρ σ) {D : SL(3, L)}
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0)
    {c : Fin Tag.F4.rank → Lˣ} (hc : ρ D = rootDiagUnit Tag.F4 c) {i j : Fin 3} (hij : i ≠ j) :
    rootChar c (σ i j) = 1 ↔
      (D : Matrix (Fin 3) (Fin 3) L) i i = (D : Matrix (Fin 3) (Fin 3) L) j j := by
  rw [← Units.val_eq_one, rootChar_of_frame_diag h D hD hc hij,
    mul_inv_eq_one₀ (diag_ne_zero D hD j)]

private theorem exists_frame_dec_center {L : Type} [Field L] [IsAlgClosed L] {ω : Lˣ}
    (hω : orderOf ω = 3) {ψA ψB : SL(3, L) →* ModGL Tag.F4 L}
    {σA : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA) (hrA : ψA.range = X1 L)
    (hrB : ψB.range = X2 L) {n : ModGL Tag.F4 L} {T : ModGL Tag.F4 L →* ModGL Tag.F4 L}
    {ΦA ΦB : SL(3, L) →* SL(3, L)} (hΦA : ∀ X, n * T (ψA X) * n⁻¹ = ψA (ΦA X))
    (hΦB : ∀ Y, n * T (ψB Y) * n⁻¹ = ψB (ΦB Y)) {m : ModGL Tag.F4 L}
    (hm : m ∈ adjointGroup Tag.F4 L)
    (hmd : m * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * m)
    (hmF : n * T m * n⁻¹ = m) :
    ∃ X Y : SL(3, L), m = ψA X * ψB Y ∧ (ΦA X)⁻¹ * X ∈ Subgroup.center (SL(3, L)) := by
  obtain ⟨X, Y, rfl⟩ := exists_frame_decomp hω hrA hrB hm hmd
  refine ⟨X, Y, rfl, ?_⟩
  have h1 : ψA (ΦA X) * ψB (ΦB Y) = ψA X * ψB Y := by
    rw [← hΦA, ← hΦB, ← hmF, map_mul]
    group
  have h2 : ψA ((ΦA X)⁻¹ * X) = ψB (ΦB Y * Y⁻¹) := by
    simp only [map_mul, map_inv]
    calc (ψA (ΦA X))⁻¹ * ψA X = (ψA (ΦA X))⁻¹ * (ψA X * ψB Y) * (ψB Y)⁻¹ := by group
      _ = (ψA (ΦA X))⁻¹ * (ψA (ΦA X) * ψB (ΦB Y)) * (ψB Y)⁻¹ := by rw [h1]
      _ = ψB (ΦB Y) * (ψB Y)⁻¹ := by group
  refine Subgroup.mem_center_iff.2 fun A => hA.injective ?_
  rw [map_mul ψA A, map_mul ψA _ A, h2]
  exact frames_commute hrA hrB A _

private theorem exists_f4_frames (L : Type) [Field L] (Fr : L →+* L)
    (hFr : Function.Bijective Fr) :
    ∃ (ψA ψB : SL(3, L) →* ModGL Tag.F4 L) (σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      IsA2Frame ψA σA ∧ IsA2Frame ψB σB ∧ ψA.range = X1 L ∧ ψB.range = X2 L ∧
      ∃ ΦA ΦB : SL(3, L) →* SL(3, L),
        (∀ X, canonicalRep (coxeterSystem Tag.F4) L QuasiF4.wF4 *
          Units.map (entrywiseHom Fr) (ψA X) *
            (canonicalRep (coxeterSystem Tag.F4) L QuasiF4.wF4)⁻¹ = ψA (ΦA X)) ∧
        ∀ Y, canonicalRep (coxeterSystem Tag.F4) L QuasiF4.wF4 *
          Units.map (entrywiseHom Fr) (ψB Y) *
            (canonicalRep (coxeterSystem Tag.F4) L QuasiF4.wF4)⁻¹ = ψB (ΦB Y) := by
  obtain ⟨πA, hπA⟩ := QuasiF4.long_graph
  obtain ⟨πB, hπB⟩ := QuasiF4.short_graph
  have hA := (f4Long_frame (L := L)).transport f4LongV
  have hB := f4Short_frame (L := L)
  have hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} = S1set :=
    QuasiF4.S₁_eq_chain.symm.trans QuasiF4.S₁_eq
  have hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} = S2set :=
    QuasiF4.S₂_eq_chain.symm.trans QuasiF4.S₂_eq
  obtain ⟨ΦA, hΦA⟩ := exists_frob_frame hA Fr hFr QuasiF4.wF4 πA fun i j hij => by
    show (QuasiF4.wF4 • (f4LongV • chainRoot f4chainLong i j) : Fin Tag.F4.rank → ℤ) =
      f4LongV • chainRoot f4chainLong (πA j) (πA i)
    rw [QuasiF4.w_smul, f4LongV_smul, f4LongV_smul]
    exact hπA i j hij
  obtain ⟨ΦB, hΦB⟩ := exists_frob_frame hB Fr hFr QuasiF4.wF4 πB fun i j hij => by
    rw [QuasiF4.w_smul]
    exact hπB i j hij
  exact ⟨_, _, _, _, hA, hB, by rw [hA.range, hSA], by rw [hB.range, hSB], ΦA.toMonoidHom,
    ΦB.toMonoidHom, hΦA, hΦB⟩

end F4Frames

section Core

open CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

private theorem negHyp_decomp {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3)
    {ψA ψB : SL(3, AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K)}
    {σA : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA)
    (hrA : ψA.range = X1 (AlgebraicClosure K)) (hrB : ψB.range = X2 (AlgebraicClosure K))
    {n : ModGL Tag.F4 (AlgebraicClosure K)}
    {T : ModGL Tag.F4 (AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K)}
    {ΦA ΦB : SL(3, AlgebraicClosure K) →* SL(3, AlgebraicClosure K)}
    (hΦA : ∀ X, n * T (ψA X) * n⁻¹ = ψA (ΦA X)) (hΦB : ∀ Y, n * T (ψB Y) * n⁻¹ = ψB (ΦB Y))
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hfix : ∀ a, n * T (conjBC g a) * n⁻¹ = conjBC g a) {e : adjointGroup Tag.F4 K}
    (he : e ∈ E₀) (he1 : e ≠ 1) (hge : conjBC g e = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)) :
    ∃ x ∈ E₀, x ∉ Subgroup.zpowers e ∧ ∃ X Y, conjBC g x = ψA X * ψB Y ∧ ΦA X = X := by
  classical
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  have hoe : orderOf e = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hE₀.2 e he) he1
  obtain ⟨x₁, hx₁, hx₁e⟩ := exists_mem_not_mem_of_card_lt (E := E₀) (H := Subgroup.zpowers e)
    (by rw [Nat.card_zpowers, hoe, hc]; norm_num)
  obtain ⟨x₂, hx₂, hx₂P⟩ := exists_mem_not_mem_of_card_lt (E := E₀)
    (H := Subgroup.closure ({e, x₁} : Set (adjointGroup Tag.F4 K)))
    (by rw [card_closure_pair_of_not_mem Nat.prime_three hE₀ he hx₁ he1 hx₁e, hc]; norm_num)
  have hx₁P : x₁ ∈ Subgroup.closure ({e, x₁} : Set (adjointGroup Tag.F4 K)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton x₁))
  have hzP : Subgroup.zpowers e ≤ Subgroup.closure ({e, x₁} : Set (adjointGroup Tag.F4 K)) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hdec : ∀ a ∈ E₀, ∃ X Y : SL(3, AlgebraicClosure K), conjBC g a = ψA X * ψB Y ∧
      (ΦA X)⁻¹ * X ∈ Subgroup.center (SL(3, AlgebraicClosure K)) := by
    intro a ha
    refine exists_frame_dec_center hω hA hrA hrB hΦA hΦB (conjBC_mem hg a) ?_ (hfix a)
    rw [← hge, ← map_mul, ← map_mul]
    exact congrArg (conjBC g) (congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, ha⟩ ⟨e, he⟩))
  have hmul : ∀ {a b : adjointGroup Tag.F4 K} {A B C D : SL(3, AlgebraicClosure K)},
      conjBC g a = ψA A * ψB B → conjBC g b = ψA C * ψB D →
        conjBC g (a * b) = ψA (A * C) * ψB (B * D) := by
    intro a b A B C D ha hb
    rw [map_mul, ha, hb, map_mul ψA, map_mul ψB]
    calc ψA A * ψB B * (ψA C * ψB D) = ψA A * (ψB B * ψA C) * ψB D := by group
      _ = ψA A * (ψA C * ψB B) * ψB D := by rw [(frames_commute hrA hrB C B).eq]
      _ = ψA A * ψA C * (ψB B * ψB D) := by group
  obtain ⟨X₁, Y₁, h₁, hc₁⟩ := hdec x₁ hx₁
  obtain ⟨X₂, Y₂, h₂, hc₂⟩ := hdec x₂ hx₂
  have hω' : IsPrimitiveRoot (ω : AlgebraicClosure K) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
  rcases exists_fixed_of_center_defect hω' ΦA hc₁ hc₂ with h | h | h | h
  · exact ⟨x₁, hx₁, hx₁e, X₁, Y₁, h₁, h⟩
  · exact ⟨x₂, hx₂, fun hx => hx₂P (hzP hx), X₂, Y₂, h₂, h⟩
  · refine ⟨x₁ * x₂, mul_mem hx₁ hx₂, fun hx => hx₂P ?_, X₁ * X₂, Y₁ * Y₂, hmul h₁ h₂, h⟩
    have h3 := mul_mem (inv_mem hx₁P) (hzP hx)
    rwa [inv_mul_cancel_left] at h3
  · refine ⟨x₁ * x₂ * x₂, mul_mem (mul_mem hx₁ hx₂) hx₂, fun hx => hx₂P ?_, X₁ * X₂ * X₂,
      Y₁ * Y₂ * Y₂, hmul (hmul h₁ h₂) h₂, h⟩
    have h3 : x₂ * x₂ ∈ Subgroup.closure ({e, x₁} : Set (adjointGroup Tag.F4 K)) := by
      have h4 := mul_mem (inv_mem hx₁P) (hzP hx)
      rwa [mul_assoc, inv_mul_cancel_left] at h4
    have h4 : x₂ = x₂ * x₂ * (x₂ * x₂) := by
      calc x₂ = x₂ ^ 3 * x₂ := by rw [hE₀.2 x₂ hx₂, one_mul]
        _ = x₂ * x₂ * (x₂ * x₂) := by rw [pow_three', mul_assoc (x₂ * x₂) x₂ x₂]
    rw [h4]
    exact mul_mem h3 h3

private theorem negHyp_normalForm {K : Type} [Field K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 3) {ψA ψB : SL(3, AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K)}
    {σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA) (hB : IsA2Frame ψB σB)
    (hrA : ψA.range = X1 (AlgebraicClosure K)) (hrB : ψB.range = X2 (AlgebraicClosure K))
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    {e x y : adjointGroup Tag.F4 K} (hx3 : x ^ 3 = 1)
    (hge : conjBC g e = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)) {X Y : SL(3, AlgebraicClosure K)}
    (hgx : conjBC g x = ψA X * ψB Y) (hgy : conjBC g y = ψA X) :
    ∃ g₁ ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∃ DA DB : SL(3, AlgebraicClosure K),
      (∀ i j : Fin 3, i ≠ j → (DA : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i j = 0) ∧
      (∀ i j : Fin 3, i ≠ j → (DB : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i j = 0) ∧
      DA ^ 3 ∈ Subgroup.center (SL(3, AlgebraicClosure K)) ∧
      conjBC g₁ e = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) ∧
      conjBC g₁ x = ψA DA * ψB DB ∧ conjBC g₁ y = ψA DA := by
  have hω' : IsPrimitiveRoot (ω : AlgebraicClosure K) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
  have hcAB := frames_commute hrA hrB
  have h3 : ψA (X ^ 3) * ψB (Y ^ 3) = 1 := by
    rw [map_pow, map_pow, ← (hcAB X Y).mul_pow, ← hgx, ← map_pow, hx3, map_one]
  have hX3 : X ^ 3 ∈ Subgroup.center (SL(3, AlgebraicClosure K)) := by
    have hXY : ψA (X ^ 3) = ψB (Y ^ 3)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left h3
    refine Subgroup.mem_center_iff.2 fun A => hA.injective ?_
    rw [map_mul ψA A, map_mul ψA _ A, hXY]
    exact hcAB A _
  have hY3 : Y ^ 3 ∈ Subgroup.center (SL(3, AlgebraicClosure K)) := by
    have hYX : ψB (Y ^ 3) = ψA (X ^ 3)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h3
    refine Subgroup.mem_center_iff.2 fun B => hB.injective ?_
    rw [map_mul ψB B, map_mul ψB _ B, hYX]
    exact (hcAB _ B).symm
  have hdiag : ∀ M : SL(3, AlgebraicClosure K),
      M ^ 3 ∈ Subgroup.center (SL(3, AlgebraicClosure K)) → ∃ P : SL(3, AlgebraicClosure K),
        ∀ i j : Fin 3, i ≠ j → ((P * M * P⁻¹ : SL(3, AlgebraicClosure K)) :
          Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i j = 0 := by
    intro M hM
    obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hM
    refine exists_conj_diag_of_pow_three_eq_smul hω' M (ζ := ζ) ?_
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hζ, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  obtain ⟨PA, hPA⟩ := hdiag X hX3
  obtain ⟨PB, hPB⟩ := hdiag Y hY3
  let Ψ : SL(3, AlgebraicClosure K) × SL(3, AlgebraicClosure K) →*
      ModGL Tag.F4 (AlgebraicClosure K) := ψA.noncommCoprod ψB hcAB
  have hΨ : ∀ A B, Ψ (A, B) = ψA A * ψB B := fun _ _ => rfl
  have hΨc : ∀ A B C D, Ψ (C, D) * (ψA A * ψB B) * (Ψ (C, D))⁻¹ =
      ψA (C * A * C⁻¹) * ψB (D * B * D⁻¹) := by
    intro A B C D
    calc Ψ (C, D) * (ψA A * ψB B) * (Ψ (C, D))⁻¹ = Ψ ((C, D) * (A, B) * (C, D)⁻¹) := by
          rw [map_mul, map_mul, map_inv, hΨ, hΨ]
      _ = ψA (C * A * C⁻¹) * ψB (D * B * D⁻¹) := hΨ (C * A * C⁻¹) (D * B * D⁻¹)
  have hΨd : Ψ (PA, PB) * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Ψ (PA, PB) := by
    rw [hΨ]
    exact commute_d_of_mem_sup hω (mul_mem (Subgroup.mem_sup_left (mem_of_range_eq hrA PA))
      (Subgroup.mem_sup_right (mem_of_range_eq hrB PB)))
  have hΨG : Ψ (PA, PB) ∈ adjointGroup Tag.F4 (AlgebraicClosure K) := by
    rw [hΨ]
    exact mem_adjointGroup_of_mem_sup (mul_mem (Subgroup.mem_sup_left (mem_of_range_eq hrA PA))
      (Subgroup.mem_sup_right (mem_of_range_eq hrB PB)))
  have hconj : ∀ a, conjBC (g * (Ψ (PA, PB))⁻¹) a =
      Ψ (PA, PB) * conjBC g a * (Ψ (PA, PB))⁻¹ := by
    intro a
    rw [conjBC_apply, conjBC_apply]
    group
  refine ⟨g * (Ψ (PA, PB))⁻¹, mul_mem hg (inv_mem hΨG), PA * X * PA⁻¹, PB * Y * PB⁻¹, hPA, hPB,
    ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, Subgroup.mem_center_iff.1 hX3 PA, mul_inv_cancel_right]
    exact hX3
  · rw [hconj, hge, hΨd, mul_inv_cancel_right]
  · rw [hconj, hgx, hΨc]
  · rw [hconj, hgy]
    simpa only [map_one, mul_one, mul_inv_cancel] using hΨc X 1 PA PB

private theorem negHyp_close {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hD : IsEmpty (LangPlaneData Tag.F4 K E₀)) {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3)
    {ψA ψB : SL(3, AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K)}
    {σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA) (hB : IsA2Frame ψB σB)
    (hrA : ψA.range = X1 (AlgebraicClosure K)) (hrB : ψB.range = X2 (AlgebraicClosure K))
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    {e x y : adjointGroup Tag.F4 K} (he : e ∈ E₀) (he1 : e ≠ 1) (hx : x ∈ E₀)
    (hxe : x ∉ Subgroup.zpowers e) {DA DB : SL(3, AlgebraicClosure K)}
    (hDA : ∀ i j : Fin 3, i ≠ j → (DA : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i j = 0)
    (hDB : ∀ i j : Fin 3, i ≠ j → (DB : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i j = 0)
    (hDA3 : DA ^ 3 ∈ Subgroup.center (SL(3, AlgebraicClosure K)))
    (hge : conjBC g e = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω))
    (hgx : conjBC g x = ψA DA * ψB DB) (hgy : conjBC g y = ψA DA) :
    ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ D : LangPlaneData Tag.F4 K F,
      ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u := by
  classical
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  set F := Subgroup.closure ({e, x} : Set (adjointGroup Tag.F4 K)) with hFdef
  have heF : e ∈ F := Subgroup.subset_closure (Set.mem_insert _ _)
  have hxF : x ∈ F := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton x))
  have hFE : F ≤ E₀ :=
    (Subgroup.closure_le E₀).2 (Set.insert_subset_iff.2 ⟨he, Set.singleton_subset_iff.2 hx⟩)
  have hFc : Nat.card F = 3 ^ 2 := card_closure_pair_of_not_mem Nat.prime_three hE₀ he hx he1 hxe
  obtain ⟨DF⟩ := planeDatum hnd (fun a ha => hE₀.2 a (hFE ha)) hFc
  have hreg := not_kills_of_le_nonToral_F4 hnd hE₀ hc hD hFE hFc
  have hkills : ∀ α, IsRoot Tag.F4 α → e ∈ killSub g α → x ∉ killSub g α := by
    intro α hα he' hx'
    have hle : F ≤ killSub g α :=
      (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨he', Set.singleton_subset_iff.2 hx'⟩)
    obtain ⟨β, hβ, hk⟩ := exists_kills_of_conj DF hg hα fun a ha => by
      obtain ⟨b, hb, hbα⟩ := mem_killSub.1 (hle ha)
      exact ⟨b, hb.trans (conjBC_apply g a), hbα⟩
    exact hreg DF β hβ hk
  obtain ⟨cA, hcA⟩ := ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup (hA.diag DA hDA)
  obtain ⟨cB, hcB⟩ := ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup (hB.diag DB hDB)
  have hAc : ∀ B, rootDiagUnit Tag.F4 cA * ψB B = ψB B * rootDiagUnit Tag.F4 cA := fun B => by
    rw [hcA]
    exact frames_commute hrA hrB DA B
  have hBc : ∀ A, rootDiagUnit Tag.F4 cB * ψA A = ψA A * rootDiagUnit Tag.F4 cB := fun A => by
    rw [hcB]
    exact (frames_commute hrA hrB A DB).symm
  have hdA : ∀ A, rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * ψA A =
      ψA A * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) := fun A =>
    (commute_d_of_mem_sup hω (Subgroup.mem_sup_left (mem_of_range_eq hrA A))).symm
  have hdB : ∀ B, rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * ψB B =
      ψB B * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) := fun B =>
    (commute_d_of_mem_sup hω (Subgroup.mem_sup_right (mem_of_range_eq hrB B))).symm
  have hxc : rootDiagUnit Tag.F4 (cA * cB) = conjBC g x := by
    rw [CFSG.LieType.Chevalley.rootDiagUnit_mul, hcA, hcB, hgx]
  have hneA : ∀ i j : Fin 3, i ≠ j → (DA : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i i ≠
      (DA : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) j j := by
    intro i j hij hdeq
    refine hkills (σA i j) (hA.isRoot i j hij)
      (mem_killSub.2 ⟨_, hge.symm, rootChar_eq_one_of_frame_commute hA hdA hij⟩)
      (mem_killSub.2 ⟨cA * cB, hxc, ?_⟩)
    rw [rootChar_mul', (rootChar_frame_eq_one_iff hA hDA hcA.symm hij).2 hdeq,
      rootChar_eq_one_of_frame_commute hA hBc hij, one_mul]
  have hneB : ∀ i j : Fin 3, i ≠ j → (DB : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) i i ≠
      (DB : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) j j := by
    intro i j hij hdeq
    refine hkills (σB i j) (hB.isRoot i j hij)
      (mem_killSub.2 ⟨_, hge.symm, rootChar_eq_one_of_frame_commute hB hdB hij⟩)
      (mem_killSub.2 ⟨cA * cB, hxc, ?_⟩)
    rw [rootChar_mul', rootChar_eq_one_of_frame_commute hB hAc hij,
      (rootChar_frame_eq_one_iff hB hDB hcB.symm hij).2 hdeq, one_mul]
  have hy3 : y ^ 3 = 1 := by
    have hDA1 : DA ^ 3 = 1 := pow_three_eq_one_of_diag hDA hneA hDA3
    refine conjBC_injective g ?_
    rw [map_pow, hgy, ← map_pow, hDA1, map_one, map_one]
  have heA : e ∈ killSub g (σA 0 1) := mem_killSub.2 ⟨_, hge.symm,
    rootChar_eq_one_of_frame_commute hA hdA (i := 0) (j := 1) (by decide)⟩
  have heB : e ∈ killSub g (σB 0 1) := mem_killSub.2 ⟨_, hge.symm,
    rootChar_eq_one_of_frame_commute hB hdB (i := 0) (j := 1) (by decide)⟩
  have hyB : y ∈ killSub g (σB 0 1) := mem_killSub.2 ⟨cA, hcA.trans hgy.symm,
    rootChar_eq_one_of_frame_commute hB hAc (i := 0) (j := 1) (by decide)⟩
  have hyA : y ∉ killSub g (σA 0 1) := by
    intro hy
    obtain ⟨b, hb, hbα⟩ := mem_killSub.1 hy
    have hbc : b = cA :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (hb.trans (hgy.trans hcA.symm))
    rw [hbc] at hbα
    exact hneA 0 1 (by decide)
      ((rootChar_frame_eq_one_iff hA hDA hcA.symm (i := 0) (j := 1) (by decide)).1 hbα)
  have hxB : x ∉ killSub g (σB 0 1) := by
    intro hx'
    obtain ⟨b, hb, hbα⟩ := mem_killSub.1 hx'
    have hbc : b = cA * cB := CFSG.LieType.Chevalley.rootDiagUnit_injective (hb.trans hxc.symm)
    rw [hbc, rootChar_mul', rootChar_eq_one_of_frame_commute hB hAc (i := 0) (j := 1)
      (by decide), one_mul] at hbα
    exact hneB 0 1 (by decide)
      ((rootChar_frame_eq_one_iff hB hDB hcB.symm (i := 0) (j := 1) (by decide)).1 hbα)
  have hyF : y ∉ F := by
    intro hyF
    by_cases hye : y ∈ Subgroup.zpowers e
    · exact hyA (Subgroup.zpowers_le.2 heA hye)
    · have hcl : Subgroup.closure ({e, y} : Set (adjointGroup Tag.F4 K)) = F :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le F).2
          (Set.insert_subset_iff.2 ⟨heF, Set.singleton_subset_iff.2 hyF⟩))
          (hFc.trans (card_closure_pair_of_not_mem Nat.prime_three hE₀ he (hFE hyF) he1
            hye).symm).le
      have hxy : x ∈ Subgroup.closure ({e, y} : Set (adjointGroup Tag.F4 K)) := by
        rw [hcl]
        exact hxF
      exact hxB ((Subgroup.closure_le _).2
        (Set.insert_subset_iff.2 ⟨heB, Set.singleton_subset_iff.2 hyB⟩) hxy)
  have hyc : F ≤ Subgroup.centralizer {y} := by
    have h1 : e ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.2 (conjBC_injective g (by
        rw [map_mul, map_mul, hge, hgy]
        exact hdA DA))
    have h2 : x ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.2 (conjBC_injective g (by
        rw [map_mul, map_mul, hgx, hgy, mul_assoc, (frames_commute hrA hrB DA DB).eq]))
    exact (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨h1, Set.singleton_subset_iff.2 h2⟩)
  have hFel : IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => hE₀.2 a (hFE ha)⟩
    have h := congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩)
    exact h
  obtain ⟨hAel, hAc⟩ : IsElemAbelian 3 (F ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(F ⊔ Subgroup.zpowers y) = Nat.card F * 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hyF F.one_mem
    exact CFSG.Quasithin.exists_elemAbelian_sup_zpowers hFel (orderOf_eq_prime hy3 hy1)
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.1 (hyc ha)) hyF
  have hAT : F ⊔ Subgroup.zpowers y ≤
      (torusGroup Tag.F4 (AlgebraicClosure K)).comap (conjBC g) := by
    have h1 : e ∈ (torusGroup Tag.F4 (AlgebraicClosure K)).comap (conjBC g) := by
      show conjBC g e ∈ torusGroup Tag.F4 (AlgebraicClosure K)
      rw [hge]
      exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _
    have h2 : x ∈ (torusGroup Tag.F4 (AlgebraicClosure K)).comap (conjBC g) := by
      show conjBC g x ∈ torusGroup Tag.F4 (AlgebraicClosure K)
      rw [hgx]
      exact mul_mem (hA.diag DA hDA) (hB.diag DB hDB)
    have h3 : y ∈ (torusGroup Tag.F4 (AlgebraicClosure K)).comap (conjBC g) := by
      show conjBC g y ∈ torusGroup Tag.F4 (AlgebraicClosure K)
      rw [hgy]
      exact hA.diag DA hDA
    exact sup_le ((Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨h1, Set.singleton_subset_iff.2 h2⟩)) (Subgroup.zpowers_le.2 h3)
  obtain ⟨DA'⟩ := SeitzExcOpenRest8bAux.langPlaneData_of_toral Nat.prime_three hnd hAel.2 hg
    fun a ha => by
      have h := hAT ha
      rw [Subgroup.mem_comap, conjBC_apply] at h
      exact h
  have hregA : ∀ α, IsRoot Tag.F4 α → ¬ DA'.Kills α := by
    intro α hα hk
    exact hreg ⟨DA'.w, DA'.Fr, DA'.hFr, DA'.g0, DA'.hg0C, DA'.hg0, DA'.c,
      fun a ha => DA'.hc a (Subgroup.mem_sup_left ha)⟩ α hα
      fun a ha => hk a (Subgroup.mem_sup_left ha)
  have hA27 : Nat.card ↥(F ⊔ Subgroup.zpowers y) = 3 ^ 3 := by
    rw [hAc, hFc] <;> norm_num
  have hw := (SeitzExcOpenRest5.f4_regular_datum_w hAel hA27 DA' hregA).2 hK
  refine ⟨F, hFE, relIndex_closure_pair_of_not_mem Nat.prime_three hE₀ hc he hx he1 hxe,
    ⟨DA'.w, DA'.Fr, DA'.hFr, DA'.g0, DA'.hg0C, DA'.hg0, DA'.c,
      fun a ha => DA'.hc a (Subgroup.mem_sup_left ha)⟩, fun u => ?_⟩
  show DA'.w • u = -u
  rw [hw]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul u

private theorem negHyp_core {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hD : IsEmpty (LangPlaneData Tag.F4 K E₀)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3)
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hlang : Units.map (entrywiseHom Fr) g =
      g * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) QuasiF4.wF4)
    {e : adjointGroup Tag.F4 K} (he : e ∈ E₀) (he1 : e ≠ 1)
    (hge : conjBC g e = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)) :
    ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ D : LangPlaneData Tag.F4 K F,
      ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u := by
  have hFb : Function.Bijective Fr := CFSG.LieType.Chevalley.frobenius_bijective Fr hFr
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hrA, hrB, ΦA, ΦB, hΦA, hΦB⟩ :=
    exists_f4_frames (AlgebraicClosure K) Fr hFb
  obtain ⟨n, hn⟩ : ∃ n, n = canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) QuasiF4.wF4 :=
    ⟨_, rfl⟩
  rw [← hn] at hlang hΦA hΦB
  have hfix : ∀ a, n * Units.map (entrywiseHom Fr) (conjBC g a) * n⁻¹ = conjBC g a := by
    intro a
    rw [conjBC_apply, map_mul, map_mul, map_inv, hlang,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr]
    group
  obtain ⟨x, hx, hxe, X, Y, hgx, hXF⟩ :=
    negHyp_decomp hE₀ hc hω hA hrA hrB hΦA hΦB hg hfix he he1 hge
  have hyF : Units.map (entrywiseHom Fr) (g * ψA X * g⁻¹) = g * ψA X * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hlang]
    calc g * n * Units.map (entrywiseHom Fr) (ψA X) * (g * n)⁻¹ =
        g * (n * Units.map (entrywiseHom Fr) (ψA X) * n⁻¹) * g⁻¹ := by group
      _ = g * ψA X * g⁻¹ := by rw [hΦA, hXF]
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1
    (CFSG.RankThree.Chevalley.mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (k := K)
      (Or.inr rfl) Fr hFr hFb (mul_mem (mul_mem hg (mem_adjointGroup_of_mem_sup
        (Subgroup.mem_sup_left (mem_of_range_eq hrA X)))) (inv_mem hg)) hyF)
  have hgy : conjBC g ⟨y, hy⟩ = ψA X := by
    rw [conjBC_apply]
    show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * g = ψA X
    rw [hyb]
    group
  obtain ⟨g₁, hg₁, DA, DB, hDA, hDB, hDA3, hge₁, hgx₁, hgy₁⟩ :=
    negHyp_normalForm hω hA hB hrA hrB hg (hE₀.2 x hx) hge hgx hgy
  exact negHyp_close hK hE₀ hc hD hω hA hB hrA hrB hg₁ he he1 hx hxe hDA hDB hDA3 hge₁ hgx₁ hgy₁

theorem f4NonToralNegHyperplane_holds : F4NonToralNegHyperplane := by
  intro K _ _ hK hs E₀ hE₀ hc _ hD
  classical
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  have h3 := three_le_card_of_threeScope_F4 hs
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨Fr, hFr, g, hgθ, hlang⟩ := exists_lang_algebraicClosure Tag.F4 K QuasiF4.wF4
    (TwClass.w_theta TwClass.f4Six)
  let D₁ : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w :=
    ⟨AlgebraicClosure K, Fr, hFr, g, hgθ, hlang⟩
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
  obtain ⟨z, hz, -, -, -⟩ := f4TwistedFrame_of K hK h3 D₁ ω hω
  obtain ⟨e, he, he1'⟩ := exists_mem_not_mem_of_card_lt (E := E₀) (H := ⊥)
    (by rw [Subgroup.card_bot, hc]; norm_num)
  have he1 : e ≠ 1 := fun h => he1' (Subgroup.mem_bot.2 h)
  have hoe : orderOf e = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hE₀.2 e he) he1
  obtain ⟨e', he', he'e⟩ := exists_mem_not_mem_of_card_lt (E := E₀) (H := Subgroup.zpowers e)
    (by rw [Nat.card_zpowers, hoe, hc]; norm_num)
  have hPE : Subgroup.closure ({e, e'} : Set (adjointGroup Tag.F4 K)) ≤ E₀ :=
    (Subgroup.closure_le E₀).2 (Set.insert_subset_iff.2 ⟨he, Set.singleton_subset_iff.2 he'⟩)
  have hPc := card_closure_pair_of_not_mem Nat.prime_three hE₀ he he' he1 he'e
  have hP3 : ∀ a ∈ Subgroup.closure ({e, e'} : Set (adjointGroup Tag.F4 K)), a ^ 3 = 1 :=
    fun a ha => hE₀.2 a (hPE ha)
  obtain ⟨DP⟩ := planeDatum hnd hP3 hPc
  obtain ⟨c, hcz⟩ := f4PureTwisted_holds K hK h3 D₁ ω hω z hz _ hP3 hPc DP
    (not_kills_of_le_nonToral_F4 hnd hE₀ hc hD hPE hPc DP) e
    (Subgroup.subset_closure (Set.mem_insert _ _)) he1
  have hgG : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K) :=
    parabolicLevi_le_adjointGroup (τ := Tag.F4) (K := AlgebraicClosure K) _ hgθ
  have hcG := baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) c.2
  refine negHyp_core hK hE₀ hc hD Fr hFr hω (mul_mem (inv_mem hcG) hgG) ?_ he he1 ?_
  · rw [map_mul, map_inv, units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr, hlang,
      mul_assoc]
  · calc conjBC ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K))⁻¹ * g) e
          = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * e * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g := by
          rw [conjBC_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
          group
      _ = g⁻¹ * (g * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * g⁻¹) * g := by
          rw [hcz]
          exact congrArg (fun t => g⁻¹ * t * g) hz
      _ = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) := by group

end Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
