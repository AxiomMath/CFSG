module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4Reduce
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphField
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph
open scoped Pointwise

@[expose] def S2019OrthD4GraphType :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q f : ℕ), q.Prime → q ≠ 2 → q ≠ 3 → Nat.card K = q ^ f →
    ∀ α : MulAut (adjointGroup Tag.D4 K), α ^ 3 = 1 →
      ∀ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), ε < 3 → ε ≠ 0 →
        α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε) →
        S2019FixCentralizes 3 α

theorem false_of_three_orbit {G X : Type*} [Group G] [MulAction G X] {F A B : X}
    (hO : ∀ g : G, g • F = F ∨ g • F = A ∨ g • F = B) {t ι δ s : G} (ht3 : t ^ 3 = 1)
    (htF : t • F ≠ F) (hι : ∀ g : G, ι • (g • F) = g • F)
    (hδ : ∀ g : G, (δ * δ) • (g • F) = g • F) (hsF : s • F = F) (hs3 : s ^ 3 = 1)
    (ht : t = ι * δ * s) : False := by
  set a := t • F with ha
  set b := (t * t) • F with hb
  have htb : t • b = F := by rw [hb, ← mul_smul, ← pow_three, ht3, one_smul]
  have hbF : b ≠ F := by
    intro h
    apply htF
    rw [h] at htb
    exact htb
  have hab : a ≠ b := by
    intro h
    apply htF
    have h1 : t • F = t • (t • F) := by rw [ha, hb, mul_smul] at h; exact h
    exact (smul_left_cancel t h1).symm
  have hO' : ∀ g : G, g • F = F ∨ g • F = a ∨ g • F = b := by
    intro g
    rcases hO t with h1 | h1 | h1
    · exact absurd h1 htF
    · rcases hO (t * t) with h2 | h2 | h2
      · exact absurd h2 hbF
      · exact absurd (h1.trans h2.symm) hab
      · rcases hO g with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (h.trans h1.symm))
        · exact Or.inr (Or.inr (h.trans h2.symm))
    · rcases hO (t * t) with h2 | h2 | h2
      · exact absurd h2 hbF
      · rcases hO g with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (h.trans h2.symm))
        · exact Or.inr (Or.inl (h.trans h1.symm))
      · exact absurd (h1.trans h2.symm) hab
  have hsa : s • a = a := by
    have h1 : s • a = (s * t) • F := by rw [ha, mul_smul]
    have h2 : s • b = (s * (t * t)) • F := by
      rw [hb]
      exact (mul_smul _ _ _).symm
    have hsaF : s • a ≠ F := fun h => htF (smul_left_cancel s (h.trans hsF.symm))
    have hsbF : s • b ≠ F := fun h => hbF (smul_left_cancel s (h.trans hsF.symm))
    rcases hO' (s * t) with h | h | h
    · exact absurd (h1.trans h) hsaF
    · exact h1.trans h
    · exfalso
      have hsab : s • a = b := h1.trans h
      have hsb : s • b = a := by
        rcases hO' (s * (t * t)) with h' | h' | h'
        · exact absurd (h2.trans h') hsbF
        · exact h2.trans h'
        · exact absurd (smul_left_cancel s (hsab.trans (h2.trans h').symm)) hab
      have h3 : (s ^ 3) • a = b := by
        rw [pow_three, mul_smul, mul_smul, hsab, hsb, hsab]
      rw [hs3, one_smul] at h3
      exact hab h3
  have hδF : δ • F = a := by
    rw [ha, ht, mul_smul, mul_smul, hsF, hι δ]
  have hδa : δ • a = b := by
    have h1 : t • a = b := by rw [ha, hb, mul_smul]
    rw [← h1, ht, mul_smul, mul_smul, hsa]
    have h2 : δ • a = (δ * t) • F := by rw [ha, mul_smul]
    rw [h2, hι (δ * t)]
  have h1 := hδ 1
  rw [one_smul, mul_smul, hδF, hδa] at h1
  exact hbF h1

section Reduce


private theorem exactNormalAut_eq_mul_entrywise {K : Type} [Field K] (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) :
    exactNormalAut Tag.D4 K a σ 0 =
      exactNormalAut Tag.D4 K a 1 0 * entrywiseAdjointAut Tag.D4 σ := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_exactNormalAut, coe_exactNormalAut, coe_entrywiseAdjointAut]
  have hid : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
      (Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K)) =
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K) :=
    Units.ext (entrywise_id _)
  rw [hid]

private theorem normalAut_one_sq {K : Type} [Field K] (a : Fin Tag.D4.rank → Kˣ) :
    exactNormalAut Tag.D4 K a 1 0 * exactNormalAut Tag.D4 K a 1 0 =
      MulAut.conj (⟨rootDiagUnit Tag.D4 (fun j => a j ^ 2),
        rootDiagUnit_sq_mem_adjointGroup_D4 a⟩ : ↥(adjointGroup Tag.D4 K)) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have hid : ∀ x : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : exactQ Tag.D4 K 0 = 1 := rfl
  have hsq : rootDiagUnit Tag.D4 (fun j => a j ^ 2) =
      rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 a := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext j
    rw [Pi.mul_apply, sq]
  rw [MulAut.mul_apply, coe_exactNormalAut, coe_exactNormalAut, hid, hid, hQ, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ = rootDiagUnit Tag.D4 (fun j => a j ^ 2) * _ * (rootDiagUnit Tag.D4 (fun j => a j ^ 2))⁻¹
  rw [hsq]
  group

private theorem conj_mul_eq_mul_conj {P : Type*} [Group P] (β : MulAut P) (y : P) :
    MulAut.conj y * β = β * MulAut.conj (β⁻¹ y) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_graph_normalForm_of_not_mem_matrixProjectiveImage (K : Type) [Field K] [Finite K]
    (q f : ℕ) (hq : q.Prime) (hK : Nat.card K = q ^ f)
    (t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (ht3 : t ^ 3 = 1)
    (htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      ε ≠ 0 ∧ σ ^ 3 = 1 ∧
      MulAut.congr (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm t =
        MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  set Φ : adjointGroup Tag.D4 K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K (isoAdj K).symm with hΦ
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    Finite.of_equiv _ Φ.toEquiv
  set α := MulAut.congr Φ.symm t with hαdef
  have htα : t = MulAut.congr Φ α :=
    MulEquiv.ext fun x => by simp [hαdef, MulAut.congr_apply]
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, ht3, map_one]
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  refine ⟨g, a, σ, ε, hε, fun hε0 => ?_, hσ3, hαeq⟩
  subst hε0
  have hEA : projectivePointFamilyAut (coordinateQuadPlus 4 K) =
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    let e0 : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)) :=
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedProjectiveReindexEquiv
        (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm
    have hm : CFSG.Open.StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
        .POmegaPlus 4 q f :=
      ⟨⟨hq, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
    exact coordinate_plus_family_eq_matrixImage hm K hK e0
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hFdef
  have hE : ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) → γ • F = F := by
    intro γ hγ
    rw [← hEA, mem_projectivePointFamilyAut_iff] at hγ
    exact hγ
  have hO : ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      γ • F = F ∨ γ • F = plusCX 4 K ∨ γ • F = plusCXstar 4 K (by norm_num) := by
    intro γ
    have h1 := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
      (MulAction.mem_orbit F γ)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  have htF : t • F ≠ F := by
    intro h1
    apply htE
    rw [← hEA, mem_projectivePointFamilyAut_iff]
    exact h1
  have hinner : ∀ y : matrixProjectiveDerived (coordinateQuadPlus 4 K),
      ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        MulAut.conj y • (γ • F) = γ • F := by
    intro y γ
    rw [← mul_smul, conj_mul_eq_mul_conj, mul_smul,
      hE _ (CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _)]
  have hcongr_conj : ∀ x : adjointGroup Tag.D4 K, MulAut.congr Φ (MulAut.conj x) =
      MulAut.conj (Φ x) := fun x =>
    MulEquiv.ext fun y => by simp [MulAut.congr_apply, MulAut.conj_apply]
  have hαdec : α = MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 *
      entrywiseAdjointAut Tag.D4 σ := by
    rw [hαeq]
    have h0 : d4Graph K 0 = 1 :=
      MulEquiv.ext fun x => Subtype.ext (by rw [coe_d4Graph, pow_zero, one_mul, inv_one,
        mul_one, MulAut.one_apply])
    rw [h0, mul_one, exactNormalAut_eq_mul_entrywise, mul_assoc]
  have hts : t = MulAut.congr Φ (MulAut.conj g) *
      MulAut.congr Φ (exactNormalAut Tag.D4 K a 1 0) *
        MulAut.congr Φ (entrywiseAdjointAut Tag.D4 σ) := by
    rw [htα, hαdec, map_mul, map_mul]
  refine false_of_three_orbit hO ht3 htF (fun γ => ?_) (fun γ => ?_)
    (hE _ (congr_entrywiseAdjointAut_mem σ)) ?_ hts
  · rw [hcongr_conj]
    exact hinner _ γ
  · rw [← map_mul, normalAut_one_sq, hcongr_conj]
    exact hinner _ γ
  · rw [← map_pow, ← entrywiseAdjointAut_pow, hσ3, entrywiseAdjointAut_one, map_one]

theorem s2019OrthD4Graph_of_graphType (h : S2019OrthD4GraphType) : S2019OrthD4Graph := by
  intro K _ _ q f hq hq2 hq3 hK t ht3 htE
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  set Φ : adjointGroup Tag.D4 K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K (isoAdj K).symm with hΦ
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    Finite.of_equiv _ Φ.toEquiv
  set α := MulAut.congr Φ.symm t with hαdef
  refine s2019FixCentralizes_of_congr Nat.prime_three Φ.symm t ?_
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, ht3, map_one]
  obtain ⟨g, a, σ, ε, hε, hε0, -, hαeq⟩ :=
    exists_graph_normalForm_of_not_mem_matrixProjectiveImage K q f hq hK t ht3 htE
  by_cases hσ1 : σ = 1
  · subst hσ1
    exact h K q f hq hq2 hq3 hK α hα3 g a ε hε hε0 hαeq
  · exact s2019FixCentralizes_d4_graphField hq2 K hK α hα3 g a σ ε hε hε0 hσ1 hαeq

theorem s2019OrthD4Outer_of_graphType (h : S2019OrthD4GraphType) : S2019OrthD4Outer :=
  s2019OrthD4Outer_of_graph (s2019OrthD4Graph_of_graphType h)

end Reduce

end CFSG.LocalAnalysis.GLTheoremA.S2019
