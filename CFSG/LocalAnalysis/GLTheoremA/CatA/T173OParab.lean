module

public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLocal
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType


private theorem exists_conj_graphFixedRootBorel_le_map_conj {K : Type} [Field K] [Finite K]
    [CharP K 2] {t : TwistTag} {σ : K ≃+* K}
    (hHolds : CFSG.LieType.BorelTits.Holds ↥(graphFixedRootGroup t K σ.toRingHom) 2)
    {R : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ∃ (g : ↥(graphFixedRootGroup t K σ.toRingHom))
      (P : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)), P ≠ ⊤ ∧
      Subgroup.normalizer (R : Set ↥(graphFixedRootGroup t K σ.toRingHom)) ≤ P ∧
      (graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom) ≤
        P.map (MulAut.conj g⁻¹).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := hHolds R hR hR2
  let C : Subgroup (ModGL t.tag K) := graphFixedRootGroup t K σ.toRingHom
  let U : Subgroup C := (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf C
  have hUp : IsPGroup 2 U := isPGroup_graphFixedPosUnipotent_subgroupOf 2
  have hUi : ¬ 2 ∣ U.index := not_dvd_index_graphFixedPosUnipotent 2 σ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C (hUp.toSylow hUi) S
  have hSeq : (S : Subgroup C) = U.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hB₀N : (graphFixedRootBorel t K σ.toRingHom).subgroupOf C ≤
      Subgroup.normalizer ((U : Subgroup C) : Set C) := by
    intro b hb
    have hb' : (b : ModGL t.tag K) ∈ graphFixedRootBorel t K σ.toRingHom := hb
    have hmem : b ∈ (Subgroup.normalizer (graphFixedPosUnipotent t K σ.toRingHom :
        Set (ModGL t.tag K))).subgroupOf C :=
      graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'
    rwa [Subgroup.subgroupOf_normalizer_eq (graphFixedPosUnipotent_le_graphFixedRootGroup t K
      σ.toRingHom)] at hmem
  refine ⟨g, P, hPtop, hNR, ?_⟩
  intro b hb
  have h1 : (MulAut.conj g).toMonoidHom b ∈ P := by
    apply hNS
    rw [hSeq]
    exact Subgroup.le_normalizer_map _ ⟨b, hB₀N hb, rfl⟩
  exact Subgroup.mem_map.2 ⟨(MulAut.conj g).toMonoidHom b, h1, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

private theorem exists_graphFixedParabolic_of_borel_le {K : Type} [Field K] {t : TwistTag}
    {σ : K ≃+* K} {P : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)} (hPtop : P ≠ ⊤)
    (hB : (graphFixedRootBorel t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom) ≤ P) :
    ∃ J : Set (Fin t.foldedTag.rank), J ≠ Set.univ ∧
      P.map (graphFixedRootGroup t K σ.toRingHom).subtype ≤
        graphFixedParabolic t K σ.toRingHom J := by
  let C : Subgroup (ModGL t.tag K) := graphFixedRootGroup t K σ.toRingHom
  let A : Subgroup (ModGL t.tag K) := P.map C.subtype
  have hBA : graphFixedRootBorel t K σ.toRingHom ≤ A := fun b hb =>
    ⟨⟨b, graphFixedRootBorel_le t K σ.toRingHom hb⟩, hB (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hAC : A ≤ C := Subgroup.map_subtype_le _
  obtain ⟨-, J, hAJ, -⟩ := fixed_Borel_overgroup_classification t K σ A hBA hAC
  have hJne : J ≠ Set.univ := by
    intro hJ
    apply hPtop
    have hAtop : A = C := by
      rw [hAJ, hJ]
      exact (fixed_standard_parabolic_cells t K σ).2.2.2.2.2
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL t.tag K) ∈ A := by rw [hAtop]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subtype.ext hyx] at hy
    exact hy
  exact ⟨J, hJne, le_of_eq hAJ⟩

theorem exists_conj_normalizer_le_graphFixedParabolic {K : Type} [Field K] [Finite K]
    [CharP K 2] {t : TwistTag} {σ : K ≃+* K}
    (hHolds : CFSG.LieType.BorelTits.Holds ↥(graphFixedRootGroup t K σ.toRingHom) 2)
    {R : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ∃ (g : ↥(graphFixedRootGroup t K σ.toRingHom)) (J : Set (Fin t.foldedTag.rank)),
      J ≠ Set.univ ∧
      ((Subgroup.normalizer (R : Set ↥(graphFixedRootGroup t K σ.toRingHom))).map
          (MulAut.conj g).toMonoidHom).map (graphFixedRootGroup t K σ.toRingHom).subtype ≤
        graphFixedParabolic t K σ.toRingHom J := by
  obtain ⟨g, P, hPtop, hNR, hB⟩ :=
    exists_conj_graphFixedRootBorel_le_map_conj hHolds hR hR2
  let P' : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom) := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hPtop
    apply Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    change P' = (⊤ : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)).map
      (MulAut.conj g⁻¹).toMonoidHom
    rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective]
  obtain ⟨J, hJne, hle⟩ := exists_graphFixedParabolic_of_borel_le hP'ne hB
  refine ⟨g⁻¹, J, hJne, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hz
  exact hle ⟨_, (Subgroup.map_mono hNR) (Subgroup.mem_map_of_mem _ hy), rfl⟩

theorem exists_conj_le_graphFixedParabolicLevi {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : TwistTag} (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (ModGL t.tag K)} (hE : E ≤ graphFixedParabolic t K σ.toRingHom J)
    (hEp : IsPGroup p E) :
    ∃ y ∈ graphFixedParabolic t K σ.toRingHom J,
      E.map (MulAut.conj y).toMonoidHom ≤ graphFixedParabolicLevi t K σ.toRingHom J := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨-, -, -, -, -, -, -, -, hQP, -, hLP, huniq, -, -, -, -, hQgrp, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hQ2 : IsPGroup 2 (graphFixedParabolicRadical t K σ.toRingHom J) := hQgrp 2
  have hcard := F4Rest.card_eq_mul_of_existsUnique hQP hLP huniq
  have hQp : ¬ p ∣ Nat.card (graphFixedParabolicRadical t K σ.toRingHom J) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨y, hyP, hyL⟩ :=
    F4Rest.exists_conj_le_of_card_eq_mul hLP hcard hQp hE hEp
  exact ⟨y, hyP, hyL⟩

private theorem exists_conj_borelGroup_le_map_conj (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] {R : Subgroup ↥(adjointGroup τ K)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ∃ (g : ↥(adjointGroup τ K)) (P : Subgroup ↥(adjointGroup τ K)), P ≠ ⊤ ∧
      Subgroup.normalizer (R : Set ↥(adjointGroup τ K)) ≤ P ∧
      (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤
        P.map (MulAut.conj g⁻¹).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := holds_adjointGroup_tag τ K 2 R hR hR2
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    CFSG.RankThree.PartOne.KFU.borelGroup_le_adjointGroup' τ
  have hUC : posUnipotent τ K ≤ adjointGroup τ K := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  set U : Subgroup (↥(adjointGroup τ K)) :=
    (posUnipotent τ K).subgroupOf (adjointGroup τ K) with hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup τ K) (hUp.toSylow hUi) S
  have hSeq : (S : Subgroup ↥(adjointGroup τ K)) = U.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, P, hPtop, hNR, ?_⟩
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (U : Set ↥(adjointGroup τ K)) :=
    CFSG.RankThree.PartOne.KFU.borelGroup_subgroupOf_le_normalizer τ hb
  have h1 : (MulAut.conj g).toMonoidHom b ∈ P := by
    apply hNS
    rw [hSeq]
    exact Subgroup.le_normalizer_map _ ⟨b, hbN, rfl⟩
  exact Subgroup.mem_map.2 ⟨(MulAut.conj g).toMonoidHom b, h1, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

theorem exists_conj_normalizer_le_parabolicSubgroup (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] {R : Subgroup ↥(adjointGroup τ K)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ∃ (g : ↥(adjointGroup τ K)) (J : Set (Fin τ.rank)), J ≠ Set.univ ∧
      ((Subgroup.normalizer (R : Set ↥(adjointGroup τ K))).map (MulAut.conj g).toMonoidHom).map
        (adjointGroup τ K).subtype ≤ parabolicSubgroup τ K J := by
  obtain ⟨g, P, hPtop, hNR, hB⟩ := exists_conj_borelGroup_le_map_conj τ hR hR2
  let P' : Subgroup ↥(adjointGroup τ K) := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hPtop
    apply Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    change P' = (⊤ : Subgroup ↥(adjointGroup τ K)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective]
  obtain ⟨J, hJ, hJP⟩ := CFSG.RankThree.PartOne.KFU.exists_parabolic_of_borel_le τ P' hB hP'ne
  refine ⟨g⁻¹, J, hJ, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hz
  exact hJP _ ((Subgroup.map_mono hNR) (Subgroup.mem_map_of_mem _ hy))

theorem exists_conj_le_parabolicLevi (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    (J : Set (Fin τ.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (ModGL τ K)}
    (hE : E ≤ parabolicSubgroup τ K J) (hEp : IsPGroup p E) :
    ∃ y ∈ parabolicSubgroup τ K J, E.map (MulAut.conj y).toMonoidHom ≤ parabolicLevi τ K J := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hQP, -, -, hLP, -, -, huniq, -, -, -, -, -, hQgrp⟩ :=
    parabolic_root_radical_Levi_factors τ K J
  have hQ2 : IsPGroup 2 (parabolicRadical τ K J) := (hQgrp 2).2.1
  have hcard := F4Rest.card_eq_mul_of_existsUnique hQP hLP huniq
  have hQp : ¬ p ∣ Nat.card (parabolicRadical τ K J) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨y, hyP, hyL⟩ := F4Rest.exists_conj_le_of_card_eq_mul hLP hcard hQp hE hEp
  exact ⟨y, hyP, hyL⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
