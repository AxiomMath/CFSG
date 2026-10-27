module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (specialImage specialRho)
open scoped MatrixGroups

section Product

variable {G : Type*} [Group G]

theorem exists_mul_of_card_le {X Y S : Subgroup G} [Finite S] [Finite X] [Finite Y]
    (hXS : X ≤ S) (hYS : Y ≤ S)
    (hXY : X ≤ centralizer (Y : Set G)) (hdisj : X ⊓ Y = ⊥)
    (hcard : Nat.card S ≤ Nat.card X * Nat.card Y) :
    ∀ s ∈ S, ∃ x ∈ X, ∃ y ∈ Y, s = x * y := by
  have hcomm : ∀ (a : X) (b : Y), Commute (X.subtype a) (Y.subtype b) := fun a b =>
    (mem_centralizer_iff.mp (hXY a.2) b b.2).symm
  set μ : X × Y →* G := X.subtype.noncommCoprod Y.subtype hcomm with hμ
  have hμapp : ∀ p : X × Y, μ p = (p.1 : G) * p.2 := fun p => rfl
  have hinj : Function.Injective μ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker, hμapp] at hab
    have ha : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have haY : (a : G) ∈ Y := ha ▸ inv_mem b.2
    have ha1 : (a : G) = 1 := by
      have h : (a : G) ∈ X ⊓ Y := ⟨a.2, haY⟩
      rwa [hdisj, mem_bot] at h
    have hb1 : (b : G) = 1 := by
      rw [ha1, eq_comm, inv_eq_one] at ha
      exact ha
    rw [mem_bot]
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hrange : μ.range ≤ S := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hμapp]
    exact mul_mem (hXS a.2) (hYS b.2)
  have hcardR : Nat.card μ.range = Nat.card X * Nat.card Y := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]
  have heq : μ.range = S := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardR]; exact hcard)
  intro s hs
  rw [← heq] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, hμapp _⟩

end Product

theorem center_SL2_eq_bot_of_charTwo {K : Type*} [Field K] [CharP K 2] :
    center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin, _root_.sq] at hr
  rw [eq_one_of_mul_self_eq_one hr, map_one] at hrA
  rw [mem_bot]
  exact Subtype.ext hrA.symm

section Bar

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {P₁ P₂ : HypPair Q}

@[expose] noncomputable def leviFixBar (P₁ P₂ : HypPair Q) : Subgroup (matrixProjectiveDerived Q) :=
  ((leviFix (orthDerived Q) P₁ P₂).subgroupOf (orthDerived Q)).map (projHom Q)

omit [Finite K] [CharP K 2] in
theorem leviFix_le_orthDerived : leviFix (orthDerived Q) P₁ P₂ ≤ orthDerived Q :=
  fun _ h => (mem_leviFix.mp h).1

@[expose] noncomputable def leviFixBarEquivFix (hQ' : ∃ v, Q v ≠ 0) :
    leviFixBar P₁ P₂ ≃* leviFix (orthDerived Q) P₁ P₂ :=
  (((leviFix (orthDerived Q) P₁ P₂).subgroupOf (orthDerived Q)).equivMapOfInjective (projHom Q)
    (projHom_injective hQ')).symm.trans (Subgroup.subgroupOfEquivOfLe leviFix_le_orthDerived)

@[expose] noncomputable def leviFixBarEquiv (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQ' : ∃ v, Q v ≠ 0) : leviFixBar P₁ P₂ ≃* SL(2, K) :=
  (leviFixBarEquivFix hQ').trans (leviFixEquiv P₁ P₂ h₁₂ (eichler_mem_orthDerived hQ hT))

theorem card_leviFixBar (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQ' : ∃ v, Q v ≠ 0) : Nat.card (leviFixBar P₁ P₂) = Nat.card SL(2, K) :=
  Nat.card_congr (leviFixBarEquiv h₁₂ hQ hT hQ').toEquiv

omit [Finite K] [CharP K 2] in
theorem projHom_mem_leviFixBar {g : orthDerived Q}
    (hg : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ leviFix (orthDerived Q) P₁ P₂) :
    projHom Q g ∈ leviFixBar P₁ P₂ :=
  ⟨g, mem_subgroupOf.mpr hg, rfl⟩

omit [Finite K] in
theorem projLift_mem_leviFix (hQ' : ∃ v, Q v ≠ 0) {x : matrixProjectiveDerived Q}
    (hx : x ∈ leviFixBar P₁ P₂) : projLift hQ' x ∈ leviFix (orthDerived Q) P₁ P₂ :=
  projLift_mem_of_mem_map hQ' hx

omit [Finite K] [CharP K 2] in
theorem map_projHom_le_centralizer {H₁ H₂ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (h : H₁ ≤ centralizer (H₂ : Set ((Fin d → K) ≃ₗ[K] (Fin d → K)))) :
    (H₁.subgroupOf (orthDerived Q)).map (projHom Q) ≤
      centralizer (((H₂.subgroupOf (orthDerived Q)).map (projHom Q) : Subgroup _) :
        Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨X, hX, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨Y, hY, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_iff.mp (h (mem_subgroupOf.mp hX)) _ (mem_subgroupOf.mp hY)

omit [CharP K 2] in
theorem leviFixBar_le_centralizer_flip (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    leviFixBar P₁ P₂ ≤ centralizer (leviFixBar P₁ (flipPair P₂) : Set (matrixProjectiveDerived Q)) :=
  map_projHom_le_centralizer (leviFix_le_centralizer_flip h₁₂ (eichler_mem_orthDerived hQ hT)
    (eichler_mem_orthDerived hQ hT))

omit [Finite K] [CharP K 2] in
theorem leviFixBar_le_centralizer_of_orth {P₃ P₄ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄) (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄) :
    leviFixBar P₁ P₂ ≤ centralizer (leviFixBar P₃ P₄ : Set (matrixProjectiveDerived Q)) :=
  map_projHom_le_centralizer (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ _ _)

theorem leviFixBar_inf_flip_eq_bot (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQ' : ∃ v, Q v ≠ 0) : leviFixBar P₁ P₂ ⊓ leviFixBar P₁ (flipPair P₂) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwX, hwY⟩
  have hYX := le_centralizer_iff.mp (leviFixBar_le_centralizer_flip h₁₂ hQ hT)
  have hcen : (⟨w, hwX⟩ : leviFixBar P₁ P₂) ∈ center (leviFixBar P₁ P₂) := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hYX hwY) x x.2)
  set ε := leviFixBarEquiv h₁₂ hQ hT hQ' with hε
  have h1 : ε ⟨w, hwX⟩ ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) y']
  rw [center_SL2_eq_bot_of_charTwo, mem_bot] at h1
  have h2 : (⟨w, hwX⟩ : leviFixBar P₁ P₂) = 1 := ε.injective (by rw [h1, map_one])
  rw [mem_bot]
  exact congrArg Subtype.val h2

theorem exists_mul_of_mem_rootLeviBar {a a' b b' : Fin d} (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {m : matrixProjectiveDerived Q} (hm : m ∈ rootLeviBar Q ha.hypPair hb.hypPair) :
    ∃ x ∈ leviFixBar ha.hypPair hb.hypPair, ∃ y ∈ stabPairsBar Q a a' b b', m = x * y := by
  have h₁₂ := ha.orth hb hd
  have hQ' := ha.exists_ne_zero
  set M := projLift hQ' m with hMdef
  have hML : M ∈ rootLevi Q ha.hypPair hb.hypPair := projLift_mem_of_mem_map hQ' hm
  have hMΩ : M ∈ orthDerived Q := projLift_mem_orthDerived hQ' m
  have hMc := mem_centralizer_singleton_iff.mp hML.1.2
  obtain ⟨⟨g, hg⟩, hgM⟩ := leviCoeff_surjective h₁₂ (eichler_mem_orthDerived hQ hT)
    ⟨planeCoeff ha.hypPair hb.hypPair M, det_planeCoeff h₁₂ hML.1.1 hMc⟩
  have hgM' : planeCoeff ha.hypPair hb.hypPair g = planeCoeff ha.hypPair hb.hypPair M :=
    congrArg Subtype.val hgM
  obtain ⟨-, hgL, -⟩ := mem_leviFix.mp hg
  have hgΩ : g ∈ orthDerived Q := (mem_leviFix.mp hg).1
  obtain ⟨g1, g2⟩ := planeCoeff_apply_e h₁₂ (leviFix_commute_e hg)
  obtain ⟨m1, m2⟩ := planeCoeff_apply_e h₁₂ hMc
  rw [hgM'] at g1 g2
  set n := g⁻¹ * M with hn
  have hnL : n ∈ rootLevi Q ha.hypPair hb.hypPair := mul_mem (inv_mem hgL) hML
  have hnΩ : n ∈ orthDerived Q := mul_mem (inv_mem hgΩ) hMΩ
  have n1 : n ha.hypPair.e = ha.hypPair.e := by
    rw [hn, LinearEquiv.mul_apply, m1, ← g1, LinearEquiv.inv_apply_apply']
  have n2 : n hb.hypPair.e = hb.hypPair.e := by
    rw [hn, LinearEquiv.mul_apply, m2, ← g2, LinearEquiv.inv_apply_apply']
  obtain ⟨n3, n4⟩ := apply_f_of_mem_rootLevi h₁₂ hnL n1 n2
  refine ⟨projHom Q ⟨g, hgΩ⟩, projHom_mem_leviFixBar hg, projHom Q ⟨n, hnΩ⟩,
    ⟨⟨n, hnΩ⟩, mem_subgroupOf.mpr ⟨⟨n1, n3⟩, n2, n4⟩, rfl⟩, ?_⟩
  rw [← map_mul]
  have he : (⟨g, hgΩ⟩ : orthDerived Q) * ⟨n, hnΩ⟩ = ⟨M, hMΩ⟩ := by
    apply Subtype.ext
    change g * (g⁻¹ * M) = M
    group
  rw [he]
  exact (projHom_projLift hQ' m).symm

end Bar

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
noncomputable abbrev plusPair (k : Fin 4) : HypPair (coordinateQuadPlus 4 K) :=
  (isHypCoord_coordinateQuadPlus (K := K) (n := 4) k).hypPair

omit [Finite K] [CharP K 2] in
theorem plusPair_orth {i j : Fin 4} (hij : i ≠ j) : (plusPair K i).Orth (plusPair K j) :=
  (isHypCoord_coordinateQuadPlus i).orth (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hij)

omit [Finite K] [CharP K 2] in
theorem plusPair_orth_flip {i j : Fin 4} (hij : i ≠ j) :
    (plusPair K i).Orth (flipPair (plusPair K j)) :=
  (isHypCoord_coordinateQuadPlus i).orth (isHypCoord_coordinateQuadPlus j).symm
    (pairDisjoint_plus hij).swap_right

theorem card_stabTwoBar_le_four (hq : 4 ≤ Nat.card K) {i j : Fin 4} (hij : i ≠ j) :
    Nat.card (stabTwoBar K i j) ≤ Nat.card SL(2, K) ^ 2 := by
  classical
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := 4 - 1) (by omega : 4 - 1 + 1 = 4) hij.symm
  obtain ⟨hR, hdim, hS⟩ := splitFour_plusPerp_three (K := K) j'
  have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hq
  have φ := (stabTwoBarEquiv (K := K) (n := 4) (by omega) hj').trans
    ((isHypCoord_coordinateQuadPlus (K := K) (n := 4 - 1) j').stabDerivedEquivOfLe
      (regular_coordinateQuadPlus (4 - 1) K (by omega)).1 hR hΩ)
  rw [Nat.card_congr φ.toEquiv]
  have hq2 : Nat.card K ≠ 2 := by omega
  have hq3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, -, -, hcov4, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      _ hR (Or.inr (Or.inr ⟨hdim, hS⟩))
  obtain ⟨-, e, -, -, hcomm, -⟩ := hcov4 hdim hS hq2 hq3
  have hJ : commutator (TauCeti.QuadraticMap.orthogonalGroup ((coordinateQuadPlus 3 K).comp
      (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype)) =
      (specialImage K).map e.symm.toMonoidHom := by
    rw [hcomm, ← Subgroup.map_sup, CFSG.LocalAnalysis.ComponentInitial.determinantFactors_sup]
  have hder : (commutator (TauCeti.QuadraticMap.orthogonalGroup ((coordinateQuadPlus 3 K).comp
      (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype))).map
      (TauCeti.QuadraticMap.orthogonalGroup ((coordinateQuadPlus 3 K).comp
        (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype)).subtype =
      orthDerived ((coordinateQuadPlus 3 K).comp
        (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype) := by
    rw [Subgroup.map_subtype_commutator]
  calc Nat.card (orthDerived ((coordinateQuadPlus 3 K).comp
        (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype))
      = Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup ((coordinateQuadPlus 3 K).comp
          (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype))) := by
        rw [← hder, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    _ = Nat.card (specialImage K) := by
        rw [hJ, Subgroup.card_map_of_injective e.symm.injective]
    _ ≤ Nat.card (SL(2, K) × SL(2, K)) :=
        Nat.card_le_card_of_surjective _ (specialRho (K := K)).rangeRestrict_surjective
    _ = Nat.card SL(2, K) ^ 2 := by rw [Nat.card_prod, _root_.sq]

omit [Finite K] [CharP K 2] in
theorem leviFixBar_le_stabTwoBar_of_orth {i j : Fin 4} {P₃ P₄ : HypPair (coordinateQuadPlus 4 K)}
    (h13 : (plusPair K i).Orth P₃) (h14 : (plusPair K i).Orth P₄) (h23 : (plusPair K j).Orth P₃)
    (h24 : (plusPair K j).Orth P₄) : leviFixBar P₃ P₄ ≤ stabTwoBar K i j := by
  rintro _ ⟨X, hX, rfl⟩
  refine ⟨X, mem_subgroupOf.mpr ?_, rfl⟩
  obtain ⟨-, -, hW⟩ := mem_leviFix.mp (mem_subgroupOf.mp hX)
  obtain ⟨a1, a2⟩ := inW_of_orth h13 h14
  obtain ⟨b1, b2⟩ := inW_of_orth h23 h24
  exact ⟨⟨hW _ a1, hW _ a2⟩, hW _ b1, hW _ b2⟩

theorem exists_mul_of_mem_stabTwoBar (hq : 4 ≤ Nat.card K) {i j k l : Fin 4} (hij : i ≠ j)
    (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    {x : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hx : x ∈ stabTwoBar K i j) :
    ∃ y ∈ leviFixBar (plusPair K k) (plusPair K l),
      ∃ z ∈ leviFixBar (plusPair K k) (flipPair (plusPair K l)), x = y * z := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have hkl' := plusPair_orth (K := K) hkl
  refine exists_mul_of_card_le
    (leviFixBar_le_stabTwoBar_of_orth (plusPair_orth hik) (plusPair_orth hil) (plusPair_orth hjk)
      (plusPair_orth hjl))
    (leviFixBar_le_stabTwoBar_of_orth (plusPair_orth hik) (plusPair_orth_flip hil)
      (plusPair_orth hjk) (plusPair_orth_flip hjl))
    (leviFixBar_le_centralizer_flip hkl' hQ hT) (leviFixBar_inf_flip_eq_bot hkl' hQ hT hQ') ?_ x hx
  rw [card_leviFixBar hkl' hQ hT hQ', card_leviFixBar (plusPair_orth_flip hkl) hQ hT hQ', ← _root_.sq]
  exact card_stabTwoBar_le_four hq hij

end Four

end CFSG.SeitzReduction.OmegaPilot
