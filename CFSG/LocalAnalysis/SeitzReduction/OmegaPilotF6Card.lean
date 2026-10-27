module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Count
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

@[expose] def fixSpace (B : Subgroup (orthDerived Q)) : Submodule K (Fin d → K) where
  carrier := {v | ∀ g ∈ B, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = v}
  add_mem' {x y} hx hy g hg := by
    change (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (x + y) = x + y
    rw [map_add, hx g hg, hy g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c x hx g hg := by
    change (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (c • x) = c • x
    rw [map_smul, hx g hg]

theorem mem_fixSpace {B : Subgroup (orthDerived Q)} {v : Fin d → K} :
    v ∈ fixSpace B ↔ ∀ g ∈ B, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = v := Iff.rfl

theorem piW_apply_comm (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a a' ⊓ stabSub b b') (v : Fin d → K) :
    piW a a' b b' (g v) = g (piW a a' b b' v) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  have hW : g (piW a a' b b' v) ∈ subW K a a' b b' := by
    have hw := piW_mem hi hj hd v
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← hi.polar_right (g (piW a a' b b' v)), ← h2, polar_map_of_mem hgO, hi.polar_right,
        hw.1.1]
    · rw [← hi.polar_left (g (piW a a' b b' v)), ← h1, polar_map_of_mem hgO, hi.polar_left,
        hw.1.2]
    · rw [← hj.polar_right (g (piW a a' b b' v)), ← h4, polar_map_of_mem hgO, hj.polar_right,
        hw.2.1]
    · rw [← hj.polar_left (g (piW a a' b b' v)), ← h3, polar_map_of_mem hgO, hj.polar_left,
        hw.2.2]
  have hz : ∀ {i : Fin d}, (i = a ∨ i = a' ∨ i = b ∨ i = b') →
      piW a a' b b' (Pi.single i (1 : K)) = 0 := fun hi' => piW_single_of_mem hi' hd hi.ne hj.ne
  conv_lhs => rw [eq_coord hd v]
  rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2, h3, h4,
    piW_add, piW_add, piW_add, piW_add, piW_smul, piW_smul, piW_smul, piW_smul, hz (Or.inl rfl),
    hz (Or.inr (Or.inl rfl)), hz (Or.inr (Or.inr (Or.inl rfl))), hz (Or.inr (Or.inr (Or.inr rfl))),
    piW_eq_self hW]
  simp

theorem commute_eichlerTriple {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hga : g (Pi.single a 1) = Pi.single a 1)
    (hgb : g (Pi.single b 1) = Pi.single b 1) {w₁ w₂ : Fin d → K} (h1 : g w₁ = w₁)
    (h2 : g w₂ = w₂) (c : K) :
    g * eichlerTriple Q a b w₁ w₂ c = eichlerTriple Q a b w₁ w₂ c * g := by
  have e1 := eichler_conj hgO (Pi.single a 1) (w₁ + c • Pi.single b 1)
  rw [hga, map_add, map_smul, h1, hgb] at e1
  have e2 := eichler_conj hgO (Pi.single b 1) w₂
  rw [hgb, h2] at e2
  rw [eichlerTriple]
  calc g * (eichler Q (Pi.single a 1) (w₁ + c • Pi.single b 1) * eichler Q (Pi.single b 1) w₂) =
      (g * eichler Q (Pi.single a 1) (w₁ + c • Pi.single b 1) * g⁻¹) *
        (g * eichler Q (Pi.single b 1) w₂ * g⁻¹) * g := by group
    _ = _ := by rw [e1, e2]

theorem map_inf_centralizer_of_injective {C G : Type*} [Group C] [Group G] {φ : C →* G}
    (hφ : Function.Injective φ) (A B : Subgroup C) :
    (A ⊓ centralizer (B : Set C)).map φ =
      A.map φ ⊓ centralizer ((B.map φ : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hyB⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨⟨y, hyA, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hyB b hb]
  · intro hx
    obtain ⟨⟨y, hyA, rfl⟩, hyB⟩ := mem_inf.1 hx
    refine ⟨y, mem_inf.2 ⟨hyA, mem_centralizer_iff.2 fun b hb => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hyB (φ b) ⟨b, hb, rfl⟩

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_rootRadical_inf_centralizer (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b')
    {B : Subgroup (orthDerived Q)}
    (hB : ∀ g ∈ B, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ stabSub a a' ⊓ stabSub b b') :
    Nat.card ((rootRadical Q hi.hypPair hj.hypPair).subgroupOf (orthDerived Q) ⊓
      centralizer (B : Set (orthDerived Q)) : Subgroup (orthDerived Q)) =
      Nat.card K * Nat.card ↥(fixSpace B ⊓ subW K a a' b b') ^ 2 := by
  classical
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hmemU : ∀ x : orthDerived Q, x ∈ centralizer (B : Set (orthDerived Q)) →
      ∀ v : Fin d → K, (∀ g ∈ B, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = v) →
      piW a a' b b' ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) ∈ fixSpace B ⊓ subW K a a' b b' := by
    intro x hx v hv
    refine ⟨fun g hg => ?_, piW_mem hi hj hd _⟩
    rw [← piW_apply_comm hi hj hd (hΩO g.2) (hB g hg)]
    congr 1
    have hc := congrArg (fun z : orthDerived Q => (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) v)
      (mem_centralizer_iff.mp hx g hg)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hv g hg] at hc
    exact hc
  set A := (rootRadical Q hi.hypPair hj.hypPair).subgroupOf (orthDerived Q) ⊓
    centralizer (B : Set (orthDerived Q)) with hA
  let Φ : A → ↥(fixSpace B ⊓ subW K a a' b b') × ↥(fixSpace B ⊓ subW K a a' b b') × K :=
    fun x => (⟨_, hmemU x.1 (mem_inf.mp x.2).2 (Pi.single a' 1) fun g hg => (hB g hg).1.2⟩,
      ⟨_, hmemU x.1 (mem_inf.mp x.2).2 (Pi.single b' 1) fun g hg => (hB g hg).2.2⟩,
      (((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a' 1)) b)
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun x y hxy => ?_, fun ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, c⟩ => ?_⟩
    · simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      exact Subtype.ext (Subtype.ext (eq_of_rootRadical_triple hi hj hd
        (mem_subgroupOf.mp (mem_inf.mp x.2).1) (mem_subgroupOf.mp (mem_inf.mp y.2).1) h1 h2 h3))
    · have hEΩ : eichlerTriple Q a b w₁ w₂ c ∈ orthDerived Q :=
        mul_mem (eichler_mem_orthDerived hQ hT _ _) (eichler_mem_orthDerived hQ hT _ _)
      have hmem : (⟨_, hEΩ⟩ : orthDerived Q) ∈ A := by
        refine mem_inf.mpr ⟨mem_subgroupOf.mpr
          (eichlerTriple_mem_rootRadical hi hj hd hw₁.2 hw₂.2 c),
          mem_centralizer_iff.mpr fun g hg => Subtype.ext ?_⟩
        exact commute_eichlerTriple (hΩO g.2) (hB g hg).1.1 (hB g hg).2.1 (hw₁.1 g hg)
          (hw₂.1 g hg) c
      refine ⟨⟨_, hmem⟩, ?_⟩
      obtain ⟨t1, t2, t3⟩ := eichlerTriple_triple hi hj hd hw₁.2 hw₂.2 c
      simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨t1, t2, t3⟩
  rw [Nat.card_eq_of_bijective Φ hΦ, Nat.card_prod, Nat.card_prod]
  ring

omit [Finite K] in
theorem mem_stabSub_of_projHom_mem (hi : IsHypCoord Q a a')
    {Y : Subgroup (matrixProjectiveDerived Q)}
    (hY : Y ≤ stabPairsBar Q a a' b b') {g : orthDerived Q} (hg : projHom Q g ∈ Y) :
    (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ stabSub a a' ⊓ stabSub b b' := by
  obtain ⟨g', hg', hgg'⟩ := hY hg
  rw [projHom_injective hi.exists_ne_zero hgg'] at hg'
  exact mem_subgroupOf.mp hg'

theorem card_rootRadicalBar_inf_centralizer (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b')
    {Y : Subgroup (matrixProjectiveDerived Q)} (hY : Y ≤ stabPairsBar Q a a' b b') :
    Nat.card (rootRadicalBar Q hi.hypPair hj.hypPair ⊓
        centralizer (Y : Set (matrixProjectiveDerived Q)) : Subgroup (matrixProjectiveDerived Q)) =
      Nat.card K * Nat.card ↥(fixSpace (Y.comap (projHom Q)) ⊓ subW K a a' b b') ^ 2 := by
  have hρ := projHom_injective (Q := Q) hi.exists_ne_zero
  have h := map_inf_centralizer_of_injective hρ
    ((rootRadical Q hi.hypPair hj.hypPair).subgroupOf (orthDerived Q)) (Y.comap (projHom Q))
  rw [map_comap_eq_self_of_surjective (projHom_surjective Q) Y] at h
  rw [rootRadicalBar, ← h, card_map_of_injective hρ]
  exact card_rootRadical_inf_centralizer hQ hT hi hj hd fun g hg =>
    mem_stabSub_of_projHom_mem hi hY hg

omit [Finite K] [CharP K 2] in
theorem card_fixSpace_eq (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {B : Subgroup (orthDerived Q)}
    (hB : ∀ g ∈ B, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ stabSub a a' ⊓ stabSub b b') :
    Nat.card (fixSpace B) = Nat.card K ^ 4 * Nat.card ↥(fixSpace B ⊓ subW K a a' b b') := by
  classical
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hz : ∀ {i : Fin d}, (i = a ∨ i = a' ∨ i = b ∨ i = b') →
      piW a a' b b' (Pi.single i (1 : K)) = 0 := fun hi' => piW_single_of_mem hi' hd hi.ne hj.ne
  have hmem : ∀ v ∈ fixSpace B, piW a a' b b' v ∈ fixSpace B ⊓ subW K a a' b b' := fun v hv =>
    ⟨fun g hg => by rw [← piW_apply_comm hi hj hd (hΩO g.2) (hB g hg), hv g hg],
      piW_mem hi hj hd v⟩
  let Φ : fixSpace B → (K × K × K × K) × ↥(fixSpace B ⊓ subW K a a' b b') :=
    fun v => ((v.1 a, v.1 a', v.1 b, v.1 b'), ⟨_, hmem v.1 v.2⟩)
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun v w hvw => ?_, fun ⟨⟨α, β, γ, δ⟩, ⟨u, hu⟩⟩ => ?_⟩
    · simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hvw
      obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hvw
      apply Subtype.ext
      rw [eq_coord hd v.1, eq_coord hd w.1, h1, h2, h3, h4, h5]
    · set v : Fin d → K := α • Pi.single a 1 + β • Pi.single a' 1 + γ • Pi.single b 1 +
        δ • Pi.single b' 1 + u with hv
      have hvB : v ∈ fixSpace B := fun g hg => by
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hB g hg
        rw [hv, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2,
          h3, h4, hu.1 g hg]
      refine ⟨⟨v, hvB⟩, ?_⟩
      obtain ⟨⟨u1, u2⟩, u3, u4⟩ := hu.2
      have ne1 := hi.ne
      have ne2 := hj.ne
      have ne3 := hd.left_ne_left
      have ne4 := hd.left_ne_right
      have ne5 := hd.right_ne_left
      have ne6 := hd.right_ne_right
      simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [hv, u1, ne1, ne3, ne5]
      · simp [hv, u2, ne1.symm, ne4, ne6]
      · simp [hv, u3, ne2, ne3.symm, ne4.symm]
      · simp [hv, u4, ne2.symm, ne5.symm, ne6.symm]
      · rw [hv, piW_add, piW_add, piW_add, piW_add, piW_smul, piW_smul, piW_smul, piW_smul,
          hz (Or.inl rfl), hz (Or.inr (Or.inl rfl)), hz (Or.inr (Or.inr (Or.inl rfl))),
          hz (Or.inr (Or.inr (Or.inr rfl))), piW_eq_self hu.2]
        simp
  rw [Nat.card_eq_of_bijective Φ hΦ, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

end CFSG.SeitzReduction.OmegaPilot
