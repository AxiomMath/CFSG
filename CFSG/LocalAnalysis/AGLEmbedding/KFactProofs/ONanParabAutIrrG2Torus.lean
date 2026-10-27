module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

section Matrix

variable {τ : Tag} {K : Type} [Field K]

noncomputable def fieldMap (τ : Tag) (σ : K ≃+* K) : ModGL τ K →* ModGL τ K :=
  Units.map (entrywiseHom (τ := τ) σ.toRingHom)

theorem fieldMap_pinnedX (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : K) :
    fieldMap τ σ (pinnedX τ K α c) = pinnedX τ K α (σ c) :=
  Units.ext (entrywise_pinnedX σ.toRingHom α c)

theorem fieldMap_fieldMap (σ ρ : K ≃+* K) (x : ModGL τ K) :
    fieldMap τ σ (fieldMap τ ρ x) = fieldMap τ (σ * ρ) x :=
  (units_map_entrywiseHom_mul_ringEquiv σ ρ x).symm

theorem fieldMap_one (x : ModGL τ K) : fieldMap τ (1 : K ≃+* K) x = x :=
  units_map_entrywiseHom_one_ringEquiv x

theorem fieldMap_mem_posUnipotent (σ : K ≃+* K) {u : ModGL τ K} (hu : u ∈ posUnipotent τ K) :
    fieldMap τ σ u ∈ posUnipotent τ K := by
  have h : (posUnipotent τ K).map (fieldMap τ σ) ≤ posUnipotent τ K := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun α hα => ?_
    show Subgroup.closure (Set.range (pinnedX τ K α)) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    show fieldMap τ σ (pinnedX τ K α c) ∈ posUnipotent τ K
    rw [fieldMap_pinnedX]
    have hroot : rootSubgroup τ K α ≤ posUnipotent τ K := le_iSup₂_of_le α hα le_rfl
    exact hroot (Subgroup.subset_closure ⟨σ c, rfl⟩)
  exact h ⟨u, hu, rfl⟩

theorem fieldMap_mem_posUnipotent_iff (σ : K ≃+* K) (u : ModGL τ K) :
    fieldMap τ σ u ∈ posUnipotent τ K ↔ u ∈ posUnipotent τ K := by
  refine ⟨fun h => ?_, fieldMap_mem_posUnipotent σ⟩
  have := fieldMap_mem_posUnipotent σ⁻¹ h
  rwa [fieldMap_fieldMap, inv_mul_cancel, fieldMap_one] at this

theorem fieldMap_torusElt (σ : K ≃+* K) (i : Fin τ.rank) (t : Kˣ) :
    fieldMap τ σ (torusElt τ K i t) =
      torusElt τ K i (Units.map σ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
  change Units.map (entrywiseHom (τ := τ) σ.toRingHom) _ = _
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext j
  simp [map_zpow]

theorem torusElt_pow (i : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    torusElt τ K i (t ^ n) = torusElt τ K i t ^ n := by
  induction n with
  | zero => simpa using torusElt_one (τ := τ) (R := K) i
  | succ n ih => rw [pow_succ, torusElt_mul, ih, pow_succ]

theorem fieldMap_torusElt_pow {σ : K ≃+* K} {k : ℕ} (hk : ∀ x : K, σ x = x ^ k)
    (i : Fin τ.rank) (t : Kˣ) :
    fieldMap τ σ (torusElt τ K i t) = torusElt τ K i t ^ k := by
  rw [fieldMap_torusElt, ← torusElt_pow]
  congr 1
  exact Units.ext (by simpa using hk t)

theorem fieldMap_eq_pow_of_mem_torusGroup {σ : K ≃+* K} {k : ℕ} (hk : ∀ x : K, σ x = x ^ k)
    {t : ModGL τ K} (ht : t ∈ torusGroup τ K) : fieldMap τ σ t = t ^ k := by
  have hcomm := (triangular_borel_structure.{0, 0} τ K).1
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, s⟩, rfl⟩ := hx
    exact fieldMap_torusElt_pow hk i s
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [map_mul, ihx, ihy]
    exact ((show Commute x y from hcomm x hx y hy).mul_pow k).symm
  | inv x hx ih => rw [map_inv, ih, inv_pow]

theorem borel_decomp {b : ModGL τ K} (hb : b ∈ borelGroup τ K) :
    ∃ t ∈ torusGroup τ K, ∃ u ∈ posUnipotent τ K, b = t * u := by
  have h := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1
  have hb' : b ∈ ((borelGroup τ K : Subgroup _) : Set (ModGL τ K)) := hb
  rw [h] at hb'
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  exact ⟨t, ht, u, hu, rfl⟩

theorem torusGroup_le_normalizer : torusGroup τ K ≤
    Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
  (triangular_borel_structure.{0, 0} τ K).2.2.1

theorem mul_pow_mem {t u : ModGL τ K}
    (ht : t ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)))
    (hu : u ∈ posUnipotent τ K) (n : ℕ) : ∃ u' ∈ posUnipotent τ K, (t * u) ^ n = t ^ n * u' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨u', hu', h⟩ := ih
    have hinv : t⁻¹ ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := inv_mem ht
    have h1 : t⁻¹ * u' * t⁻¹⁻¹ ∈ posUnipotent τ K :=
      (Subgroup.mem_normalizer_iff.1 hinv u').1 hu'
    refine ⟨(t⁻¹ * u' * t⁻¹⁻¹) * u, mul_mem h1 hu, ?_⟩
    rw [pow_succ, h]
    group

theorem commutator_mem_posUnipotent {b c : ModGL τ K} (hb : b ∈ borelGroup τ K)
    (hc : c ∈ borelGroup τ K) : ⁅b, c⁆ ∈ posUnipotent τ K := by
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hnorm := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  obtain ⟨t, ht, u, hu, rfl⟩ := borel_decomp hb
  obtain ⟨t', ht', u', hu', rfl⟩ := borel_decomp hc
  have hTB : torusGroup τ K ≤ borelGroup τ K := le_sup_left
  set ρ : ↥(borelGroup τ K) →* ↥(borelGroup τ K) ⧸ (posUnipotent τ K).subgroupOf (borelGroup τ K) :=
    QuotientGroup.mk' _ with hρ
  have hUρ : ∀ (w : ModGL τ K) (hw : w ∈ posUnipotent τ K), ρ ⟨w, hUB hw⟩ = 1 := fun w hw =>
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hw)
  have hρb : ρ ⟨t * u, mul_mem (hTB ht) (hUB hu)⟩ = ρ ⟨t, hTB ht⟩ := by
    have : (⟨t * u, mul_mem (hTB ht) (hUB hu)⟩ : ↥(borelGroup τ K)) =
        ⟨t, hTB ht⟩ * ⟨u, hUB hu⟩ := rfl
    rw [this, map_mul, hUρ u hu, mul_one]
  have hρc : ρ ⟨t' * u', mul_mem (hTB ht') (hUB hu')⟩ = ρ ⟨t', hTB ht'⟩ := by
    have : (⟨t' * u', mul_mem (hTB ht') (hUB hu')⟩ : ↥(borelGroup τ K)) =
        ⟨t', hTB ht'⟩ * ⟨u', hUB hu'⟩ := rfl
    rw [this, map_mul, hUρ u' hu', mul_one]
  have hcomm : ρ ⟨t, hTB ht⟩ * ρ ⟨t', hTB ht'⟩ = ρ ⟨t', hTB ht'⟩ * ρ ⟨t, hTB ht⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 t ht t' ht')
  have h1 : ρ ⁅(⟨t * u, mul_mem (hTB ht) (hUB hu)⟩ : ↥(borelGroup τ K)),
      ⟨t' * u', mul_mem (hTB ht') (hUB hu')⟩⁆ = 1 := by
    rw [map_commutatorElement, hρb, hρc]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  exact Subgroup.mem_subgroupOf.1 h2

theorem fieldMap_mul_pow_inv_mem {σ : K ≃+* K} {k : ℕ} (hk : ∀ x : K, σ x = x ^ k)
    {b : ModGL τ K} (hb : b ∈ borelGroup τ K) :
    fieldMap τ σ b * (b ^ k)⁻¹ ∈ posUnipotent τ K := by
  obtain ⟨t, ht, u, hu, rfl⟩ := borel_decomp hb
  have htN := torusGroup_le_normalizer ht
  obtain ⟨u', hu', hpow⟩ := mul_pow_mem htN hu k
  have hσu := fieldMap_mem_posUnipotent σ hu
  rw [map_mul, fieldMap_eq_pow_of_mem_torusGroup hk ht, hpow]
  have htk : t ^ k ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := pow_mem htN k
  have h1 : t ^ k * (fieldMap τ σ u * u'⁻¹) * (t ^ k)⁻¹ ∈ posUnipotent τ K :=
    (Subgroup.mem_normalizer_iff.1 htk _).1 (mul_mem hσu (inv_mem hu'))
  have h2 : t ^ k * fieldMap τ σ u * (t ^ k * u')⁻¹ =
      t ^ k * (fieldMap τ σ u * u'⁻¹) * (t ^ k)⁻¹ := by group
  rw [h2]
  exact h1

end Matrix

section Adjoint


theorem autScalarTorus_adjoint_g2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq4 : 4 ≤ Nat.card K) : AutScalarTorus (adjointGroup .G2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hK⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow K
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f ≤ 1 := by omega
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  let S₁ : Sylow 2 (adjointGroup .G2 K) := hUp.toSylow hUi
  have hS₁ : (S₁ : Subgroup (adjointGroup .G2 K)) =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := IsPGroup.toSylow_coe hUp hUi
  have hmemS : ∀ w : adjointGroup .G2 K, w ∈ (S₁ : Subgroup _) ↔
      (w : ModGL .G2 K) ∈ posUnipotent .G2 K := fun w => by
    rw [hS₁, Subgroup.mem_subgroupOf]
  have hN : ∀ g : adjointGroup .G2 K,
      g ∈ Subgroup.normalizer ((S₁ : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) →
        (g : ModGL .G2 K) ∈ borelGroup .G2 K := by
    intro g hg
    have hnorm : (g : ModGL .G2 K) ∈
        Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have := (Subgroup.mem_normalizer_iff.1 hg ⟨h, posUnipotent_le_adjointGroup hh⟩).1
          ((hmemS _).2 hh)
        exact (hmemS _).1 this
      · intro hh
        have hhX : h ∈ adjointGroup .G2 K := by
          have e : h = (g : ModGL .G2 K)⁻¹ * ((g : ModGL .G2 K) * h * (g : ModGL .G2 K)⁻¹) *
              (g : ModGL .G2 K) := by group
          rw [e]
          exact mul_mem (mul_mem (inv_mem g.2) (posUnipotent_le_adjointGroup hh)) g.2
        have h3 := (Subgroup.mem_normalizer_iff.1 hg ⟨h, hhX⟩).2
          ((hmemS (g * ⟨h, hhX⟩ * g⁻¹)).2 hh)
        exact (hmemS _).1 h3
    have := (borel_self_normalizers .G2 K).1
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨g.2, hnorm⟩
  refine AutScalarTorus.of_decomp S₁ ?_ ?_
  · intro b hb c hc
    rw [hmemS]
    exact commutator_mem_posUnipotent (hN b hb) (hN c hc)
  · rintro α ⟨e, he, he6, hinn⟩
    obtain ⟨hex, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf2 K hK
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex α
    obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
    have hφ : ∀ w : adjointGroup .G2 K,
        (((MulAut.conj g⁻¹ * α) w : adjointGroup .G2 K) : ModGL .G2 K) = fieldMap .G2 σ w := by
      intro w
      have h1 := hgσ w
      have e : (MulAut.conj g⁻¹ * α) w = g⁻¹ * α w * g := by
        rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
      rw [e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1]
      show _ = Units.map (entrywiseHom (τ := .G2) σ.toRingHom) (w : ModGL .G2 K)
      group
    refine ⟨g, MulAut.conj g⁻¹ * α, 2 ^ j, ?_, ?_, ?_⟩
    · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    · intro w
      rw [hmemS, hmemS, hφ, fieldMap_mem_posUnipotent_iff]
    · intro b hb
      rw [hmemS]
      have hk : ∀ x : K, σ x = x ^ 2 ^ j := hj
      have h2 : (((MulAut.conj g⁻¹ * α) b * (b ^ 2 ^ j)⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
          fieldMap .G2 σ (b : ModGL .G2 K) * ((b : ModGL .G2 K) ^ 2 ^ j)⁻¹ := by
        rw [Subgroup.coe_mul, hφ]
        simp
      rw [h2]
      exact fieldMap_mul_pow_inv_mem hk (hN b hb)

theorem g2R2 : G2R2 := fun _ _ _ _ hq4 => autScalarTorus_adjoint_g2 hq4

theorem yLevelIrrOn_isG2Two : YLevelIrrOn IsG2Two := yLevelIrrOn_g2 g2R2

end Adjoint

end CFSG.AGLEmbedding.ParabAutIrr
