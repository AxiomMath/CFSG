module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2P
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Kernel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

variable {G : Type} [Group G] {R E H : Subgroup G}
  {T : Subgroup (Equiv.Perm ↥(pointsIn R E))}

theorem mem_normalizer_of_fix (hRE : R ≤ E) {m : ↥(normalizer (E : Set G))}
    (h : pointsAction R E m ⟨R, self_mem_pointsIn hRE⟩ = ⟨R, self_mem_pointsIn hRE⟩) :
    (m : G) ∈ normalizer (R : Set G) := by
  have h' := congrArg Subtype.val h
  rw [coe_pointsAction_apply] at h'
  exact (normalizer (R : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff R _).mp h')

theorem fix_of_mem_normalizer (hRE : R ≤ E) {m : ↥(normalizer (E : Set G))}
    (hm : (m : G) ∈ normalizer (R : Set G)) :
    pointsAction R E m ⟨R, self_mem_pointsIn hRE⟩ = ⟨R, self_mem_pointsIn hRE⟩ := by
  apply Subtype.ext
  rw [coe_pointsAction_apply, rightConjugate_eq_self_iff]
  exact inv_mem hm

theorem TranslationData.exists_conj_eq_fix (hT : TranslationData R E T) (hRE : R ≤ E)
    {t₁ t₂ : Equiv.Perm ↥(pointsIn R E)} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) (ht₁1 : t₁ ≠ 1)
    (ht₂1 : t₂ ≠ 1) :
    ∃ m : ↥(normalizer (E : Set G)), (m : G) ∈ normalizer (R : Set G) ∧
      pointsAction R E m * t₁ * (pointsAction R E m)⁻¹ = t₂ := by
  set p₀ : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hRE⟩
  have h₁ : t₁ p₀ ≠ p₀ := fun h => ht₁1 (hT.eq_one_of_apply_eq ht₁ h)
  have h₂ : t₂ p₀ ≠ p₀ := fun h => ht₂1 (hT.eq_one_of_apply_eq ht₂ h)
  obtain ⟨m, hm₁, hm₂⟩ := hT.two_trans p₀ (t₁ p₀) p₀ (t₂ p₀) h₁.symm h₂.symm
  refine ⟨m, mem_normalizer_of_fix hRE hm₁, ?_⟩
  have hmem : pointsAction R E m * t₁ * (pointsAction R E m)⁻¹ ∈ T :=
    (mem_normalizer_iff.mp (hT.range_le ⟨m, rfl⟩) t₁).mp ht₁
  have hfix : (t₂⁻¹ * (pointsAction R E m * t₁ * (pointsAction R E m)⁻¹)) p₀ = p₀ := by
    have hinv : (pointsAction R E m)⁻¹ p₀ = p₀ := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hm₁.symm
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hm₂,
      Equiv.Perm.inv_eq_iff_eq]
  have := hT.eq_one_of_apply_eq (T.mul_mem (T.inv_mem ht₂) hmem) hfix
  rw [inv_mul_eq_one] at this
  exact this.symm

variable [Finite G]

omit [Finite G] in
theorem TranslationData.eq_bot_of_fix (hT : TranslationData R E T) (hRE : R ≤ E)
    {M : Subgroup (Equiv.Perm ↥(pointsIn R E))} (hM2 : IsPGroup 2 M)
    (hMfix : ∀ μ ∈ M, μ ⟨R, self_mem_pointsIn hRE⟩ = ⟨R, self_mem_pointsIn hRE⟩)
    (hMT : M ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))))
    (hMn : ∀ m : ↥(normalizer (E : Set G)), (m : G) ∈ normalizer (R : Set G) →
      ∀ μ ∈ M, pointsAction R E m * μ * (pointsAction R E m)⁻¹ ∈ M) : M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(pointsIn R E) := Nat.finite_of_card_ne_zero (by rw [hT.card_points]; omega)
  set p₀ : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hRE⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 4) (by rw [hT.card]; norm_num)
  have hMT2 : IsPGroup 2 (M ⊔ T : Subgroup _) := IsPGroup.to_sup_of_normal_right' hM2 hT2 hMT
  have hT1 : T ≠ ⊥ := fun h => by
    have := hT.card
    rw [h, card_bot] at this
    omega
  have hne := Sec2.inf_centerIn_ne_bot' hMT2 le_sup_right (sup_le hMT le_normalizer) hT1
  obtain ⟨⟨t₀, ht₀T, ht₀c⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀M : ∀ μ ∈ M, μ * t₀ = t₀ * μ := fun μ hμ =>
    mem_centralizer_iff.mp ht₀c.2 μ (mem_sup_left hμ)
  have hcomm : ∀ μ ∈ M, ∀ t ∈ T, μ * t = t * μ := by
    intro μ hμ t ht
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, one_mul]
    obtain ⟨m, hmR, hm⟩ := hT.exists_conj_eq_fix hRE ht₀T ht ht₀1' ht1
    have hμ' : (pointsAction R E m)⁻¹ * μ * pointsAction R E m ∈ M := by
      have := hMn m⁻¹ (by simpa using inv_mem hmR) μ hμ
      simpa [map_inv] using this
    have h1 := ht₀M _ hμ'
    rw [← hm]
    calc μ * (pointsAction R E m * t₀ * (pointsAction R E m)⁻¹) =
        pointsAction R E m * (((pointsAction R E m)⁻¹ * μ * pointsAction R E m) * t₀) *
          (pointsAction R E m)⁻¹ := by group
      _ = pointsAction R E m * (t₀ * ((pointsAction R E m)⁻¹ * μ * pointsAction R E m)) *
          (pointsAction R E m)⁻¹ := by rw [h1]
      _ = pointsAction R E m * t₀ * (pointsAction R E m)⁻¹ * μ := by group
  rw [eq_bot_iff]
  intro μ hμ
  rw [mem_bot]
  refine Equiv.ext fun q => ?_
  obtain ⟨t, ht, rfl⟩ := hT.trans p₀ q
  have h1 : (μ * t) p₀ = (t * μ) p₀ := by rw [hcomm μ hμ t ht]
  simp only [Equiv.Perm.mul_apply] at h1
  rw [Equiv.Perm.coe_one, id_eq, h1, hMfix μ hμ]

omit [Finite G] in
theorem TranslationData.pointsAction_eq_one (hT : TranslationData R E T) (hRE : R ≤ E)
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXE : X ≤ normalizer (E : Set G))
    (hXR : X ≤ normalizer (R : Set G))
    (hXn : normalizer (E : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : pointsAction R E ⟨x, hXE hx⟩ = 1 := by
  set M := (X.subgroupOf (normalizer (E : Set G))).map (pointsAction R E)
  have hM2 : IsPGroup 2 M := (hX2.comap_subtype).map _
  have hMfix : ∀ μ ∈ M, μ ⟨R, self_mem_pointsIn hRE⟩ = ⟨R, self_mem_pointsIn hRE⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    exact fix_of_mem_normalizer hRE (hXR hk)
  have hMT : M ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))) := by
    rintro _ ⟨k, -, rfl⟩
    exact hT.range_le ⟨k, rfl⟩
  have hMn : ∀ m : ↥(normalizer (E : Set G)), (m : G) ∈ normalizer (R : Set G) →
      ∀ μ ∈ M, pointsAction R E m * μ * (pointsAction R E m)⁻¹ ∈ M := by
    rintro m hmR _ ⟨k, hk, rfl⟩
    refine ⟨m * k * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hmX := hXn ⟨m.2, hmR⟩
    show ((m * k * m⁻¹ : ↥(normalizer (E : Set G))) : G) ∈ X
    rw [coe_mul, coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp hmX _).mp hk
  have h := hT.eq_bot_of_fix hRE hM2 hMfix hMT hMn
  have hmem : pointsAction R E ⟨x, hXE hx⟩ ∈ M := ⟨⟨x, hXE hx⟩, hx, rfl⟩
  rw [h, mem_bot] at hmem
  exact hmem

theorem PointsData.le_centralizer (hD : PointsData R E H) (hT : TranslationData R E T)
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXE : X ≤ normalizer (E : Set G))
    (hXR : X ≤ normalizer (R : Set G))
    (hXn : normalizer (E : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (X : Set G)) :
    X ≤ centralizer (E : Set G) := by
  intro x hx
  have h1 := hT.pointsAction_eq_one hD.R_le hX2 hXE hXR hXn hx
  have h2 := mem_normalizer_of_pointsAction_eq_one h1
  obtain ⟨n, hn⟩ := hX2 ⟨x, hx⟩
  have hxn : x ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact hD.mem_centralizer_of_pow_eq_one (hXE hx) h2 hxn

omit [Finite G] in
theorem TranslationData.map_le (hT : TranslationData R E T) (hRE : R ≤ E) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXn : normalizer (E : Set G) ≤ normalizer (X : Set G)) :
    (X.subgroupOf (normalizer (E : Set G))).map (pointsAction R E) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set p₀ : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hRE⟩
  set Y := (X.subgroupOf (normalizer (E : Set G))).map (pointsAction R E)
  have hY2 : IsPGroup 2 Y := (hX2.comap_subtype).map _
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 4) (by rw [hT.card]; norm_num)
  have hYT : Y ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))) := by
    rintro _ ⟨k, -, rfl⟩
    exact hT.range_le ⟨k, rfl⟩
  set N := Y ⊔ T
  set M := N ⊓ MulAction.stabilizer (Equiv.Perm ↥(pointsIn R E)) p₀
  have hN2 : IsPGroup 2 N := IsPGroup.to_sup_of_normal_right' hY2 hT2 hYT
  have hNT : N ≤ normalizer (T : Set (Equiv.Perm ↥(pointsIn R E))) := sup_le hYT le_normalizer
  have hM : M = ⊥ := by
    refine hT.eq_bot_of_fix hRE (hN2.to_le inf_le_left) (fun μ hμ => hμ.2)
      (inf_le_left.trans hNT) fun m hmR μ hμ => ⟨?_, ?_⟩
    ·
      have hmY : pointsAction R E m ∈ normalizer (Y : Set (Equiv.Perm ↥(pointsIn R E))) := by
        rw [mem_normalizer_iff]
        intro σ
        constructor
        · rintro ⟨k, hk, rfl⟩
          refine ⟨m * k * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
          show ((m * k * m⁻¹ : ↥(normalizer (E : Set G))) : G) ∈ X
          rw [coe_mul, coe_mul, coe_inv]
          exact (mem_normalizer_iff.mp (hXn m.2) _).mp hk
        · rintro ⟨k, hk, hkσ⟩
          refine ⟨m⁻¹ * k * m, ?_, ?_⟩
          · show ((m⁻¹ * k * m : ↥(normalizer (E : Set G))) : G) ∈ X
            rw [coe_mul, coe_mul, coe_inv]
            have := (mem_normalizer_iff.mp (hXn (inv_mem m.2)) _).mp hk
            simpa using this
          · rw [map_mul, map_mul, map_inv, hkσ]
            group
      have hmT := hT.range_le ⟨m, rfl⟩
      have hmN : pointsAction R E m ∈ normalizer (N : Set (Equiv.Perm ↥(pointsIn R E))) :=
        mem_normalizer_sup hmY hmT
      exact (mem_normalizer_iff.mp hmN μ).mp hμ.1
    ·
      have hfix := fix_of_mem_normalizer hRE hmR
      have hμp : μ p₀ = p₀ := hμ.2
      show (pointsAction R E m * μ * (pointsAction R E m)⁻¹) • p₀ = p₀
      rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hinv : (pointsAction R E m)⁻¹ p₀ = p₀ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hfix.symm
      rw [hinv, hμp, hfix]
  intro μ hμ
  obtain ⟨t, ht, htμ⟩ := hT.trans p₀ (μ p₀)
  have h1 : t⁻¹ * μ ∈ M := by
    refine ⟨N.mul_mem (mem_sup_right (T.inv_mem ht)) (mem_sup_left hμ), ?_⟩
    show (t⁻¹ * μ) • p₀ = p₀
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, ← htμ]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  rw [hM, mem_bot, inv_mul_eq_one] at h1
  rw [← h1]
  exact ht

end CFSG.ComponentClassification.AS81
