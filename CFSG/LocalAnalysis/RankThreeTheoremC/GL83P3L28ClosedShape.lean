module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {X₁ X₂ : Type} [Group X₁] [Group X₂] {P : Subgroup X₁} (φ : ↥P →* X₂)

@[expose] def shapeMap (S : Subgroup X₁) : Subgroup X₂ := (S.subgroupOf P).map φ

theorem shapeMap_le (S : Subgroup X₁) : shapeMap φ S ≤ φ.range := Subgroup.map_le_range _ _

theorem shapeMap_self : shapeMap φ P = φ.range := by
  rw [shapeMap, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

noncomputable def shapeEquiv (hφ : Function.Injective φ) {S : Subgroup X₁} (hSP : S ≤ P) :
    S ≃* shapeMap φ S :=
  (Subgroup.subgroupOfEquivOfLe hSP).symm.trans (Subgroup.equivMapOfInjective _ φ hφ)

theorem card_shapeMap (hφ : Function.Injective φ) {S : Subgroup X₁} (hSP : S ≤ P) :
    Nat.card (shapeMap φ S) = Nat.card S :=
  (Nat.card_congr (shapeEquiv φ hφ hSP).toEquiv).symm

theorem shapeMap_inf (hφ : Function.Injective φ) (S T : Subgroup X₁) :
    shapeMap φ (S ⊓ T) = shapeMap φ S ⊓ shapeMap φ T := by
  unfold shapeMap Subgroup.subgroupOf
  rw [Subgroup.comap_inf, Subgroup.map_inf _ _ _ hφ]

theorem shapeMap_sup {S T : Subgroup X₁} (hS : S ≤ P) (hT : T ≤ P) :
    shapeMap φ (S ⊔ T) = shapeMap φ S ⊔ shapeMap φ T := by
  unfold shapeMap
  rw [Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

theorem shapeMap_bot (hφ : Function.Injective φ) : shapeMap φ ⊥ = ⊥ := by
  have h := card_shapeMap φ hφ (bot_le : (⊥ : Subgroup X₁) ≤ P)
  rw [Subgroup.card_bot] at h
  exact Subgroup.eq_bot_of_card_eq _ h

theorem mem_L28Z_range (hφ : Function.Injective φ) {z : X₂} :
    z ∈ L28Z φ.range ↔ ∃ (z₀ : X₁) (h₀ : z₀ ∈ P), z₀ ∈ L28Z P ∧ φ ⟨z₀, h₀⟩ = z := by
  constructor
  · intro hz
    obtain ⟨hzr, hzc⟩ := GL83P3L28Aux.mem_L28Z_iff.mp hz
    obtain ⟨w, rfl⟩ := hzr
    refine ⟨w, w.2, ?_, rfl⟩
    refine GL83P3L28Aux.mem_L28Z_iff.mpr ⟨w.2, fun p hp => ?_⟩
    have h1 := hzc (φ ⟨p, hp⟩) ⟨⟨p, hp⟩, rfl⟩
    have h2 : φ (⟨p, hp⟩ * w) = φ (w * ⟨p, hp⟩) := by
      rw [map_mul, map_mul]
      exact h1
    exact congrArg Subtype.val (hφ h2)
  · rintro ⟨z₀, h₀, hz₀, rfl⟩
    refine GL83P3L28Aux.mem_L28Z_iff.mpr ⟨⟨_, rfl⟩, ?_⟩
    rintro _ ⟨p, rfl⟩
    have h1 := (GL83P3L28Aux.mem_L28Z_iff.mp hz₀).2 p p.2
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext h1)

theorem shapeMap_normalizer {A : Subgroup X₁} (hPA : P ≤ normalizer (A : Set X₁)) :
    φ.range ≤ normalizer (shapeMap φ A : Set X₂) := by
  rintro _ ⟨p, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : X₁) ∈ A := mem_subgroupOf.mp (SetLike.mem_coe.mp ha)
    refine ⟨p * a * p⁻¹, SetLike.mem_coe.mpr (mem_subgroupOf.mpr ?_), by simp⟩
    exact (mem_normalizer_iff.mp (hPA p.2) a).mp ha'
  · rintro ⟨a, ha, hay⟩
    have ha' : (a : X₁) ∈ A := mem_subgroupOf.mp (SetLike.mem_coe.mp ha)
    refine ⟨p⁻¹ * a * p, SetLike.mem_coe.mpr (mem_subgroupOf.mpr ?_), ?_⟩
    · have := (mem_normalizer_iff.mp (hPA (P.inv_mem p.2)) a).mp ha'
      simpa using this
    · have : φ (p⁻¹ * a * p) = (φ p)⁻¹ * (φ p * y * (φ p)⁻¹) * φ p := by
        rw [map_mul, map_mul, map_inv, hay]
      rw [this]
      group

theorem L28Shape.of_injective_hom [Finite X₂] (hφ : Function.Injective φ) (h : L28Shape 3 P) :
    L28Shape 3 φ.range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPc, Q₀, hQ₀P, hQ₀max, ⟨e⟩, ⟨C, hCP, hQC, hQCP⟩, ⟨A, B, hA, hB, hAB, hABQ, hPA, hPB⟩,
    hZ⟩ := h
  have hQ₀le : Q₀ ≤ P := hQ₀P.le
  have hAle : A ≤ P := (le_sup_left.trans hABQ.le).trans hQ₀le
  have hBle : B ≤ P := (le_sup_right.trans hABQ.le).trans hQ₀le
  have hQc : Nat.card Q₀ = 3 ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
    ring
  have hrange : Nat.card φ.range = 3 ^ 5 := by
    rw [← hPc]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hQc' : Nat.card (shapeMap φ Q₀) = 3 ^ 4 := by
    rw [card_shapeMap φ hφ hQ₀le, hQc]
  refine ⟨hrange, shapeMap φ Q₀, ?_, ?_, ⟨(shapeEquiv φ hφ hQ₀le).symm.trans e⟩,
    ⟨shapeMap φ C, shapeMap_le φ C, ?_, ?_⟩,
    ⟨shapeMap φ A, shapeMap φ B, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (shapeMap_le φ Q₀) fun heq => ?_
    have := congrArg (fun S : Subgroup X₂ => Nat.card S) heq
    rw [hQc', hrange] at this
    norm_num at this
  · intro R hR hRle
    have h1 : 3 ^ 4 ∣ Nat.card R := hQc' ▸ Subgroup.card_dvd_of_le hR.le
    have h2 : Nat.card R ∣ 3 ^ 5 := hrange ▸ Subgroup.card_dvd_of_le hRle
    have h3 : Nat.card R ≠ 3 ^ 4 := fun h => hR.ne
      (Subgroup.eq_of_le_of_card_ge hR.le (by rw [h, hQc']))
    obtain ⟨i, hi, hRi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rw [hRi] at h1 h3
    have hi4 : 4 ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
    have hi5 : i = 5 := by
      have : i ≠ 4 := fun h => h3 (by rw [h])
      omega
    exact Subgroup.eq_of_le_of_card_ge hRle (by rw [hrange, hRi, hi5])
  · rw [← shapeMap_inf φ hφ, hQC, shapeMap_bot φ hφ]
  · rw [← shapeMap_sup φ hQ₀le hCP, hQCP, shapeMap_self]
  · intro hbot
    apply hA
    have h1 := card_shapeMap φ hφ hAle
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1.symm
  · intro hbot
    apply hB
    have h1 := card_shapeMap φ hφ hBle
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1.symm
  · rw [← shapeMap_inf φ hφ, hAB, shapeMap_bot φ hφ]
  · rw [← shapeMap_sup φ hAle hBle, hABQ]
  · exact shapeMap_normalizer φ hPA
  · exact shapeMap_normalizer φ hPB
  · intro z
    rw [mem_L28Z_range φ hφ]
    constructor
    · rintro ⟨z₀, h₀, hz₀, rfl⟩
      obtain ⟨hz₀Q, hz₀3⟩ := (hZ z₀).mp hz₀
      refine ⟨⟨⟨z₀, h₀⟩, mem_subgroupOf.mpr hz₀Q, rfl⟩, ?_⟩
      rw [← map_pow]
      have : (⟨z₀, h₀⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hz₀3)
      rw [this, map_one]
    · rintro ⟨⟨w, hw, rfl⟩, hw3⟩
      refine ⟨w.1, w.2, (hZ _).mpr ⟨mem_subgroupOf.mp hw, ?_⟩, rfl⟩
      rw [← map_pow] at hw3
      have : w ^ 3 = 1 := hφ (by rw [hw3, map_one])
      simpa using congrArg Subtype.val this

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
