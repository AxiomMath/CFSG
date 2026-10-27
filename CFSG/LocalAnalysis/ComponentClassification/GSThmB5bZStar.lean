module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitType

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H]

theorem fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    Open.fusionOddCore X = pPrimeCore 2 X :=
  GSLit.oddCore_eq_pPrimeCore_two X

theorem map_fusionZStar_eq (X : Subgroup H) :
    (Open.fusionZStar ↥X).map X.subtype = X ⊓ coreActionKernel X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨x.2, mem_coreActionKernel.mpr ⟨le_normalizer x.2, fun j hj => ?_⟩⟩
    have hx' : (QuotientGroup.mk x : ↥X ⧸ Open.fusionOddCore ↥X) ∈ center _ := hx
    have hc := Subgroup.mem_center_iff.mp hx' (QuotientGroup.mk ⟨j, hj⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      fusionOddCore_eq_pPrimeCore] at hc
    have h2 := mem_map_of_mem X.subtype (inv_mem hc)
    convert h2 using 1
    simp only [subtype_apply, mul_inv_rev, inv_inv, coe_mul, coe_inv]
    group
  · intro hy
    obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    show QuotientGroup.mk ⟨y, hyX⟩ ∈ center (↥X ⧸ Open.fusionOddCore ↥X)
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        fusionOddCore_eq_pPrimeCore]
      have h1 := (mem_coreActionKernel.mp hyC).2 j j.2
      obtain ⟨o, ho, hoe⟩ := mem_map.mp h1
      have : (j * ⟨y, hyX⟩)⁻¹ * (⟨y, hyX⟩ * j) = o⁻¹ := by
        apply Subtype.ext
        simp only [subtype_apply] at hoe
        simp only [coe_mul, coe_inv, mul_inv_rev, hoe]
        group
      rw [this]
      exact inv_mem ho

theorem mem_coreActionKernel_of_sup {X Y : Subgroup H} {g : H} (hYX : Y ≤ X)
    (hsup : Y ⊔ (pPrimeCore 2 X).map X.subtype = X) (hgN : g ∈ normalizer (X : Set H))
    (hY : ∀ y ∈ Y, y⁻¹ * g⁻¹ * y * g ∈ (pPrimeCore 2 X).map X.subtype) :
    g ∈ coreActionKernel X := by
  set O := (pPrimeCore 2 X).map X.subtype with hO
  have hON : g ∈ normalizer (O : Set H) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic X (pPrimeCore 2 X) hgN
  have hOX : O ≤ X := map_subtype_le _
  have hOnorm : ∀ k ∈ X, ∀ o ∈ O, k⁻¹ * o * k ∈ O := by
    intro k hk o ho
    have hk' : k⁻¹ ∈ normalizer (O : Set H) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic X (pPrimeCore 2 X)
        (le_normalizer (inv_mem hk))
    have := (mem_normalizer_iff.mp hk' o).mp ho
    rwa [inv_inv] at this
  let M : Subgroup H :=
    { carrier := {j | j ∈ X ∧ j⁻¹ * g⁻¹ * j * g ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro j k ⟨hjX, hj⟩ ⟨hkX, hk⟩
        refine ⟨mul_mem hjX hkX, ?_⟩
        have h1 := hOnorm k hkX _ hj
        rw [show (j * k)⁻¹ * g⁻¹ * (j * k) * g =
          (k⁻¹ * (j⁻¹ * g⁻¹ * j * g) * k) * (k⁻¹ * g⁻¹ * k * g) by group]
        exact mul_mem h1 hk
      inv_mem' := by
        rintro j ⟨hjX, hj⟩
        refine ⟨inv_mem hjX, ?_⟩
        have h1 := hOnorm j⁻¹ (inv_mem hjX) _ (inv_mem hj)
        rw [inv_inv] at h1
        rw [show j⁻¹⁻¹ * g⁻¹ * j⁻¹ * g = j * (j⁻¹ * g⁻¹ * j * g)⁻¹ * j⁻¹ by group]
        exact h1 }
  have hYM : Y ≤ M := fun y hy => ⟨hYX hy, hY y hy⟩
  have hOM : O ≤ M := by
    intro o ho
    refine ⟨hOX ho, ?_⟩
    have h1 : g⁻¹ * o * g ∈ O := by
      have := (mem_normalizer_iff.mp (inv_mem hON) o).mp ho
      rwa [inv_inv] at this
    rw [show o⁻¹ * g⁻¹ * o * g = o⁻¹ * (g⁻¹ * o * g) by group]
    exact mul_mem (inv_mem ho) h1
  have hXM : X ≤ M := hsup ▸ sup_le hYM hOM
  exact mem_coreActionKernel.mpr ⟨hgN, fun j hj => (hXM hj).2⟩

theorem mem_of_sylow_of_mem_normalizer [Finite H] {B C : Subgroup H}
    (hB : ∃ R : Sylow 2 ↥C, (R : Subgroup C) = B.subgroupOf C) (hBC : B ≤ C) {y : H}
    (hyC : y ∈ C) (hyN : y ∈ normalizer (B : Set H)) (hy2 : ∃ k : ℕ, orderOf y = 2 ^ k) :
    y ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hB
  have hB2 : IsPGroup 2 B := by
    have h1 : IsPGroup 2 ((R : Subgroup C).map C.subtype) := R.isPGroup'.map _
    rwa [hR, map_subgroupOf_eq_of_le hBC] at h1
  have hy : IsPGroup 2 (zpowers y) := by
    obtain ⟨k, hk⟩ := hy2
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hX : IsPGroup 2 ↥(zpowers y ⊔ B) :=
    hy.to_sup_of_normal_right' hB2 (zpowers_le.mpr hyN)
  have hXC : zpowers y ⊔ B ≤ C := sup_le (zpowers_le.mpr hyC) hBC
  have hle : (R : Subgroup C) ≤ (zpowers y ⊔ B).subgroupOf C := by
    rw [hR]
    exact fun z hz => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hz))
  have heq := R.is_maximal' (Q := (zpowers y ⊔ B).subgroupOf C) hX.comap_subtype hle
  have h1 : (⟨y, hyC⟩ : C) ∈ (zpowers y ⊔ B).subgroupOf C :=
    mem_subgroupOf.mpr (mem_sup_left (mem_zpowers y))
  rw [heq, hR] at h1
  exact mem_subgroupOf.mp h1

end CFSG.ComponentClassification.GSThmB
