module

public import CFSG.HardMathSupport.Lang.E6Descent.SylowCore

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Open (IsElemAbelian)

variable {X : Type} [Group X] (L : Subgroup X)

@[expose] def liftToX (B : Subgroup (↥L ⧸ Subgroup.center ↥L)) : Subgroup X :=
  (B.comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype

variable {L}

theorem mem_liftToX {B : Subgroup (↥L ⧸ Subgroup.center ↥L)} {x : X} :
    x ∈ liftToX L B ↔ ∃ h : x ∈ L, ((⟨x, h⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hB⟩
    exact ⟨⟨x, h⟩, hB, rfl⟩

theorem liftToX_le (B : Subgroup (↥L ⧸ Subgroup.center ↥L)) : liftToX L B ≤ L := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

@[expose] def centerX (L : Subgroup X) : Subgroup X := (Subgroup.center ↥L).map L.subtype

theorem mem_centerX {z : X} : z ∈ centerX L ↔ ∃ _ : z ∈ L, ∀ l ∈ L, z * l = l * z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun l hl => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨h, hc⟩
    refine ⟨⟨z, h⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2).symm

theorem centerX_le : centerX L ≤ L := by
  rintro z ⟨y, -, rfl⟩
  exact y.2

theorem card_centerX : Nat.card (centerX L) = Nat.card (Subgroup.center ↥L) :=
  Subgroup.card_map_of_injective L.subtype_injective

theorem mem_centerX_iff {z : X} (h : z ∈ L) :
    z ∈ centerX L ↔ (⟨z, h⟩ : ↥L) ∈ Subgroup.center ↥L := by
  constructor
  · rintro ⟨y, hy, hyz⟩
    have : y = ⟨z, h⟩ := Subtype.ext hyz
    rwa [this] at hy
  · intro hc
    exact ⟨⟨z, h⟩, hc, rfl⟩

theorem centerX_le_liftToX (B : Subgroup (↥L ⧸ Subgroup.center ↥L)) : centerX L ≤ liftToX L B := by
  rintro z hz
  obtain ⟨hzL, -⟩ := mem_centerX.1 hz
  refine mem_liftToX.2 ⟨hzL, ?_⟩
  have h1 : ((⟨z, hzL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ((mem_centerX_iff hzL).1 hz)
  rw [h1]
  exact B.one_mem

theorem isPGroup_liftToX (hZ : IsPGroup 3 (Subgroup.center ↥L))
    {B : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hB : IsPGroup 3 B) : IsPGroup 3 (liftToX L B) := by
  have hc : IsPGroup 3 (B.comap (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    intro g
    obtain ⟨k, hk⟩ := hB ⟨QuotientGroup.mk' (Subgroup.center ↥L) g.1, g.2⟩
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) (g.1 ^ 3 ^ k) = 1 := by
      rw [map_pow]; exact congrArg Subtype.val hk
    have h2 : g.1 ^ 3 ^ k ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨j, hj⟩ := hZ ⟨_, h2⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  exact hc.of_equiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)

theorem card_liftToX [Finite X] (B : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
    Nat.card (liftToX L B) = Nat.card (Subgroup.center ↥L) * Nat.card B := by
  have hle : Subgroup.center ↥L ≤ B.comap (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    intro y hy
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    show QuotientGroup.mk' (Subgroup.center ↥L) y ∈ B
    rw [h1]
    exact B.one_mem
  have h1 := card_eq_mul_card_map_mk (Subgroup.center ↥L)
    (B.comap (QuotientGroup.mk' (Subgroup.center ↥L))) hle
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
  rw [liftToX, Subgroup.card_map_of_injective L.subtype_injective]
  exact h1

theorem liftToX_comm {B : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ liftToX L B, ∀ b ∈ liftToX L B, a * b * a⁻¹ * b⁻¹ ∈ centerX L := by
  intro a ha b hb
  obtain ⟨haL, haB⟩ := mem_liftToX.1 ha
  obtain ⟨hbL, hbB⟩ := mem_liftToX.1 hb
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ L := by
    exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)
  rw [mem_centerX_iff hmem, ← QuotientGroup.eq_one_iff]
  have hc := hB _ haB _ hbB
  change (QuotientGroup.mk' (Subgroup.center ↥L)) ((⟨a, haL⟩ : ↥L) * ⟨b, hbL⟩ * (⟨a, haL⟩ : ↥L)⁻¹ *
    (⟨b, hbL⟩ : ↥L)⁻¹) = 1
  simp only [map_mul, map_inv]
  change ((⟨a, haL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) * ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) *
    ((⟨a, haL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)⁻¹ * ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)⁻¹ = 1
  rw [hc]
  group

theorem liftToX_exp {B : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hB : ∀ a ∈ B, a ^ 3 = 1) :
    ∀ a ∈ liftToX L B, a ^ 3 ∈ centerX L := by
  intro a ha
  obtain ⟨haL, haB⟩ := mem_liftToX.1 ha
  have hmem : a ^ 3 ∈ L := L.pow_mem haL 3
  rw [mem_centerX_iff hmem, ← QuotientGroup.eq_one_iff]
  have := hB _ haB
  change (QuotientGroup.mk' (Subgroup.center ↥L)) ((⟨a, haL⟩ : ↥L) ^ 3) = 1
  rw [map_pow]
  exact this

end CFSG.HardMathSupport.Lang.E6Descent
