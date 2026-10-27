module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup

@[expose] def normMap {X : Type*} [Group X] (x b : X) : X :=
  b * (x * b * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹)

section NormKernel

variable {X : Type*} [Group X]

private def conjB {B : Subgroup X} (x : X) (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) : B →* B :=
  MonoidHom.mk' (fun b => ⟨x * (b : X) * x⁻¹, hxB _ b.2⟩)
    (fun a b => Subtype.ext (by simp [mul_assoc]))

private theorem coe_conjB {B : Subgroup X} {x : X} (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (b : B) :
    ((conjB x hxB b : B) : X) = x * (b : X) * x⁻¹ :=
  rfl

private def phiB {B : Subgroup X} [IsMulCommutative B] (x : X)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) : B →* B :=
  MonoidHom.mk' (fun b => conjB x hxB b * b⁻¹) (fun a b => by
    simp only [map_mul, mul_inv_rev]
    ac_rfl)

private def normB {B : Subgroup X} [IsMulCommutative B] (x : X)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) : B →* B :=
  MonoidHom.mk' (fun b => b * conjB x hxB b * conjB x hxB (conjB x hxB b)) (fun a b => by
    simp only [map_mul]
    ac_rfl)

private theorem phiB_apply {B : Subgroup X} [IsMulCommutative B] {x : X}
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    phiB x hxB g = conjB x hxB g * g⁻¹ :=
  rfl

private theorem normB_apply {B : Subgroup X} [IsMulCommutative B] {x : X}
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    normB x hxB g = g * conjB x hxB g * conjB x hxB (conjB x hxB g) :=
  rfl

private theorem conjB_cube {B : Subgroup X} {x : X} (hx3 : x ^ 3 = 1)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    conjB x hxB (conjB x hxB (conjB x hxB g)) = g := by
  apply Subtype.ext
  simp only [coe_conjB]
  have h : x * (x * (x * (g : X) * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * g * (x ^ 3)⁻¹ := by
    rw [pow_three']
    group
  rw [h, hx3]
  simp

private theorem conjB_normB {B : Subgroup X} [IsMulCommutative B] {x : X} (hx3 : x ^ 3 = 1)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    conjB x hxB (normB x hxB g) = normB x hxB g := by
  rw [normB_apply, map_mul, map_mul, conjB_cube hx3 hxB g]
  ac_rfl

private theorem phiB_eq_one_iff {B : Subgroup X} [IsMulCommutative B] {x : X}
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    phiB x hxB g = 1 ↔ conjB x hxB g = g := by
  rw [phiB_apply, mul_inv_eq_one]

private theorem phiB_normB {B : Subgroup X} [IsMulCommutative B] {x : X} (hx3 : x ^ 3 = 1)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    phiB x hxB (normB x hxB g) = 1 :=
  (phiB_eq_one_iff hxB _).2 (conjB_normB hx3 hxB g)

private theorem phiB_phiB {B : Subgroup X} [IsMulCommutative B] {x : X}
    (hB3 : ∀ t : B, t ^ 3 = 1) (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) (g : B) :
    phiB x hxB (phiB x hxB g) = normB x hxB g := by
  have h3 : conjB x hxB g * conjB x hxB g * conjB x hxB g = 1 := by
    rw [← hB3 (conjB x hxB g), pow_three']
  have ht2 : (conjB x hxB g)⁻¹ * (conjB x hxB g)⁻¹ = conjB x hxB g := by
    calc (conjB x hxB g)⁻¹ * (conjB x hxB g)⁻¹
        = (conjB x hxB g)⁻¹ * (conjB x hxB g)⁻¹ *
            (conjB x hxB g * conjB x hxB g * conjB x hxB g) := by rw [h3, mul_one]
      _ = conjB x hxB g := by group
  simp only [phiB_apply, normB_apply]
  rw [map_mul, map_inv, mul_inv_rev, inv_inv]
  calc conjB x hxB (conjB x hxB g) * (conjB x hxB g)⁻¹ * (g * (conjB x hxB g)⁻¹)
      = conjB x hxB (conjB x hxB g) * (g * ((conjB x hxB g)⁻¹ * (conjB x hxB g)⁻¹)) := by
        ac_rfl
    _ = conjB x hxB (conjB x hxB g) * (g * conjB x hxB g) := by rw [ht2]
    _ = g * conjB x hxB g * conjB x hxB (conjB x hxB g) := by ac_rfl

end NormKernel

theorem exists_subgroup_ker_normMap {X : Type*} [Group X] [Finite X] {B : Subgroup X} {x z : X}
    (hBe : IsElemAbelian 3 B) (hBc : Nat.card B = 27)
    (hx3 : x ^ 3 = 1) (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B)
    (hzB : z ∈ B) (hzo : orderOf z = 3) (hzx : x * z = z * x)
    (hCB : ∀ b ∈ B, x * b = b * x → b ∈ zpowers z) :
    ∃ KN : Subgroup X, KN ≤ B ∧ Nat.card KN = 9 ∧
      (∀ b ∈ B, normMap x b = 1 ↔ b ∈ KN) ∧ ∀ b ∈ B, normMap x b ∈ zpowers z := by
  haveI : IsMulCommutative B := hBe.1
  have hB3 : ∀ t : B, t ^ 3 = 1 := fun t => Subtype.ext (by simpa using hBe.2 t.1 t.2)
  have hker : (phiB x hxB).ker = zpowers (⟨z, hzB⟩ : B) := by
    ext g
    rw [MonoidHom.mem_ker, phiB_eq_one_iff]
    constructor
    · intro hg
      have hgX : x * (g : X) * x⁻¹ = g := by
        have h := Subtype.ext_iff.mp hg
        rwa [coe_conjB] at h
      have hxg : x * (g : X) = (g : X) * x := mul_inv_eq_iff_eq_mul.mp hgX
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hCB (g : X) g.2 hxg)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hc : Commute x z := hzx
      have hck : x * z ^ k = z ^ k * x := (hc.zpow_right k).eq
      apply Subtype.ext
      simp only [coe_conjB, SubgroupClass.coe_zpow]
      show x * z ^ k * x⁻¹ = z ^ k
      rw [hck, mul_inv_cancel_right]
  have hcardker : Nat.card (phiB x hxB).ker = 3 := by
    rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, hzo]
  have hcardrange : Nat.card (phiB x hxB).range = 9 := by
    have h := Subgroup.card_ker_mul_card_range (phiB x hxB)
    rw [hcardker, hBc] at h
    omega
  have hNker : (normB x hxB).range ≤ (phiB x hxB).ker := by
    rintro _ ⟨g, rfl⟩
    exact MonoidHom.mem_ker.mpr (phiB_normB hx3 hxB g)
  have hcardN_le : Nat.card (normB x hxB).range ≤ 3 := by
    have h := Subgroup.card_le_of_le hNker
    rwa [hcardker] at h
  have hN_nontriv : ∃ g : B, normB x hxB g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : (phiB x hxB).range ≤ (phiB x hxB).ker := by
      rintro _ ⟨g, rfl⟩
      rw [MonoidHom.mem_ker, phiB_phiB hB3 hxB g]
      exact hcon g
    have h := Subgroup.card_le_of_le hle
    rw [hcardrange, hcardker] at h
    omega
  have hrN : Nat.card (normB x hxB).range = 3 := by
    have hne : (normB x hxB).range ≠ ⊥ := by
      obtain ⟨g, hg⟩ := hN_nontriv
      intro hbot
      apply hg
      have hmem : normB x hxB g ∈ (normB x hxB).range := ⟨g, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hgt : 1 < Nat.card (normB x hxB).range := (normB x hxB).range.one_lt_card_iff_ne_bot.mpr hne
    have hdvd : Nat.card (normB x hxB).range ∣ 27 := by
      have h := Subgroup.card_subgroup_dvd_card (normB x hxB).range
      rwa [hBc] at h
    have key : ∀ r : ℕ, 1 < r → r ≤ 3 → r ∣ 27 → r = 3 := by
      intro r h1 h2 h3
      interval_cases r <;> first | rfl | (norm_num at h3)
    exact key _ hgt hcardN_le hdvd
  have hcardNker : Nat.card (normB x hxB).ker = 9 := by
    have h := Subgroup.card_ker_mul_card_range (normB x hxB)
    rw [hrN, hBc] at h
    omega
  refine ⟨(normB x hxB).ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective, hcardNker]
  · intro b hb
    constructor
    · intro h
      have hbB : normB x hxB ⟨b, hb⟩ = 1 := Subtype.ext h
      exact Subgroup.mem_map.mpr ⟨⟨b, hb⟩, MonoidHom.mem_ker.mpr hbB, rfl⟩
    · intro h
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp h
      have hy' : y = ⟨b, hb⟩ := Subtype.ext hyb
      rw [hy', MonoidHom.mem_ker] at hy
      exact congrArg Subtype.val hy
  ·
    intro b hb
    have h1 : normB x hxB ⟨b, hb⟩ ∈ zpowers (⟨z, hzB⟩ : B) := by
      rw [← hker]
      exact hNker ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : ((normB x hxB ⟨b, hb⟩ : B) : X) = normMap x b := rfl
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← h2, ← hk]
    simp

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
