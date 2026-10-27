module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ABGLocalTools

section Natural

variable {G : Type*} [Group G]

@[expose] def zW (W : Subgroup G) : Subgroup G := W ⊓ centralizer (W : Set G)

@[expose] def oP (W : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ centralizer (zW W : Set G) ∧ Odd (orderOf x)}

@[expose] def cW (W : Subgroup G) : Subgroup G := W ⊓ centralizer ((W ⊓ oP W : Subgroup G) : Set G)

@[expose] def uW (W : Subgroup G) : Subgroup G := ⁅cW W, W⁆ ⊓ zW W

theorem conj_mem_centralizer' {N A : Subgroup G} (hA : ∀ y ∈ N, ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    ∀ y ∈ N, ∀ x ∈ centralizer (A : Set G), y * x * y⁻¹ ∈ centralizer (A : Set G) := by
  intro y hy x hx
  rw [mem_centralizer_iff]
  intro a ha
  have h1 := hA y⁻¹ (inv_mem hy) a ha
  rw [inv_inv] at h1
  have h2 := mem_centralizer_iff.mp hx _ h1
  calc a * (y * x * y⁻¹) = y * ((y⁻¹ * a * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * a * y)) * y⁻¹ := by rw [h2]
    _ = y * x * y⁻¹ * a := by group

theorem conj_mem_inf' {N A B : Subgroup G} (hA : ∀ y ∈ N, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hB : ∀ y ∈ N, ∀ b ∈ B, y * b * y⁻¹ ∈ B) : ∀ y ∈ N, ∀ x ∈ A ⊓ B, y * x * y⁻¹ ∈ A ⊓ B :=
  fun y hy x hx => mem_inf.mpr ⟨hA y hy x (mem_inf.mp hx).1, hB y hy x (mem_inf.mp hx).2⟩

theorem conj_mem_closure' {N : Subgroup G} {s : Set G} (hs : ∀ y ∈ N, ∀ x ∈ s, y * x * y⁻¹ ∈ s) :
    ∀ y ∈ N, ∀ x ∈ closure s, y * x * y⁻¹ ∈ closure s := by
  intro y hy x hx
  have hle : closure s ≤ (closure s).comap (MulAut.conj y).toMonoidHom := by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact subset_closure (hs y hy a ha)
  have := hle hx
  rw [mem_comap] at this
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem conj_mem_commutator' {N A B : Subgroup G} (hA : ∀ y ∈ N, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hB : ∀ y ∈ N, ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    ∀ y ∈ N, ∀ x ∈ ⁅A, B⁆, y * x * y⁻¹ ∈ ⁅A, B⁆ := by
  intro y hy x hx
  have hle : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj y).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_comap, map_commutatorElement]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact commutator_mem_commutator (hA y hy a ha) (hB y hy b hb)
  have := hle hx
  rw [mem_comap] at this
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem le_normalizer_of_conj_mem {N H : Subgroup G} (hH : ∀ y ∈ N, ∀ x ∈ H, y * x * y⁻¹ ∈ H) :
    N ≤ normalizer (H : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hH y hy x, fun hx => ?_⟩
  have := hH y⁻¹ (inv_mem hy) _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

variable {W : Subgroup G}

theorem conj_mem_W : ∀ y ∈ normalizer (W : Set G), ∀ x ∈ W, y * x * y⁻¹ ∈ W :=
  fun _ hy x hx => (mem_normalizer_iff.mp hy x).mp hx

theorem conj_mem_zW : ∀ y ∈ normalizer (W : Set G), ∀ x ∈ zW W, y * x * y⁻¹ ∈ zW W :=
  conj_mem_inf' conj_mem_W (conj_mem_centralizer' conj_mem_W)

theorem conj_mem_centralizer_zW :
    ∀ y ∈ normalizer (W : Set G), ∀ x ∈ centralizer (zW W : Set G),
      y * x * y⁻¹ ∈ centralizer (zW W : Set G) :=
  conj_mem_centralizer' conj_mem_zW

theorem conj_mem_oP_of {N : Subgroup G}
    (hN : ∀ y ∈ N, ∀ x ∈ centralizer (zW W : Set G), y * x * y⁻¹ ∈ centralizer (zW W : Set G)) :
    ∀ y ∈ N, ∀ x ∈ oP W, y * x * y⁻¹ ∈ oP W := by
  refine conj_mem_closure' fun y hy x hx => ⟨hN y hy x hx.1, ?_⟩
  have : orderOf (y * x * y⁻¹) = orderOf x := MulEquiv.orderOf_eq (MulAut.conj y) x
  rw [this]
  exact hx.2

theorem conj_mem_oP : ∀ y ∈ normalizer (W : Set G), ∀ x ∈ oP W, y * x * y⁻¹ ∈ oP W :=
  conj_mem_oP_of conj_mem_centralizer_zW

theorem conj_mem_cW : ∀ y ∈ normalizer (W : Set G), ∀ x ∈ cW W, y * x * y⁻¹ ∈ cW W :=
  conj_mem_inf' conj_mem_W (conj_mem_centralizer' (conj_mem_inf' conj_mem_W conj_mem_oP))

theorem conj_mem_commutator_cW :
    ∀ y ∈ normalizer (W : Set G), ∀ x ∈ ⁅cW W, W⁆, y * x * y⁻¹ ∈ ⁅cW W, W⁆ :=
  conj_mem_commutator' conj_mem_cW conj_mem_W

theorem conj_mem_uW : ∀ y ∈ normalizer (W : Set G), ∀ x ∈ uW W, y * x * y⁻¹ ∈ uW W :=
  conj_mem_inf' conj_mem_commutator_cW conj_mem_zW

theorem le_normalizer_self : W ≤ normalizer (W : Set G) := fun y hy => by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact mul_mem (mul_mem hy hx) (inv_mem hy)
  · intro hx
    have := mul_mem (mul_mem (inv_mem hy) hx) hy
    rwa [show y⁻¹ * (y * x * y⁻¹) * y = x by group] at this

theorem le_normalizer_commutator_cW : W ≤ normalizer ((⁅cW W, W⁆ : Subgroup G) : Set G) :=
  le_normalizer_self.trans (le_normalizer_of_conj_mem conj_mem_commutator_cW)

theorem normalizer_le_of_uW {β : G} (hβ : β ∈ uW W) (hβ1 : β ≠ 1)
    (hU : ∀ x ∈ uW W, x = 1 ∨ x = β) : normalizer (W : Set G) ≤ centralizer {β} := by
  intro y hy
  rw [mem_centralizer_singleton_iff]
  rcases hU _ (conj_mem_uW y hy β hβ) with h | h
  · exact absurd (by simpa using h) hβ1
  · calc y * β = (y * β * y⁻¹) * y := by group
      _ = β * y := by rw [h]

end Natural

theorem inf_zW_ne_bot {G : Type*} [Group G] [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hUn : T ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) : U ⊓ zW T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := mem_inf.1 hy
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, mem_inf.2 ⟨mem_subgroupOf.1 hyU,
    mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun s hs => ?_⟩⟩⟩, fun h => hy1 ?_⟩
  · have := mem_center_iff.mp hyZ ⟨s, hs⟩
    exact (congrArg Subtype.val this)
  · have h' : ((y : ↥T) : G) = 1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem exists_odd_pow_map_eq {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H) (m : G)
    (hm : Odd (orderOf (φ m))) : ∃ k : ℕ, Odd (orderOf (m ^ k)) ∧ φ (m ^ k) = φ m := by
  have hn0 : orderOf m ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite m)
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hn0 hab
  have hcop : Nat.Coprime (2 ^ a) b := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hb0
  refine ⟨2 ^ a * c, ?_, ?_⟩
  · have h1 : (m ^ (2 ^ a * c)) ^ b = 1 := by
      rw [← pow_mul, show 2 ^ a * c * b = 2 ^ a * b * c by ring, pow_mul, ← hab,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)
  ·
    have hdvd : orderOf (φ m) ∣ 2 ^ a * b := hab ▸ orderOf_map_dvd φ m
    have hcop' : Nat.Coprime (orderOf (φ m)) (2 ^ a) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    have hdb : orderOf (φ m) ∣ b := hcop'.dvd_of_dvd_mul_left hdvd
    have hmod : 2 ^ a * c ≡ 1 [MOD orderOf (φ m)] :=
      Nat.ModEq.of_dvd hdb (show 2 ^ a * c ≡ 1 [MOD b] from hc)
    rw [map_pow]
    exact (pow_eq_pow_of_modEq hmod (pow_orderOf_eq_one _)).trans (pow_one _)

theorem le_of_isSylowOf_top {G : Type*} [Group G] [Finite G] {A N : Subgroup G} [N.Normal]
    (hA : IsSylowOf 2 A ⊤) (hN : IsPGroup 2 N) : N ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hA2, hidx⟩ := isSylowOf_iff.mp hA
  rw [Subgroup.relIndex_top_right] at hidx
  have := hN.le_sylow_of_normal (hA2.toSylow hidx)
  rwa [IsPGroup.toSylow_coe] at this

end CFSG.ComponentClassification.HarrisLit.EndB
