module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped IsMulCommutative
open scoped Pointwise

private lemma fz21b_zpow_emod {G : Type*} [Group G] {g : G} {n : ℕ} (hg : g ^ n = 1) (k : ℤ) :
    g ^ k = g ^ (k % n) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k n]
  rw [zpow_add, zpow_mul]
  have hgz : g ^ (n : ℤ) = 1 := by rw [zpow_natCast]; exact hg
  rw [hgz, one_zpow, mul_one]

private lemma fz21b_zpowers_sup {N : Type*} [Group N] (ρ lam : N)
    (hlam : lam ^ 2 = 1) (hconj : lam * ρ * lam⁻¹ = ρ⁻¹) :
    ∀ x ∈ Subgroup.zpowers ρ ⊔ Subgroup.zpowers lam, ∃ j i : ℤ, x = lam ^ j * ρ ^ i := by
  have hlam2 : lam * lam = 1 := by rw [← pow_two]; exact hlam
  have hlam_inv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  have hlamnorm : Subgroup.zpowers lam ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set N) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h1 : lam * ρ ^ k * lam⁻¹ = ρ ^ (-k) := by
        rw [← conj_zpow (a := lam) (b := ρ) (i := k), hconj]; simp
      rw [h1]
      exact Subgroup.zpow_mem_zpowers ρ (-k)
    · intro hh
      have h1 : h = lam * (lam * h * lam⁻¹) * lam⁻¹ := by
        rw [hlam_inv]
        symm
        calc lam * (lam * h * lam) * lam = (lam * lam) * h * (lam * lam) := by group
          _ = h := by rw [hlam2, one_mul, mul_one]
      rw [h1]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h2 : lam * ρ ^ k * lam⁻¹ = ρ ^ (-k) := by
        rw [← conj_zpow (a := lam) (b := ρ) (i := k), hconj]; simp
      rw [← hk, h2]
      exact Subgroup.zpow_mem_zpowers ρ (-k)
  intro x hx
  rw [sup_comm] at hx
  change x ∈ (↑(Subgroup.zpowers lam ⊔ Subgroup.zpowers ρ) : Set N) at hx
  have hset : (↑(Subgroup.zpowers lam ⊔ Subgroup.zpowers ρ) : Set N) =
      (↑(Subgroup.zpowers lam) : Set N) * (↑(Subgroup.zpowers ρ) : Set N) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hlamnorm
  rw [hset] at hx
  obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hl
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hr
  exact ⟨j, i, by rw [← hlr, ← hj, ← hi]⟩

@[expose]
def fz21b_invAut (G : Type*) [CommGroup G] : MulAut G where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := by simp [mul_comm]

lemma fz21b_invAut_mem_center (G : Type*) [CommGroup G] :
    fz21b_invAut G ∈ Subgroup.center (MulAut G) := by
  rw [Subgroup.mem_center_iff]
  intro α
  ext x
  simp [fz21b_invAut]
lemma fz21b_zpowers_sup_fin {N : Type*} [Group N] (ρ lam : N)
    (hρ : orderOf ρ = 3) (hlam : orderOf lam = 2) (hrel : lam * ρ * lam⁻¹ = ρ⁻¹) :
    ∀ x ∈ Subgroup.zpowers ρ ⊔ Subgroup.zpowers lam,
      ∃ j : Fin 2, ∃ i : Fin 3, x = lam ^ (j : ℕ) * ρ ^ (i : ℕ) := by
  intro x hx
  have hlam2 : lam ^ 2 = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hρ3 : ρ ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  obtain ⟨J, I, hxI⟩ := fz21b_zpowers_sup ρ lam hlam2 hrel x hx
  have hJ : lam ^ J = lam ^ (J % 2) := fz21b_zpow_emod hlam2 J
  have hI : ρ ^ I = ρ ^ (I % 3) := fz21b_zpow_emod hρ3 I
  have hJ0 : 0 ≤ J % 2 := Int.emod_nonneg J (by norm_num)
  have hJ2 : J % 2 < 2 := Int.emod_lt_of_pos J (by norm_num)
  have hI0 : 0 ≤ I % 3 := Int.emod_nonneg I (by norm_num)
  have hI3 : I % 3 < 3 := Int.emod_lt_of_pos I (by norm_num)
  refine ⟨⟨(J % 2).toNat, by omega⟩, ⟨(I % 3).toNat, by omega⟩, ?_⟩
  have hJ' : lam ^ (J % 2) = lam ^ ((J % 2).toNat : ℕ) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hJ0]
    rw [zpow_natCast]
  have hI' : ρ ^ (I % 3) = ρ ^ ((I % 3).toNat : ℕ) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hI0]
    rw [zpow_natCast]
  rw [hxI, hJ, hI, hJ', hI']

lemma fz21b_card_sup {G : Type*} [Group G] (H K : Subgroup G)
    (h : K ≤ Subgroup.normalizer (H : Set G)) (hdisj : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let A : Subgroup G := H ⊔ K
  have hA : A = H ⊔ K := rfl
  have hset : (↑A : Set G) = (↑H : Set G) * (↑K : Set G) := by
    rw [hA]; exact Subgroup.coe_mul_of_right_le_normalizer_left H K h
  let f : H × K → A := fun p =>
    ⟨(p.1 : G) * p.2, by rw [← SetLike.mem_coe, hset]; exact Set.mul_mem_mul p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
      have hG : (h1 : G) * k1 = (h2 : G) * k2 := by
        have := congrArg (Subtype.val) heq
        simpa [f] using this
      have hrel : (h2 : G)⁻¹ * h1 = k2 * (k1 : G)⁻¹ := by
        calc (h2 : G)⁻¹ * h1 = (h2 : G)⁻¹ * ((h1 : G) * k1) * (k1 : G)⁻¹ := by group
          _ = (h2 : G)⁻¹ * ((h2 : G) * k2) * (k1 : G)⁻¹ := by rw [hG]
          _ = k2 * (k1 : G)⁻¹ := by group
      have hmem : (h2 : G)⁻¹ * h1 ∈ H ⊓ K := by
        rw [Subgroup.mem_inf]
        exact ⟨H.mul_mem (H.inv_mem h2.2) h1.2,
          by rw [hrel]; exact K.mul_mem k2.2 (K.inv_mem k1.2)⟩
      have h1' : (h2 : G)⁻¹ * h1 = 1 := by
        rw [hdisj] at hmem; exact Subgroup.mem_bot.mp hmem
      have hk : k2 * (k1 : G)⁻¹ = 1 := by rw [← hrel, h1']
      have hh : h1 = h2 := by
        apply Subtype.ext
        have h := congrArg (fun z => (h2 : G) * z) h1'
        simpa [mul_assoc] using h
      have hk' : k1 = k2 := by
        apply Subtype.ext
        have h := congrArg (fun z => z * (k1 : G)) hk
        exact (by simpa [mul_assoc] using h : (k2 : G) = k1).symm
      rw [hh, hk']
    · intro y
      have hy : (y : G) ∈ (↑H : Set G) * (↑K : Set G) := by
        rw [← hset]; exact y.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  rw [← hA]
  exact hcard.symm

lemma fz21b_card_map_of_disjoint {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (h : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.domRestrict K) := by
    intro x y hxy
    have hmem : (x : G) * (y : G)⁻¹ ∈ K ⊓ f.ker := by
      rw [Subgroup.mem_inf]
      refine ⟨K.mul_mem x.2 (K.inv_mem y.2), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, show f (x : G) = f (y : G) from hxy,
        mul_inv_cancel]
    rw [h] at hmem
    have h1 : (x : G) * (y : G)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have hxy' : (x : G) = y := by
      calc (x : G) = (x : G) * (y : G)⁻¹ * (y : G) := by group
        _ = 1 * (y : G) := by rw [h1]
        _ = (y : G) := one_mul _
    exact Subtype.ext hxy'
  rw [← MonoidHom.domRestrict_range (f := f) (K := K)]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG.OddStandard.SmallF3.FritzII
