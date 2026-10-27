module

public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem ka_pl4_exists_pow_four_of_pow_odd {G : Type*} [CommGroup G] (d c : G) (k : ℕ)
    (h : d ^ (2 * k + 1) = c ^ 4) : ∃ μ : G, d = μ ^ 4 := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((2 * k + 1 : ℕ) : ℤ) ((4 : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (odd_two_mul_add_one k))
  refine ⟨c ^ a * d ^ b, ?_⟩
  calc d = d ^ (a * ((2 * k + 1 : ℕ) : ℤ) + b * ((4 : ℕ) : ℤ)) := by rw [hab, zpow_one]
    _ = (d ^ (2 * k + 1)) ^ a * (d ^ 4) ^ b := by
        rw [zpow_add, zpow_mul', zpow_mul', zpow_natCast, zpow_natCast]
    _ = (c ^ 4) ^ a * (d ^ 4) ^ b := by rw [h]
    _ = (c ^ a * d ^ b) ^ 4 := by
        rw [mul_pow, ← zpow_natCast c 4, ← zpow_natCast d 4, ← zpow_natCast (c ^ a) 4,
          ← zpow_natCast (d ^ b) 4, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm a,
          mul_comm b]

theorem ka_pl4_isCyclic_of_comparable {G : Type*} [Group G] [Finite G]
    (h : ∀ x y : G, x ∈ Subgroup.zpowers y ∨ y ∈ Subgroup.zpowers x) : IsCyclic G := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨g, -, hg⟩ := Finset.exists_max_image (Finset.univ : Finset G) (fun x => orderOf x)
    ⟨1, Finset.mem_univ _⟩
  refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, eq_top_iff.2 fun y _ => ?_⟩
  rcases h y g with hy | hy
  · exact hy
  · have hle : Subgroup.zpowers g ≤ Subgroup.zpowers y := (Subgroup.zpowers_le).2 hy
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers, Nat.card_zpowers]
      exact hg y (Finset.mem_univ _)
    rw [Subgroup.eq_of_le_of_card_ge hle hcard]
    exact Subgroup.mem_zpowers y

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem ka_conj_inj_pl4 {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2) :
    Function.Injective
      (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)) :=
  CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)

theorem ka_conjAut_inner_of_det_pow4 {F : Type} [Field F] [Finite F] (M : GL (Fin 4) F)
    (μ : Fˣ) (h : (M : Matrix (Fin 4) (Fin 4) F).det = (μ : F) ^ 4) :
    conjAut 4 F M ∈ innSub (projectiveSL 4 F) := by
  have hdet : GeneralLinearGroup.det M = μ ^ 4 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_pow_eq_pow_val]
  have hscal : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 4) μ⁻¹) = (μ⁻¹) ^ 4 := by
    ext
    simp [GeneralLinearGroup.scalar]
  set B : GL (Fin 4) F := GeneralLinearGroup.scalar (Fin 4) μ⁻¹ * M with hB
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, hscal, hdet, ← mul_pow, inv_mul_cancel, one_pow]
  have hBmem : (B : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    have := congrArg (fun x : Fˣ => (x : F)) hdetB
    simpa using this
  let g : SpecialLinearGroup (Fin 4) F := ⟨(B : Matrix (Fin 4) (Fin 4) F), hBmem⟩
  refine ⟨proj 4 F g, ?_⟩
  rw [← conjAut_toGL]
  have hg : SpecialLinearGroup.toGL g = B := by
    ext1
    rfl
  rw [hg, hB, map_mul, conjAut_scalar, one_mul]

theorem ka_conjAut_inner_of_odd_pl4 {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2)
    (A : GL (Fin 4) F) (ho : Odd (orderOf (conjAut 4 F A))) :
    conjAut 4 F A ∈ innSub (projectiveSL 4 F) := by
  obtain ⟨k, hk⟩ := ho
  have h1 : conjAut 4 F A ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have h2 : conjAut 4 F (A ^ (2 * k + 1)) * fieldAut 4 F 1 = 1 := by
    rw [map_pow, map_one, mul_one]
    exact h1
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h2
  have hdet : GeneralLinearGroup.det A ^ (2 * k + 1) = c ^ 4 := by
    rw [← map_pow, ← hc]
    ext
    simp [GeneralLinearGroup.scalar]
  obtain ⟨μ, hμ⟩ := ka_pl4_exists_pow_four_of_pow_odd (GeneralLinearGroup.det A) c k hdet
  refine ka_conjAut_inner_of_det_pow4 A μ ?_
  rw [← Units.val_pow_eq_pow_val, ← hμ, Matrix.GeneralLinearGroup.val_det_apply]

theorem ka_outCyc_pl4 {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2) :
    KAOutCyc (projectiveSL 4 F) := by
  intro p hp hp2 P hPp hPinn
  have hdiag : ¬ p ∣ Nat.gcd 4 (Nat.card F - 1) := by
    intro hd
    have h4 : p ∣ 2 ^ 2 := hd.trans (Nat.gcd_dvd_left _ _)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  obtain ⟨D, E, -, hD2, hpE, -, hcomp⟩ :=
    CFSG.RankThree.PartOne.OutStructure.outPNice_projectiveSL hp hp2 (by norm_num) hdiag
  have hpow : ∀ x : ↥P, ∃ k : ℕ, (x : MulAut (projectiveSL 4 F)) ^ (p ^ k) ∈ D := by
    intro x
    obtain ⟨k, hk⟩ := hPp x
    refine ⟨k, ?_⟩
    have : (x : MulAut (projectiveSL 4 F)) ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    rw [this]
    exact D.one_mem
  have key : ∀ x y : ↥P, (∃ m : ℤ, (x : MulAut (projectiveSL 4 F)) *
      (y : MulAut (projectiveSL 4 F)) ^ m ∈ D) → x ∈ Subgroup.zpowers y := by
    rintro x y ⟨m, hm⟩
    have hzP : (x : MulAut (projectiveSL 4 F)) * (y : MulAut (projectiveSL 4 F)) ^ m ∈ P :=
      P.mul_mem x.2 (P.zpow_mem y.2 m)
    obtain ⟨k, hk⟩ := hPp ⟨_, hzP⟩
    have hk' : ((x : MulAut (projectiveSL 4 F)) * (y : MulAut (projectiveSL 4 F)) ^ m) ^ (p ^ k) =
        1 := by
      simpa using congrArg Subtype.val hk
    have hinn := hD2 _ hm k (by rw [hk']; exact one_mem _)
    have h1 := hPinn _ hzP hinn
    refine ⟨-m, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, _root_.zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  refine ka_pl4_isCyclic_of_comparable fun x y => ?_
  rcases hcomp x (hpE x (hpow x)) y (hpE y (hpow y)) (hpow x) (hpow y) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (key x y ⟨m, hm⟩)
  · exact Or.inr (key y x ⟨m, hm⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
