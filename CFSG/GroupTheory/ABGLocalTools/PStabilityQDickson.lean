module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.GroupTheory.ABGLocalTools.PStabilityQBorel
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Certificates.Certificate43
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.ZMod.Torsion

public section

open Subgroup

namespace CFSG.ABGLocalTools

open SL2Facts
open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower)

section SL2Basics

variable {F : Type*} [Field F]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem sl2_eq_one_or_neg_one_of_sq_eq_one (h2 : (2 : F) ≠ 0) {A : SL2} (hA : A ^ 2 = 1) :
    A = 1 ∨ A = -1 := by
  have hsq := pow_succ_eq A 1
  rw [hA, Matrix.SpecialLinearGroup.coe_one] at hsq
  simp only [U_add_two, U_one, U_zero, zero_add, mul_one, sub_zero, one_smul] at hsq
  set τ := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) with hτ
  have hτA : τ • (A : Matrix (Fin 2) (Fin 2) F) = (2 : F) • 1 := by
    rw [two_smul, sub_eq_iff_eq_add.mp hsq.symm]
  by_cases hτ0 : τ = 0
  · exfalso
    rw [hτ0, zero_smul] at hτA
    have := congrFun (congrFun hτA 0) 0
    simp at this
    exact h2 this.symm
  · have hAc : (A : Matrix (Fin 2) (Fin 2) F) = (τ⁻¹ * 2) • 1 := by
      have := congrArg (fun M => τ⁻¹ • M) hτA
      simp only [smul_smul, inv_mul_cancel₀ hτ0, one_smul] at this
      exact this
    have hdet := det_eq A
    have h00 := congrFun (congrFun hAc 0) 0
    have h11 := congrFun (congrFun hAc 1) 1
    have h01 := congrFun (congrFun hAc 0) 1
    have h10 := congrFun (congrFun hAc 1) 0
    simp at h00 h11 h01 h10
    rw [h00, h11, h01, h10] at hdet
    set c := τ⁻¹ * 2
    have : (c - 1) * (c + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with hc | hc
    · left
      apply Subtype.ext
      rw [hAc, Matrix.SpecialLinearGroup.coe_one, sub_eq_zero.mp hc, one_smul]
    · right
      apply Subtype.ext
      rw [hAc, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        eq_neg_of_add_eq_zero_left hc, neg_smul, one_smul]

theorem sl2_neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : SL2) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL2 => A 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
  simp at this
  apply h2
  linear_combination -this

theorem sl2_mem_center_iff {A : SL2} : A ∈ center SL2 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    simp only [Fintype.card_fin] at hr
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h | h
    · left
      apply Subtype.ext
      rw [← hrA, sub_eq_zero.mp h, Matrix.SpecialLinearGroup.coe_one, map_one]
    · right
      apply Subtype.ext
      rw [← hrA, eq_neg_of_add_eq_zero_left h, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, map_neg, map_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem two_ne_zero_of_odd_card [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  intro h2
  have hchar : ringChar F = 2 := by
    have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by exact_mod_cast h2)
    have hp2 : (ringChar F).Prime := by
      obtain ⟨n, hn⟩ := FiniteField.card F (ringChar F)
      exact hn.1
    exact (Nat.prime_dvd_prime_iff_eq hp2 Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card] at heven
  have := Nat.odd_iff.mp hodd
  omega

theorem isOddPrimePower_card [Finite F] (hodd : Odd (Nat.card F)) :
    IsOddPrimePower (Nat.card F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r, hr, n, hrp, hn⟩ := FiniteField.card' (K := F)
  rw [← Nat.card_eq_fintype_card] at hn
  refine ⟨r, n, hrp, ?_, n.pos, hn⟩
  rcases hrp.eq_two_or_odd' with h | h
  · exfalso
    rw [hn, h] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  · exact h

end SL2Basics

section PSL2Facts

variable {K : Type*} [Field K]

theorem psl2_exists_not_commute :
    ∃ x y : PSL2 K, x * y ≠ y * x := by
  let a : Matrix.SpecialLinearGroup (Fin 2) K := uT 1
  let b : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨(a : PSL2 K), (b : PSL2 K), fun h => ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have hba : b * a = (a * b) * ((a * b)⁻¹ * (b * a)) := by group
  have hab : ((a * b : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![2, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [a, b, coe_uT]
    norm_num
  have hba' : ((b * a : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 1; 1, 2] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [a, b, coe_uT]
    norm_num
  rcases sl2_mem_center_iff.mp h with h1 | h1
  · rw [h1, mul_one] at hba
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => A 0 0) hba
    simp only [hab, hba'] at this
    simp at this
    have h' : (1 : K) = 0 := by linear_combination -this
    exact one_ne_zero h'
  · rw [h1] at hba
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => A 0 1) hba
    simp only [mul_neg, mul_one, Matrix.SpecialLinearGroup.coe_neg, hab, hba'] at this
    simp at this
    have h' : (2 : K) = 0 := by linear_combination this
    have h'' : (1 : K) = 0 := by
      have h3 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => A 0 0) hba
      simp only [mul_neg, mul_one, Matrix.SpecialLinearGroup.coe_neg, hab, hba'] at h3
      simp at h3
      linear_combination h3 - h'
    exact one_ne_zero h''

variable [Finite K]

theorem alternatingGroup_four_index_ne_two (M : Subgroup (alternatingGroup (Fin 4))) :
    M.index ≠ 2 := by
  classical
  intro hM
  have hsub' : Subgroup.closure {σ : Equiv.Perm (Fin 4) | σ.IsThreeCycle} ≤
      M.map (alternatingGroup (Fin 4)).subtype := by
    rw [Subgroup.closure_le]
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 4) := Equiv.Perm.IsThreeCycle.mem_alternatingGroup hσ
    refine ⟨⟨σ, hσA⟩, ?_, rfl⟩
    have h3 : (⟨σ, hσA⟩ : alternatingGroup (Fin 4)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← Equiv.Perm.IsThreeCycle.orderOf hσ, pow_orderOf_eq_one]
      rfl
    have hsq := Subgroup.sq_mem_of_index_two hM ((⟨σ, hσA⟩ : alternatingGroup (Fin 4)) ^ 2)
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul] at hsq
    exact hsq
  have hsub : (alternatingGroup (Fin 4) : Subgroup (Equiv.Perm (Fin 4))) ≤
      M.map (alternatingGroup (Fin 4)).subtype := by
    rw [Equiv.Perm.closure_three_cycles_eq_alternating] at hsub'
    exact hsub'
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hsub x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  rw [htop, Subgroup.index_top] at hM
  exact absurd hM (by norm_num)

theorem psl2_index_ne_two (hK : Odd (Nat.card K)) (M : Subgroup (PSL2 K)) : M.index ≠ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro hM
  by_cases h3 : Nat.card K = 3
  · have hFcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact h3
    let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let e : PSL2 K ≃* alternatingGroup (Fin 4) :=
      (CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
        CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup
    apply alternatingGroup_four_index_ne_two (M.map e.toMonoidHom)
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact hM
  · have hK4 : 4 ≤ Nat.card K := by
      have h2 : 2 ≤ Nat.card K := by
        have := Fintype.one_lt_card (α := K)
        rw [Nat.card_eq_fintype_card]; omega
      rcases hK with ⟨m, hm⟩
      omega
    have hsimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
    have hMn : M.Normal := Subgroup.normal_of_index_eq_two hM
    rcases (haveI := hMn; hsimple.eq_bot_or_eq_top_of_normal M) with h | h
    · obtain ⟨x, y, hxy⟩ := psl2_exists_not_commute (K := K)
      rw [h, Subgroup.index_bot] at hM
      have hcomm : ∀ a b : PSL2 K, a * b = b * a := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hcyc : IsCyclic (PSL2 K) := isCyclic_of_prime_card hM
        exact fun a b => (IsCyclic.commGroup.mul_comm a b)
      exact hxy (hcomm x y)
    · rw [h, Subgroup.index_top] at hM
      exact absurd hM (by norm_num)

theorem psl2_card_eq (hK : Odd (Nat.card K)) :
    Nat.card (PSL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
  CFSG.GorensteinWalter.psl2_card_formula K (isOddPrimePower_card hK)

end PSL2Facts

section Arithmetic

theorem psl2_card_values {k : ℕ} (hk : Odd k) (h3 : 3 ≤ k) :
    (k * (k ^ 2 - 1) / 2 = 12 ∧ k = 3) ∨ (k * (k ^ 2 - 1) / 2 = 60 ∧ k = 5) ∨
      168 ≤ k * (k ^ 2 - 1) / 2 := by
  rcases hk with ⟨m, rfl⟩
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m
    · omega
    · left; norm_num
    · right; left; norm_num
  · right; right
    have h7 : 7 ≤ 2 * m + 1 := by omega
    have h48 : 48 ≤ (2 * m + 1) ^ 2 - 1 := by
      have : 49 ≤ (2 * m + 1) ^ 2 := by nlinarith
      omega
    have : 336 ≤ (2 * m + 1) * ((2 * m + 1) ^ 2 - 1) := by nlinarith
    omega

theorem eq_of_mul_sq_sub_one_div_two_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * (x ^ 2 - 1) / 2 = y * (y ^ 2 - 1) / 2) : x = y := by
  have key : ∀ a b : ℕ, 1 ≤ a → a < b → a * (a ^ 2 - 1) + 6 ≤ b * (b ^ 2 - 1) := by
    intro a b ha hab
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
    have h1 : (n + 1) ^ 2 - 1 = n * (n + 2) := by
      have : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring
      omega
    have h2 : (n + 2) ^ 2 - 1 = (n + 1) * (n + 3) := by
      have : (n + 2) ^ 2 = (n + 1) * (n + 3) + 1 := by ring
      omega
    have hmono : (n + 2) * ((n + 2) ^ 2 - 1) ≤ b * (b ^ 2 - 1) := by
      apply Nat.mul_le_mul (by omega)
      apply Nat.sub_le_sub_right
      exact Nat.pow_le_pow_left (by omega) 2
    rw [h1]
    rw [h2] at hmono
    nlinarith
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := key x y hx hxy
    omega
  · exact hxy
  · have := key y x hy hxy
    omega

end Arithmetic

section GroupHelpers

variable {G G' : Type*} [Group G] [Group G'] [Finite G]

omit [Finite G] in
theorem card_eq_card_ker_mul_of_surjective {f : G →* G'} (hf : Function.Surjective f) :
    Nat.card G = Nat.card f.ker * Nat.card G' := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem le_center_of_normal_of_card_eq_two {M : Subgroup G} (hM : M.Normal)
    (h2 : Nat.card M = 2) : M ≤ Subgroup.center G := by
  intro m hm
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hm1 : m = 1
  · rw [hm1, one_mul, mul_one]
  have hconj : g * m * g⁻¹ ∈ M := hM.conj_mem m hm g
  have hne : g * m * g⁻¹ ≠ 1 := by
    intro h
    apply hm1
    have : m = g⁻¹ * (g * m * g⁻¹) * g := by group
    rw [this, h]; group
  have h2' : ∀ a b : M, a ≠ 1 → b ≠ 1 → a = b := by
    classical
    intro a b ha hb
    have hcard : Nat.card M = 2 := h2
    by_contra hab
    have : Fintype M := Fintype.ofFinite M
    have h3 : ({1, a, b} : Finset M).card ≤ Fintype.card M := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair hab, ← Nat.card_eq_fintype_card, hcard] at h3
    omega
  have := h2' ⟨g * m * g⁻¹, hconj⟩ ⟨m, hm⟩ (fun h => hne (congrArg Subtype.val h))
    (fun h => hm1 (congrArg Subtype.val h))
  have heq : g * m * g⁻¹ = m := congrArg Subtype.val this
  calc g * m = g * m * g⁻¹ * g := by group
    _ = m * g := by rw [heq]

theorem card_ne_two_mul_of_center_eq_bot (hZ : Subgroup.center G = ⊥) {f : G →* G'}
    (hf : Function.Surjective f) : Nat.card G ≠ 2 * Nat.card G' := by
  intro h
  have : Finite G' := Finite.of_surjective f hf
  have hcard := card_eq_card_ker_mul_of_surjective hf
  have hpos : 0 < Nat.card G' := Nat.card_pos
  have hker : Nat.card f.ker = 2 := by
    rw [h] at hcard
    exact (Nat.eq_of_mul_eq_mul_right hpos hcard).symm
  have hle := le_center_of_normal_of_card_eq_two (MonoidHom.normal_ker f) hker
  rw [hZ, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hker
  omega

theorem isSimpleGroup_of_mulEquiv {H : Type*} [Group H] [IsSimpleGroup G'] (e : H ≃* G') :
    IsSimpleGroup H := by
  have : Nontrivial H := e.surjective.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end GroupHelpers

section Dickson

variable {F K : Type} [Field F] [Finite F] [Field K] [Finite K]

theorem center_perm_fin_four_eq_bot : Subgroup.center (Equiv.Perm (Fin 4)) = ⊥ := by
  rw [← Subgroup.map_center_eq CFSG.GorensteinWalter.pgl2_three_equiv_perm,
    CFSG.GorensteinWalter.pgl2_center_eq_bot, Subgroup.map_bot]

theorem center_eq_bot_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : Subgroup.center G' = ⊥) : Subgroup.center G = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

omit [Finite K] in
theorem false_of_comm_of_surjective {G : Type*} [Group G] {θ : G →* PSL2 K}
    (hθ : Function.Surjective θ) (hcomm : ∀ a b : G, a * b = b * a) : False := by
  obtain ⟨x, y, hxy⟩ := psl2_exists_not_commute (K := K)
  obtain ⟨a, rfl⟩ := hθ x
  obtain ⟨b, rfl⟩ := hθ y
  exact hxy (by rw [← map_mul, ← map_mul, hcomm])

theorem three_le_card_of_odd (hK : Odd (Nat.card K)) : 3 ≤ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : 2 ≤ Nat.card K := by
    have := Fintype.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card]; omega
  rcases hK with ⟨m, hm⟩
  omega

theorem psl2_card_cases (hK : Odd (Nat.card K)) :
    (Nat.card (PSL2 K) = 12 ∧ Nat.card K = 3) ∨ (Nat.card (PSL2 K) = 60 ∧ Nat.card K = 5) ∨
      168 ≤ Nat.card (PSL2 K) := by
  rw [psl2_card_eq hK]
  exact psl2_card_values hK (three_le_card_of_odd hK)

theorem twelve_le_card_psl2 (hK : Odd (Nat.card K)) : 12 ≤ Nat.card (PSL2 K) := by
  rcases psl2_card_cases hK with ⟨h, -⟩ | ⟨h, -⟩ | h <;> omega

theorem card_psl2_of_dvd_24 (hK : Odd (Nat.card K)) (h : Nat.card (PSL2 K) ∣ 24) :
    Nat.card (PSL2 K) = 12 ∧ Nat.card K = 3 := by
  have := Nat.le_of_dvd (by norm_num) h
  rcases psl2_card_cases hK with h' | ⟨h', -⟩ | h'
  · exact h'
  · omega
  · omega

omit [Finite K] in
theorem card_psl2_dvd_of_surjective {G : Type*} [Group G] [Finite G] {θ : G →* PSL2 K}
    (hθ : Function.Surjective θ) : Nat.card (PSL2 K) ∣ Nat.card G :=
  Dvd.intro_left _ (card_eq_card_ker_mul_of_surjective hθ).symm

theorem card_eq_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hK : Odd (Nat.card K)) {θ : G →* PSL2 K} (hθ : Function.Surjective θ) :
    Nat.card G = Nat.card (PSL2 K) := by
  have hcard := card_eq_card_ker_mul_of_surjective hθ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with h | h
  · rw [hcard, h, Subgroup.card_bot, one_mul]
  · exfalso
    rw [h, Subgroup.card_top] at hcard
    have hG : 0 < Nat.card G := Nat.card_pos
    have h1 : Nat.card (PSL2 K) = 1 := by
      have : Nat.card G * 1 = Nat.card G * Nat.card (PSL2 K) := by rw [mul_one]; exact hcard
      exact (Nat.eq_of_mul_eq_mul_left hG this).symm
    have := twelve_le_card_psl2 hK
    omega

theorem map_eq_top_of_index_two {G : Type*} [Group G] (hK : Odd (Nat.card K))
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) {A : Subgroup G} (hA : A.index = 2) :
    A.map θ = ⊤ := by
  have hB : (A.map θ).index ∣ 2 := (Subgroup.index_map_dvd A hθ).trans (dvd_of_eq hA)
  rw [← Subgroup.index_eq_one]
  rcases (Nat.dvd_prime Nat.prime_two).mp hB with h | h
  · exact h
  · exact absurd h (psl2_index_ne_two hK _)

omit [Finite K] in
theorem false_of_map_eq_top_of_comm {G : Type*} [Group G] {θ : G →* PSL2 K} {A : Subgroup G}
    (hA : A.map θ = ⊤) (hcomm : ∀ a b : G, a ∈ A → b ∈ A → a * b = b * a) : False := by
  apply false_of_comm_of_surjective (θ := θ.comp A.subtype) (G := A)
  · intro y
    have hy : y ∈ A.map θ := hA ▸ Subgroup.mem_top y
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨⟨a, ha⟩, rfl⟩
  · intro a b
    exact Subtype.ext (hcomm a b a.2 b.2)

theorem false_of_dihedral (hK : Odd (Nat.card K)) {G : Type*} [Group G] [Finite G]
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) {z : ℕ} (e : G ≃* DihedralGroup z) : False := by
  have hz : z ≠ 0 := by
    rintro rfl
    have h1 := Nat.card_pos (α := G)
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h1
    omega
  have : NeZero z := ⟨hz⟩
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1)
  let A : Subgroup G := R.comap e.toMonoidHom
  have hRidx : R.index = 2 := by
    have h1 := R.index_mul_card
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hz) h1
  have hAidx : A.index = 2 := by
    rw [Subgroup.index_comap_of_surjective R e.surjective, hRidx]
  apply false_of_map_eq_top_of_comm (map_eq_top_of_index_two hK hθ hAidx)
  intro a b ha hb
  apply e.injective
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  change DihedralGroup.r 1 ^ i = e a at hi
  change DihedralGroup.r 1 ^ j = e b at hj
  rw [map_mul, map_mul, ← hi, ← hj]
  exact Commute.zpow_zpow_self _ i j

theorem false_of_perm_four (hK : Odd (Nat.card K)) {G : Type*} [Group G] [Finite G]
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) (e : G ≃* Equiv.Perm (Fin 4)) : False := by
  have h24 : Nat.card G = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hs := card_psl2_of_dvd_24 hK (h24 ▸ card_psl2_dvd_of_surjective hθ)
  exact card_ne_two_mul_of_center_eq_bot
    (center_eq_bot_of_mulEquiv e center_perm_fin_four_eq_bot) hθ (by omega)

theorem false_of_semidirect (hK : Odd (Nat.card K)) {G : Type*} [Group G] [Finite G]
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) {r : ℕ} (hr : r.Prime) (hrodd : Odd r)
    {N C : Subgroup G} (hNn : N.Normal) [CFSG.IsElementaryAbelian r N] (hC : IsCyclic C)
    (hsup : N ⊔ C = ⊤) : False := by
  have hN' : N.map θ = ⊥ :=
    CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_psl2_odd K (isOddPrimePower_card hK) r hr
      hrodd (N.map θ) (hNn.map θ hθ) ((CFSG.IsElementaryAbelian.isPGroup r N).map θ)
  have hC' : C.map θ = ⊤ := by
    rw [eq_top_iff, ← MonoidHom.range_eq_top.mpr hθ, MonoidHom.range_eq_map, ← hsup,
      Subgroup.map_sup, hN', bot_sup_eq]
  apply false_of_map_eq_top_of_comm hC'
  intro a b ha hb
  have := (IsCyclic.commGroup (α := C)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem four_le_pow_of_ne_three {r m : ℕ} (hr : r.Prime) (hrodd : Odd r) (hm : m ≠ 0)
    (h3 : r ^ m ≠ 3) : 4 ≤ r ^ m := by
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    rcases hrodd with ⟨k, hk⟩
    omega
  have : r ≤ r ^ m := Nat.le_self_pow hm r
  omega

theorem card_eq_of_psl2_subfield (hK : Odd (Nat.card K)) {G : Type*} [Group G] [Finite G]
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) {r m : ℕ} [Fact r.Prime] (hrodd : Odd r)
    (hm : m ≠ 0) (e : G ≃* PSL2 (GaloisField r m)) (hchar : ringChar K ≠ r ∨ Nat.card K = 5) :
    Nat.card G = Nat.card (PSL2 K) ∧ (Nat.card K = 3 ∨ Nat.card K = 5) := by
  have hrp : r.Prime := Fact.out
  have hq0 : Nat.card (GaloisField r m) = r ^ m := GaloisField.card r m hm
  have hGF : Odd (Nat.card (GaloisField r m)) := by rw [hq0]; exact hrodd.pow
  have hGcard : Nat.card G = r ^ m * ((r ^ m) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, ← hq0]
    exact psl2_card_eq hGF
  by_cases hq3 : r ^ m = 3
  · have h12 : Nat.card G = 12 := by rw [hGcard, hq3]; norm_num
    have hdvd := card_psl2_dvd_of_surjective hθ
    rw [h12] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases psl2_card_cases hK with h' | ⟨h', -⟩ | h'
    · exact ⟨by omega, Or.inl h'.2⟩
    · omega
    · omega
  · have hq4 : 4 ≤ Nat.card (GaloisField r m) := by
      rw [hq0]; exact four_le_pow_of_ne_three hrp hrodd hm hq3
    have : IsSimpleGroup (PSL2 (GaloisField r m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
    have : IsSimpleGroup G := isSimpleGroup_of_mulEquiv e
    have hGs := card_eq_of_isSimpleGroup hK hθ
    have hkq : Nat.card K = r ^ m := by
      apply eq_of_mul_sq_sub_one_div_two_eq (three_le_card_of_odd hK |>.trans' (by norm_num))
        (Nat.one_le_pow _ _ hrp.pos)
      rw [← psl2_card_eq hK, ← hGs, hGcard]
    refine ⟨hGs, ?_⟩
    rcases hchar with h | h
    · exfalso
      have : CharP K r := charP_of_card_eq_prime_pow hrp hkq
      exact h (ringChar.eq K r)
    · exact Or.inr h

theorem false_of_pgl2_subfield (hK : Odd (Nat.card K)) {G : Type} [Group G] [Finite G]
    {θ : G →* PSL2 K} (hθ : Function.Surjective θ) {r m : ℕ} [Fact r.Prime] (hrodd : Odd r)
    (hm : m ≠ 0) (e : G ≃* PGL2 (GaloisField r m)) : False := by
  have hrp : r.Prime := Fact.out
  have hq0 : Nat.card (GaloisField r m) = r ^ m := GaloisField.card r m hm
  have hGF : Odd (Nat.card (GaloisField r m)) := by rw [hq0]; exact hrodd.pow
  have hZ : Subgroup.center G = ⊥ :=
    center_eq_bot_of_mulEquiv e (CFSG.GorensteinWalter.pgl2_center_eq_bot _)
  have hGcard : Nat.card G = r ^ m * ((r ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, ← hq0]
    exact CFSG.GorensteinWalter.pgl2_card_formula _
  have heven : 2 ∣ r ^ m * ((r ^ m) ^ 2 - 1) := by
    have hodd : Odd (r ^ m) := hrodd.pow
    have : Even ((r ^ m) ^ 2 - 1) := by
      rcases hodd with ⟨a, ha⟩
      rw [ha]
      exact ⟨2 * a ^ 2 + 2 * a, by ring_nf; omega⟩
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp this) _
  by_cases hq3 : r ^ m = 3
  · have h24 : Nat.card G = 24 := by rw [hGcard, hq3]; norm_num
    have hs := card_psl2_of_dvd_24 hK (h24 ▸ card_psl2_dvd_of_surjective hθ)
    exact card_ne_two_mul_of_center_eq_bot hZ hθ (by omega)
  · have hq3' : 3 < Nat.card (GaloisField r m) := by
      rw [hq0]; have := four_le_pow_of_ne_three hrp hrodd hm hq3; omega
    obtain ⟨L, -, -, ⟨eL⟩⟩ :=
      CFSG.GorensteinWalter.exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
        (⊤ : Subgroup G) inferInstance (GaloisField r m) (isOddPrimePower_card hGF) hq3'
        (Subgroup.topEquiv.trans e)
    have hLcard : Nat.card L = r ^ m * ((r ^ m) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eL.toEquiv, ← hq0]
      exact psl2_card_eq hGF
    have hLidx : L.index = 2 := by
      have h1 := L.index_mul_card
      rw [hLcard, hGcard] at h1
      obtain ⟨c, hc⟩ := heven
      rw [hc, Nat.mul_div_cancel_left _ two_pos] at h1
      have hpos : 0 < c := by
        rw [← Nat.mul_div_cancel_left c two_pos, ← hc, ← hLcard]
        exact Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1])
    have hB1 := map_eq_top_of_index_two hK hθ hLidx
    let θL : L →* PSL2 K := θ.comp L.subtype
    have hθL : Function.Surjective θL := by
      intro y
      have hy : y ∈ L.map θ := hB1 ▸ Subgroup.mem_top y
      obtain ⟨a, ha, rfl⟩ := hy
      exact ⟨⟨a, ha⟩, rfl⟩
    have : IsSimpleGroup (PSL2 (GaloisField r m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have : IsSimpleGroup L := isSimpleGroup_of_mulEquiv eL
    have hLs := card_eq_of_isSimpleGroup hK hθL
    apply card_ne_two_mul_of_center_eq_bot hZ hθ
    have h1 := L.index_mul_card
    rw [hLidx, hLs] at h1
    exact h1.symm

theorem dickson_core
    {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (hK : Odd (Nat.card K)) (hchar : ringChar K ≠ ringChar F ∨ Nat.card K = 5)
    (H : Subgroup (PSL2 F)) (θ : H →* PSL2 K) (hθ : Function.Surjective θ) :
    Nat.card H = Nat.card (PSL2 K) ∧ (Nat.card K = 3 ∨ Nat.card K = 5) := by
  classical
  obtain ⟨r, f, hrp, hrodd, -, hFcard⟩ := isOddPrimePower_card hF
  have : Fact r.Prime := ⟨hrp⟩
  have : CharP F r := charP_of_card_eq_prime_pow hrp hFcard
  have hcharF : ringChar F = r := ringChar.eq F r
  rw [hcharF] at hchar
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFcard H with
    helem | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hNn, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  · exact (false_of_comm_of_surjective hθ fun a b => helem.is_comm.comm a b).elim
  · exact (false_of_comm_of_surjective hθ fun a b =>
      (IsCyclic.commGroup (α := H)).mul_comm a b).elim
  · exact (false_of_dihedral hK hθ e).elim
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hdvd := card_psl2_dvd_of_surjective hθ
    rw [h12] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases psl2_card_cases hK with h' | ⟨h', -⟩ | h'
    · exact ⟨by omega, Or.inl h'.2⟩
    · omega
    · omega
  · exact (false_of_perm_four hK hθ e).elim
  ·
    have : IsSimpleGroup H := isSimpleGroup_of_mulEquiv e
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hHs := card_eq_of_isSimpleGroup hK hθ
    rcases psl2_card_cases hK with ⟨h', -⟩ | ⟨-, h'⟩ | h'
    · omega
    · exact ⟨hHs, Or.inr h'⟩
    · omega
  · exact (false_of_semidirect hK hθ hrp hrodd hNn hCcyc hsup).elim
  · exact card_eq_of_psl2_subfield hK hθ hrodd hm e hchar
  · exact (false_of_pgl2_subfield hK hθ hrodd hm e).elim

end Dickson

section SL2Quotient

variable {F K : Type} [Field F] [Finite F] [Field K] [Finite K]

theorem card_sl2_eq_two_mul_card_psl2 (hK : Odd (Nat.card K)) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 * Nat.card (PSL2 K) := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, psl2_card_eq hK]
  have : Even (Nat.card K ^ 2 - 1) := by
    rcases hK with ⟨a, ha⟩
    rw [ha]
    exact ⟨2 * a ^ 2 + 2 * a, by ring_nf; omega⟩
  obtain ⟨c, hc⟩ := Dvd.dvd.mul_left (even_iff_two_dvd.mp this) (Nat.card K)
  rw [hc, Nat.mul_div_cancel_left _ two_pos]

theorem card_center_sl2 (hF : Odd (Nat.card F)) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [card_sl2_eq_two_mul_card_psl2 hF] at h1
  have hpos : 0 < Nat.card (PSL2 F) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h1)).symm

theorem sl2_quotient_core
    (hF : Odd (Nat.card F)) (hK : Odd (Nat.card K))
    (hchar : ringChar K ≠ ringChar F ∨ Nat.card K = 5)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) K) (hφ : Function.Surjective φ) :
    (Nat.card K = 3 ∨ Nat.card K = 5) ∧ Function.Injective φ := by
  classical
  have h2F := two_ne_zero_of_odd_card hF
  have h2K := two_ne_zero_of_odd_card hK
  set ZF := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)
  set ZK := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈ X := by
    have h2 : 2 ∣ Nat.card X := by
      have hdvd : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ Nat.card X :=
        Dvd.intro_left _ (card_eq_card_ker_mul_of_surjective hφ).symm
      exact (Dvd.intro _ (card_sl2_eq_two_mul_card_psl2 hK).symm).trans hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
    have hx2 : ((x : Matrix.SpecialLinearGroup (Fin 2) F)) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      have := congrArg Subtype.val h
      simpa using this
    rcases sl2_eq_one_or_neg_one_of_sq_eq_one h2F hx2 with h | h
    · exfalso
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · exact h ▸ x.2
  let m1 : X := ⟨-1, hneg⟩
  have hφm1 : φ m1 ∈ ZK := by
    have : φ m1 ^ 2 = 1 := by
      rw [← map_pow]
      have : m1 ^ 2 = 1 := Subtype.ext (by simp [m1])
      rw [this, map_one]
    exact sl2_mem_center_iff.mpr (sl2_eq_one_or_neg_one_of_sq_eq_one h2K this)
  let ρ : X →* PSL2 F := (QuotientGroup.mk' ZF).comp X.subtype
  let θ0 : X →* PSL2 K := (QuotientGroup.mk' ZK).comp φ
  have hle : ρ.ker ≤ θ0.ker := by
    intro x hx
    have hxZ : (x : Matrix.SpecialLinearGroup (Fin 2) F) ∈ ZF :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' ZK (φ x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rcases sl2_mem_center_iff.mp hxZ with h | h
    · have : x = 1 := Subtype.ext h
      rw [this, map_one]
      exact one_mem _
    · have : x = m1 := Subtype.ext h
      rw [this]
      exact hφm1
  let θ1 : X ⧸ ρ.ker →* PSL2 K := QuotientGroup.lift ρ.ker θ0 hle
  let eρ : X ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  let θ : ρ.range →* PSL2 K := θ1.comp eρ.symm.toMonoidHom
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective ZK y
    obtain ⟨x, rfl⟩ := hφ z
    refine ⟨eρ (x : X ⧸ ρ.ker), ?_⟩
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, θ1,
      QuotientGroup.lift_mk, θ0]
  obtain ⟨hHcard, hK35⟩ := dickson_core hF hK hchar ρ.range θ hθ
  refine ⟨hK35, ?_⟩
  have hX := card_eq_card_ker_mul_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hX
  have hker : Nat.card ρ.ker ≤ 2 := by
    have hinj : Function.Injective (fun x : ρ.ker => (⟨((x : X) : Matrix.SpecialLinearGroup
        (Fin 2) F), (QuotientGroup.eq_one_iff _).mp x.2⟩ : ZF)) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    calc Nat.card ρ.ker ≤ Nat.card ZF := Nat.card_le_card_of_injective _ hinj
      _ = 2 := card_center_sl2 hF
  have hle' : Nat.card X ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [hX, card_sl2_eq_two_mul_card_psl2 hK, ← hHcard]
    exact Nat.mul_le_mul_right _ hker
  exact (hφ.bijective_of_nat_card_le hle').1

end SL2Quotient

theorem sl2DicksonQuotient : SL2DicksonQuotient := by
  intro F _ _ p _ hp hFodd hpF g₁ g₂ hg₁ _ hsurj
  classical
  have hpp : p.Prime := Fact.out
  set X := closure ({g₁, g₂} : Set (Matrix.SpecialLinearGroup (Fin 2) F))
  have hg₁X : g₁ ∈ X := subset_closure (Set.mem_insert _ _)
  have hexp : ∀ (K : Type) [Field K] [Finite K] (φ : X →* Matrix.SpecialLinearGroup (Fin 2) K),
      Function.Injective φ → (Nat.card K = 3 ∨ Nat.card K = 5) →
      ∀ w ∈ X, w ^ 4 = 1 ∨ w ^ 6 = 1 ∨ w ^ 10 = 1 := by
    intro K _ _ φ hinj hK35 w hw
    have hpow : ∀ n : ℕ, φ ⟨w, hw⟩ ^ n = 1 → w ^ n = 1 := by
      intro n hn
      rw [← map_pow, ← map_one φ] at hn
      have := hinj hn
      exact congrArg Subtype.val this
    rcases hK35 with h3 | h5
    · have : CharP K 3 := charP_of_card_eq_prime_pow (n := 1) Nat.prime_three (by rw [h3]; rfl)
      rcases SL2Facts.pow_four_or_six_or_ten_of_prime_card h3 SL2Facts.U_exponent_three
          (φ ⟨w, hw⟩) with h | h | h
      · exact Or.inl (hpow 4 h)
      · exact Or.inr (Or.inl (hpow 6 h))
      · exact Or.inr (Or.inr (hpow 10 h))
    · have : CharP K 5 := charP_of_card_eq_prime_pow (n := 1) Nat.prime_five (by rw [h5]; rfl)
      rcases SL2Facts.pow_four_or_six_or_ten_of_prime_card h5 SL2Facts.U_exponent_five
          (φ ⟨w, hw⟩) with h | h | h
      · exact Or.inl (hpow 4 h)
      · exact Or.inr (Or.inl (hpow 6 h))
      · exact Or.inr (Or.inr (hpow 10 h))
  have hcharF : ringChar F ≠ p := by
    intro h
    apply hpF
    classical
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hn⟩ := FiniteField.card F (ringChar F)
    rw [Nat.card_eq_fintype_card, hn.2, h]
    exact dvd_pow_self p n.ne_zero
  rcases hsurj with ⟨K, _, _, hKp, φ, hφ⟩ | ⟨φ, hφ⟩
  ·
    have hKodd : Odd (Nat.card K) := by
      classical
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K p
      rw [Nat.card_eq_fintype_card, hn]
      exact (hpp.odd_of_ne_two hp).pow
    obtain ⟨hK35, hinj⟩ := sl2_quotient_core hFodd hKodd
      (Or.inl (by rw [ringChar.eq K p]; exact fun h => hcharF h.symm)) X φ hφ
    refine ⟨?_, hexp K φ hinj hK35⟩
    rcases hK35 with h | h
    · left
      have h3 : CharP K 3 := charP_of_card_eq_prime_pow (n := 1) Nat.prime_three (by rw [h]; rfl)
      exact CharP.eq K hKp h3
    · right
      have h5 : CharP K 5 := charP_of_card_eq_prime_pow (n := 1) Nat.prime_five (by rw [h]; rfl)
      exact CharP.eq K hKp h5
  ·
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h5 : Nat.card (ZMod 5) = 5 := by simp
    have h5odd : Odd (Nat.card (ZMod 5)) := by rw [h5]; exact ⟨2, rfl⟩
    obtain ⟨-, hinj⟩ := sl2_quotient_core hFodd h5odd (Or.inr h5) X φ hφ
    refine ⟨?_, hexp (ZMod 5) φ hinj (Or.inr h5)⟩
    have hcardX : Nat.card X = 120 := by
      rw [Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hφ⟩), CFSG.GorensteinWalter.sl2_card_formula,
        h5]
      norm_num
    have hpX : p ∣ 120 := by
      rw [← hcardX, ← hg₁]
      have := Subgroup.orderOf_dvd_natCard X hg₁X
      exact this
    have : p ∣ 2 ^ 3 * (3 * 5) := hpX
    rcases (Nat.Prime.dvd_mul hpp).mp this with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h)) hp
    · rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).mp h)

end CFSG.ABGLocalTools
