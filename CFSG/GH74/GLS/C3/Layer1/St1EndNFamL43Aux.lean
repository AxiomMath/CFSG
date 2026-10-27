module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL4
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamK2
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamA6

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.L43

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open scoped commutatorElement

section Det

variable {K : Type*} [Field K]

theorem det_coe_scalar {n : ℕ} (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem det_pow_mul_scalar_inv {n : ℕ} (A : GL (Fin n) K) :
    (((A ^ n * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det A)⁻¹ : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [Units.val_mul, Matrix.det_mul, det_coe_scalar, Units.val_pow_eq_pow_val, Matrix.det_pow,
    ← GeneralLinearGroup.val_det_apply, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]

theorem conjAut_mem_inner_of_det {n : ℕ} (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K).det = 1) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  set g : Matrix.SpecialLinearGroup (Fin n) K := ⟨A, hA⟩
  have hg : Matrix.SpecialLinearGroup.toGL g = A := Units.ext rfl
  exact ⟨proj n K g, by rw [← conjAut_toGL, hg]⟩

theorem conjAut_pow_n_mem_inner {n : ℕ} (A : GL (Fin n) K) :
    conjAut n K A ^ n ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have h := conjAut_mem_inner_of_det _ (det_pow_mul_scalar_inv A)
  rwa [map_mul, conjAut_scalar, mul_one, map_pow] at h

end Det

theorem aut_pow_eight_inner {K : Type} [Field K] [Finite K] (hK : Subsingleton (K ≃+* K))
    (τ : MulAut (projectiveSL 4 K)) : τ ^ 8 ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    (LinearFlag.automorphism_generation (K := K) (n := 4) (by norm_num)).2 τ
  have htrans := LinearFlag.standard_automorphism_transport (K := K) (n := 4)
  rw [Subsingleton.elim σ 1, map_one, mul_one]
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 4) K,
      (LinearFlag.conjAut 4 K A * LinearFlag.dualAut 4 K ^ ε) ^ 2 = LinearFlag.conjAut 4 K B := by
    interval_cases ε
    · exact ⟨A * A, by rw [pow_zero, mul_one, pow_two, htrans.1]⟩
    · refine ⟨A * Matrix.GeneralLinearGroup.inverseTranspose A, ?_⟩
      rw [pow_one, pow_two, ← htrans.1, ← htrans.2.2.2.2.1 A]
      group
  have h8 : (LinearFlag.conjAut 4 K A * LinearFlag.dualAut 4 K ^ ε) ^ 8 =
      LinearFlag.conjAut 4 K B ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hB]
  rw [h8]
  exact conjAut_pow_n_mem_inner B

theorem aut_odd_inner {K : Type} [Field K] [Finite K] (hK : Subsingleton (K ≃+* K))
    (τ : MulAut (projectiveSL 4 K)) (hτ : Odd (orderOf τ)) :
    τ ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  have hcop : Nat.Coprime 8 (orderOf τ) := by
    have : Nat.Coprime 2 (orderOf τ) := Nat.coprime_two_left.2 hτ
    exact (show 8 = 2 ^ 3 by norm_num) ▸ Nat.Coprime.pow_left 3 this
  by_cases h1 : orderOf τ = 1
  · rw [orderOf_eq_one_iff.1 h1]
    exact ⟨1, by simp⟩
  · have hgt : 1 < orderOf τ := by
      have := orderOf_pos τ
      omega
    obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hgt
    have : τ = (τ ^ 8) ^ j := by
      rw [← pow_mul, ← pow_mod_orderOf, hj.2, pow_one]
    rw [this]
    exact pow_mem (aut_pow_eight_inner hK τ) j

end CFSG.GH74.GLS.C3.Layer1.EndN.L43
namespace CFSG.GH74.GLS.C3.Layer1.EndN.L43

theorem exists_conj_pow_of_order_five {P : Type} [Group P] [Finite P] (hP : ¬ 25 ∣ Nat.card P)
    {ζ z : P} (hζ : orderOf ζ = 5) (hz : orderOf z = 5) : ∃ (s : P) (i : ℤ), s * ζ ^ i * s⁻¹ = z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card P := hζ ▸ orderOf_dvd_natCard ζ
  have hfac : (Nat.card P).factorization 5 = 1 := by
    have hne : Nat.card P ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card P).factorization 5 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hne, pow_one]
      exact h5
    by_contra hne1
    have h2 : 2 ≤ (Nat.card P).factorization 5 := by omega
    have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 5) (by norm_num) hne).2 h2
    exact hP (by simpa using this)
  have hc1 : Nat.card (Subgroup.zpowers ζ) = 5 ^ (Nat.card P).factorization 5 := by
    rw [Nat.card_zpowers, hζ, hfac, pow_one]
  have hc2 : Nat.card (Subgroup.zpowers z) = 5 ^ (Nat.card P).factorization 5 := by
    rw [Nat.card_zpowers, hz, hfac, pow_one]
  let S1 : Sylow 5 P := Sylow.ofCard (Subgroup.zpowers ζ) hc1
  let S2 : Sylow 5 P := Sylow.ofCard (Subgroup.zpowers z) hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S1 S2
  have hz2 : z ∈ (S2 : Subgroup P) := Subgroup.mem_zpowers z
  rw [← hg] at hz2
  rw [Sylow.smul_def] at hz2
  obtain ⟨t, ht, htz⟩ := (Subgroup.mem_smul_pointwise_iff_exists z (MulAut.conj g) (S1 : Subgroup P)).1 hz2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  refine ⟨g, i, ?_⟩
  rw [← htz]
  simp [MulAut.conj_apply]

end CFSG.GH74.GLS.C3.Layer1.EndN.L43

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem pPrimeCore_eq_bot_of_proj2 (h : Lem711Cfg X L K x y) {E : Type} [Field E] [Finite E]
    (hE : 4 ≤ Nat.card E) (eK : ↥K ≃* projectiveSL 2 E) :
    IsSimpleGroup ↥K ∧ pPrimeCore 2 ↥K = ⊥ := by
  have hsimple : IsSimpleGroup ↥K := by
    have h4 : ∃ s : Finset E, s.card = 4 := by
      classical
      have : Fintype E := Fintype.ofFinite E
      have hcard : 4 ≤ Fintype.card E := by rwa [← Nat.card_eq_fintype_card]
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) (n := 4) hcard
      exact ⟨s, hs⟩
    have h0 := (CFSG.LinearGroups.linear_projective_simple (K := E) (n := 2) le_rfl (Or.inr h4)).2.1
    have h1 : IsSimpleGroup (projectiveSL 2 E) :=
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm.isSimpleGroup
    exact eK.isSimpleGroup
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := h.K_quasi
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun hc => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc])⟩
  refine ⟨hsimple, ?_⟩
  rw [h.pPrimeCore_eq_center]
  exact LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnab


end Lem711Cfg

open CFSG.GH74.GLS.C3.Layer1.EndN.A6 in
theorem lem711_l43_five {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}
    (h : Lem711Cfg X L K x y) {E : Type} [Field E] [Finite E] (hE9 : Nat.card E = 9)
    (eK : ↥K ≃* projectiveSL 2 E) :
    ∃ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set X)), 5 ∣ orderOf w := by
  obtain ⟨hKsimple, hZ⟩ := h.pPrimeCore_eq_bot_of_proj2 (by rw [hE9]; norm_num) eK
  have hZc : center ↥K = ⊥ := by rw [← h.pPrimeCore_eq_center]; exact hZ
  obtain ⟨p, f, hp, hf, hq, hmodel⟩ := h.l2
  have hp3 : p = 3 := by
    have h1 : p ∣ 3 ^ 2 := by
      have : p ∣ p ^ f := dvd_pow_self p (by omega)
      rw [hq] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1)
  subst hp3
  have hf2 : f = 2 := by
    have : 3 ^ f = 3 ^ 2 := by rw [hq]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  subst hf2
  obtain ⟨eKb⟩ := CFSG.GH74.KGroups.A6.equiv_of_lieModel hmodel
  let eA6 : ↥K ≃* CFSG.GH74.KGroups.A6.QP.originalSubgroup :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eKb
  obtain ⟨k, w, hkK, hk1, hkodd, hwO, hkw, hky, hcomm⟩ := h.local_data hZ
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.hy, pow_two] at this
  have hyC : y ∈ centralizer ({x} : Set X) := mem_centralizer_singleton_iff.2 h.hxy.symm
  have hyN : y ∈ normalizer (K : Set X) := h.normalizes_of_centralizer y hyC
  let α : MulAut ↥K := TwoThin.conjAut hyN
  have hαapp : ∀ a : ↥K, ((α a : ↥K) : X) = y * a * y⁻¹ := fun a => rfl
  have hαα : α * α = 1 := by
    ext a
    show (((α (α a)) : ↥K) : X) = a
    rw [hαapp, hαapp]
    calc y * (y * (a : X) * y⁻¹) * y⁻¹ = (y * y) * (a : X) * (y * y)⁻¹ := by group
      _ = a := by rw [hyy]; simp
  let κ : ↥K := ⟨k, hkK⟩
  have hκα : α κ = κ := by
    apply Subtype.ext
    rw [hαapp]
    show y * k * y⁻¹ = k
    rw [hky]; group
  have hκ1 : κ ≠ 1 := fun h1 => hk1 (congrArg Subtype.val h1)
  have hκodd : Odd (orderOf κ) := by
    rw [← Subgroup.orderOf_coe]; exact hkodd
  set O := pPrimeCoreOf 2 (centralizer ({y} : Set X)) with hO
  have hfix : ∀ g : ↥K, α g = g ↔ y * (g : X) = (g : X) * y := fun g => by
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      rw [hαapp] at this
      calc y * (g : X) = (y * (g : X) * y⁻¹) * y := by group
        _ = (g : X) * y := by rw [this]
    · intro h1
      apply Subtype.ext
      rw [hαapp, h1]; group
  have hOnorm : ∀ g : ↥K, α g = g → ∀ n ∈ O, (g : X) * n * (g : X)⁻¹ ∈ O := fun g hg n hn =>
    TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer
      (Subgroup.le_normalizer (mem_centralizer_singleton_iff.2 ((hfix g).1 hg).symm)) hn
  by_cases hα1 : α = 1
  · exfalso
    have hKy : ∀ g : ↥K, y * (g : X) = (g : X) * y := fun g => (hfix g).1 (by rw [hα1]; rfl)
    let N0 : Subgroup ↥K := O.subgroupOf K
    have hN0n : N0.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := hOnorm g (by rw [hα1]; rfl) _ hn
      simpa using h1⟩
    have := hN0n
    rcases hKsimple.eq_bot_or_eq_top_of_normal N0 with hbot | htop
    · apply hκ1
      have hc : κ ∈ center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : ⁅k, (g : X)⁆ ∈ O := hcomm g g.2 (hKy g)
        have h2 : (⁅κ, g⁆ : ↥K) ∈ N0 := by
          rw [Subgroup.mem_subgroupOf]
          simpa [commutatorElement_def] using h1
        rw [hbot, Subgroup.mem_bot] at h2
        exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
      rw [hZc, Subgroup.mem_bot] at hc
      exact hc
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h.two_dvd_card_K
      have hu' : u ∈ N0 := by rw [htop]; exact Subgroup.mem_top u
      rw [Subgroup.mem_subgroupOf] at hu'
      have := odd_orderOf_of_mem_pPrimeCoreOf hu'
      rw [Subgroup.orderOf_coe, hu] at this
      exact absurd this (by decide)
  · let N : Subgroup ↥K := O.subgroupOf K
    have hord5 : orderOf κ = 5 := by
      refine a6_fixed_odd eA6 α hαα hα1 κ hκ1 hκodd hκα N ?_ ?_ ?_
      · intro n hn
        rw [Subgroup.mem_subgroupOf] at hn
        have := odd_orderOf_of_mem_pPrimeCoreOf hn
        rwa [Subgroup.orderOf_coe] at this
      · intro g hg n hn
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hOnorm g hg _ hn
      · intro g hg
        rw [Subgroup.mem_subgroupOf]
        simpa [commutatorElement_def] using hcomm g g.2 ((hfix g).1 hg)
    have hk5 : orderOf k = 5 := by
      rw [← Subgroup.orderOf_coe] at hord5
      exact hord5
    exact ⟨w, hwO, hk5 ▸ hkw⟩


theorem card_proj4_zmod3_not_dvd : ¬ 25 ∣ Nat.card (projectiveSL 4 (ZMod 3)) := by
  have h1 : Nat.card (projectiveSL 4 (ZMod 3)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :=
    Subgroup.card_dvd_of_surjective (f := proj 4 (ZMod 3)) (proj_surjective 4 (ZMod 3))
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) = 12130560 := by
    rw [Matrix.card_SL_field 4]
    norm_num [ZMod.card, Fin.prod_univ_four]
  intro h25
  have := h25.trans h1
  rw [h2] at this
  norm_num at this

open CFSG.GH74.GLS.C3.Layer1.EndN.L43 in
theorem lem711_l43_aux
    (zS : projectiveSL 4 (ZMod 3)) (hz5 : orderOf zS = 5)
    (hwit : ∀ α : MulAut (projectiveSL 4 (ZMod 3)), α * α = 1 → α zS = zS →
      ∃ g, α g = g ∧ Even (orderOf (zS * (g * zS * g⁻¹)))) :
    Lem711Empty (fun X _ => LieModel X .PSL 4 3 1) := by
  intro X _ _ L K x y h hL
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 4 3 1 (by norm_num)
    (by rw [Nat.card_zmod, pow_one]) hL
  let eP : ↥L ≃* projectiveSL 4 (ZMod 3) :=
    e1.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 3))
  have hLn := h.normal
  have hZP : center (projectiveSL 4 (ZMod 3)) = ⊥ := by
    rw [← Subgroup.map_center_eq eP, h.center_L_eq_bot, Subgroup.map_bot]
  obtain ⟨ρ, hρinj, hρW, -, hρconj⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot eP hZP
  obtain ⟨E, _, _, hE, ⟨eK⟩⟩ := h.l4_rowS (ℓ := 3) (e := 1) Nat.prime_three (by norm_num) le_rfl
    (by rw [Nat.card_zmod, pow_one]) eP
  have hE9 : Nat.card E = 9 := by rw [hE, Nat.card_zmod]; norm_num
  obtain ⟨w, hwO, h5w⟩ := lem711_l43_five h hE9 eK
  set O := pPrimeCoreOf 2 (centralizer ({y} : Set X)) with hO
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.hy, pow_two] at this
  have hwy : w ∈ centralizer ({y} : Set X) := (TwoThin.pPrimeCoreOf_le _) hwO
  set z0 : X := w ^ (orderOf w / 5) with hz0
  have hz0O : z0 ∈ O := pow_mem hwO _
  have hz0ord : orderOf z0 = 5 := orderOf_pow_orderOf_div (orderOf_pos w).ne' h5w
  have hz0y : y * z0 = z0 * y := by
    have h1 : w * y = y * w := mem_centralizer_singleton_iff.1 hwy
    exact ((Commute.pow_right (show Commute y w from h1.symm) _).eq)
  have hsub : Subsingleton (ZMod 3 ≃+* ZMod 3) := inferInstance
  have hρz0 : ρ z0 ∈ (MulAut.conj : projectiveSL 4 (ZMod 3) →* MulAut (projectiveSL 4 (ZMod 3))).range := by
    refine aut_odd_inner hsub (ρ z0) ?_
    have : orderOf (ρ z0) ∣ 5 := hz0ord ▸ orderOf_map_dvd ρ z0
    exact Odd.of_dvd_nat (by decide) this
  obtain ⟨ζ, hζ⟩ := hρz0
  let ℓ0 : ↥L := eP.symm ζ
  have hℓ0 : ((ℓ0 : ↥L) : X) = z0 := by
    apply hρinj
    rw [hρW ℓ0]
    simp [ℓ0, hζ]
  have hζord : orderOf ζ = 5 := by
    have h1 : orderOf (eP ℓ0) = orderOf ℓ0 := MulEquiv.orderOf_eq eP ℓ0
    have h2 : orderOf ((ℓ0 : ↥L) : X) = orderOf ℓ0 := Subgroup.orderOf_coe ℓ0
    have h3 : eP ℓ0 = ζ := by simp [ℓ0]
    rw [← h3, h1, ← h2, hℓ0, hz0ord]
  obtain ⟨s, i, hs⟩ := exists_conj_pow_of_order_five card_proj4_zmod3_not_dvd hζord hz5
  have hρyζ : ρ y ζ = ζ := by
    have h1 := hρconj y ℓ0
    have h2 : eP ℓ0 = ζ := by simp [ℓ0]
    rw [h2] at h1
    rw [h1]
    have : MulAut.conjNormal y ℓ0 = ℓ0 := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hℓ0]
      calc y * z0 * y⁻¹ = (z0 * y) * y⁻¹ := by rw [hz0y]
        _ = z0 := by group
    rw [this]
    simp [ℓ0]
  let α : MulAut (projectiveSL 4 (ZMod 3)) := MulAut.conj s * ρ y * (MulAut.conj s)⁻¹
  have hαα : α * α = 1 := by
    have h1 : ρ y * ρ y = 1 := by rw [← map_mul, hyy, map_one]
    calc α * α = MulAut.conj s * (ρ y * ρ y) * (MulAut.conj s)⁻¹ := by simp only [α]; group
      _ = 1 := by rw [h1]; group
  have hαz : α zS = zS := by
    have hρyζi : ρ y (ζ ^ i) = ζ ^ i := by
      rw [map_zpow, hρyζ]
    have hconjinv : (MulAut.conj s : MulAut (projectiveSL 4 (ZMod 3)))⁻¹ = MulAut.conj s⁻¹ :=
      (map_inv (MulAut.conj : projectiveSL 4 (ZMod 3) →* MulAut (projectiveSL 4 (ZMod 3))) s).symm
    have h1 : α (s * ζ ^ i * s⁻¹) = s * ζ ^ i * s⁻¹ := by
      show (MulAut.conj s * ρ y * (MulAut.conj s)⁻¹) (s * ζ ^ i * s⁻¹) = _
      rw [MulAut.mul_apply, MulAut.mul_apply, hconjinv, MulAut.conj_apply, MulAut.conj_apply]
      have : s⁻¹ * (s * ζ ^ i * s⁻¹) * s⁻¹⁻¹ = ζ ^ i := by group
      rw [this, hρyζi]
    rwa [hs] at h1
  obtain ⟨g, hαg, hev⟩ := hwit α hαα hαz
  set g₁ : projectiveSL 4 (ZMod 3) := s⁻¹ * g * s with hg₁
  have hρyg₁ : ρ y g₁ = g₁ := by
    have hconjinv : (MulAut.conj s : MulAut (projectiveSL 4 (ZMod 3)))⁻¹ = MulAut.conj s⁻¹ :=
      (map_inv (MulAut.conj : projectiveSL 4 (ZMod 3) →* MulAut (projectiveSL 4 (ZMod 3))) s).symm
    have h1 : (MulAut.conj s * ρ y * (MulAut.conj s)⁻¹) g = g := hαg
    rw [MulAut.mul_apply, MulAut.mul_apply, hconjinv, MulAut.conj_apply, MulAut.conj_apply] at h1
    have h2 : ρ y (s⁻¹ * g * s⁻¹⁻¹) = s⁻¹ * g * s⁻¹⁻¹ := by
      have := congrArg (fun t => s⁻¹ * t * s) h1
      calc ρ y (s⁻¹ * g * s⁻¹⁻¹) = s⁻¹ * (s * ρ y (s⁻¹ * g * s⁻¹⁻¹) * s⁻¹) * s := by group
        _ = s⁻¹ * g * s := this
        _ = s⁻¹ * g * s⁻¹⁻¹ := by group
    simpa [hg₁] using h2
  let gL : ↥L := eP.symm g₁
  have hgL : ((gL : ↥L) : X) * y = y * ((gL : ↥L) : X) := by
    have h1 := hρconj y gL
    have h2 : eP gL = g₁ := by simp [gL]
    rw [h2, hρyg₁] at h1
    have h3 : MulAut.conjNormal y gL = gL := by
      apply eP.injective
      rw [← h1, h2]
    have h4 := congrArg Subtype.val h3
    rw [MulAut.conjNormal_apply] at h4
    calc ((gL : ↥L) : X) * y = (y * ((gL : ↥L) : X) * y⁻¹) * y := by rw [h4]
      _ = y * ((gL : ↥L) : X) := by group
  have hgC : ((gL : ↥L) : X) ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.2 hgL
  have ha₁ : ((eP.symm (ζ ^ i) : ↥L) : X) = z0 ^ i := by
    rw [map_zpow]
    change (((eP.symm ζ) ^ i : ↥L) : X) = z0 ^ i
    rw [Subgroup.coe_zpow]
    change (((ℓ0 : ↥L) : X)) ^ i = z0 ^ i
    rw [hℓ0]
  have ha₁O : ((eP.symm (ζ ^ i) : ↥L) : X) ∈ O := by rw [ha₁]; exact zpow_mem hz0O i
  have hb₁O : ((gL : ↥L) : X) * ((eP.symm (ζ ^ i) : ↥L) : X) * ((gL : ↥L) : X)⁻¹ ∈ O :=
    TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer hgC) ha₁O
  have hprodO := O.mul_mem ha₁O hb₁O
  have hodd := odd_orderOf_of_mem_pPrimeCoreOf hprodO
  have hζi : ζ ^ i = s⁻¹ * zS * s := by
    rw [← hs]; group
  have hprod : ((eP.symm (ζ ^ i) : ↥L) : X) * (((gL : ↥L) : X) * ((eP.symm (ζ ^ i) : ↥L) : X) * ((gL : ↥L) : X)⁻¹) =
      ((eP.symm (s⁻¹ * (zS * (g * zS * g⁻¹)) * s) : ↥L) : X) := by
    have h1 : s⁻¹ * (zS * (g * zS * g⁻¹)) * s = ζ ^ i * (g₁ * ζ ^ i * g₁⁻¹) := by
      rw [hζi, hg₁]; group
    rw [h1, map_mul, map_mul, map_mul, map_inv]
    simp [gL]
  have horder : orderOf (((eP.symm (s⁻¹ * (zS * (g * zS * g⁻¹)) * s) : ↥L) : X)) =
      orderOf (zS * (g * zS * g⁻¹)) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have := MulEquiv.orderOf_eq (MulAut.conj s⁻¹ : projectiveSL 4 (ZMod 3) ≃* projectiveSL 4 (ZMod 3))
      (zS * (g * zS * g⁻¹))
    rw [MulAut.conj_apply] at this
    simpa using this
  rw [hprod, horder] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) hev

end CFSG.GH74.GLS
