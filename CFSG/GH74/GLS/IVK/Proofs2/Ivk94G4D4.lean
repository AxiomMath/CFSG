module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExOrd

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  Subgroup CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem shape_card_eq {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (S : Shape Y F₁ F₂) :
    Nat.card Y = Nat.card SL(2, F₁) * Nat.card SL(2, F₂) := by
  have h₁ := S.sq_scalar₁
  have h₂ := S.sq_scalar₂
  have hsurj := S.psi_surjective S.g₁ S.g₂ h₁ h₂ rfl rfl
  have hker := S.ker_psi S.g₁ S.g₂ h₁ h₂ rfl rfl
  have hrange : (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl).range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have hk2 : Nat.card (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl).ker = 2 := by
    rw [hker, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · have hsq : ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) ^ 2 = 1 := by
        rw [pow_two]
        exact Prod.ext CFSG.ClassicalInvolution.G2D4Models.neg_one_mul_neg_one_SL2
          CFSG.ClassicalInvolution.G2D4Models.neg_one_mul_neg_one_SL2
      show (SemidirectProduct.inl ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) :
        Pgrp S.g₁ S.g₂ h₁ h₂) ^ 2 = 1
      rw [← map_pow, hsq, map_one]
    · intro h
      have h' : ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) = 1 :=
        SemidirectProduct.inl_injective (by rw [map_one]; exact h)
      have h1 : (-1 : SL(2, F₁)) = 1 := congrArg Prod.fst h'
      apply S.z_ne
      have h2 := S.symm_neg_one₁
      rw [h1, map_one] at h2
      exact (congrArg Subtype.val h2).symm
  have hcardP : Nat.card (Pgrp S.g₁ S.g₂ h₁ h₂) =
      Nat.card SL(2, F₁) * Nat.card SL(2, F₂) * 2 := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_prod]
    have : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨1, -1, by decide, Set.eq_univ_iff_forall.2 fun u => ?_⟩
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    rw [this]
  have h := Subgroup.card_ker_mul_card_range (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl)
  rw [hk2, hrange, Subgroup.card_top, hcardP] at h
  linarith

theorem card_centralizer_equiv {G H : Type} [Group G] [Group H] (φ : G ≃* H) (z : G) :
    Nat.card ↥(centralizer ({z} : Set G)) = Nat.card ↥(centralizer ({φ z} : Set H)) :=
  Nat.card_congr
    { toFun := fun x => ⟨φ x, by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        exact congrArg φ (Subgroup.mem_centralizer_singleton_iff.1 x.2)⟩
      invFun := fun y => ⟨φ.symm y, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_centralizer_singleton_iff.1 y.2⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (φ.apply_symm_apply _) }

theorem card_centralizer_d4 {p f : ℕ} [Fact p.Prime] {M : Type} [Group M]
    (hp2 : p ≠ 2) (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    Nat.card ↥(centralizer ({z} : Set M)) =
      ((p ^ f) ^ 3 * (((p ^ f) ^ 3) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  have hf := one_le_of_lieModel_D4 hM
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hD : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) := d4Data_sig0 hp2 hf
  have hσ := hD.sigma3
  have hcardF : Nat.card (CFSG.LieType.Steinberg.TwistedD4.fixedField (sig0 p f)) = p ^ f :=
    card_fixedField_eq (Fact.out : p.Prime) hf hD.card hD.frob
  have hsq : φ z * φ z = 1 ∧ φ z ≠ 1 := by
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    · intro h
      have : z = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
    hsq.1 (tauL_mul_self hσ) hsq.2 (tauL_ne_one hσ hD.neg_one)
  let ψ : M ≃* twistedGroup (sig0 p f) := φ.trans (MulAut.conj g)
  have hψz : ψ z = τL hσ := hg
  obtain ⟨S, -⟩ := exists_native_shape_d4 hσ hD
  rw [card_centralizer_equiv ψ z, hψz]
  have hY := shape_card_eq S
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hD.card, hcardF] at hY
  exact hY

theorem ordObsC {N : ℕ} (hN : N ≤ 1000000) (hpos : 0 < N)
    (hdvd : ∀ q : ℕ, 5 ≤ q → q < 40 → ¬ (q * (q ^ 2 - 1)) ^ 2 / 2 ∣ N) :
    ∀ q : ℕ, 5 ≤ q → ∀ m : ℕ, m ∣ N →
      2 * m ≠ (q * (q ^ 2 - 1)) ^ 2 ∧
        2 * m ≠ (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) := by
  intro q hq m hm
  have hm2 : m ≤ N := Nat.le_of_dvd hpos hm
  have h125 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h25 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have ha : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
  constructor
  · intro h
    have hq40 : q < 40 := by
      by_contra hge
      have hge : 40 ≤ q := Nat.le_of_not_lt hge
      have h1600 : 1600 ≤ q ^ 2 := by
        calc 1600 = 40 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
      have h1 : 40 * 1599 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
      have h2 : (40 * 1599) ^ 2 ≤ (q * (q ^ 2 - 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      norm_num at h2
      omega
    refine hdvd q hq hq40 ?_
    have hm' : m = (q * (q ^ 2 - 1)) ^ 2 / 2 := by omega
    rw [← hm']
    exact hm
  · intro h
    have h125' : 125 ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left h125 2
    have h1 : 125 * (125 ^ 2 - 1) ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) :=
      Nat.mul_le_mul h125 (by omega)
    have h2 := Nat.mul_le_mul h1 ha
    norm_num at h2
    omega

theorem k94_d4_three :
    K94Excl fun K _ => LieModel K .trialityD4 0 3 1 := by
  intro K _ _ hs hnab hgen htwo hP z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  obtain ⟨m, hmC, -, -, p, f, hp, hp2, h5, hmq⟩ := cfg.exists_order_data hs hnab
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hC := card_centralizer_d4 (p := 3) (f := 1) (by norm_num) hP z cfg.z_ord
  have hC' : Nat.card ↥(centralizer ({z} : Set K)) = 471744 := by rw [hC]; norm_num
  rw [hC'] at hmC
  have := ordObsC (N := 471744) (by norm_num) (by norm_num) (by decide) (p ^ f) h5 m hmC
  rcases hmq with h | h
  · exact this.1 h
  · exact this.2 h

theorem k94_three :
    K94Excl fun K _ => LieModel K .G2 0 3 1 ∨ LieModel K .trialityD4 0 3 1 :=
  k94Excl_or k94_g2_three k94_d4_three

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
