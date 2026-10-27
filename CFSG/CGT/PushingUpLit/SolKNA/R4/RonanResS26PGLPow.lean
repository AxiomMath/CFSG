module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VCore
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.FieldTheory.Finite.Trace

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG.GorensteinWalter

theorem pgl_units_eq_one_or_neg_one {K : Type} [Field K] {δ : Kˣ} (h : δ ^ 2 = 1) :
    δ = 1 ∨ δ = -1 := by
  have h10 : (δ : K) * (δ : K) = 1 := by
    rw [← sq, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  rcases mul_self_eq_one_iff.mp h10 with h' | h'
  · exact Or.inl (Units.ext (by rw [Units.val_one]; exact h'))
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h'))

theorem pgl_mu_comm_Z {K : Type} [Field K] {C μ : PGammaL2 K} {γ : Kˣ}
    (hCZ : C * TwinSocF4.tor (-1) = TwinSocF4.tor (-1) * C) (hC : C = TwinSocF4.tor γ * μ) :
    μ * TwinSocF4.tor (-1) = TwinSocF4.tor (-1) * μ := by
  have hμ' : μ = (TwinSocF4.tor γ)⁻¹ * C := by
    rw [hC, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hμ', mul_assoc, hCZ, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← map_inv, TwinSocF4.tor_comm]

theorem pgl_card_ringEquiv {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] : Nat.card (K ≃+* K) = Module.finrank (ZMod p) K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  rw [Nat.card_congr e.toEquiv]
  exact IsGalois.card_aut_eq_finrank (ZMod p) K

theorem pgl_sigma_pow_eq_one {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {r : ℕ}
    (hN : padicValNat 2 (Nat.card K - 1) = r) {σ : K ≃+* K} (hσ : σ ^ 2 ^ (r - 1) = 1) :
    σ ^ 2 ^ (r - 2) = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hchar
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  have hcardK : Nat.card K = p ^ Module.finrank (ZMod p) K :=
    (FiniteField.pow_finrank_eq_natCard p K).symm
  set f := Module.finrank (ZMod p) K with hfdef
  have hcardaut : Nat.card (K ≃+* K) = f := pgl_card_ringEquiv p
  have hpodd : Odd p := by
    refine hp.odd_of_ne_two ?_
    intro hp2
    apply h2
    have h0 := CharP.cast_eq_zero K p
    rw [hp2] at h0
    exact_mod_cast h0
  have hx : ¬ 2 ∣ p := by
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcardK, h0, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hN' : padicValNat 2 (p ^ f - 1) = r := by
    rw [← hcardK]
    exact hN
  obtain ⟨i, -, hσi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσ)
  have hσf : orderOf σ ∣ f := by
    have h := orderOf_dvd_natCard σ
    rwa [hcardaut] at h
  rw [← orderOf_dvd_iff_pow_eq_one, hσi]
  refine pow_dvd_pow 2 ?_
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · omega
  · have h2i : 2 ^ i ∣ f := by
      rw [← hσi]
      exact hσf
    have hev : Even f := by
      rw [even_iff_two_dvd]
      exact (dvd_pow_self 2 hpos.ne').trans h2i
    have hbound := padicValNat.pow_two_sub_one_ge hp.one_lt hx hf0 hev
    rw [hN'] at hbound
    have hi2 : i ≤ padicValNat 2 f := (padicValNat_dvd_iff_le (p := 2) hf0).mp h2i
    omega

theorem l2_pow_dichotomy {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {r : ℕ} (hr : 4 ≤ r)
    (hN : padicValNat 2 (Nat.card K - 1) = r) {α : Kˣ} (hα : orderOf α = 2 ^ (r - 1))
    {C : PGammaL2 K} (hCα : C * TwinSocF4.tor α = TwinSocF4.tor α * C)
    (hC2 : C ^ 2 ^ (r - 1) = 1) :
    C ^ 2 ^ (r - 2) = 1 ∨ C ^ 2 ^ (r - 2) = TwinSocF4.tor (-1) := by
  classical
  have hα1 : α ^ 2 ^ (r - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hα)
  have hsq : (α ^ 2 ^ (r - 2)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, (by omega : r - 2 + 1 = r - 1), hα1]
  have hne : α ^ 2 ^ (r - 2) ≠ 1 := by
    intro h
    have h1 : orderOf α ∣ 2 ^ (r - 2) := orderOf_dvd_of_pow_eq_one h
    rw [hα, Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)] at h1
    omega
  have hneg : α ^ 2 ^ (r - 2) = -1 := by
    have h10 : ((α ^ 2 ^ (r - 2) : Kˣ) : K) * ((α ^ 2 ^ (r - 2) : Kˣ) : K) = 1 := by
      rw [← sq, ← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    rcases mul_self_eq_one_iff.mp h10 with h | h
    · exfalso
      apply hne
      apply Units.ext
      rw [Units.val_one]
      exact h
    · apply Units.ext
      rw [Units.val_neg, Units.val_one]
      exact h
  have hZ : TwinSocF4.tor (-1) = TwinSocF4.tor α ^ 2 ^ (r - 2) := by
    rw [← map_pow, hneg]
  have hCZ : C * TwinSocF4.tor (-1) = TwinSocF4.tor (-1) * C := by
    rw [hZ]
    exact (Commute.pow_right (show Commute C (TwinSocF4.tor α) from hCα) _).eq
  obtain ⟨γ, ε, σ, -, hCd⟩ := TwinSocF4.exists_decomp h2 hCZ
  obtain ⟨μ, hμdef⟩ : ∃ μ : PGammaL2 K, μ = TwinSocF4.wref ^ ε * SemidirectProduct.inr σ :=
    ⟨_, rfl⟩
  have hCμ : C = TwinSocF4.tor γ * μ := by
    rw [hCd, hμdef, mul_assoc]
  have hμZ : μ * TwinSocF4.tor (-1) = TwinSocF4.tor (-1) * μ := pgl_mu_comm_Z hCZ hCμ
  obtain ⟨m, -, hm⟩ := TwinSocF4.exists_pow_conj h2 hμZ
  have hform := TwinSocF4.pow_tor_mul hm γ
  have hrC : (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) C = σ := by
    rw [hCd, map_mul, map_mul, map_pow, TwinSocF4.rightHom_tor, TwinSocF4.rightHom_wref,
      SemidirectProduct.rightHom_inr]
    simp
  have hσk : σ ^ 2 ^ (r - 1) = 1 := by
    have h1 := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hC2
    rw [map_pow, map_one, hrC] at h1
    exact h1
  have hσn : σ ^ 2 ^ (r - 2) = 1 := pgl_sigma_pow_eq_one h2 hN hσk
  have hn2 : 2 ∣ 2 ^ (r - 2) := dvd_pow_self 2 (by omega)
  have hw2 : (TwinSocF4.wref : PGammaL2 K) ^ 2 = 1 := by
    rw [sq, TwinSocF4.wref_mul_wref]
  have hμn : μ ^ 2 ^ (r - 2) = 1 := by
    have hc : Commute (TwinSocF4.wref ^ ε : PGammaL2 K) (SemidirectProduct.inr σ) :=
      Commute.pow_left (TwinSocF4.inr_mul_wref σ).symm ε
    obtain ⟨j, hj⟩ : 2 ∣ ε * 2 ^ (r - 2) := Dvd.dvd.mul_left hn2 ε
    rw [hμdef, hc.mul_pow, ← pow_mul, hj, pow_mul, hw2, one_pow, ← map_pow, hσn, map_one,
      mul_one]
  obtain ⟨δ, hCn⟩ : ∃ δ : Kˣ, C ^ 2 ^ (r - 2) = TwinSocF4.tor δ :=
    ⟨γ ^ (∑ i ∈ Finset.range (2 ^ (r - 2)), m ^ i), by
      rw [hCμ, hform, hμn, mul_one]⟩
  have he : (2 : ℕ) ^ (r - 2) * 2 = 2 ^ (r - 1) := by
    rw [← pow_succ, (by omega : r - 2 + 1 = r - 1)]
  have hδ2 : TwinSocF4.tor (δ ^ 2) = 1 := by
    rw [map_pow, ← hCn, ← pow_mul, he, hC2]
  have hδsq : δ ^ 2 = 1 := by
    apply TwinSocF4.tor_injective
    rw [map_one]
    exact hδ2
  rcases pgl_units_eq_one_or_neg_one hδsq with rfl | rfl
  · left
    rw [hCn, map_one]
  · right
    exact hCn

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
