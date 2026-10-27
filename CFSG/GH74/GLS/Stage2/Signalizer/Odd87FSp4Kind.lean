module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87KindIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Aut
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Core

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open CFSG.GH74.Generic CFSG.GH74.GLS.Stage2.Final.Thm6.L203


@[expose] def MinIndexU42 : Prop :=
  ∀ (Y : Type) [Group Y], LieModel Y .PSp 2 3 1 → ∀ H : Subgroup Y, H ≠ ⊤ → 11 < H.index

theorem FSp4.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FSp4 Y) : FSp4 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := h
  exact ⟨p, f, hp, hf, hp2, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hlie⟩

theorem ringChar_ne_two_of_card_psp4 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ f) : ringChar F ≠ 2 := by
  have := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hc : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  rw [ringChar.eq F p]
  exact hp2

section Q8

open CFSG.RankThree.Classical.SteinbergBY in
theorem exists_quaternion_psp4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    ∃ ψ : QuaternionGroup 2 →* StatedProj (StatedSp 2 F), Function.Injective ψ := by
  obtain ⟨φ, hφ, w, hww, hsw⟩ := exists_q8q8_Sp4 hF
  refine ⟨(QuotientGroup.mk' _).comp (φ.comp (MonoidHom.inl _ _)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have h1 := congrArg (fun u : StatedSp 2 F => (u : GL (Fin 2 ⊕ Fin 2) F)) (hsw g 1)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hc' : ((φ (MonoidHom.inl _ _ g) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := hc.symm
  have h2 : ((φ (g, 1) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := hc'
  rw [h2] at h1
  have h3 : (w : GL (Fin 2 ⊕ Fin 2) F) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c *
      (w : GL (Fin 2 ⊕ Fin 2) F)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    rw [← scalar_mul_comm_gl (r := 2) c (w : GL (Fin 2 ⊕ Fin 2) F), mul_assoc, mul_inv_cancel, mul_one]
  rw [h3] at h1
  have h4 : φ (g, 1) = φ (1, g) := Subtype.ext (h2.trans h1)
  have h5 := hφ h4
  exact (Prod.mk.inj h5).1

end Q8

theorem exists_quaternion_subgroup_of_FSp4 {Y : Type} [Group Y] (hF : FSp4 Y) :
    ∃ H : Subgroup Y, Nonempty (↥H ≃* QuaternionGroup 2) := by
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := hF
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  obtain ⟨ψ, hψ⟩ := exists_quaternion_psp4 (ringChar_ne_two_of_card_psp4 hp hp2 hcard)
  let ψ' : QuaternionGroup 2 →* Y := e.symm.toMonoidHom.comp ψ
  have hψ' : Function.Injective ψ' := e.symm.injective.comp hψ
  exact ⟨ψ'.range, ⟨(MonoidHom.ofInjective hψ').symm⟩⟩

theorem not_isL2_of_FSp4 {Y : Type} [Group Y] [Finite Y] (hF : FSp4 Y) :
    ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  intro hL
  have hD : CFSG.GH74.GLS.Stage2.Local.P34.DihJ Y := by
    left
    obtain ⟨F₀, i1, i2, hP, e⟩ := hL
    exact ⟨F₀, i1, i2, hP.1, e⟩
  obtain ⟨H, hH⟩ := exists_quaternion_subgroup_of_FSp4 hF
  exact not_quaternion_of_hasDihedralSylowTwo hD.hasDihedralSylowTwo H hH

theorem prime_pow_four_dvd_factorial {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : (p ^ f) ^ 4 ∣ Nat.factorial 11) : p = 3 ∧ f = 1 := by
  have hp11 : p ∣ Nat.factorial 11 := by
    have : p ∣ (p ^ f) ^ 4 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    exact this.trans h
  have hle : p ≤ 11 := (Nat.Prime.dvd_factorial hp).mp hp11
  have hp4 : p ^ 4 ∣ Nat.factorial 11 := by
    refine dvd_trans ?_ h
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  have hge : 2 ≤ p := hp.two_le
  interval_cases p
  · exact absurd rfl hp2
  · refine ⟨rfl, ?_⟩
    by_contra hf1
    have hf2 : 2 ≤ f := by omega
    have : 3 ^ 8 ∣ Nat.factorial 11 := by
      refine dvd_trans ?_ h
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega)
    norm_num [Nat.factorial] at this
  · exfalso; norm_num at hp
  · exfalso; norm_num [Nat.factorial] at hp4
  · exfalso; norm_num at hp
  · exfalso; norm_num [Nat.factorial] at hp4
  · exfalso; norm_num at hp
  · exfalso; norm_num at hp
  · exfalso; norm_num at hp
  · exfalso; norm_num [Nat.factorial] at hp4

theorem pow_four_dvd_card_of_psp4 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : LieModel Y .PSp 2 p f) : (p ^ f) ^ 4 ∣ Nat.card Y := by
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  have h2 := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := F) (n := 2)
    (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hcard) (by norm_num)
  rw [hcard] at h2
  rw [Nat.card_congr e.toEquiv]
  have hdvd : (p ^ f) ^ 4 ∣ Nat.card (StatedProj (StatedSp 2 F)) * 2 := ⟨_, h2⟩
  have hcop : Nat.Coprime ((p ^ f) ^ 4) 2 :=
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left f).pow_left 4
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem not_kindFactorAll_of_FSp4 (hMin : MinIndexU42) {Y : Type} [Group Y] [Finite Y] (hF : FSp4 Y)
    (k : Kind) : ¬ KindFactorAll k Y := by
  intro h
  have hnotL2 := not_isL2_of_FSp4 hF
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := hF
  have hdvd4 := pow_four_dvd_card_of_psp4 hp hp2 hlie
  have hnt : (p ^ f) ^ 4 ∣ Nat.factorial 11 → Nontrivial Y := fun hd => by
    obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 hf hd
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hdvd4
    norm_num at this
    omega
  cases k with
  | g2 => exact hnotL2 h
  | m12 => exact hnotL2 h
  | psp4 => exact hnotL2 h
  | l4 ε =>
    rcases h with h | h
    · exact hnotL2 h
    · have h7 : (p ^ f) ^ 4 ∣ Nat.factorial 7 :=
        hdvd4.trans ((h.card_dvd).trans (card_alt_dvd_factorial 7 (by norm_num)))
      have h11 : (p ^ f) ^ 4 ∣ Nat.factorial 11 := h7.trans (Nat.factorial_dvd_factorial (by norm_num))
      obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 hf h11
      norm_num [Nat.factorial] at h7
  | mcl =>
    have h11 : (p ^ f) ^ 4 ∣ Nat.factorial 11 := hdvd4.trans (KindFactorAll.card_dvd h (Or.inl rfl))
    have := hnt h11
    obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 hf h11
    exact not_kindFactorAll_mclly_of_index (Or.inl rfl) (hMin Y hlie) h
  | ly =>
    have h11 : (p ^ f) ^ 4 ∣ Nat.factorial 11 := hdvd4.trans (KindFactorAll.card_dvd h (Or.inr rfl))
    have := hnt h11
    obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 hf h11
    exact not_kindFactorAll_mclly_of_index (Or.inr rfl) (hMin Y hlie) h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
