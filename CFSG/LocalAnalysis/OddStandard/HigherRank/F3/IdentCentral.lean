module

import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.Holt.Lemma22Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
import CFSG.Holt.Witt

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG

section Helpers

theorem pPrimeCore_quotient_eq_bot {A : Type} [Group A] [Finite A] :
    pPrimeCore 2 (A ⧸ pPrimeCore 2 A) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have h := (prime_complement_kernel_core_preimage (QuotientGroup.mk' (pPrimeCore 2 A))
    (QuotientGroup.mk'_surjective _) hk).2
  rw [← h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem isPGroup_map_mk_pPrimeCore {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hC : C ≤ center P) : IsPGroup 2 (C.map (QuotientGroup.mk' (pPrimeCore 2 P))) := by
  intro y
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp y.2
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨k, Subtype.ext ?_⟩
  change (y : P ⧸ pPrimeCore 2 P) ^ 2 ^ k = 1
  rw [← hcy, ← map_pow]
  have hpow : c ^ 2 ^ k ∈ C := C.pow_mem hc _
  have horder : orderOf (c ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  have hle : Subgroup.zpowers (c ^ 2 ^ k) ≤ pPrimeCore 2 P := by
    refine le_sSup ⟨normal_of_le_center (Subgroup.zpowers_le.mpr (hC hpow)), ?_⟩
    rw [Nat.card_zpowers, horder]
    exact Nat.coprime_two_left.mpr hm
  exact (QuotientGroup.eq_one_iff _).mpr (hle (Subgroup.mem_zpowers _))

theorem le_center_of_central_two_subgroup {G : Type} [Group G] [Finite G]
    (hO : pPrimeCore 2 G = ⊥) {K Z : Subgroup G} (hK : K.Normal) (hZK : Z ≤ K)
    (hZc : Z ≤ center G) (hZ2 : IsPGroup 2 Z) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card K = Nat.card Z * m) : K ≤ center G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hnotdvd : ¬ 2 ∣ m := by
    intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [Nat.odd_iff] at hm
    omega
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hfac : (Nat.card K).factorization 2 = n := by
    rw [hcard, hn, Nat.factorization_mul (pow_ne_zero n two_ne_zero) hm0,
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]
  have hcardZ : Nat.card Z = 2 ^ (Nat.card K).factorization 2 := by
    rw [hn, hfac]
  have hZ : CFSG.Open.fusionIsSylowIn 2 Z K :=
    CFSG.Holt.fusionIsSylowIn_of_card_eq hZK hZ2 hcardZ
  have hcomm : ∀ k ∈ K, ∀ z ∈ Z, z * k = k * z := fun k _ z hz =>
    (Subgroup.mem_center_iff.mp (hZc hz) k).symm
  obtain ⟨O, hOK, hOdd, hcover, hoddmem⟩ :=
    CFSG.Holt.exists_odd_complement_of_commute hZ hcomm
  have hOnormal : O.Normal := by
    refine ⟨fun o ho g => hoddmem (g * o * g⁻¹) (hK.conj_mem o (hOK ho) g) ?_⟩
    have hoo : Odd (orderOf o) := by
      have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      exact hOdd.of_dvd_nat hdvd
    rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj g) o]
  have hOle : O ≤ pPrimeCore 2 G := le_sSup ⟨hOnormal, Nat.coprime_two_left.mpr hOdd⟩
  have hObot : O = ⊥ := by
    rw [hO] at hOle
    exact le_bot_iff.mp hOle
  intro k hk
  obtain ⟨z, hz, o, ho, hko⟩ := hcover k hk
  have ho1 : o = 1 := by
    have : o ∈ (⊥ : Subgroup G) := hObot ▸ ho
    simpa using this
  rw [hko, ho1, mul_one]
  exact hZc hz

theorem card_ker_lift_dvd {P R Q : Type} [Group P] [Finite P] [Group R] [Finite R] [Group Q]
    [Finite Q] (ρ : P →* R) (g : R →* Q) (hρ : Function.Surjective ρ) (N : Subgroup P)
    [N.Normal] (hN : N ≤ (g.comp ρ).ker) :
    Nat.card (QuotientGroup.lift N (g.comp ρ) hN).ker ∣
      Nat.card (ρ.ker.map (QuotientGroup.mk' N)) * Nat.card g.ker := by
  rw [QuotientGroup.ker_lift]
  set K : Subgroup P := (g.comp ρ).ker with hK
  set C : Subgroup P := ρ.ker with hC
  set Z : Subgroup (P ⧸ N) := C.map (QuotientGroup.mk' N) with hZ
  have hC_le_K : C ≤ K := by
    intro x hx
    rw [hK, MonoidHom.mem_ker]
    rw [hC, MonoidHom.mem_ker] at hx
    rw [MonoidHom.comp_apply, hx, map_one]
  have hN_le_K : N ≤ K := by rw [hK]; exact hN
  have hKmρ : K.map ρ = g.ker := by
    rw [hK]
    ext r
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hp)
    · intro hr
      obtain ⟨p, hp⟩ := hρ r
      refine ⟨p, ?_, hp⟩
      show g (ρ p) = 1
      rw [hp]
      exact MonoidHom.mem_ker.mp hr
  have hZleK : Z ≤ K.map (QuotientGroup.mk' N) := by
    rw [hZ]
    exact Subgroup.map_mono hC_le_K
  have hZleK' : C.map (QuotientGroup.mk' N) ≤ K.map (QuotientGroup.mk' N) :=
    Subgroup.map_mono hC_le_K
  have hrel : C.relIndex K = Nat.card g.ker := by
    rw [hC, Subgroup.relIndex_ker, hKmρ]
  have hdvd : Z.relIndex (K.map (QuotientGroup.mk' N)) ∣ Nat.card g.ker := by
    rw [hZ, ← hrel]
    have hmap := Subgroup.relIndex_map_map (QuotientGroup.mk' N) C K
    rw [hmap, QuotientGroup.ker_mk', show K ⊔ N = K from sup_eq_left.mpr hN_le_K]
    refine ⟨C.relIndex (C ⊔ N), ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex (H := C) (K := C ⊔ N) (L := K)
      le_sup_left (sup_le hC_le_K hN_le_K)
    simpa [mul_comm] using hmul.symm
  have hcardK : Nat.card (K.map (QuotientGroup.mk' N)) =
      Z.relIndex (K.map (QuotientGroup.mk' N)) * Nat.card Z := by
    rw [hZ]
    have h := Subgroup.relIndex_mul_card (H := C.map (QuotientGroup.mk' N))
      (K := K.map (QuotientGroup.mk' N))
    rw [inf_eq_left.mpr hZleK'] at h
    exact h.symm
  rw [hcardK]
  exact (mul_dvd_mul_right hdvd (Nat.card Z)).trans (by rw [mul_comm])

end Helpers

theorem exists_central_reduction {P R Q : Type} [Group P] [Finite P] [Group R] [Finite R]
    [Group Q] [Finite Q] (ρ : P →* R) (g : R →* Q) (hP : Group.IsPerfect P)
    (hρ : Function.Surjective ρ) (hg : Function.Surjective g) (hcen : ρ.ker ≤ center P)
    (hodd : ¬ 2 ∣ Nat.card g.ker) (hO : pPrimeCore 2 Q = ⊥) :
    ∃ (P₁ : Type) (_ : Group P₁) (_ : Finite P₁) (ρ₁ : P →* P₁) (f₁ : P₁ →* Q),
      Group.IsPerfect P₁ ∧ Function.Surjective ρ₁ ∧ Function.Surjective f₁ ∧
        ¬ 2 ∣ Nat.card ρ₁.ker ∧ f₁.ker ≤ center P₁ ∧ ∀ p : P, f₁ (ρ₁ p) = g (ρ p) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect P := hP
  have hfs : Function.Surjective (g.comp ρ) := hg.comp hρ
  have hNf : pPrimeCore 2 P ≤ (g.comp ρ).ker := by
    have h1 : (pPrimeCore 2 P).map (g.comp ρ) ≤ pPrimeCore 2 Q := map_pPrimeCore_le _ hfs
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    exact h1
  have hker₁ : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 P)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  refine ⟨P ⧸ pPrimeCore 2 P, inferInstance, inferInstance, QuotientGroup.mk' (pPrimeCore 2 P),
    QuotientGroup.lift (pPrimeCore 2 P) (g.comp ρ) hNf,
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 P))
      (QuotientGroup.mk'_surjective _), QuotientGroup.mk'_surjective _, ?_, hker₁, ?_,
    fun p => rfl⟩
  · intro q
    obtain ⟨p, rfl⟩ := hfs q
    exact ⟨QuotientGroup.mk p, rfl⟩
  · set f₁ := QuotientGroup.lift (pPrimeCore 2 P) (g.comp ρ) hNf with hf₁
    set Z : Subgroup (P ⧸ pPrimeCore 2 P) := ρ.ker.map (QuotientGroup.mk' (pPrimeCore 2 P))
      with hZ
    have hZK : Z ≤ f₁.ker := by
      rintro _ ⟨c, hc, rfl⟩
      rw [MonoidHom.mem_ker]
      show (g.comp ρ) c = 1
      simp [MonoidHom.mem_ker.mp hc]
    have hZc : Z ≤ center (P ⧸ pPrimeCore 2 P) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 P) q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hcen hc) b]
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hZK
    have hdvd := card_ker_lift_dvd ρ g hρ (pPrimeCore 2 P) hNf
    have hmdvd : m ∣ Nat.card g.ker := by
      rw [hm] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd
    have hmodd : Odd m :=
      Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)) hmdvd
    exact le_center_of_central_two_subgroup pPrimeCore_quotient_eq_bot f₁.normal_ker hZK hZc
      (isPGroup_map_mk_pPrimeCore hcen) hmodd hm

end CFSG.OddStandard.HigherRank.F3.Ident
