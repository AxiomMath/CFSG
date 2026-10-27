module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Sl23
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem inf_oddCore_eq_bot_of_card_eq [Finite G] {K : Subgroup G}
    {H : Subgroup ↥K} (hH : Nat.card H = 8) :
    H ⊓ CFSG.oddCore ↥K = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hNodd : Odd (Nat.card (CFSG.oddCore ↥K)) := odd_card_oddCore' ↥K
  have hcop : Nat.Coprime 8 (Nat.card (CFSG.oddCore ↥K)) := by
    have h : Nat.Coprime 2 (Nat.card (CFSG.oddCore ↥K)) := Nat.coprime_two_left.mpr hNodd
    simpa using h.pow_left 3
  exact Nat.eq_one_of_dvd_coprimes hcop
    (by rw [← hH]; exact Subgroup.card_dvd_of_le inf_le_left)
    (Subgroup.card_dvd_of_le inf_le_right)

private theorem injective_mk'_subtype_of_inf_eq_bot {K : Subgroup G} {H : Subgroup ↥K}
    (hH : H ⊓ CFSG.oddCore ↥K = ⊥) :
    Function.Injective ((QuotientGroup.mk' (CFSG.oddCore ↥K)).comp H.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  apply Subtype.ext
  have hxN : (x : ↥K) ∈ CFSG.oddCore ↥K := by
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥K) (x : ↥K) = 1 := MonoidHom.mem_ker.mp hx
    have h2 : (x : ↥K) ∈ MonoidHom.ker (QuotientGroup.mk' (CFSG.oddCore ↥K)) :=
      MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hthis : (x : ↥K) ∈ H ⊓ CFSG.oddCore ↥K := ⟨x.2, hxN⟩
  rw [hH] at hthis
  exact Subgroup.mem_bot.mp hthis

private theorem injective_of_inf_oddCore_eq_bot {K : Subgroup G} {H : Subgroup ↥K}
    {Q : Type*} [Group Q] (e : ↥K ⧸ CFSG.oddCore ↥K ≃* Q)
    (hH : H ⊓ CFSG.oddCore ↥K = ⊥) :
    Function.Injective
      ((e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥K))).comp H.subtype) := by
  rw [MonoidHom.comp_assoc]
  exact e.injective.comp (injective_mk'_subtype_of_inf_eq_bot (K := K) (H := H) hH)

private theorem q8_sq' {q : QuaternionGroup 2} (h : q ^ 2 = 1) :
    q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q; decide +kernel

theorem exists_quaternion_of_isSL23Mod [Finite G] {K : Subgroup G} (hK : IsSL23Mod K) {y : G}
    (hyK : y ∈ K) (hy : orderOf y = 2) :
    ∃ f : QuaternionGroup 2 →* G, Function.Injective f ∧ f (QuaternionGroup.a 2) = y ∧
      f.range ≤ K := by
  classical
  obtain ⟨e⟩ := hK
  let φ : ↥K →* ↥K ⧸ CFSG.oddCore ↥K := QuotientGroup.mk' (CFSG.oddCore ↥K)
  let ψ : ↥K →* SL23 := e.toMonoidHom.comp φ
  let y' : ↥K := ⟨y, hyK⟩
  have hy'order : orderOf y' = 2 := by
    dsimp [y']
    rw [Subgroup.orderOf_mk, hy]
  have hy'ne : y' ≠ 1 := by
    intro h
    have h1 : orderOf (1 : ↥K) = 2 := h ▸ hy'order
    rw [orderOf_one] at h1
    norm_num at h1
  have hzp : IsPGroup 2 (Subgroup.zpowers y') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy'order]
    norm_num
  obtain ⟨P, hyP⟩ := hzp.exists_le_sylow
  have hy'P : y' ∈ (P : Subgroup ↥K) := hyP (Subgroup.mem_zpowers y')
  have hNodd : Odd (Nat.card (CFSG.oddCore ↥K)) := odd_card_oddCore' ↥K
  have hquot : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcardK : Nat.card ↥K = Nat.card (CFSG.oddCore ↥K) * 24 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K), hquot, Nat.mul_comm]
  haveI : Nonempty ↥(CFSG.oddCore ↥K) := ⟨⟨1, (CFSG.oddCore ↥K).one_mem⟩⟩
  have hNfact : Nat.factorization (Nat.card (CFSG.oddCore ↥K)) 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => hNodd.not_two_dvd_nat h
  have h24fact : Nat.factorization 24 2 = 3 := by
    have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  have hfact : Nat.factorization (Nat.card ↥K) 2 = 3 := by
    rw [hcardK, Nat.factorization_mul (Nat.card_pos (α := ↥(CFSG.oddCore ↥K))).ne'
        (by norm_num),
      Finsupp.add_apply, hNfact, h24fact, zero_add]
  have hPcard : Nat.card (P : Subgroup ↥K) = 8 := by
    rw [Sylow.card_eq_multiplicity P, hfact]
    norm_num
  have hPNbot : (P : Subgroup ↥K) ⊓ CFSG.oddCore ↥K = ⊥ :=
    inf_oddCore_eq_bot_of_card_eq hPcard
  let ψP : ↥(P : Subgroup ↥K) →* SL23 := ψ.comp (P : Subgroup ↥K).subtype
  have hψP : Function.Injective ψP := injective_of_inf_oddCore_eq_bot e hPNbot
  have hcardT : Nat.card ψP.range = 8 := by
    have h1 : Nat.card ψP.range = Nat.card (P : Subgroup ↥K) :=
      (Nat.card_congr (MonoidHom.ofInjective hψP).toEquiv).symm
    rw [h1, hPcard]
  obtain ⟨eQ⟩ := nonempty_mulEquiv_quaternion_of_natCard_eq_eight_sl23 ψP.range hcardT
  let g : QuaternionGroup 2 ≃* ↥(P : Subgroup ↥K) :=
    eQ.trans (MonoidHom.ofInjective hψP).symm
  let f : QuaternionGroup 2 →* G :=
    K.subtype.comp (((P : Subgroup ↥K).subtype).comp g.toMonoidHom)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b hab
    exact g.injective
      ((P : Subgroup ↥K).subtype_injective (K.subtype_injective hab))
  · let y'' : ↥(P : Subgroup ↥K) := ⟨y', hy'P⟩
    have hy''2 : y'' ^ 2 = 1 := by
      apply Subtype.ext
      show y' ^ 2 = 1
      rw [← orderOf_dvd_iff_pow_eq_one, hy'order]
    have hq2 : (g.symm y'') ^ 2 = 1 := by
      apply g.injective
      rw [map_pow, g.apply_symm_apply, hy''2, map_one]
    have hq : g.symm y'' = QuaternionGroup.a 2 := by
      rcases q8_sq' hq2 with h | h
      · exfalso
        have hy''1 : y'' = 1 := by
          rw [← g.apply_symm_apply y'', h, map_one]
        exact hy'ne (Subtype.ext_iff.mp hy''1)
      · exact h
    have hgq : g (QuaternionGroup.a 2) = y'' := by
      rw [← hq, g.apply_symm_apply]
    change K.subtype ((P : Subgroup ↥K).subtype (g (QuaternionGroup.a 2))) = y
    rw [hgq]
    rfl
  · rintro z ⟨q, rfl⟩
    exact ((P : Subgroup ↥K).subtype (g q)).2

theorem le_pCore_of_isSL23Mod [Finite G] {K : Subgroup G} (hK : IsSL23Mod K)
    (hO : oddCore K ≤ Subgroup.center K) {S : Subgroup G} (hSK : S ≤ K) (hS : Nat.card S = 8) :
    S ≤ CFSG.inSubgroup (CFSG.pCore 2) K := by
  classical
  obtain ⟨e⟩ := hK
  let φ : ↥K →* ↥K ⧸ CFSG.oddCore ↥K := QuotientGroup.mk' (CFSG.oddCore ↥K)
  let ψ : ↥K →* SL23 := e.toMonoidHom.comp φ
  let S' : Subgroup ↥K := S.subgroupOf K
  have hS'card : Nat.card S' = 8 := by
    have h1 : Nat.card (S'.map K.subtype) = Nat.card S' := Subgroup.card_subtype K S'
    rw [← h1, Subgroup.map_subgroupOf_eq_of_le hSK, hS]
  have hS'Nbot : S' ⊓ CFSG.oddCore ↥K = ⊥ := inf_oddCore_eq_bot_of_card_eq hS'card
  have hψS' : Function.Injective (ψ.comp S'.subtype) :=
    injective_of_inf_oddCore_eq_bot e hS'Nbot
  have hSψcard : Nat.card (S'.map ψ) = 8 := by
    have hrange : (ψ.comp S'.subtype).range = S'.map ψ := by
      ext z
      simp [MonoidHom.mem_range, Subgroup.mem_map]
    have h1 : Nat.card (S'.map ψ) = Nat.card S' := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hψS').toEquiv).symm
    rw [h1, hS'card]
  have hSψnormal : (S'.map ψ).Normal :=
    normal_of_natCard_eq_eight_sl23 (S'.map ψ) hSψcard
  have hcop : Nat.Coprime 8 (Nat.card (CFSG.oddCore ↥K)) := by
    have hNodd : Odd (Nat.card (CFSG.oddCore ↥K)) := odd_card_oddCore' ↥K
    have h : Nat.Coprime 2 (Nat.card (CFSG.oddCore ↥K)) := Nat.coprime_two_left.mpr hNodd
    simpa using h.pow_left 3
  have hS'normal : S'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmem : ψ (g * n * g⁻¹) ∈ S'.map ψ := by
      have h : ψ (g * n * g⁻¹) = ψ g * ψ n * (ψ g)⁻¹ := by simp
      rw [h]
      exact hSψnormal.conj_mem (ψ n) (Subgroup.mem_map_of_mem ψ hn) (ψ g)
    obtain ⟨s', hs', hs'eq⟩ := Subgroup.mem_map.mp hmem
    let o : ↥K := s'⁻¹ * (g * n * g⁻¹)
    have hoN : o ∈ CFSG.oddCore ↥K := by
      have hψ1 : ψ o = 1 := by
        dsimp [o]
        rw [map_mul, map_inv, hs'eq, inv_mul_cancel]
      have hψ1' : e ((QuotientGroup.mk' (CFSG.oddCore ↥K)) o) = 1 := hψ1
      have hφ1 : φ o = 1 := e.injective (by rw [hψ1', map_one])
      have h2 : o ∈ MonoidHom.ker φ := MonoidHom.mem_ker.mpr hφ1
      rwa [QuotientGroup.ker_mk'] at h2
    have hocomm : Commute s' o := by
      have hc : o ∈ Subgroup.center ↥K := hO hoN
      exact Subgroup.mem_center_iff.mp hc s'
    have hso : s' * o = g * n * g⁻¹ := by
      dsimp [o]; group
    have hn8 : n ^ 8 = 1 := by
      have hdvd : orderOf n ∣ 8 := by
        rw [← hS'card]
        exact Subgroup.orderOf_dvd_natCard S' hn
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hs'8 : s' ^ 8 = 1 := by
      have hdvd : orderOf s' ∣ 8 := by
        rw [← hS'card]
        exact Subgroup.orderOf_dvd_natCard S' hs'
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have ho8 : o ^ 8 = 1 := by
      have hgs8 : (g * n * g⁻¹) ^ 8 = 1 := by
        have h1 : g * n * g⁻¹ = (MulAut.conj g) n := by simp [MulAut.conj_apply]
        rw [h1, ← map_pow, hn8, map_one]
      have hso8 : (s' * o) ^ 8 = 1 := by rw [hso, hgs8]
      rw [hocomm.mul_pow, hs'8, one_mul] at hso8
      exact hso8
    have ho1 : o = 1 := by
      have hord : orderOf o = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.mpr ho8)
          (Subgroup.orderOf_dvd_natCard (CFSG.oddCore ↥K) hoN)
      exact orderOf_eq_one_iff.mp hord
    rw [← hso, ho1, mul_one]
    exact hs'
  have hS'pgroup : IsPGroup 2 S' := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hS'card]
    norm_num
  have hS'le : S' ≤ CFSG.pCore 2 ↥K :=
    le_sSup (show S' ∈ {H : Subgroup ↥K | H.Normal ∧ IsPGroup 2 H} from
      ⟨hS'normal, hS'pgroup⟩)
  calc S = S'.map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hSK).symm
    _ ≤ (CFSG.pCore 2 ↥K).map K.subtype := Subgroup.map_mono hS'le
    _ = CFSG.inSubgroup (CFSG.pCore 2) K := rfl

end CFSG.OddStandard.SmallF3.Omega
