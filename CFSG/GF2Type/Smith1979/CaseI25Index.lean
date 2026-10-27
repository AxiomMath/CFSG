module

public import CFSG.GF2Type.Smith1979.CaseI25Num

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open CFSG.ComponentClassification

section Generic

theorem eq_one_or_eq_or_eq_inv_of_card_three {A : Type*} [Group A] (P : Subgroup A)
    (hP : Nat.card P = 3) {θ : A} (hθ : θ ∈ P) (hθ1 : θ ≠ 1) {u : A} (hu : u ∈ P) :
    u = 1 ∨ u = θ ∨ u = θ⁻¹ := by
  have hord : orderOf θ = 3 := by
    have hd : orderOf θ ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hθ
    rw [hP] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hθ1
    · exact h
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hzp : zpowers θ = P := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hθ) ?_
    rw [Nat.card_zpowers, hord, hP]
  have h3 : θ ^ 3 = 1 := by
    have := pow_orderOf_eq_one θ
    rwa [hord] at this
  have hu' : u ∈ zpowers θ := by rw [hzp]; exact hu
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu'
  have hk : θ ^ k = θ ^ (k % 3) := by
    have := zpow_mod_orderOf θ k
    rw [hord] at this
    simpa using this.symm
  rw [hk]
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · left
    rw [h, zpow_zero]
  · right
    left
    rw [h, zpow_one]
  · right
    right
    rw [h, zpow_two]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_three']
    exact h3

theorem index_two_or_four_of_card {nM nN nE i j : ℕ} (hnE : nE = 9797760) (hnM : nM = nE * i)
    (hM0 : nM ≠ 0) (hMN : nM = nN * j) (hj : j ≤ 4095) (hnN : nN = 11520 ∨ nN = 23040)
    (hv : nM.factorization 2 = nN.factorization 2) : i = 2 ∨ i = 4 := by
  have hpow : 2 ^ nM.factorization 2 ∣ nM := Nat.ordProj_dvd nM 2
  have hnpow : ¬ 2 ^ (nM.factorization 2 + 1) ∣ nM :=
    Nat.pow_succ_factorization_not_dvd hM0 Nat.prime_two
  subst hnE
  rcases hnN with h | h
  · rw [h, factorization_two_11520] at hv
    rw [hv] at hpow hnpow
    have h1 : 256 ∣ nM := by simpa using hpow
    have h2 : ¬ 512 ∣ nM := by simpa using hnpow
    clear hv hpow hnpow
    have hi : i < 5 := by
      have h3 : 9797760 * i < 9797760 * 5 := by
        calc 9797760 * i = nM := hnM.symm
          _ = 11520 * j := by rw [hMN, h]
          _ ≤ 11520 * 4095 := Nat.mul_le_mul_left _ hj
          _ < 9797760 * 5 := by norm_num
      exact Nat.lt_of_mul_lt_mul_left h3
    subst hnM
    interval_cases i <;> first | (left; rfl) | (right; rfl) | (exfalso; revert h1 h2 hM0; norm_num)
  · rw [h, factorization_two_23040] at hv
    rw [hv] at hpow hnpow
    have h1 : 512 ∣ nM := by simpa using hpow
    have h2 : ¬ 1024 ∣ nM := by simpa using hnpow
    clear hv hpow hnpow
    have hi : i < 10 := by
      have h3 : 9797760 * i < 9797760 * 10 := by
        calc 9797760 * i = nM := hnM.symm
          _ = 23040 * j := by rw [hMN, h]
          _ ≤ 23040 * 4095 := Nat.mul_le_mul_left _ hj
          _ < 9797760 * 10 := by norm_num
      exact Nat.lt_of_mul_lt_mul_left h3
    subst hnM
    interval_cases i <;> first | (left; rfl) | (right; rfl) | (exfalso; revert h1 h2 hM0; norm_num)

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_NLbar_iff (H : Hyp4 S g) {x : S.O} :
    x ∈ NLbar S g ↔ x ∈ S.Mbar ∧
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  refine ⟨fun hx => ⟨hx.1, fix_of_mem_normalizer H hx.2⟩, fun ⟨hxM, hfix⟩ => ⟨hxM, ?_⟩⟩
  have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne hxM
    (by simpa using hfix)
  simpa using this

theorem exists_card_Mbar (H : Hyp4 S g) (h12 : finrank (ZMod 2) S.Qt = 12) :
    ∃ j : ℕ, j ≤ 4095 ∧ Nat.card S.Mbar = Nat.card (NLbar S g) * j := by
  classical
  set a : S.Qt := S.cl (g * S.z * g⁻¹) with ha
  have hsmul : ∀ (x : S.Mbar) (v : S.Qt), x • v = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
    fun _ _ => rfl
  have hstab : (MulAction.stabilizer S.Mbar a).map S.Mbar.subtype = NLbar S g := by
    ext x
    rw [Subgroup.mem_map, mem_NLbar_iff H]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by rw [MulAction.mem_stabilizer_iff, hsmul] at hy; exact hy⟩
    · rintro ⟨hxM, hfix⟩
      exact ⟨⟨x, hxM⟩, by rw [MulAction.mem_stabilizer_iff, hsmul]; exact hfix, rfl⟩
  have hcard_stab : Nat.card (MulAction.stabilizer S.Mbar a) = Nat.card (NLbar S g) := by
    rw [← hstab, Subgroup.card_map_of_injective S.Mbar.subtype_injective]
  have hOS := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S.Mbar a)
  rw [Nat.card_prod, hcard_stab] at hOS
  refine ⟨Nat.card (MulAction.orbit S.Mbar a), ?_, by rw [← hOS, mul_comm]⟩
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hne : ∀ v : MulAction.orbit S.Mbar a, (v : S.Qt) ≠ 0 := by
    rintro ⟨_, x, rfl⟩ h
    exact ha0 ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hinj : Function.Injective
      (fun o : Option (MulAction.orbit S.Mbar a) => o.elim (0 : S.Qt) (fun x => (x : S.Qt))) := by
    intro o₁ o₂ h
    rcases o₁ with _ | x₁ <;> rcases o₂ with _ | x₂
    · rfl
    · exact absurd h.symm (hne x₂)
    · exact absurd h (hne x₁)
    · exact congrArg some (Subtype.ext h)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option, S.card_Qt, h12] at hle
  omega

theorem factorization_two_Mbar_eq (H : Hyp4 S g) (C : Cons311 S g) :
    (Nat.card S.Mbar).factorization 2 = (Nat.card (NLbar S g)).factorization 2 := by
  obtain ⟨T, hTsyl, -, hTN⟩ := exists_sylow_le_NLbar H C
  have hTN' : S5.IsSylowTwoIn T (NLbar S g) :=
    ⟨hTN, hTsyl.isPGroup, fun hd => hTsyl.not_dvd (by
      rw [← Subgroup.relIndex_mul_relIndex T (NLbar S g) S.Mbar hTN inf_le_left]
      exact Dvd.dvd.mul_right hd _)⟩
  have h2 := hTN'.card_eq
  rw [hTsyl.card_eq] at h2
  exact Nat.pow_right_injective le_rfl h2

theorem center_map_eq_oddCore (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3) :
    (center (timmesfeldLayer S.Mbar)).map (timmesfeldLayer S.Mbar).subtype =
      timmesfeldOddCore S.Mbar := by
  refine Subgroup.eq_of_le_of_card_ge (center_layer_le_oddCore S) ?_
  rw [Subgroup.card_map_of_injective (timmesfeldLayer S.Mbar).subtype_injective, hZ]
  exact Nat.le_of_dvd (by norm_num) hodd

theorem card_oddCore_eq_three (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3) :
    Nat.card (timmesfeldOddCore S.Mbar) = 3 := by
  rw [← center_map_eq_oddCore hodd hZ,
    Subgroup.card_map_of_injective (timmesfeldLayer S.Mbar).subtype_injective, hZ]

theorem card_center_layer_eq_three_of_ne_one (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) ≠ 1) :
    Nat.card (center (timmesfeldLayer S.Mbar)) = 3 :=
  ((Nat.dvd_prime Nat.prime_three).mp (card_center_layer_dvd hodd)).resolve_left hZ

theorem card_layer_eq (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3)
    (hX : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) = 3265920) :
    Nat.card (timmesfeldLayer S.Mbar) = 9797760 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (timmesfeldLayer S.Mbar)), hX, hZ]

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem index_two_or_four (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3)
    (hX : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) = 3265920)
    (hΔ : (Delta S g t).ncard = 6) :
    (timmesfeldLayer S.Mbar).index = 2 ∨ (timmesfeldLayer S.Mbar).index = 4 := by
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have h12 : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨j, hj, hMj⟩ := exists_card_Mbar H h12
  exact index_two_or_four_of_card (card_layer_eq hZ hX) (Subgroup.card_mul_index _).symm
    Nat.card_pos.ne' hMj hj (card_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ)
    (factorization_two_Mbar_eq H C)

theorem inverts_Obar (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3) (hperf : PerfectInLayer S)
    (hΔ : (Delta S g t).ncard = 6) : ∀ θ ∈ Obar S, t * θ * t⁻¹ = θ⁻¹ := by
  intro θ hθ
  have hZO := center_map_eq_oddCore hodd hZ
  have hO3 := card_oddCore_eq_three hodd hZ
  have hOb3 : Nat.card (Obar S) = 3 := by
    rw [Obar, Subgroup.card_map_of_injective S.Mbar.subtype_injective, hO3]
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  by_cases hθ1 : θ = 1
  · rw [hθ1, mul_one, mul_inv_cancel, inv_one]
  obtain ⟨zc, hzc, hzθ⟩ : ∃ zc ∈ center (timmesfeldLayer S.Mbar),
      ((zc : S.Mbar) : S.O) = θ := by
    rw [Obar, ← hZO] at hθ
    obtain ⟨_, ⟨zc, hzc, rfl⟩, rfl⟩ := hθ
    exact ⟨zc, hzc, rfl⟩
  have hcomE : ∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, y * θ = θ * y := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hzθ]
    have := Subgroup.mem_center_iff.mp hzc ⟨e, he⟩
    exact congrArg (fun w : timmesfeldLayer S.Mbar => ((w : S.Mbar) : S.O)) this
  have hθ3 : θ ^ 3 = 1 := by
    have h1 : orderOf θ ∣ Nat.card (Obar S) := Subgroup.orderOf_dvd_natCard _ hθ
    rw [hOb3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hnc : t * θ ≠ θ * t := by
    intro hc
    have hRc : ∀ r ∈ Rbar S g t, θ * r = r * θ := by
      have hle : Rbar S g t ≤ centralizer ({θ} : Set S.O) := by
        rw [Rbar_eq_commutator_sup hCE H hNo C ht ht1 hVQ hΩ hN h6]
        refine sup_le (fun y hy => ?_) (zpowers_le.mpr ?_)
        · rw [mem_centralizer_singleton_iff]
          exact hcomE y (hperf _ ((Subgroup.commutator_le_self _).trans Rbar_le_Mbar)
            (Rbar_split hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ).2.2.2.2.1 hy)
        · rw [mem_centralizer_singleton_iff]
          exact hc
      intro r hr
      exact (mem_centralizer_singleton_iff.mp (hle hr)).symm
    have hmem := CFSG.LargeExtraspecial.S14.mem_zpowers_of_commute hCE H hNo C ht ht1 hVQ
      (Or.inl hΩ) hRc
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hmem with h | h
    · exact hθ1 h
    · apply ht1
      rw [h] at hθ3
      calc t = t * t * t := by rw [htt, one_mul]
        _ = t ^ 3 := (pow_three' t).symm
        _ = 1 := hθ3
  have hconj : t * θ * t⁻¹ ∈ Obar S := conj_mem_Obar htM hθ
  rcases eq_one_or_eq_or_eq_inv_of_card_three (Obar S) hOb3 hθ hθ1 hconj with h | h | h
  · exfalso
    apply hθ1
    have := congrArg (fun w => t⁻¹ * w * t) h
    simpa [mul_assoc] using this
  · exfalso
    apply hnc
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · exact h

theorem index_and_inversion (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hZ : Nat.card (center (timmesfeldLayer S.Mbar)) = 3)
    (hX : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) = 3265920)
    (hperf : PerfectInLayer S) (hΔ : (Delta S g t).ncard = 6) :
    (center (timmesfeldLayer S.Mbar)).map (timmesfeldLayer S.Mbar).subtype =
        timmesfeldOddCore S.Mbar ∧
      Nat.card (timmesfeldOddCore S.Mbar) = 3 ∧ (∀ θ ∈ Obar S, t * θ * t⁻¹ = θ⁻¹) ∧
      ((timmesfeldLayer S.Mbar).index = 2 ∨ (timmesfeldLayer S.Mbar).index = 4) :=
  ⟨center_map_eq_oddCore hodd hZ, card_oddCore_eq_three hodd hZ,
    inverts_Obar hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hZ hperf hΔ,
    index_two_or_four hCE H hNo C ht ht1 hVQ hΩ hN h6 hZ hX hΔ⟩

end Context

end Setting

end Case25

end CFSG.GF2Type.Smith1979
