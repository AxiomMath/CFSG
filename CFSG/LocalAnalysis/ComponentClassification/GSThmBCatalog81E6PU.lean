module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUl

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup P211

theorem cf81E6P211U4 : CF81E6P211U4 := by
  intro X _ _ hsimp hC ⟨p', f', hp', hp2', hf', h8, hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  refine Or.inr (Or.inr ?_)
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  set F := generalizedFitting X with hFdef
  have hSCM := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  have hder : derivedSeries (MulAut F) 2 ≤ (MulAut.conj : F →* MulAut F).range := by
    have h1 := map_derivedSeries_eq
      (QuotientGroup.mk'_surjective (OuterAutomorphisms.inner F)) 2
    rw [(LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_rank_two_classical_model_schreier
      (Or.inl rfl) hSCM).1, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have hKF : K ≤ F := le_fstar_of_perfect hC (MulEquiv.refl _) hder
    (commutator_eq_of_isPComp hKC hK)
  obtain ⟨-, Kf, _, _, hKf, ⟨e⟩⟩ := hSCM
  have hud : LocalAnalysis.ComponentInitial.UnitaryFieldData p' f' Kf :=
    ⟨hp', hf', by rw [hKf, ← pow_mul, mul_comm]⟩
  have hFcard : Nat.card F = Open.ordTwistedA 3 (p' ^ f') :=
    GH74.card_of_lieModel_PSU (by norm_num) hp2' hLie
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have hq'odd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hq'3 : 3 ≤ p' ^ f' :=
    le_trans (by have := hp'.two_le; omega) (Nat.le_self_pow (by omega) p')
  set n := padicValNat 2 ((p' ^ f') ^ 2 - 1) with hn
  set m := padicValNat 2 ((p ^ f) ^ 2 - 1) with hm
  have hn3 : 3 ≤ n := three_le_v2 hq'odd hq'3
  have hD : Nat.card D = 2 ^ m := by
    obtain ⟨R, hR⟩ := hDsyl
    have h1 := R.card_eq_multiplicity
    rw [hR, Nat.factorization_def _ Nat.prime_two, v2_card_quot, card_sec8J hJt,
      show p ^ (2 * f) = (p ^ f) ^ 2 by ring, v2_ordA hqodd hq3] at h1
    rw [← h1]
    exact (Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv).symm
  have hKv : 2 ^ (2 * m) ∣ Nat.card K := by
    refine dvd_trans ?_ (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K))
    rcases hKt with hL | ⟨rfl, rfl, ⟨eA⟩⟩
    · rw [GH74.card_of_lieModel_PSp (by norm_num) hp2 hL, ← v2_ordBC hqodd hq3]
      exact pow_padicValNat_dvd
    · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hm,
        show (3 ^ 1) ^ 2 - 1 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
      decide
  have hnm : n ≤ m := by
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
    have hT := T.card_eq_multiplicity
    rw [Nat.factorization_def _ Nat.prime_two, hFcard, v2_ordTwistedA_three hq'odd hq'3 h8] at hT
    have hb2 := hbound ((T : Subgroup ↥F).map F.subtype) (map_subtype_le _) (T.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective F.subtype_injective, hT, hD, ← pow_mul 2 m 2,
      ← pow_succ'] at hb2
    have := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hb2
    omega
  have hK2n : 2 ^ (2 * n) ∣ Nat.card K := (pow_dvd_pow 2 (by omega)).trans hKv
  set α₀ : MulAut ↥F := MulAut.conjNormal b with hα₀
  set β := MulAut.congr e α₀ with hβdef
  have hcomm : ∀ x, e (α₀ x) = β (e x) := fun x => by
    simp [hβdef, MulAut.congr_apply]
  have hβ2 : β * β = 1 := by
    have h1 : α₀ * α₀ = 1 := by rw [hα₀, ← map_mul, hb, map_one]
    rw [hβdef, ← map_mul, h1, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    have h1 : α₀ = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    exact hb1 (conjNormal_injective' F hC (h1.trans (map_one _).symm))
  have hfix : CatFactsSp4.fixOf α₀ = (centralizer ({b} : Set X)).subgroupOf F := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_iff]
    change α₀ x = x ↔ _
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := congrArg Subtype.val h
      simp only [hα₀, MulAut.conjNormal_apply] at h1
      calc b * (x : X) = b * (x : X) * b⁻¹ * b := by group
        _ = x * b := by rw [h1]
    · intro h
      apply Subtype.ext
      simp only [hα₀, MulAut.conjNormal_apply]
      rw [h b rfl, mul_inv_cancel_right]
  have hK₀C : K.subgroupOf F ≤ (centralizer ({b} : Set X)).subgroupOf F :=
    fun x hx => hKC hx
  have hK₀X : K.subgroupOf F ≤ CatFactsSp4.fixOf α₀ := hfix ▸ hK₀C
  have hK₀ : IsPComponent 2 ((K.subgroupOf F).subgroupOf (CatFactsSp4.fixOf α₀)) := by
    rw [hfix, ← CatFactsSp4.isPComponent_map_subgroupOf_iff 2 F.subtype F.subtype_injective hK₀C,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hKF]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKC hKF) inf_le_left hK
  obtain ⟨hMX, hM⟩ := CatFactsSp4.isPComponent_map_fixOf hcomm hK₀X hK₀
  set M := (K.subgroupOf F).map e.toMonoidHom with hMdef
  have hcardM : Nat.card M = Nat.card K := by
    rw [hMdef, card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hKF).toEquiv
  have hMperf : ⁅M, M⁆ = M := commutator_eq_of_isPComp hMX hM
  have hMfix : ∀ x ∈ M, β x = x := fun x hx => CatFactsSp4.mem_fixOf.mp (hMX hx)
  have hM2n : 2 ^ (2 * n) ∣ Nat.card M := by
    rw [hcardM]
    exact hK2n
  have hβinv : ∀ x, β (β x) = x := fun x => by
    rw [← MulAut.mul_apply, hβ2, MulAut.one_apply]
  obtain ⟨A, ψ, hAu, hlift, hcase⟩ := exists_lift_U4 hud hp2' β hβinv
  have hker : (QuotientGroup.mk' (CatFactsL4U4.StabU.scal p' f' Kf)).ker ≤
      center (ClassicalGroups.UnitaryFlag.unitarySU p' f' Kf 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact CatFactsL4U4.StabU.mem_center_of_mem_scal hz
  have hMle : M ≤ (ψ.eqLocus (MonoidHom.id _)).map
      (QuotientGroup.mk' (CatFactsL4U4.StabU.scal p' f' Kf)) :=
    perfect_le_map_eqLocus (β := β.toMonoidHom) (QuotientGroup.mk'_surjective _) hker ψ
      (fun g => hlift g) hMperf hMfix
  rcases hcase with hψv | ⟨hψv, hAA | hAA⟩
  ·
    exfalso
    have hIsCU : CatFactsL4U4.DiagU.IsCU hud A β := by
      refine ⟨hAu, fun g g' hg' => ?_⟩
      change β (QuotientGroup.mk g) = QuotientGroup.mk g'
      rw [hlift g]
      congr 1
      apply CatFactsL4U4.StabU.ext_val
      rw [hψv g, hg', Units.val_mul, Units.val_mul]
    exact false_of_inner_U4 hud hp2' hIsCU hβ1 (by rw [sq]; exact hβ2) hMperf hMfix hM2n
  ·
    exfalso
    have hd := four_mul_card_dvd_of_symm_U4 hud hp2' hAu hAA ψ hψv hMle
    have hq'0 : p' ^ f' ≠ 0 := by omega
    have hq2 : (p' ^ f') ^ 2 - 1 ≠ 0 := by
      have : 9 ≤ (p' ^ f') ^ 2 := by nlinarith
      omega
    have hq4 : (p' ^ f') ^ 4 - 1 ≠ 0 := by
      have : 81 ≤ (p' ^ f') ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (p' ^ f') ^ 4 := Nat.pow_le_pow_left hq'3 4
      omega
    have hk : 2 ^ (2 * n + 2) ∣ 4 * Nat.card M := by
      rw [pow_add, mul_comm (2 ^ (2 * n))]
      exact Nat.mul_dvd_mul (by norm_num) hM2n
    have h0 : (p' ^ f') ^ 2 * (((p' ^ f') ^ 2 - 1) * ((p' ^ f') ^ 4 - 1)) ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero 2 hq'0) (Nat.mul_ne_zero hq2 hq4)
    have h3 := le_v2_of_dvd h0 hk hd
    rw [padicValNat.mul (pow_ne_zero 2 hq'0) (Nat.mul_ne_zero hq2 hq4), padicValNat.pow,
      v2_odd hq'odd, mul_zero, zero_add, padicValNat.mul hq2 hq4, v2_four hq'odd hq'3] at h3
    omega
  obtain ⟨hSs, hScard⟩ := exists_simple_of_alt_U4 hud hp2' hAu hAA ψ hψv
  set S := (ψ.eqLocus (MonoidHom.id _)).map
    (QuotientGroup.mk' (CatFactsL4U4.StabU.scal p' f' Kf)) with hS
  have hST : S ≤ CatFactsSp4.fixOf β := by
    rintro _ ⟨g, hg, rfl⟩
    rw [CatFactsSp4.mem_fixOf]
    change β (QuotientGroup.mk g) = QuotientGroup.mk g
    rw [hlift g, show ψ g = g from hg]
  obtain ⟨-, -, hsn, -, -⟩ := hM
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hM2n
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd one_pos hM2n
    omega
  have hMeq : M = S := eq_of_isSubnormal_of_le_simple hsn hST hMle hSs hMne
  have := hSs
  have hsM : IsSimpleGroup ↥M := (MulEquiv.subgroupCongr hMeq).isSimpleGroup
  have hsK : IsSimpleGroup ↥K := ((Subgroup.subgroupOfEquivOfLe hKF).symm.trans
    ((K.subgroupOf F).equivMapOfInjective e.toMonoidHom e.injective)).isSimpleGroup
  have hO : pPrimeCore 2 ↥K = ⊥ := by
    have := pPrimeCore_normal (p := 2) (G := ↥K)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h | h
    · exact h
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥K)
      rw [h, Subgroup.card_top] at hcop
      have h2K : 2 ∣ Nat.card K := (dvd_pow_self 2 (by omega : 2 * n ≠ 0)).trans hK2n
      exact absurd (Nat.Coprime.coprime_dvd_right h2K hcop) (by decide)
  have hKO : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
    have h3 : Nat.card (pPrimeCore 2 ↥K) = 1 := by rw [hO, Subgroup.card_bot]
    rw [h3, mul_one] at h1
    exact h1.symm
  have hKcard : Nat.card K = Open.ordBC 2 (p' ^ f') := by
    rw [← hcardM, hMeq, hScard]
  have hqq : p ^ f = p' ^ f' := by
    rcases card_socle_cases hp2 hKt with hc | hc
    · rw [hKO, hKcard] at hc
      rcases lt_trichotomy (p ^ f) (p' ^ f') with h | h | h
      · exact absurd hc.symm (ordBC_two_lt hqodd hq'odd hq3 h).ne
      · exact h
      · exact absurd hc (ordBC_two_lt hq'odd hqodd hq'3 h).ne
    · exfalso
      rw [hKO, hKcard] at hc
      have h3 : Open.ordBC 2 3 ≤ Open.ordBC 2 (p' ^ f') := by
        rcases eq_or_lt_of_le hq'3 with h | h
        · rw [h]
        · exact (ordBC_two_lt ⟨1, rfl⟩ hq'odd le_rfl h).le
      have h4 : Open.ordBC 2 3 = 25920 := by decide
      omega
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hp hp' (by omega) (by omega) hqq
  exact hLie

theorem cf81E6P211L4U4 : CF81E6P211L4U4 := cf81E6P211L4U4_of_U4 cf81E6P211U4

end CFSG.ComponentClassification.GSThmB
