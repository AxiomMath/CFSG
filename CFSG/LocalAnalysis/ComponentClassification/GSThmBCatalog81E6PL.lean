module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLa

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GH74L4 (G : Type) [Group G] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ Blueprint.LieModel G .PSL 4 p f

@[expose] def GH74U4 (G : Type) [Group G] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ Blueprint.LieModel G .PSU 4 p f

@[expose] def CF81E6P211L4 : Prop := P211For GH74L4

@[expose] def CF81E6P211U4 : Prop := P211For GH74U4

theorem cf81E6P211L4U4_of (hL : CF81E6P211L4) (hU : CF81E6P211U4) : CF81E6P211L4U4 :=
  p211For_of_or (fun _ _ h => h) hL hU

namespace P211

theorem odd_of_pow_mod_eight {p f : ℕ} (hp : Odd p) (h8 : p ^ f % 8 ≠ 1) : Odd f := by
  by_contra h
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp h
  apply h8
  have hodd : Odd (p ^ k) := hp.pow
  have h1 : 8 ∣ (p ^ k) ^ 2 - 1 := eight_dvd_sq_sub_one hodd
  have h2 : 1 ≤ (p ^ k) ^ 2 := Nat.one_le_pow _ _ hodd.pos
  rw [show p ^ (k + k) = (p ^ k) ^ 2 by rw [sq, ← pow_add]]
  omega

theorem ordBC_two_lt {x y : ℕ} (hx : Odd x) (hy : Odd y) (hx3 : 3 ≤ x) (hxy : x < y) :
    Open.ordBC 2 x < Open.ordBC 2 y := by
  have h1 := ordBC_two_mul hx
  have h2 := ordBC_two_mul hy
  have a1 : x ^ 4 < y ^ 4 := Nat.pow_lt_pow_left hxy (by norm_num)
  have a2 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 2) 1
  have a3 : x ^ 4 - 1 ≤ y ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 4) 1
  have a4 : 0 < (x ^ 2 - 1) * (x ^ 4 - 1) := by
    have b1 : 9 ≤ x ^ 2 := by nlinarith
    have b2 : 81 ≤ x ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ x ^ 4 := Nat.pow_le_pow_left hx3 4
    exact Nat.mul_pos (by omega) (by omega)
  have key : x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) < y ^ 4 * ((y ^ 2 - 1) * (y ^ 4 - 1)) :=
    calc x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) < y ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) :=
          mul_lt_mul_of_pos_right a1 a4
      _ ≤ y ^ 4 * ((y ^ 2 - 1) * (y ^ 4 - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul a2 a3)
  omega

theorem eq_of_isSubnormal_of_le_simple {G : Type*} [Group G] {T M S : Subgroup G}
    (hsn : (M.subgroupOf T).IsSubnormal) (hST : S ≤ T) (hMS : M ≤ S) (hS : IsSimpleGroup S)
    (hM : M ≠ ⊥) : M = S := by
  have h1 : ((M.subgroupOf T).subgroupOf (S.subgroupOf T)).IsSubnormal := hsn.subgroupOf
  have hsS : IsSimpleGroup (S.subgroupOf T) := (Subgroup.subgroupOfEquivOfLe hST).isSimpleGroup
  rcases h1.eq_bot_or_top_of_isSimpleGroup hsS with h | h
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
    have hy1 : (⟨x, hST (hMS x.2)⟩ : T) ∈ M.subgroupOf T := Subgroup.mem_subgroupOf.mpr x.2
    have hy2 : (⟨x, hST (hMS x.2)⟩ : T) ∈ S.subgroupOf T := Subgroup.mem_subgroupOf.mpr (hMS x.2)
    have hy : (⟨x, hST (hMS x.2)⟩ : T) ∈ (⊥ : Subgroup T) := h.le_bot ⟨hy1, hy2⟩
    rw [Subgroup.mem_bot] at hy
    exact hx1 (Subtype.ext (congrArg (fun z : T => (z : G)) hy))
  · rw [Subgroup.subgroupOf_eq_top] at h
    refine le_antisymm hMS fun x hx => ?_
    have hy : (⟨x, hST hx⟩ : T) ∈ S.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (h hy)

end P211

open P211 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem cf81E6P211L4 : CF81E6P211L4 := by
  intro X _ _ hsimp hC ⟨p', f', hp', hp2', hf', h8, hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  refine Or.inr (Or.inl ?_)
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨K', _, _, hK', ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  let _ := Fintype.ofFinite K'
  set F := generalizedFitting X with hFdef
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have hq'odd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hq'3 : 3 ≤ p' ^ f' :=
    le_trans (by have := hp'.two_le; omega) (Nat.le_self_pow (by omega) p')
  have hchar' : ringChar K' ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp' hp2' hK'
  have h2 : (2 : K') ≠ 0 := Ring.two_ne_zero hchar'
  have hf'odd : Odd f' := odd_of_pow_mod_eight (hp'.odd_of_ne_two hp2') h8
  have hKF : K ≤ F := le_fstar_of_perfect hC e
    (derivedSeries_three_le_projectiveSL_n (by norm_num)) (commutator_eq_of_isPComp hKC hK)
  have hFcard : Nat.card F = Open.ordA 3 (p' ^ f') := GH74.card_of_lieModel_PSL (by norm_num) hLie
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
    rw [Nat.factorization_def _ Nat.prime_two, hFcard, v2_ordA_three hq'odd hq'3 h8] at hT
    have hb2 := hbound ((T : Subgroup ↥F).map F.subtype) (map_subtype_le _) (T.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective F.subtype_injective, hT, hD, ← pow_mul 2 m 2,
      ← pow_succ'] at hb2
    have := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hb2
    omega
  have hK2n : 2 ^ (2 * n) ∣ Nat.card K := (pow_dvd_pow 2 (by omega)).trans hKv
  set α₀ : MulAut ↥F := MulAut.conjNormal b with hα₀
  set β : MulAut (projectiveSL 4 K') := MulAut.congr e α₀ with hβdef
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
  obtain ⟨A, σ, ε, hε, hβA⟩ := (automorphism_generation (K := K') (n := 4) (by norm_num)).2 β
  have hσ : σ = 1 := CatFactsL4U4.StabL.fieldAut_eq_one_of_pow hp' hK' hf'odd A σ hε (m := 0)
    (by rw [← hβA, zero_add, pow_one, sq]; exact hβ2)
  subst hσ
  rw [map_one, mul_one] at hβA
  interval_cases ε
  · exfalso
    rw [pow_zero, mul_one] at hβA
    rw [hβA] at hβ1 hβ2 hMfix
    exact false_of_conjAut hp' hp2' hK' A hβ1 hβ2 hMperf hMfix hM2n
  · rw [pow_one] at hβA
    have hβsq : (conjAut 4 K' A * dualAut 4 K') ^ 2 = 1 := by rw [← hβA, sq]; exact hβ2
    have hMfix' : ∀ x ∈ M, (conjAut 4 K' A * dualAut 4 K') x = x := by
      rw [← hβA]
      exact hMfix
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hβsq with hsym | halt
    · exact (false_of_symmetric hp' hp2' hK' A hsym hMperf hMfix' hM2n).elim
    obtain ⟨S, hSs, hScard, hSfix, hSle⟩ := exists_simple_of_alternating hp' hp2' hf' hK' h2 A halt
    have hMS : M ≤ S := hSle M hMperf hMfix'
    have hST : S ≤ CatFactsSp4.fixOf β := fun y hy => by
      rw [CatFactsSp4.mem_fixOf, hβA]
      exact hSfix y hy
    obtain ⟨-, -, hsn, -, -⟩ := hM
    have hMne : M ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hM2n
      have h64 : 64 ≤ 2 ^ (2 * n) := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd one_pos hM2n
      omega
    have hMeq : M = S := eq_of_isSubnormal_of_le_simple hsn hST hMS hSs hMne
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

theorem cf81E6P211L4U4_of_U4 (hU : CF81E6P211U4) : CF81E6P211L4U4 :=
  cf81E6P211L4U4_of cf81E6P211L4 hU

end CFSG.ComponentClassification.GSThmB
