module

public import CFSG.LargeExtraspecial.AS35YRSet
public import CFSG.LargeExtraspecial.AS35YRFrameX
public import CFSG.LargeExtraspecial.AS35YLMOm
public import CFSG.LargeExtraspecial.AS35YLSCen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint
  CFSG.ClassicalGroups.Orthogonal AS35YR

namespace AS35YR

theorem eq_two_mul_of_dvd_YR {A P N L O ε ε' : ℤ} (hA : 0 < A) (hP : 0 < P) (hN : 8 ≤ N)
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1) (hL : L = A * (N - ε) * P)
    (hO : O = 2 * A * (N - ε') * P) (hdvd : L ∣ O) : O = 2 * L := by
  have hAP : A * P ≠ 0 := (mul_pos hA hP).ne'
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
  · rw [hO, hL]
    ring
  · exfalso
    have e1 : L = (N - 1) * (A * P) := by rw [hL]; ring
    have e2 : O = (2 * (N + 1)) * (A * P) := by rw [hO]; ring
    rw [e1, e2] at hdvd
    have h2 := (mul_dvd_mul_iff_right hAP).mp hdvd
    have h3 : (N - 1) ∣ 4 := by
      have := dvd_sub h2 (dvd_mul_left (N - 1) 2)
      rwa [show 2 * (N + 1) - 2 * (N - 1) = 4 by ring] at this
    have := Int.le_of_dvd (by norm_num) h3
    omega
  · exfalso
    have e1 : L = (N + 1) * (A * P) := by rw [hL]; ring
    have e2 : O = (2 * (N - 1)) * (A * P) := by rw [hO]; ring
    rw [e1, e2] at hdvd
    have h2 := (mul_dvd_mul_iff_right hAP).mp hdvd
    have h3 : (N + 1) ∣ 4 := by
      have := dvd_sub (dvd_mul_left (N + 1) 2) h2
      rwa [show 2 * (N + 1) - 2 * (N - 1) = 4 by ring] at this
    have := Int.le_of_dvd (by norm_num) h3
    omega
  · rw [hO, hL]
    ring

theorem Frame.comm_t_of_fix {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V} (F : Frame q)
    (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) (ga : g F.a = F.a) (gb : g F.b = F.b) :
    g * F.t = F.t * g := by
  have h := F.conj_t_eq hq hg fun z hz => by
    rw [Frame.apply_eq_of_mem_ell ga gb hz]
    exact hz
  calc g * F.t = g * F.t * g⁻¹ * g := by group
    _ = F.t * g := by rw [h]

end AS35YR

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem index_two_of_omega_YR (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus S.width 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus S.width 2 1) :
    4 ≤ S.width ∧ Nat.card S.LbarAsc * 2 = Nat.card S.O := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hLc : Nat.card S.LbarAsc = Nat.card (S.LbarAsc ⧸ center S.LbarAsc) :=
    (Nat.card_congr (AS35YL.quotEquiv_YL S.LbarAsc hc).toEquiv).symm
  set n := S.width with hn
  obtain ⟨hn4, ε, hε, hLz⟩ : 4 ≤ n ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (Nat.card (S.LbarAsc ⧸ center S.LbarAsc) : ℤ) =
        2 ^ (n * (n - 1)) * (2 ^ n - ε) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    rcases hL with hL | hL
    · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      have := Fintype.ofFinite K
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
      have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hn4
      rw [hK, pow_one] at hz
      refine ⟨hn4, 1, Or.inl rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv]
      exact_mod_cast hz
    · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      have := Fintype.ofFinite K
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
      have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K)
        hn4 hirr
      rw [hK, pow_one] at hz
      refine ⟨hn4, -1, Or.inr rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv, sub_neg_eq_add]
      exact_mod_cast hz
  refine ⟨hn4, ?_⟩
  have hdim : finrank (ZMod 2) S.Qt = 2 * ((n - 1) + 1) := by
    rw [S.finrank_Qt_eq_two_mul_width, ← hn, Nat.sub_add_cancel (by omega)]
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  obtain ⟨ε', hε', hO⟩ : ∃ ε' : ℤ, (ε' = 1 ∨ ε' = -1) ∧
      (Nat.card S.O : ℤ) = 2 * 2 ^ ((n - 1) * ((n - 1) + 1)) * (2 ^ ((n - 1) + 1) - ε') *
        ∏ i ∈ Finset.Icc 1 (n - 1), (((2 : ℤ) ^ 2) ^ i - 1) := by
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType S.q
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [h2] at h
      exact ⟨1, Or.inl rfl, h⟩
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [h2] at h
      exact ⟨-1, Or.inr rfl, h⟩
  have e1 : (n - 1) * ((n - 1) + 1) = n * (n - 1) := by
    rw [Nat.sub_add_cancel (by omega), mul_comm]
  have e2 : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
  have e3 : ∏ i ∈ Finset.Icc 1 (n - 1), (((2 : ℤ) ^ 2) ^ i - 1) =
      ∏ i ∈ Finset.Icc 1 (n - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
  rw [e1, e2, e3] at hO
  have hdvd : (Nat.card S.LbarAsc : ℤ) ∣ (Nat.card S.O : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Subgroup.card_subgroup_dvd_card S.LbarAsc)
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (n - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have hi1 := (Finset.mem_Icc.mp hi).1
    have : (2 : ℤ) ^ 2 ≤ 2 ^ (2 * i) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hN : (8 : ℤ) ≤ 2 ^ n := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  have key := eq_two_mul_of_dvd_YR (pow_pos (by norm_num : (0 : ℤ) < 2) _) hP hN hε hε'
    (hLc ▸ hLz) hO hdvd
  have : Nat.card S.O = 2 * Nat.card S.LbarAsc := by exact_mod_cast key
  omega

end Setting

namespace S14

theorem asc512POmegaNatStmt : Asc512POmegaNatStmt := by
  intro G _ _ S hS hst hnd hL _
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hn4, hidx⟩ := Setting.index_two_of_omega_YR hS hst hnd hL
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := Setting.DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨F, hFℓ, hFt⟩ := Setting.exists_frame_YR hS ht htM
  have hrad := Setting.radHyp_YR hS hidx ht htM F hFℓ hFt
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := finite_linearEquiv_YR
  refine hrad.false_of_omega S.q_nondegenerate hn4 S.finrank_Qt_eq_two_mul_width
    (Setting.card_PbarL_YR hS ht htM) ?_ ?_
  · intro v hvX w hwX hv hw p hp
    obtain ⟨ha, hb, -, -⟩ := Frame.refl1_fix hvX hv
    obtain ⟨ha', hb', -, -⟩ := Frame.refl1_fix hwX hw
    have hmem := mul_mem (refl1_mem hv) (refl1_mem hw)
    refine Setting.conj_mem_PbarL_YR hS hidx ht htM F hFt hmem
      (even_finrank_commSpace_refl1_mul S.q_nondegenerate hv hw)
      (F.comm_t_of_fix S.q_nondegenerate hmem ?_ ?_) p hp
    · rw [LinearEquiv.mul_apply, ha', ha]
    · rw [LinearEquiv.mul_apply, hb', hb]
  · intro u huX w hwX hu hw huw p hp
    obtain ⟨ha, hb, -, -⟩ := Frame.siegel_fix huX hwX hu hw huw
    have hmem := eichler_mem_orthogonalGroup S.q u w
    exact Setting.conj_mem_PbarL_YR hS hidx ht htM F hFt hmem
      (even_finrank_commSpace_siegel S.q_nondegenerate hu hw huw)
      (F.comm_t_of_fix S.q_nondegenerate hmem ha hb) p hp

end S14

end CFSG.LargeExtraspecial
