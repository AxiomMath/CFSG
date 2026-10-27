module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma card_sup_le_mul {H K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ := (mem_sup_iff_of_normalizes hK).mp x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
  have h := Nat.card_le_card_of_surjective f hsurj
  rwa [Nat.card_prod] at h

private lemma zpowers_lam_normalizes_zpowers_rho
    (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ zpowers lam, ∀ h ∈ zpowers rho, k * h * k⁻¹ ∈ zpowers rho := by
  have hlam_norm : lam ∈ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (lam * rho * lam⁻¹) = Subgroup.zpowers rho
    rw [hc.lam_rho, Subgroup.zpowers_inv]
  intro k hk h hh
  have hk' : k ∈ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hlam_norm hk
  exact ((Subgroup.mem_normalizer_iff.mp hk') h).mp hh

theorem k18_card_OK (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card (ctxOK t tau x₁ x₂ rho) = 2 ^ 11 := by
  have hc13 := hc.toCtx13
  have hOKdvd : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ∣ 2 ^ 12 := by
    rw [← l18_card_sylow hc]
    exact Subgroup.card_dvd_of_le (l18_OK_le_sylow hc)
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hOKdvd
  have hOKne : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ≠ 2 ^ 12 := by
    intro hcard
    have hEq : ctxOK t tau x₁ x₂ rho = 𝒮 :=
      Subgroup.eq_of_le_of_card_ge (l18_OK_le_sylow hc)
        (by rw [hcard, l18_card_sylow hc])
    exact l18_lam_not_mem_OK hc13 (hEq ▸ (l18_T_le_sylow hc).2.2.2)
  have hjne : j ≠ 12 := by
    intro hj12
    exact hOKne (by rw [hj, hj12])
  have hj11 : j ≤ 11 := by omega
  have hOKle : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ≤ 2 ^ 11 := by
    rw [hj]
    exact pow_le_pow_right' (a := 2) (by norm_num) hj11
  set T : Subgroup G := closure ({rho, lam} : Set G) with hT
  have hK_eq : ctxK t tau x₁ x₂ rho = ctxOK t tau x₁ x₂ rho ⊔ T := by
    rw [hT]
    show ctxK t tau x₁ x₂ rho =
      CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊔ closure {rho, lam}
    exact hc.K_eq
  have hTnorm : ∀ k ∈ T, ∀ h ∈ ctxOK t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxOK t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkK : k ∈ ctxK t tau x₁ x₂ rho := by
      rw [hK_eq]
      exact Subgroup.mem_sup_right hk
    exact (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
      k hkK h hh
  have hKle : Nat.card (ctxK t tau x₁ x₂ rho) ≤
      Nat.card (ctxOK t tau x₁ x₂ rho) * Nat.card T := by
    rw [hK_eq]
    exact card_sup_le_mul hTnorm
  have hT_eq : T = zpowers rho ⊔ zpowers lam := by
    rw [hT]
    have hset : ({rho, lam} : Set G) = {rho} ∪ {lam} := by
      ext x
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
    rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure rho,
      Subgroup.zpowers_eq_closure lam]
  have hTcard : Nat.card T ≤ 6 := by
    rw [hT_eq]
    have hbound := card_sup_le_mul (H := zpowers rho) (K := zpowers lam)
      (zpowers_lam_normalizes_zpowers_rho hc13)
    have hrho : Nat.card (zpowers rho) = 3 := by
      rw [Nat.card_zpowers, hc13.ord_rho]
    have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc13).1
    have hlam1 : lam ≠ 1 := by
      intro h
      exact l18_lam_not_mem_OK hc13 (by rw [h]; exact Subgroup.one_mem _)
    have hlam_ord : orderOf lam = 2 := orderOf_eq_prime hlam2 hlam1
    have hlamcard : Nat.card (zpowers lam) = 2 := by
      rw [Nat.card_zpowers, hlam_ord]
    rw [hrho, hlamcard] at hbound
    simpa using hbound
  have hge : 2 ^ 11 ≤ Nat.card ↥(ctxOK t tau x₁ x₂ rho) := by
    have h1 : 3 * 2 ^ 12 ≤ Nat.card (ctxOK t tau x₁ x₂ rho) * Nat.card T := by
      rw [← hc.card_K]
      exact hKle
    have h2 : 3 * 2 ^ 12 ≤ Nat.card (ctxOK t tau x₁ x₂ rho) * 6 :=
      le_trans h1 (Nat.mul_le_mul_left _ hTcard)
    have h3 : (2 : ℕ) ^ 11 * 6 = 3 * 2 ^ 12 := by norm_num
    rw [← h3] at h2
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  exact le_antisymm hOKle hge

theorem k18_sylow_eq (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    𝒮 = ctxOK t tau x₁ x₂ rho ⊔ zpowers lam := by
  have hc13 := hc.toCtx13
  have hle : ctxOK t tau x₁ x₂ rho ⊔ zpowers lam ≤ 𝒮 := by
    refine sup_le (l18_OK_le_sylow hc) ?_
    exact Subgroup.zpowers_le.mpr (l18_T_le_sylow hc).2.2.2
  have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc13).1
  have hlam1 : lam ≠ 1 := by
    intro h
    exact l18_lam_not_mem_OK hc13 (by rw [h]; exact Subgroup.one_mem _)
  have hlam_ord : orderOf lam = 2 := orderOf_eq_prime hlam2 hlam1
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ ctxOK t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxOK t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkK : k ∈ ctxK t tau x₁ x₂ rho :=
      Subgroup.zpowers_le.mpr (l17_mem_K hc13).2.2.2.1 hk
    exact (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
      k hkK h hh
  have hHK : ctxOK t tau x₁ x₂ rho ⊓ zpowers lam = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxOK, hxzp⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_zpowers_iff] at hxzp
    obtain ⟨k, rfl⟩ := hxzp
    have hk'' : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one k
    rcases hk'' with hk | hk
    · rw [zpow_eq_zpow_emod' (x := lam) (n := 2) k hlam2, hk]
      simp
    · rw [zpow_eq_zpow_emod' (x := lam) (n := 2) k hlam2, hk] at hxOK
      simp only [zpow_one] at hxOK
      exact absurd hxOK (l18_lam_not_mem_OK hc13)
  have hcard : Nat.card ↥(ctxOK t tau x₁ x₂ rho ⊔ zpowers lam) = 2 ^ 12 := by
    rw [card_sup_eq_mul hnorm hHK, k18_card_OK hc, Nat.card_zpowers lam, hlam_ord]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, l18_card_sylow hc])).symm

theorem k18A_C_eq (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxCY t tau x₁ x₂ rho = ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
  have hc13 := hc.toCtx13
  have hle : ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) ≤
      ctxCY t tau x₁ x₂ rho := l18_QA_le_C hc13
  have hXK : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    rcases ha with rfl | rfl
    · exact (l17_mem_K hc13).2.1
    · exact (l17_mem_K hc13).2.2.1
  have hnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    exact hc.normal_Q_K.2 k (hXK hk) h hh
  have hXcent : closure ({tau, om} : Set G) ≤ Subgroup.centralizer ({rho} : Set G) := by
    rw [← l18_C_cap_cent_rho hc13]
    exact inf_le_right
  have hbot : ctxQ t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxQ, hxX⟩ := Subgroup.mem_inf.mp hx
    have hxP : x ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc13 hxQ
    have hxcomm : x * rho = rho * x :=
      ((Subgroup.mem_centralizer_iff.mp (hXcent hxX)) rho (by simp)).symm
    exact l17_CP_rho hc13 x hxP hxcomm
  have hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) = 2 ^ 8 := by
    rw [card_sup_eq_mul hnorm hbot, IsZ4Z4E4.card hc13.q_iso, l17_card_tauom hc13]
    norm_num
  have hcardle : Nat.card (ctxCY t tau x₁ x₂ rho) ≤
      Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) := by
    rw [hcard, hc.card_C]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
