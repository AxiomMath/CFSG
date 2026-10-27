module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4D4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Top3
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3E16
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3E16b


public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open scoped MatrixGroups

theorem card_centralizer_involution_M12'
    {p : NativeSporadic.M12} (hp : orderOf p = 2) :
    Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) = 192 ∨
      Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) = 240 := by
  have hp' : orderOf (p : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hp
  obtain ⟨r, hr, c, hcM, hpc⟩ :=
    m12_involution_cover.1 (p : Equiv.Perm (Fin 12))
      (by simp) hp'
  have hmap : (Subgroup.centralizer ({p} : Set NativeSporadic.M12)).map
      NativeSporadic.M12.subtype =
      centralizerIn NativeSporadic.M12 (p : Equiv.Perm (Fin 12)) := by
    ext x
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxp), rfl⟩
  have hcard : Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) =
      Nat.card (centralizerIn NativeSporadic.M12
        (p : Equiv.Perm (Fin 12))) := by
    rw [← hmap, Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective]
  rw [hcard, hpc, centralizerIn_conj NativeSporadic.M12 hcM,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    exact card_centralizerIn_m12Rep1
  · right
    exact card_centralizerIn_m12Rep2


theorem sixtyfour_dvd_of_odd {q : ℕ} (hq : q % 2 = 1) : 64 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have h1 : 8 ∣ q ^ 2 - 1 := eight_dvd_sq_sub_one hq
  have hq3 : q ^ 3 % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hq).pow)
  have h2 : 8 ∣ (q ^ 3) ^ 2 - 1 := eight_dvd_sq_sub_one hq3
  rw [← pow_mul] at h2
  exact (by norm_num : (64 : ℕ) = 8 * 8) ▸ mul_dvd_mul h2 h1

theorem card_alt_fin (n : ℕ) (hn : 2 ≤ n) : Nat.card (alternatingGroup (Fin n)) = Nat.factorial n / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]


theorem card_centralizer_eq_of_top {K : Type} [Group K] [Finite K] {z : K}
    (htop : oPrimeResidual 2 ↥(centralizer ({z} : Set K)) = ⊤) {Y' : Subgroup K}
    (hY'C : Y' ≤ centralizer ({z} : Set K))
    (hY'all : ∀ x ∈ centralizer ({z} : Set K), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Y') :
    Nat.card ↥(centralizer ({z} : Set K)) = Nat.card Y' := by
  refine le_antisymm ?_ (Subgroup.card_le_of_le hY'C)
  have hle : centralizer ({z} : Set K) ≤ Y' := by
    intro c hc
    have hc' : (⟨c, hc⟩ : ↥(centralizer ({z} : Set K))) ∈ oPrimeResidual 2 ↥(centralizer ({z} : Set K)) := by
      rw [htop]; exact Subgroup.mem_top _
    have hcl : oPrimeResidual 2 ↥(centralizer ({z} : Set K)) ≤
        Y'.subgroupOf (centralizer ({z} : Set K)) := by
      unfold oPrimeResidual
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨k, hk⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hY'all x x.2 ⟨k, by
        have := congrArg Subtype.val hk
        simpa using this⟩
    exact Subgroup.mem_subgroupOf.1 (hcl hc')
  exact Subgroup.card_le_of_le hle

theorem classify_g2_three
    {K : Type} [Group K] [Finite K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : Catalog K) (hgen : Gen4 K)
    (htwo : Open.twoRank K = 3) (hfilter : GH74FilterStmt) {z : K} (hz : orderOf z = 2)
    (h32 : 32 ∣ Nat.card K) (h128 : ¬ 128 ∣ Nat.card K)
    (hY : 64 ∣ Nat.card K → ∃ Y' : Subgroup K, Y' ≤ centralizer ({z} : Set K) ∧ Nat.card Y' = 576 ∧
      ∀ x ∈ centralizer ({z} : Set K), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Y') :
    LieModel K .G2 0 3 1 := by
  have hconc := hfilter K hcat hnab (by omega) hgen
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, hM | hM⟩ := h1
    ·
      have hqodd : (p₀ ^ f₀) % 2 = 1 := Nat.odd_iff.mp ((hp₀.odd_of_ne_two hp₀2).pow)
      have hq3le : 3 ≤ p₀ ^ f₀ := by
        have h2 := hp₀.two_le
        have h3 : p₀ ≤ p₀ ^ f₀ := Nat.le_self_pow (by omega) p₀
        omega
      have hcard := CFSG.GH74.card_of_lieModel_G2 hp₀2 hM
      have h64 : 64 ∣ Nat.card K := by
        rw [hcard, CFSG.Open.ordG2]
        exact Dvd.dvd.trans (sixtyfour_dvd_of_odd hqodd)
          ⟨(p₀ ^ f₀) ^ 6, by ring⟩
      obtain ⟨Y', hY'C, hY'c, hY'all⟩ := hY h64
      obtain ⟨F, hF, hFin, S, hFc, hSz⟩ := GHInv.exists_shape_G2 hp₀ hp₀2 hM z hz
      have hFodd : Odd (Nat.card F) := hFc ▸ (hp₀.odd_of_ne_two hp₀2).pow
      have htop := S.oPrimeResidual_eq_top_of_odd hFodd hFodd
      have hCc : Nat.card ↥(centralizer ({z} : Set K)) = 576 := by
        rw [card_centralizer_eq_of_top htop hY'C hY'all, hY'c]
      have hS := shape_card_eq S
      rw [hCc, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFc] at hS
      have h24 : (p₀ ^ f₀) * ((p₀ ^ f₀) ^ 2 - 1) = 24 := by
        have : ((p₀ ^ f₀) * ((p₀ ^ f₀) ^ 2 - 1)) * ((p₀ ^ f₀) * ((p₀ ^ f₀) ^ 2 - 1)) = 24 * 24 := by
          omega
        exact Nat.mul_self_inj.mp this
      have hq3 : p₀ ^ f₀ = 3 := by
        by_contra hne
        have h4q : 4 ≤ p₀ ^ f₀ := by omega
        have h16 : 16 ≤ (p₀ ^ f₀) ^ 2 := by nlinarith
        have : 4 * 15 ≤ (p₀ ^ f₀) * ((p₀ ^ f₀) ^ 2 - 1) := Nat.mul_le_mul h4q (by omega)
        omega
      have hp3 : p₀ = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_three).1
          (hq3 ▸ dvd_pow_self p₀ (by omega : f₀ ≠ 0))
      have hf1 : f₀ = 1 := by
        rw [hp3] at hq3
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using hq3)
      rw [hp3, hf1] at hM
      exact hM
    ·
      exfalso
      have hqodd : (p₀ ^ f₀) % 2 = 1 := Nat.odd_iff.mp ((hp₀.odd_of_ne_two hp₀2).pow)
      have hq3le : 3 ≤ p₀ ^ f₀ := by
        have h2 := hp₀.two_le
        have h3 : p₀ ≤ p₀ ^ f₀ := Nat.le_self_pow (by omega) p₀
        omega
      have hcard := CFSG.GH74.card_of_lieModel_trialityD4 hp₀2 hM
      have h64 : 64 ∣ Nat.card K := by
        rw [hcard, CFSG.Open.ordTrialityD4]
        exact Dvd.dvd.trans (sixtyfour_dvd_of_odd hqodd)
          ⟨(p₀ ^ f₀) ^ 12 * ((p₀ ^ f₀) ^ 8 + (p₀ ^ f₀) ^ 4 + 1), by ring⟩
      obtain ⟨Y', hY'C, hY'c, hY'all⟩ := hY h64
      obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hSz⟩ :=
        GHInv.exists_shape_D4 hp₀ hp₀2 hM z hz
      have hodd₂ : Odd (Nat.card F₂) := hc₂ ▸ (hp₀.odd_of_ne_two hp₀2).pow
      have hodd₁ : Odd (Nat.card F₁) := hc₁ ▸ ((hp₀.odd_of_ne_two hp₀2).pow).pow
      have htop := S.oPrimeResidual_eq_top_of_odd hodd₁ hodd₂
      have hCc : Nat.card ↥(centralizer ({z} : Set K)) = 576 := by
        rw [card_centralizer_eq_of_top htop hY'C hY'all, hY'c]
      have hS := shape_card_eq S
      rw [hCc, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hc₁, hc₂] at hS
      have h27 : 27 ≤ (p₀ ^ f₀) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p₀ ^ f₀) ^ 3 := Nat.pow_le_pow_left hq3le 3
      have h729 : 729 ≤ ((p₀ ^ f₀) ^ 3) ^ 2 := by
        calc 729 = 27 ^ 2 := by norm_num
          _ ≤ ((p₀ ^ f₀) ^ 3) ^ 2 := Nat.pow_le_pow_left h27 2
      have h9 : 9 ≤ (p₀ ^ f₀) ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ (p₀ ^ f₀) ^ 2 := Nat.pow_le_pow_left hq3le 2
      have ha : 27 * 728 ≤ (p₀ ^ f₀) ^ 3 * (((p₀ ^ f₀) ^ 3) ^ 2 - 1) :=
        Nat.mul_le_mul h27 (by omega)
      have hb : 3 * 8 ≤ (p₀ ^ f₀) * ((p₀ ^ f₀) ^ 2 - 1) := Nat.mul_le_mul hq3le (by omega)
      have := Nat.mul_le_mul ha hb
      omega
  · exact (let ⟨E, hE2, hE16⟩ := e16_psp4 h2; false_of_E16 htwo E hE2 hE16).elim
  ·
    exfalso
    obtain ⟨f, hf⟩ := h3
    obtain ⟨k, -, hcard⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hf
    rw [hcard] at h32
    have := ordRee_pow_three_mod k
    omega
  · exact (let ⟨E, hE2, hE16⟩ := e16_psl4 h4; false_of_E16 htwo E hE2 hE16).elim
  · exact (let ⟨E, hE2, hE16⟩ := e16_psu4 h5; false_of_E16 htwo E hE2 hE16).elim
  · exact (let ⟨E, hE2, hE16⟩ := e16_psl5 h6; false_of_E16 htwo E hE2 hE16).elim
  · exact (let ⟨E, hE2, hE16⟩ := e16_psu5 h7; false_of_E16 htwo E hE2 hE16).elim
  · exfalso
    rcases h8 with hA | hB | hC | hD
    · have hc : Nat.card K = 504 := by
        rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hA]; decide
      rw [hc] at h32
      omega
    · have hc : Nat.card K = 4080 := by
        rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hB]; decide
      rw [hc] at h32
      omega
    · exact (let ⟨E, hE2, hE16⟩ := e16_psl3_four hC; false_of_E16 htwo E hE2 hE16)
    · have hc : Nat.card K = 29120 := by
        rw [CFSG.GH74.card_of_lieModel_twistedB2 hD]; decide
      have h64 : 64 ∣ Nat.card K := by rw [hc]; norm_num
      obtain ⟨Y', -, hY'c, -⟩ := hY h64
      have hdvd : Nat.card Y' ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
      rw [hY'c, hc] at hdvd
      omega
  · exfalso
    obtain ⟨n, hn8, hn11, ⟨e⟩⟩ := h9
    have hcn : Nat.card K = Nat.factorial n / 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_alt_fin n (by omega)
    interval_cases n
    · exact (let ⟨E, hE2, hE16⟩ := e16_alt_eight_nine (by norm_num) (by norm_num) e
        false_of_E16 htwo E hE2 hE16)
    · exact (let ⟨E, hE2, hE16⟩ := e16_alt_eight_nine (by norm_num) (by norm_num) e
        false_of_E16 htwo E hE2 hE16)
    · rw [hcn] at h128
      exact h128 (by norm_num [Nat.factorial])
    · rw [hcn] at h128
      exact h128 (by norm_num [Nat.factorial])
  · exfalso
    rcases h10 with hM12 | hM22 | hM23 | hJ1 | hJ2 | hJ3 | hMcL | hLy
    · have hc := card_of_isSporadic_M12 hM12
      obtain ⟨e⟩ := hM12
      have h64 : 64 ∣ Nat.card K := by rw [hc]; norm_num
      obtain ⟨Y', hY'C, hY'c, -⟩ := hY h64
      have hzord' : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
      have hC := card_centralizer_involution_M12' hzord'
      have hcardC : Nat.card ↥(centralizer ({z} : Set K)) =
          Nat.card ↥(centralizer ({e z} : Set NativeSporadic.M12)) := card_centralizer_equiv e z
      have hle : Nat.card Y' ≤ Nat.card ↥(centralizer ({z} : Set K)) :=
        Subgroup.card_le_of_le hY'C
      omega
    · have hc := card_of_isSporadic_M22 hM22
      rw [hc] at h128
      exact h128 (by norm_num)
    · have hc := card_of_isSporadic_M23 hM23
      rw [hc] at h128
      exact h128 (by norm_num)
    · have hc := card_of_isSporadic_J1 hJ1
      rw [hc] at h32
      exact absurd h32 (by norm_num)
    · have hc := card_of_isSporadic_J2 hJ2
      rw [hc] at h128
      exact h128 (by norm_num)
    · have hc := card_of_isSporadic_J3 hJ3
      rw [hc] at h128
      exact h128 (by norm_num)
    · have hc := card_of_isSporadic_McL hMcL
      rw [hc] at h128
      exact h128 (by norm_num)
    · have hc := card_of_isSporadic_Ly hLy
      rw [hc] at h128
      exact h128 (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
