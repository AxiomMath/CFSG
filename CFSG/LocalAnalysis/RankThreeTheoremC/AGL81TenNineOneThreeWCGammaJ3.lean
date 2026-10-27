module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import Certificates.Certificate5172
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCU42
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.Sporadic.Schreier CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne


theorem j3_line4_norm :
    permOfArr 6156 j3tTrans[4]! * permOfArr 6156 j3tLines[4]! * (permOfArr 6156 j3tTrans[4]!)⁻¹ =
      j3tXB * permOfArr 6156 j3tLines[4]! := by
  obtain ⟨hv, he⟩ := Certificates.certificate5172
  have hvL := rep_of_validA (linesOK3_line j3t_lines_check.1 (by norm_num : 4 < 13)).1
  have hvX := rep_of_validA (j3tReps_spec (by norm_num : 1 < 2)).1
  have h := eq_of_eqA (rep_compA (rep_of_validA hv) hvL) (rep_compA (rep_compA hvX hvL)
    (rep_of_validA hv)) he
  rw [h, mul_inv_cancel_right]
  rfl

theorem j3_fuse_perm_gamma {T' : Subgroup (Equiv.Perm (Fin 6156))} (hT'R : T' ≤ j3P)
    (hT'c : Nat.card T' = 243) {x : Equiv.Perm (Fin 6156)} (hx : x ∈ j3P) (hxo : orderOf x = 3)
    (hcent : ∀ t ∈ T', t * x = x * t) :
    ∃ n ∈ j3P, ∃ E : Subgroup (Equiv.Perm (Fin 6156)), E ≤ T' ∧ x ∈ E ∧
      n ∈ normalizer (E : Set (Equiv.Perm (Fin 6156))) ∧ n * x * n⁻¹ ∈ E ∧
      n * x * n⁻¹ ∉ zpowers x := by
  obtain ⟨k, hk, c, hc, m, hm, rfl⟩ := j3t_fusion hx hxo
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl
    · exact (j3tReps_spec (by norm_num : 0 < 2)).2
    · exact (j3tReps_spec (by norm_num : 1 < 2)).2
  have hpp : ∀ {y : Equiv.Perm (Fin 6156)}, y ^ 3 = 1 → (y ^ m) ^ m = y := by
    intro y hy
    rcases hm with rfl | rfl
    · simp
    · rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hy, one_mul]
  have hcmm : (c ^ m) ^ m = c := hpp hc3
  set d := c ^ m with hd
  have hdR : d ∈ j3P := by
    have : d = k⁻¹ * (k * d * k⁻¹) * k := by group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hk) hx) hk
  have hcR : c ∈ j3P := hcmm ▸ j3P.pow_mem hdR m
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, one_pow] at hd
    rw [hd, mul_one, mul_inv_cancel, orderOf_one] at hxo
    omega
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  set Tk := T'.map (MulAut.conj k⁻¹).toMonoidHom with hTk
  have hTkc : Nat.card Tk = 243 := by
    rw [hTk, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hT'c]
  have hTkC : ∀ s ∈ Tk, s ∈ j3P ∧ s * c = c * s := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hk) (hT'R ht)) hk, ?_⟩
    have h1 : Commute (k⁻¹ * t * k) d := by
      show k⁻¹ * t * k * d = d * (k⁻¹ * t * k)
      have : k⁻¹ * t * k * d = k⁻¹ * (t * (k * d * k⁻¹)) * k := by group
      rw [this, hcent t ht]
      group
    have h2 := h1.pow_right m
    rw [hcmm] at h2
    exact h2
  have hle : ∀ {X : Equiv.Perm (Fin 6156)}, c = X →
      Tk ≤ centralizer {X} ⊓ j3P := by
    rintro X rfl s hs
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hTkC s hs).2, (hTkC s hs).1⟩
  rcases hc with hcA | hcB
  · exfalso
    have h := Subgroup.card_dvd_of_le (j3t_caseA.1 ▸ hle hcA)
    rw [hTkc, j3t_caseA.2] at h
    norm_num at h
  · have hQ : Tk = closure (permsA 6156 j3tCBGens) :=
      Subgroup.eq_of_le_of_card_ge (j3t_caseB.1 ▸ hle hcB) (by rw [j3t_caseB.2, hTkc])
    obtain ⟨hh, hconj, hcomm, hne1, hne2⟩ := j3_line4
    have hnorm := j3_line4_norm
    set h := permOfArr 6156 j3tTrans[4]!
    set y := permOfArr 6156 j3tLines[4]!
    rw [← hcB] at hconj hcomm hne1 hne2 hnorm
    have hyR : y ∈ j3P := hconj ▸ j3P.mul_mem (j3P.mul_mem hh hcR) (j3P.inv_mem hh)
    have hy3 : y ^ 3 = 1 := by rw [← hconj, conj_pow, hc3, mul_one, mul_inv_cancel]
    set E₀ := closure ({c, y} : Set (Equiv.Perm (Fin 6156))) with hE₀
    have hcE : c ∈ E₀ := subset_closure (by simp)
    have hyE : y ∈ E₀ := subset_closure (by simp)
    have hE₀T : E₀ ≤ Tk := by
      rw [closure_le]
      rintro w (rfl | rfl)
      · rw [hQ, j3t_caseB.1, ← hcB]
        exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, hcR⟩
      · rw [hQ, j3t_caseB.1, ← hcB]
        exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hcomm, hyR⟩
    have hhE : h ∈ normalizer (E₀ : Set (Equiv.Perm (Fin 6156))) :=
      mem_normalizer_closure_pair (by rw [hconj]; exact hyE)
        (by rw [hnorm]; exact E₀.mul_mem hcE hyE)
    have hnx : (k * h * k⁻¹) * (k * d * k⁻¹) * (k * h * k⁻¹)⁻¹ = k * y ^ m * k⁻¹ := by
      rw [← hconj, conj_pow, hd]
      group
    refine ⟨k * h * k⁻¹, j3P.mul_mem (j3P.mul_mem hk hh) (j3P.inv_mem hk),
      E₀.map (MulAut.conj k).toMonoidHom, ?_, ?_, conj_mem_normalizer_map hhE k, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨t, ht, htw⟩ := hE₀T hw
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at htw ⊢
      rw [← htw]
      simpa [mul_assoc] using ht
    · exact ⟨d, E₀.pow_mem hcE m, by simp⟩
    · rw [hnx]
      exact ⟨y ^ m, E₀.pow_mem hyE m, by simp⟩
    · rw [hnx]
      intro hmem
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
      rw [conj_zpow] at hj
      have hj' : d ^ j = y ^ m := by
        have := congrArg (fun w => k⁻¹ * w * k) hj
        simpa [mul_assoc] using this
      have hyc : y ∈ zpowers c := by
        rw [← hpp hy3, ← hj']
        exact Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.pow_mem _ (mem_zpowers c) m) j) m
      rw [mem_zpowers_iff_mem_range_orderOf, hco] at hyc
      simp only [Finset.mem_image, Finset.mem_range] at hyc
      obtain ⟨i, hi, hiy⟩ := hyc
      interval_cases i
      · apply hc1
        rw [pow_zero] at hiy
        have : c = h⁻¹ * (h * c * h⁻¹) * h := by group
        rw [this, hconj, ← hiy, mul_one, inv_mul_cancel]
      · exact hne1 (by rw [← hiy, pow_one])
      · exact hne2 hiy.symm

@[expose] def KFactTenNineWCGammaJ3 : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
    Nonempty (K ≃* j3P) →
    ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
      (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
      GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
      ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y


theorem kFactTenNineWCGammaJ3 : KFactTenNineWCGammaJ3 := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRc : Nat.card j3P = 50232960 := card_j3P
  have hZR : Subgroup.center j3P = ⊥ := by
    haveI : IsSimpleGroup j3P :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 j3PermEquiv.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center j3P) with h | h
    · exact h
    · exfalso
      have hc : IsMulCommutative j3P := Subgroup.center_eq_top_iff.mp h
      have hp := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup j3P)
      rw [hRc] at hp
      norm_num at hp
  have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center j3P := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [hZR, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  set ι : K →* Equiv.Perm (Fin 6156) := j3P.subtype.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  refine false_of_fuse_gamma hZK ?_ ?_ S A hA3 Y hY hwc
  ·
    intro _ φ hφ _
    obtain ⟨-, -, -, -, hA⟩ :=
      CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
    have hK : Nat.card K = 50232960 := by rw [Nat.card_congr e.toEquiv, hRc]
    have hAK : Nat.card (MulAut K) = 100465920 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv, hA]
    exact inner_of_card_le_two_mul hZK (by rw [hK, hAK]) φ (m := 1) hφ
  · intro T a haT hoa hcent
    have hTc : Nat.card ((T : Subgroup K).map ι) = 243 := by
      rw [Subgroup.card_map_of_injective hι, T.card_eq_multiplicity, Nat.card_congr e.toEquiv,
        j3_card_three]
    have hT'R : (T : Subgroup K).map ι ≤ j3P := by
      rintro _ ⟨t, -, rfl⟩
      exact (e t).2
    have hxo : orderOf (ι a) = 3 := by rw [orderOf_injective ι hι a, hoa]
    have hcent' : ∀ t ∈ (T : Subgroup K).map ι, t * ι a = ι a * t := by
      rintro _ ⟨t, ht, rfl⟩
      have h := congrArg ι (hcent t ht)
      rw [map_mul, map_mul, map_inv] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    obtain ⟨nP, hnR, E, hET, haE, hnE, hinE, hout⟩ :=
      j3_fuse_perm_gamma hT'R hTc (e a).2 hxo hcent'
    set n : K := e.symm ⟨nP, hnR⟩
    have hιn : ι n = nP := by simp [hιdef, n]
    have hιb : ι (n * a * n⁻¹) = nP * ι a * nP⁻¹ := by rw [map_mul, map_mul, map_inv, hιn]
    have hbT : n * a * n⁻¹ ∈ (T : Subgroup K) := by
      rw [← Subgroup.mem_map_iff_mem hι, hιb]
      exact hET hinE
    have hba : n * a * n⁻¹ ∉ zpowers a := by
      intro hmem
      apply hout
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
      refine mem_zpowers_iff.mpr ⟨j, ?_⟩
      have h' := congrArg ι hj
      rw [map_zpow, hιb] at h'
      exact h'
    have hRT : E.comap ι ≤ (T : Subgroup K) := by
      intro r hr
      obtain ⟨t, ht, htr⟩ := hET hr
      rw [hι htr] at ht
      exact ht
    refine ⟨E.comap ι, n, hRT, ?_, mem_normalizer_comap ι (by rw [hιn]; exact hnE), hbT, hba⟩
    refine not_isCyclic_of_mem (a := a) (b := n * a * n⁻¹) (show ι a ∈ E from haE)
      (show ι (n * a * n⁻¹) ∈ E by rw [hιb]; exact hinE) hoa ?_ hba
    rw [show n * a * n⁻¹ = MulAut.conj n a from rfl, MulEquiv.orderOf_eq, hoa]

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
