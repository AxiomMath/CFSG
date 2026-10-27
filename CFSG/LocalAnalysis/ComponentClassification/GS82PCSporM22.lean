module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporSL2
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporOrd
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_sylow_seven [Fact (Nat.Prime 7)] {C : Type*} [Group C] [Finite C] (R : Sylow 7 C)
    (h7 : 7 ∣ Nat.card C) (h49 : ¬ 49 ∣ Nat.card C) : Nat.card R = 7 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hidx := (R : Subgroup C).index_mul_card
  have hnd := R.not_dvd_index
  rcases k with _ | _ | k
  · rw [hk, pow_zero, mul_one] at hidx
    exact absurd (hidx ▸ h7) hnd
  · rw [hk, pow_one]
  · exfalso
    apply h49
    rw [← hidx, hk]
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (dvd_refl 7) 2 |>.trans
      (pow_dvd_pow 7 (by omega))) _

theorem exists_involution_commute_seven {C : Type*} [Group C] [Finite C]
    (hC : Nat.card C = 1344) {N : Subgroup C} [N.Normal] (hN : Nat.card N = 168) :
    ∃ g r : C, orderOf g = 2 ∧ orderOf r = 7 ∧ g * r = r * g := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : ∀ Q : Sylow 7 C, (Q : Subgroup C) ≤ N := by
    intro Q x hx
    have hQ7 := card_sylow_seven Q (by rw [hC]; norm_num) (by rw [hC]; norm_num)
    have hx7 : orderOf x ∣ 7 := by
      rw [← hQ7, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    have hq : Nat.card (C ⧸ N) = 8 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hC, hN] at h1
      omega
    have hx8 : orderOf (QuotientGroup.mk' N x) ∣ 8 := hq ▸ orderOf_dvd_natCard _
    have hx7' : orderOf (QuotientGroup.mk' N x) ∣ 7 :=
      (orderOf_map_dvd (QuotientGroup.mk' N) x).trans hx7
    have h1 : orderOf (QuotientGroup.mk' N x) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 7 8) hx7' hx8
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hcard8 : Nat.card (Sylow 7 C) ≤ 8 := by
    obtain ⟨R'⟩ : Nonempty (Sylow 7 N) := inferInstance
    have hR' := card_sylow_seven R' (by rw [hN]; norm_num) (by rw [hN]; norm_num)
    have hidx : (R' : Subgroup N).index = 24 := by
      have h1 := (R' : Subgroup N).index_mul_card
      rw [hR', hN] at h1
      omega
    have hdvd : Nat.card (Sylow 7 N) ∣ 24 := hidx ▸ R'.card_dvd_index
    have hmod := card_sylow_modEq_one 7 N
    have hle : Nat.card (Sylow 7 N) ≤ 8 := by
      have hpos : 0 < Nat.card (Sylow 7 N) := Nat.card_pos
      have h24 : Nat.card (Sylow 7 N) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      unfold Nat.ModEq at hmod
      interval_cases h : Nat.card (Sylow 7 N) <;> simp_all
    refine le_trans (Nat.card_le_card_of_injective (fun Q : Sylow 7 C => Q.subtype (hQN Q))
      fun Q₁ Q₂ h => Sylow.subtype_injective h) hle
  obtain ⟨R⟩ : Nonempty (Sylow 7 C) := inferInstance
  have hR7 := card_sylow_seven R (by rw [hC]; norm_num) (by rw [hC]; norm_num)
  set NR := normalizer ((R : Subgroup C) : Set C) with hNRdef
  have hNR : 168 ≤ Nat.card NR := by
    have h1 := NR.index_mul_card
    have h2 : Nat.card (Sylow 7 C) = NR.index := R.card_eq_index_normalizer
    rw [← h2, hC] at h1
    have hpos : 0 < Nat.card (Sylow 7 C) := Nat.card_pos
    nlinarith
  set φ := (R : Subgroup C).normalizerMonoidHom with hφ
  have hAut : Nat.card (MulAut (R : Subgroup C)) = 6 := by
    have : IsCyclic (R : Subgroup C) := isCyclic_of_prime_card hR7
    rw [IsCyclic.card_mulAut, hR7, Nat.totient_prime (by norm_num)]
  have hrange : Nat.card φ.range ∣ 6 := hAut ▸ Subgroup.card_subgroup_dvd_card _
  have hker : Nat.card NR = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker φ, mul_comm]
    exact (φ.ker.index_mul_card).symm
  have hk28 : 28 ≤ Nat.card φ.ker := by
    have h6 : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hrange
    nlinarith
  have hkC : Nat.card φ.ker ∣ 1344 := by
    rw [← hC]
    exact (Subgroup.card_subgroup_dvd_card φ.ker).trans (Subgroup.card_subgroup_dvd_card NR)
  have hk2 : 2 ∣ Nat.card φ.ker := by
    by_contra hk
    have hcop : Nat.Coprime (Nat.card φ.ker) 64 :=
      Nat.Coprime.pow_right 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk).symm
    have h21 : Nat.card φ.ker ∣ 21 :=
      hcop.dvd_of_dvd_mul_left (by rw [show 64 * 21 = 1344 by norm_num]; exact hkC)
    have := Nat.le_of_dvd (by norm_num) h21
    omega
  have hker' : φ.ker = (centralizer ((R : Subgroup C) : Set C)).subgroupOf NR :=
    Subgroup.normalizerMonoidHom_ker _
  rw [hker'] at hk2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((centralizer ((R : Subgroup C) : Set C)).subgroupOf NR)) 2 hk2
  have hgk : (((g : NR) : C)) ∈ centralizer ((R : Subgroup C) : Set C) := g.2
  have : IsCyclic (R : Subgroup C) := isCyclic_of_prime_card hR7
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (R : Subgroup C))
  refine ⟨((g : NR) : C), r, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  · rw [Subgroup.orderOf_coe, hr, hR7]
  · exact (mem_centralizer_iff.mp hgk r r.2).symm

theorem exists_ne_of_quasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem isSimpleGroup_of_quasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  exact IsSimpleGroup.isSimpleGroup_of_surjective
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toMonoidHom
    (MulEquiv.surjective _)

theorem isSimpleGroup_of_mulEquiv' {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [Nontrivial B] (e : A ≃* B) : IsSimpleGroup B :=
  IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

section M22


theorem card_of_lieModel_psl_two_seven {X : Type} [Group X] (hL : LieModel X .PSL 2 7 1) :
    Nat.card X = 168 := by
  have ha := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL
  obtain ⟨-, h1, -⟩ := CatLeafProof.lieOrderFormulasInput X .PSL 2 7 1 ha hL
  have hd : CatLeaf.lieOrderDivisor .PSL 2 (7 ^ 1) = 2 := by decide
  have hn : CatLeaf.lieOrderNumerator .PSL 2 (7 ^ 1) = 336 := by decide
  rw [hd, hn] at h1
  omega

theorem false_of_m22_commute {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M22) {c r : S} (hc : orderOf c = 2)
    (hr : orderOf r = 7) (hcr : c * r = r * c) : False := by
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hα : MulAut.congr e (MulAut.conj c) = MulAut.conj (e c) := by
    ext x
    simp [MulAut.congr_apply]
  have hαα : MulAut.conj (e c) * MulAut.conj (e c) = 1 := by
    rw [← map_mul, ← map_mul, hc2, map_one, map_one]
  have hα1 : MulAut.conj (e c) ≠ 1 := by
    intro h1
    have hcZ : c ∈ center S := by
      rw [mem_center_iff]
      intro y
      apply e.injective
      have h2 := congrArg (fun φ : MulAut NativeSporadic.M22 => φ (e y)) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      rw [map_mul, map_mul]
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hb | ht
    · rw [hb, mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.mp (ht ▸ mem_top b : b ∈ center S) a)
  have h384 := GH74.Generic.S45.m22_inner_fixed_card (MulAut.conj (e c)) hαα hα1 ⟨e c, rfl⟩
  have hcard : Nat.card (fixedSubgroup (MulAut.conj c)) = 384 := by
    rw [SporFix.card_fixedSubgroup_eq e, hα]
    exact h384
  have hrmem : r ∈ fixedSubgroup (MulAut.conj c) := by
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, MulAut.conj_apply, hcr,
      mul_inv_cancel_right]
  have h7 := orderOf_dvd_natCard (⟨r, hrmem⟩ : fixedSubgroup (MulAut.conj c))
  rw [Subgroup.orderOf_mk, hr, hcard] at h7
  norm_num at h7

theorem false_of_m22 (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hfree : CatalogueU.SporadicOddCoreFree .M22)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .M22) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  have hna := nonabelian_quot h.quasisimple h.oddCore
  set e' := (quotEquiv h.oddCore).trans e
  obtain ⟨σ, hI⟩ := exists_image_of_oddCore h hTtop (oddCore_fixed_eq_bot hfree hna e')
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hI.proper.1 y) hI.proper.ne_one
  have hCard := SporFix.card_fixedSubgroup_m22 e' hσ2
  set P := T.map (rho Y) with hPdef
  have hPC : Nat.card P ∣ Nat.card (fixedSubgroup σ) := Subgroup.card_dvd_of_le hI.proper.2.1
  have hcP : Nat.card (P ⧸ center P) ∣ Nat.card P := Subgroup.card_quotient_dvd_card _
  have hdvd : Nat.card (T ⧸ center T) ∣ Nat.card (fixedSubgroup σ) := hI.card ▸ hcP.trans hPC
  have hZT : Open.fusionZStar T = center T :=
    fusionZStar_eq_center_of_quasisimple hI.quasiT (by
      have := LocalCores.isQuasisimple_nontrivial hI.quasiT
      rw [hI.oddCoreT]; exact bot_ne_top)
  have hcT : Nat.card (T ⧸ Open.fusionZStar T) = Nat.card (T ⧸ center T) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZT).toEquiv
  have hle : Nat.card (T ⧸ center T) ≤ 1344 := by
    have := Nat.le_of_dvd Nat.card_pos hdvd
    rcases hCard with h1 | h1 | h1 <;> omega
  have hL : LieModel (T ⧸ center T) .PSL 2 7 1 := by
    rcases h.typC with ⟨τ, n, p, f, hp, hp2, -, hLm⟩ | ⟨n, hn, -, -, ⟨eA⟩⟩ | ⟨hL, -⟩
    · have hLm' := Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZT) hLm
      rcases hCard with h1 | h1 | h1
      · exact (SporLie.false_of_dvd_384 hp2 hLm' (h1 ▸ hdvd)).elim
      · exact (SporLie.false_of_dvd_320 hp2 hLm' (h1 ▸ hdvd)).elim
      · have ht := SporLie.tuple_of_dvd_21504 hp2 hLm' ((h1 ▸ hdvd).trans (by norm_num))
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        exact hLm'
    · exfalso
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hcn : Nat.card (T ⧸ center T) = n.factorial / 2 := by
        rw [← hcT, card_fusionZStar_eq, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
          card_alternatingGroup, Fintype.card_fin]
      have h7 : Nat.factorial 7 / 2 ≤ n.factorial / 2 :=
        Nat.div_le_div_right (Nat.factorial_le hn)
      have h2520 : Nat.factorial 7 / 2 = 2520 := by decide
      omega
    · exfalso
      have h20160 : Nat.card (T ⧸ center T) = 20160 := by
        rw [← hcT, card_fusionZStar_eq]
        exact OddStandard.GlueL34.card_eq_of_lieModel_psl34 hL
      omega
  have h168 : Nat.card (T ⧸ center T) = 168 := card_of_lieModel_psl_two_seven hL
  obtain ⟨t, hSL, -⟩ := exists_sl2Facts hGA hGC hI.quasiT
    (isPGroup_center_of_pPrimeCore_eq_bot hI.oddCoreT) hI.centerT (p := 7) (f := 1)
    (by norm_num) (by norm_num) hL
  have hT336 : Nat.card T = 336 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [h168, hSL.card_center] at h1
    exact h1
  by_cases ht : rho Y t = 1
  ·
    have hP168 : Nat.card P = 168 := by
      have h2 : Nat.card T = 2 * Nat.card P := hSL.card_map_rho h.oddCore ht
      omega
    have hZP : center P = ⊥ := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
      rw [hP168, ← hI.card, h168] at h1
      exact Subgroup.eq_bot_of_card_eq _ (by omega)
    have hPs : IsSimpleGroup P := isSimpleGroup_of_quasisimple hI.quasiP hZP
    set P' := P.subgroupOf (fixedSubgroup σ)
    have ePP' : P ≃* P' := (subgroupOfEquivOfLe hI.proper.2.1).symm
    have : Nontrivial P' := (LocalCores.isQuasisimple_nontrivial hI.compP.1)
    have hP's : IsSimpleGroup P' := isSimpleGroup_of_mulEquiv' ePP'
    have hnab : ∃ a b : P', a * b ≠ b * a := exists_ne_of_quasisimple hI.compP.1
    have hP'card : Nat.card P' = 168 := by rw [← Nat.card_congr ePP'.toEquiv, hP168]
    have hC : Nat.card (fixedSubgroup σ) = 1344 := by
      have h7 : 168 ∣ Nat.card (fixedSubgroup σ) := hP168 ▸ hPC
      rcases hCard with h1 | h1 | h1 <;> rw [h1] at h7 <;> first | exact h1 | norm_num at h7
    have hNorm : P'.Normal := SolMax.FiveFHe.normal_of_isSubnormal_simple hI.compP.2 hnab
      (by rw [hP'card, hC]; norm_num)
    obtain ⟨g, r, hg, hr, hgr⟩ := exists_involution_commute_seven hC hP'card
    exact false_of_m22_commute hna e' (c := (g : Quot Y)) (r := (r : Quot Y))
      (by rw [Subgroup.orderOf_coe, hg]) (by rw [Subgroup.orderOf_coe, hr])
      (by rw [← Subgroup.coe_mul, hgr, Subgroup.coe_mul])
  ·
    obtain ⟨r₀, hr₀⟩ := exists_prime_orderOf_dvd_card' (G := T) 7 (by rw [hT336]; norm_num)
    have hr : orderOf (rho Y r₀) = 7 := by
      have h1 : orderOf (rho Y r₀) ∣ 7 := by
        rw [← hr₀, ← Subgroup.orderOf_coe]
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime (by norm_num)).1 h1 with h1 | h1
      · exfalso
        rw [orderOf_eq_one_iff] at h1
        have h2 := hSL.rho_injective h.oddCore ht h1
        rw [h2, orderOf_one] at hr₀
        norm_num at hr₀
      · exact h1
    exact false_of_m22_commute hna e' (hSL.orderOf_rho ht) hr (hSL.rho_commute r₀).symm

end M22

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
