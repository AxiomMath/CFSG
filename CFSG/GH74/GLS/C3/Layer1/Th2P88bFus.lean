module

public import CFSG.GH74.GLS.C3.Layer1.Th2P88bRows
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE
public import CFSG.GH74.GLS.C3.Layer1.Th2P88b
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Defs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.GH74.GLS.Th2.P88b

open Equiv Perm Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2.AltInv

theorem cycleType_two_two_of_five_dvd {m : ℕ} (hm : m = 9 ∨ m = 10 ∨ m = 11) {X : Type} [Group X]
    [Finite X] (e : X ≃* alternatingGroup (Fin m)) {a : X} (ha : orderOf a = 2)
    (h5 : 5 ∣ Nat.card ↥(centralizer ({a} : Set X))) :
    ((e a : alternatingGroup (Fin m)) : Perm (Fin m)).cycleType = {2, 2} := by
  have hm11 : m ≤ 11 := by omega
  have : NeZero m := ⟨by omega⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨hn5, -⟩ := numerics hm
  have hone : e a * e a = 1 ∧ e a ≠ 1 := by
    refine ⟨by rw [← map_mul, orderOf_two_sq ha, map_one], fun h => ?_⟩
    have : a = 1 := e.injective (by rw [h, map_one])
    rw [this, orderOf_one] at ha
    omega
  obtain ⟨ha2, ha1⟩ := hone
  have hCa : Nat.card ↥(centralizer ({a} : Set X)) = Nat.card ↥(centralizer ({e a} : Set _)) :=
    card_centralizer_equiv e a
  have hAa := card_centralizer_alt ha2 ha1
  rcases cycleType_involution hm11 ha2 ha1 with h | h
  · exact h
  · exfalso
    have hS := nat_card_centralizer_two_four h
    have : 5 ∣ (m - 8).factorial * 384 := by
      rw [← hS, ← hAa]
      exact (hCa ▸ h5).mul_right 2
    exact hn5 this

theorem involutions_conj_of_five_dvd {m : ℕ} (hm : m = 9 ∨ m = 10 ∨ m = 11) {X : Type} [Group X]
    [Finite X] (e : X ≃* alternatingGroup (Fin m)) {a b : X} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (h5a : 5 ∣ Nat.card ↥(centralizer ({a} : Set X)))
    (h5b : 5 ∣ Nat.card ↥(centralizer ({b} : Set X))) : IsConj a b := by
  have h1 := cycleType_two_two_of_five_dvd hm e ha h5a
  have h2 := cycleType_two_two_of_five_dvd hm e hb h5b
  have hm0 : NeZero m := ⟨by omega⟩
  have hone : e a * e a = 1 ∧ e a ≠ 1 := by
    refine ⟨by rw [← map_mul, orderOf_two_sq ha, map_one], fun h => ?_⟩
    have : a = 1 := e.injective (by rw [h, map_one])
    rw [this, orderOf_one] at ha
    omega
  exact (isConj_equiv_iff' e).1 (isConj_of_cycleType_eq hone.1 hone.2 (h1.trans h2.symm))

section Fusion

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_fusion {x : G} {Q M : Subgroup G} (hCx : centralizer ({x} : Set G) ≤ M)
    (hT : ∀ q ∈ Q, q ≠ 1 → ∃ m ∈ M, m * x * m⁻¹ = q) {V : Subgroup G} (hVQ : V ≤ Q)
    (hVne : V ≠ ⊥) : normalizer (V : Set G) ≤ M := by
  intro n hn
  obtain ⟨⟨q₀, hq₀V⟩, hq₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVne
  have hq₀ne : q₀ ≠ 1 := fun h => hq₀1 (Subtype.ext h)
  have hnqV : n * q₀ * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hn q₀).1 hq₀V
  have hnqne : n * q₀ * n⁻¹ ≠ 1 := by
    intro h
    apply hq₀ne
    have : q₀ = n⁻¹ * (n * q₀ * n⁻¹) * n := by group
    rw [this, h]
    group
  obtain ⟨m, hmM, hm⟩ := hT q₀ (hVQ hq₀V) hq₀ne
  obtain ⟨m', hm'M, hm'⟩ := hT _ (hVQ hnqV) hnqne
  have hc : m'⁻¹ * n * m ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : m'⁻¹ * n * m * x * (m'⁻¹ * n * m)⁻¹ = x := by
      calc m'⁻¹ * n * m * x * (m'⁻¹ * n * m)⁻¹ = m'⁻¹ * n * (m * x * m⁻¹) * n⁻¹ * m' := by group
        _ = m'⁻¹ * (n * q₀ * n⁻¹) * m' := by rw [hm]; group
        _ = m'⁻¹ * (m' * x * m'⁻¹) * m' := by rw [hm']
        _ = x := by group
    calc m'⁻¹ * n * m * x = (m'⁻¹ * n * m * x * (m'⁻¹ * n * m)⁻¹) * (m'⁻¹ * n * m) := by group
      _ = x * (m'⁻¹ * n * m) := by rw [h1]
  have hcM := hCx hc
  have : n = m' * (m'⁻¹ * n * m) * m⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hm'M hcM) (M.inv_mem hmM)

omit [Finite G] in
theorem imgM_comm' {M K : Subgroup G} {x : G} (hxM : x ∈ M) (hKx : K ≤ centralizer ({x} : Set G)) :
    ∀ w ∈ imgM M K, w * barMk ↥M (⟨x, hxM⟩ : ↥M) = barMk ↥M (⟨x, hxM⟩ : ↥M) * w := by
  intro w hw
  obtain ⟨m, hm', rfl⟩ := mem_imgM_iff.1 hw
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hKx hm'))

omit [Finite G] in
theorem five_dvd_centralizer_of_comm {n : ℕ} (hn' : n = 5 ∨ n = 6 ∨ n = 7) {M K : Subgroup G}
    {b : Mb M} (hKb : ∀ w ∈ imgM M K, w * b = b * w)
    (eK : (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin n)) :
    5 ∣ Nat.card ↥(centralizer ({b} : Set (Mb M))) := by
  have hKC : imgM M K ≤ centralizer ({b} : Set (Mb M)) := fun w hw =>
    mem_centralizer_singleton_iff.2 (hKb w hw)
  have h1 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∣ Nat.card ↥(imgM M K) :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥(imgM M K)))
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(imgM M K)))
  have h2 : Nat.card ↥(imgM M K) ∣ Nat.card ↥(centralizer ({b} : Set (Mb M))) :=
    Subgroup.card_dvd_of_le hKC
  have h3 : Nat.card (alternatingGroup (Fin n)) =
      Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := (Nat.card_congr eK.toEquiv).symm
  have h4 : 5 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rcases hn' with rfl | rfl | rfl <;>
      (rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide)
  exact h4.trans ((h3 ▸ h1).trans h2)

theorem fusion_Q_of_alt {x y : G} {K T S M L : Subgroup G}
    (hstd : Th2Std x y K T S) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K))
    (halt : Ivk73Alt (imgM M K) (imgM M L)) :
    ∀ q ∈ T ⊓ CxK x K, q ≠ 1 → ∃ m ∈ M, m * x * m⁻¹ = q := by
  intro q hq hq1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxM : x ∈ M := hQM ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hqM : q ∈ M := hQM hq
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hq2 : orderOf q = 2 := by
    refine orderOf_eq_prime ?_ hq1
    rw [sq]
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hQel).2 q hq
  obtain ⟨hLtop, n, hn, ⟨eK⟩, ⟨eL⟩⟩ := halt
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    exact hn
  have hm : n + 4 = 9 ∨ n + 4 = 10 ∨ n + 4 = 11 := by omega
  let e₀ : Mb M ≃* alternatingGroup (Fin (n + 4)) :=
    ((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans eL
  have hxb2 : orderOf (barMk ↥M (⟨x, hxM⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hqb2 : orderOf (barMk ↥M (⟨q, hqM⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk q hqM).trans hq2)
  have h5x := five_dvd_centralizer_of_comm hn' (imgM_comm' hxM hstd.K_le_C) eK
  have hqC : barMk ↥M (⟨q, hqM⟩ : ↥M) ∈ imgM M (CMbar M K) :=
    mem_imgM_iff.2 ⟨⟨q, hqM⟩, hQ.le hq, rfl⟩
  rw [imgM_cmbar_eq hKM] at hqC
  have hKq : ∀ w ∈ imgM M K,
      w * barMk ↥M (⟨q, hqM⟩ : ↥M) = barMk ↥M (⟨q, hqM⟩ : ↥M) * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 hqC w hw
  have h5q := five_dvd_centralizer_of_comm hn' hKq eK
  have hconj := involutions_conj_of_five_dvd hm e₀ hxb2 hqb2 h5x h5q
  obtain ⟨m, hm'⟩ := Th2.P85.Alt.exists_conj_of_barMk_conj (s := (⟨q, hqM⟩ : ↥M)) (u := (⟨x, hxM⟩ : ↥M))
    ((Subgroup.orderOf_mk q hqM).trans hq2) ((Subgroup.orderOf_mk x hxM).trans hx2) hconj.symm
  exact ⟨m, m.2, congrArg Subtype.val hm'⟩

theorem ivk73_alt_of_A7
    (hL34 : B_gen4_noL34_elem) (h73 : IVK.IVK_7_3_g4) {x y : G} {K T S M L : Subgroup G}
    (hstruct : P85Struct x y K T S M L) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    Ivk73Alt (imgM M K) (imgM M L) := by
  have hG := hstruct.hG
  have hchoice := hstruct.choice
  have hstd : Th2Std x y K T S := hchoice.std
  have hKM : K ≤ M := hstruct.KM
  have hQ := hstruct.hQ
  have hL := hstruct.hL
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxM : x ∈ M := hQM ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hMtop : M ≠ ⊤ := hchoice.maximal.1
  have hterm := hstruct.terminal
  have hsocle := hstruct.socle
  have hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := two_le_pRank_Q_of_struct hstruct
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := hstd.T_pGroup.to_le inf_le_left
  obtain ⟨eQ⟩ := equiv_imgM hQM hQ2
  have hU2 : InU2 (kBar K) := ⟨TwoThin.isQuasisimple_hat hstd.comp, Or.inr (Or.inl h7)⟩
  have hno34 : ¬ IsL34Quotient (kBar K) := fun hl34 =>
    hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hl34, (inU2_center hU2).1, (inU2_center hU2).2⟩
  obtain ⟨eK⟩ := kBar_equiv_imgM hKM
  have hU2' : InU2 (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := inU2_of_mulEquiv eK.symm hU2
  have hx2 : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hstd.orderOf_x
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 := orderOf_barMk hx2
  have hxbc : ∀ k ∈ imgM M K, barMk ↥M ⟨x, hxM⟩ * k = k * barMk ↥M ⟨x, hxM⟩ := fun k hk =>
    (imgM_comm' hxM hstd.K_le_C k hk).symm
  have hKcomp := hterm _ hxb2 hxbc
  have hKq : IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKcomp.1)
      hKcomp.2.1
  have hrk' : 2 ≤ pRank 2 ↥(imgM M (T ⊓ CxK x K)) := by
    rw [← Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' eQ]
    exact hrk
  have hSyl : IsSylowOf 2 (imgM M (T ⊓ CxK x K))
      (centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)) ⊓ ⊤) := by
    rw [inf_top_eq]
    exact isSylowOf_imgM_cmbar hKM hQ
  have hterm' : ∀ z ∈ (⊤ : Subgroup (Mb M)), orderOf z = 2 →
      z ∈ centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)) →
      IsCompIn (centralizer ({z} : Set (Mb M)) ⊓ ⊤) (imgM M K) := by
    intro z _ hz2 hzc
    rw [inf_top_eq]
    exact hterm z hz2 (fun k hk => (Subgroup.mem_centralizer_iff.1 hzc k hk).symm)
  have hnat : IsKGroupNative ↥(⊤ : Subgroup (Mb M)) :=
    SectionRank.IsKGroupCat.of_mulEquiv (isKGroupNative_Mb hG.kproper hMtop)
      Subgroup.topEquiv
  have hgen4 : Gen4 ↥(⊤ : Subgroup (Mb M)) :=
    Gen4.of_mulEquiv Subgroup.topEquiv.symm (Gen4.quotient _ (Gen4.subgroup M hG.gen4))
  have hGH : GHList ↥(imgM M L) :=
    IVK.ghList_of_subgroup_of_quotient hG.kgh hMtop (barMk ↥M) barMk_surjective (imgM M L)
      hsocle.simple (IVK.exists_noncomm_of_le_isQuasisimple (imgM_mono hL.1) hKq)
  obtain ⟨-, -, hcase⟩ := h73 (Mb M) ⊤ (imgM M L) (imgM M K) (imgM M (T ⊓ CxK x K)) hgen4 hGH
    hnat ⟨hsocle.le, hsocle.normal, hsocle.simple, hsocle.centralizer_trivial⟩
    (imgM_mono hL.1) hKq hU2' hSyl hrk' hterm'
  have hcardne : ∀ (X : Type) [Group X], Nonempty (X ≃* alternatingGroup (Fin 5)) →
      Nonempty (X ≃* alternatingGroup (Fin 7)) → False := by
    rintro X _ ⟨a⟩ ⟨b⟩
    have h1 := Nat.card_congr (a.symm.trans b).toEquiv
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
      card_alternatingGroup, Fintype.card_fin, Fintype.card_fin] at h1
    revert h1
    decide
  obtain ⟨b7⟩ := h7
  have hK7 : Nonempty ((↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin 7)) :=
    ⟨eK.trans b7⟩
  rcases hcase with ⟨h5, -, -⟩ | ⟨h5, -, -⟩ | ⟨hN, n, hn, hK, hL'⟩ | ⟨hl34, -⟩ | ⟨hl34, -⟩
  · exact (hcardne _ h5 hK7).elim
  · exact (hcardne _ h5 hK7).elim
  · exact ⟨hN.symm, n, hn, hK, hL'⟩
  · exact (hno34 (isL34Quotient_of_mulEquiv eK hl34)).elim
  · exact (hno34 (isL34Quotient_of_mulEquiv eK hl34)).elim

end Fusion

end CFSG.GH74.GLS.Th2.P88b

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.Th2.P88b

theorem b_thm2_p88b_of
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (h73 : IVK.IVK_7_3_g4) : B_thm2_p88b := by
  intro G _ _ x y K T S M L hstruct hnt
  by_cases h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  · have hCx := centralizer_le_M_A7 hL34 h82 hstruct hnt h7
    have halt := ivk73_alt_of_A7 hL34 h73 hstruct h7
    have hT := fusion_Q_of_alt hstruct.choice.std hstruct.KM hstruct.hQ hstruct.Qelem halt
    have hstd : Th2Std x y K T S := hstruct.choice.std
    exact Th2.P812.gammaK_le_of_forall_elem (hstd.T_pGroup.to_le inf_le_left)
      (fun V hVQ _ hVne => normalizer_le_of_fusion hCx hT hVQ hVne)
  · exact gammaK_le_M_nonA7 hL34 h82 hstruct hnt h7

end CFSG.GH74.GLS
