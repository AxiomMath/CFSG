module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotFaith
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem mcl_outer_fixSub_data
    {G : Type} [Group G] (e : G ≃* NativeSporadic.McL)
    (α : MulAut G) (hα2 : α * α = 1) (hα : α ∉ inner G) :
    ∃ E : Subgroup G, (∀ y : G, y ∈ E ↔ α y = y) ∧ IsSimpleGroup ↥E ∧
      (∃ a b : ↥E, a * b ≠ b * a) ∧ Nat.card ↥E = 7920 := by
  set θ : G ≃* mclP := e.trans mclPermEquiv
  set β : MulAut mclP := transportAut θ α
  have hβ2 : β * β = 1 := transportAut_mul_self θ hα2
  have hβ : β ∉ inner mclP := transportAut_not_mem_inner θ hα
  obtain ⟨x, hxR, hx⟩ := mcl_autModel.surj β
  have hxP : x ∉ mclP := by
    intro hxP
    apply hβ
    refine ⟨⟨x, hxP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hx p]
    rfl
  have hx2 : x * x = 1 := by
    apply mcl_autModel.inj (x * x) (mclR.mul_mem hxR hxR)
    intro p hp
    have h := congrArg (fun φ : MulAut mclP => ((φ ⟨p, hp⟩ : mclP) : Equiv.Perm (Fin 275))) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hx, hx] at h
    calc x * x * p = x * (x * p * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = p * (x * x) := by rw [h]
  have hx1 : x ≠ 1 := fun h1 => hxP (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hxo
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hxu : x = g * mclU1 * g⁻¹ := by
    rcases hr with rfl | rfl
    · exfalso
      dsimp only at hxg
      apply hxP
      rw [hxg]
      exact mclP.mul_mem (mclP.mul_mem hg mclT0_facts.1) (mclP.inv_mem hg)
    · dsimp only at hxg
      exact hxg
  have hfix := map_fixSub_conjOn mclP β x hx
  rw [hxu, centralizerIn_conj mclP hg] at hfix
  have eC : ↥(fixSub α) ≃* ↥mclC1 :=
    ((fixSubTransportEquiv θ α).trans ((((fixSub β).equivMapOfInjective mclP.subtype
      mclP.subtype_injective).trans (MulEquiv.subgroupCongr hfix)))).trans
        (conjEquiv mclC1 g).symm
  obtain ⟨hs, hnab, hcard⟩ := mclC1_simple
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨fixSub α, fun y => Iff.rfl, eC.isSimpleGroup, ⟨eC.symm a, eC.symm b, fun h' => hab ?_⟩, ?_⟩
  · have := congrArg eC h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · rw [Nat.card_congr eC.toEquiv, hcard]

end CFSG.ComponentClassification.RestrictedStd.Spor

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem isQuasisimple_of_perfect_simple_quot {E : Type} [Group E] (hP : Group.IsPerfect E)
    (hS : IsSimpleGroup (E ⧸ Subgroup.center E)) : CFSG.IsQuasisimple E := by
  refine ⟨hP, hS, ?_⟩
  by_contra hcon
  have hcomm : ∀ a b : E ⧸ Subgroup.center E, a * b = b * a :=
    fun a b => by_contra fun hne => hcon ⟨a, b, hne⟩
  have hle : (⊤ : Subgroup E) ≤ Subgroup.center E := by
    have hperf : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ := by
      have := hP.commutator_eq_top
      rwa [_root_.commutator_def] at this
    rw [← hperf, Subgroup.commutator_le]
    intro x _ y _
    show ⁅x, y⁆ ∈ Subgroup.center E
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (x : E ⧸ Subgroup.center E) y]
    group
  have hsub : Subsingleton (E ⧸ Subgroup.center E) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.eq]
    exact hle (Subgroup.mem_top _)
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hS.toNontrivial


theorem mcl_inner_data
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .McL) {t : Y} (ht : orderOf t = 2) :
    CFSG.IsQuasisimple ↥(centralizer ({t} : Set Y)) ∧
      Nat.card ↥(Subgroup.center ↥(centralizer ({t} : Set Y))) = 2 ∧
      Nat.card ↥(centralizer ({t} : Set Y)) = 40320 := by
  obtain ⟨hperf, hcen, ⟨q⟩⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate hY ht
  have hA : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 8))
  let q' : ↥(centralizer ({t} : Set Y)) ⧸ Subgroup.center ↥(centralizer ({t} : Set Y)) ≃*
      alternatingGroup (Fin 8) := (QuotientGroup.quotientMulEquivOfEq hcen).trans q
  have hS : IsSimpleGroup (↥(centralizer ({t} : Set Y)) ⧸ Subgroup.center ↥(centralizer ({t} : Set Y))) :=
    q'.isSimpleGroup
  have hZ : Nat.card ↥(Subgroup.center ↥(centralizer ({t} : Set Y))) = 2 := by
    rw [hcen, Nat.card_zpowers, Subgroup.orderOf_mk, ht]
  have hAc : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  refine ⟨isQuasisimple_of_perfect_simple_quot hperf hS, hZ, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(centralizer ({t} : Set Y)))
  rw [hZ, Nat.card_congr q'.toEquiv, hAc] at h1
  rw [h1]

@[expose] def McLOuterCC (Y : Type) [Group Y] : Prop :=
  ∀ α : MulAut Y, α * α = 1 → α ∉ MulAut.conj.range →
    ∀ x : Y, Odd (orderOf x) → (∀ e : Y, α e = e → e * x = x * e) → x = 1

theorem noQuotCfg_McL
    {Y : Type} [Group Y] [Finite Y] (hY : NativeSporadic.IsSporadic Y .McL)
    (hCC : McLOuterCC Y) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y} (h : QuotCfg p α Xh) : False := by
  classical
  have hY' := hY
  obtain ⟨e⟩ := hY'
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card Y = 898128000 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.McL.card_McL
  have hpdvd : p ∣ 898128000 := hcard ▸ h.dvd_card
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    have h1 : p ∈ Nat.primeFactorsList 898128000 :=
      (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hp, hpdvd⟩
    have e1 : Nat.primeFactorsList 898128000 =
        [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 11] := by
      norm_num
    rw [e1] at h1
    have h2 := h.odd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    omega
  have hα2 : α * α = 1 := MulEquiv.ext fun s => h.invol s
  by_cases hin : α ∈ MulAut.conj.range
  ·
    obtain ⟨t, hαt⟩ := hin
    obtain ⟨hto, ht2, hfix, htα⟩ := h.of_inner hαt.symm
    obtain ⟨hquasi, hZc, hCcard⟩ := mcl_inner_data hY hto
    have htC : t ∈ centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hEα : ∀ y ∈ centralizer ({t} : Set Y), α y = y := fun y hy => (hfix y).2 hy
    rcases hp' with rfl | rfl | rfl | rfl
    ·
      refine h.false_of_quasisimple_row (E := centralizer ({t} : Set Y)) hquasi hEα htC htα
        (q := 7) (by norm_num) (by norm_num) (by rw [hCcard]; norm_num)
        (by rw [hZc]; norm_num) hcard hCcard ?_
      intro r k hdiv hk1 hkr
      have hr : r ≤ 4 := by
        by_contra hr
        have h1 : 3 ^ 5 * 40320 ∣ 3 ^ r * 40320 :=
          Nat.mul_dvd_mul_right (pow_dvd_pow 3 (by omega)) _
        have := h1.trans hdiv
        norm_num at this
      have hk4 : k ≤ 4 := by omega
      interval_cases k <;> norm_num
    ·
      refine h.false_of_quasisimple_row (E := centralizer ({t} : Set Y)) hquasi hEα htC htα
        (q := 7) (by norm_num) (by norm_num) (by rw [hCcard]; norm_num)
        (by rw [hZc]; norm_num) hcard hCcard ?_
      intro r k hdiv hk1 hkr
      have hr : r ≤ 2 := by
        by_contra hr
        have h1 : 5 ^ 3 * 40320 ∣ 5 ^ r * 40320 :=
          Nat.mul_dvd_mul_right (pow_dvd_pow 5 (by omega)) _
        have := h1.trans hdiv
        norm_num at this
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> norm_num
    ·
      have hsyl : ∀ Q : Subgroup Y, IsPGroup 7 ↥Q → Nat.card ↥Q ≤ 7 := by
        apply sylow_card_le_of_not_sq_dvd hp
        rw [hcard]; norm_num
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hCcard]; norm_num)
      exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), hEα _ s.2, by
        rw [Subgroup.orderOf_coe]; exact hs⟩)
    ·
      have hsyl : ∀ Q : Subgroup Y, IsPGroup 11 ↥Q → Nat.card ↥Q ≤ 11 := by
        apply sylow_card_le_of_not_sq_dvd hp
        rw [hcard]; norm_num
      have htclos : t ∈ Subgroup.closure {y : Y | α y = y ∧ Odd (orderOf y)} :=
        fixSub_le_closure_odd_of_perfect_aux _ α hEα
          (perfect_le_closure_odd _ hquasi.1 htC)
      refine h.false_of_sylow_row hsyl (Or.inr ⟨t, ht2, ?_, htclos, ?_⟩)
      · intro ht1; rw [ht1, orderOf_one] at hto; omega
      · rw [hCcard]; norm_num
  ·
    obtain ⟨E, hEmem, hEs, hEnab, hEcard⟩ :=
      CFSG.ComponentClassification.RestrictedStd.Spor.mcl_outer_fixSub_data e α hα2 hin
    have hEα : ∀ y ∈ E, α y = y := fun y hy => (hEmem y).1 hy
    have hnc : ∃ y ∈ E, ∃ x ∈ Xh, y * x * y⁻¹ ≠ x := by
      by_contra hall
      have hall' : ∀ y ∈ E, ∀ x ∈ Xh, y * x * y⁻¹ = x := fun y hy x hx =>
        by_contra fun hne => hall ⟨y, hy, x, hx, hne⟩
      apply h.ne_bot
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxodd : Odd (orderOf x) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.pgroup) ⟨x, hx⟩
        rw [Subgroup.orderOf_mk] at hk
        rw [hk]
        exact (hp.odd_of_ne_two h.odd).pow
      refine hCC α hα2 hin x hxodd (fun y hy => ?_)
      have := hall' y ((hEmem y).2 hy) x hx
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [this]
    rcases hp' with rfl | rfl | rfl | rfl
    · refine h.false_of_simple_row hEs hEnab hEα hnc (q := 11) (by norm_num) (by norm_num)
        (by rw [hEcard]; norm_num) hcard hEcard ?_
      intro r k hdiv hk1 hkr
      have hr : r ≤ 4 := by
        by_contra hr
        have h1 : 3 ^ 5 * 7920 ∣ 3 ^ r * 7920 :=
          Nat.mul_dvd_mul_right (pow_dvd_pow 3 (by omega)) _
        have := h1.trans hdiv
        norm_num at this
      have hk4 : k ≤ 4 := by omega
      interval_cases k <;> norm_num
    · refine h.false_of_simple_row hEs hEnab hEα hnc (q := 11) (by norm_num) (by norm_num)
        (by rw [hEcard]; norm_num) hcard hEcard ?_
      intro r k hdiv hk1 hkr
      have hr : r ≤ 2 := by
        by_contra hr
        have h1 : 5 ^ 3 * 7920 ∣ 5 ^ r * 7920 :=
          Nat.mul_dvd_mul_right (pow_dvd_pow 5 (by omega)) _
        have := h1.trans hdiv
        norm_num at this
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> norm_num
    · refine h.false_of_simple_row hEs hEnab hEα hnc (q := 11) (by norm_num) (by norm_num)
        (by rw [hEcard]; norm_num) hcard hEcard ?_
      intro r k hdiv hk1 hkr
      have hr : r ≤ 1 := by
        by_contra hr
        have h1 : 7 ^ 2 * 7920 ∣ 7 ^ r * 7920 :=
          Nat.mul_dvd_mul_right (pow_dvd_pow 7 (by omega)) _
        have := h1.trans hdiv
        norm_num at this
      have hk1' : k ≤ 1 := by omega
      have hk : k = 1 := by omega
      subst hk
      norm_num
    ·
      have hsyl : ∀ Q : Subgroup Y, IsPGroup 11 ↥Q → Nat.card ↥Q ≤ 11 := by
        apply sylow_card_le_of_not_sq_dvd hp
        rw [hcard]; norm_num
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 11 (by rw [hEcard]; norm_num)
      exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), hEα _ s.2, by
        rw [Subgroup.orderOf_coe]; exact hs⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
