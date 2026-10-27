module

import CFSG.ClassicalInvolution.Balance.CentralizedDeltaBasic
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyGen

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.CentralizedDeltaTools
  (oddCoreIn_le_normalizer_of_perfect_of_isSubnormal
    commutator_mem_oddCoreIn_of_perfect_of_isSubnormal)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf perfectResidualOf_normalizer_contains
  finite_perfectResidualOf_isPerfect)
open scoped commutatorElement

section Abstract

variable {Y : Type*} [Group Y]

theorem le_of_commute_of_le_sup {Q Q' W : Subgroup Y} (hWQ : Q ≤ Subgroup.normalizer (W : Set Y))
    (hQ' : Group.IsPerfect ↥Q') (hle : Q' ≤ W ⊔ Q) (hcomm : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x) :
    Q' ≤ W := by
  have hN : W ⊔ Q ≤ Subgroup.normalizer (W : Set Y) := sup_le Subgroup.le_normalizer hWQ
  have hcomm' : ⁅Q', Q'⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ (↑(W ⊔ Q) : Set Y) := hle hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W Q hWQ] at hx'
    obtain ⟨w, hw, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have hyN : y ∈ Subgroup.normalizer (W : Set Y) := hN (hle hy)
    have hqy : q * y = y * q := hcomm q hq y hy
    have e : ⁅w * q, y⁆ = w * (y * w⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      calc w * q * y * (w * q)⁻¹ * y⁻¹ = w * (q * y) * q⁻¹ * w⁻¹ * y⁻¹ := by group
        _ = w * (y * q) * q⁻¹ * w⁻¹ * y⁻¹ := by rw [hqy]
        _ = w * (y * w⁻¹ * y⁻¹) := by group
    rw [e]
    exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp hyN w⁻¹).mp (W.inv_mem hw))
  have hself : ⁅Q', Q'⁆ = Q' := by
    have := hQ'
    exact Subgroup.commutator_eq_self
  exact hself ▸ hcomm'

theorem centralizes_of_commutator_mem_center {Q : Subgroup Y} (hQ : commutator ↥Q = ⊤) {s : Y}
    (hsq : ∀ q ∈ Q, ⁅s, q⁆ ∈ Q) (hz : ∀ q ∈ Q, ∀ r ∈ Q, r * ⁅s, q⁆ = ⁅s, q⁆ * r) :
    ∀ q ∈ Q, s * q = q * s := by
  let φ : ↥Q →* ↥(Subgroup.center ↥Q) :=
    { toFun := fun q => ⟨⟨⁅s, (q : Y)⁆, hsq q q.2⟩, Subgroup.mem_center_iff.mpr fun r =>
        Subtype.ext (hz q q.2 r r.2)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show ⁅s, (a : Y) * (b : Y)⁆ = ⁅s, (a : Y)⁆ * ⁅s, (b : Y)⁆
        have hb := hz b b.2 a a.2
        calc ⁅s, (a : Y) * (b : Y)⁆ = ⁅s, (a : Y)⁆ * ((a : Y) * ⁅s, (b : Y)⁆ * (a : Y)⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅s, (a : Y)⁆ * ⁅s, (b : Y)⁆ := by rw [hb]; group }
  have hker : commutator ↥Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro q hq
  have hmem : (⟨q, hq⟩ : ↥Q) ∈ φ.ker := hker (by rw [hQ]; exact Subgroup.mem_top _)
  have h1 : ⁅s, q⁆ = 1 :=
    congrArg (fun x => ((x : ↥(Subgroup.center ↥Q)) : ↥Q).1) (MonoidHom.mem_ker.mp hmem)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem centralizes_of_isComponent_of_commutator_mem [Finite Y] {Q : Subgroup Y}
    (hQ : CFSG.Open.IsComponentOf Q ⊤) {W : Subgroup Y} (hW : Odd (Nat.card W))
    (hWQ : Q ≤ Subgroup.normalizer (W : Set Y)) {s : Y} (hs : ∀ q ∈ Q, ⁅s, q⁆ ∈ W) :
    ∀ q ∈ Q, s * q = q * s := by
  have hQq : CFSG.Open.IsQuasisimple ↥Q := hQ.2.2
  set Q' : Subgroup Y := Q.map (MulAut.conj s).toMonoidHom with hQ'
  let ε : ↥Q ≃* ↥Q' :=
    Subgroup.equivMapOfInjective Q (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  have hQ'q : CFSG.Open.IsQuasisimple ↥Q' := Components.quasisimple_of_equiv ε.symm hQq
  have hQ'sub : IsSubnormal Q' ⊤ := by
    have h1 := isSubnormal_map_conj hQ.2.1 s
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj s).surjective] at h1
  have hQ'c : CFSG.Open.IsComponentOf Q' ⊤ := ⟨le_top, hQ'sub, hQ'q⟩
  have hmemQ' : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q' := fun q hq => ⟨q, hq, rfl⟩
  have hle : Q' ≤ W ⊔ Q := by
    rintro _ ⟨q, hq, rfl⟩
    have e : (MulAut.conj s).toMonoidHom q = ⁅s, q⁆ * q := by
      show s * q * s⁻¹ = ⁅s, q⁆ * q
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem_sup (hs q hq) hq
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute
    ((AssemblyBPredicates.isComponentOf_iff_open Q ⊤).mpr hQ)
    ((AssemblyBPredicates.isComponentOf_iff_open Q' ⊤).mpr hQ'c) with h | h
  · have hnorm : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := fun q hq => h ▸ hmemQ' q hq
    have hcm : ∀ q ∈ Q, ⁅s, q⁆ ∈ Q := fun q hq => by
      have : ⁅s, q⁆ = (s * q * s⁻¹) * q⁻¹ := rfl
      rw [this]
      exact Q.mul_mem (hnorm q hq) (Q.inv_mem hq)
    have hN : ((Q ⊓ W).subgroupOf Q).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hkW := Subgroup.mem_normalizer_iff.mp (hWQ hk) y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hyQ, hyW⟩
        exact ⟨Q.mul_mem (Q.mul_mem hk hyQ) (Q.inv_mem hk), hkW.mp hyW⟩
      · rintro ⟨hyQ, hyW⟩
        refine ⟨?_, hkW.mpr hyW⟩
        have e : y = k⁻¹ * (k * y * k⁻¹) * k := by group
        rw [e]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem hk) hyQ) hk
    have hNodd : Odd (Nat.card ((Q ⊓ W).subgroupOf Q)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ W ≤ Q)).toEquiv]
      exact hW.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hNZ : (Q ⊓ W).subgroupOf Q ≤ Subgroup.center ↥Q :=
      (OddCore.maximal ↥Q _ hN hNodd).trans (oddCore_le_center_of_isQuasisimple hQq)
    refine centralizes_of_commutator_mem_center hQq.1 hcm fun q hq r hr => ?_
    have hmem : (⟨⁅s, q⁆, hcm q hq⟩ : ↥Q) ∈ (Q ⊓ W).subgroupOf Q :=
      Subgroup.mem_subgroupOf.mpr ⟨hcm q hq, hs q hq⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hNZ hmem) ⟨r, hr⟩)
  · exfalso
    have hcomm : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x := by
      intro x hx y hy
      have h1 : ⁅x, y⁆ ∈ ⁅Q, Q'⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hQ'perf : Group.IsPerfect ↥Q' := ⟨hQ'q.1⟩
    have hQ'W := le_of_commute_of_le_sup hWQ hQ'perf hle hcomm
    have hodd : Odd (Nat.card ↥Q') := hW.of_dvd_nat (Subgroup.card_dvd_of_le hQ'W)
    have hoddQ : Odd (Nat.card ↥Q) := by rwa [← Nat.card_congr ε.toEquiv] at hodd
    have hsolv : Group.IsSolvable ↥Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddQ
    have hnt : Nontrivial ↥Q := Quasisimple.nontrivial hQq
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Q
    rw [hQq.1] at hlt
    exact lt_irrefl _ hlt

end Abstract

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSectionMember_self_of_isClassicalMember {J : Subgroup G} {v : G}
    (h : IsClassicalMember p f J v) :
    IsSectionMember p f (Subgroup.centralizer ({v} : Set G)) J v where
  le := isSubnormal_le h.subnormal
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  perfect := h.perfect
  subnormal := by rw [inf_idem]; exact h.subnormal
  nonempty_equiv := h.nonempty_equiv

theorem isComponentOf_modOdd {J : Subgroup G} {v : G} (hJ : IsClassicalMember p f J v)
    (hq : 5 ≤ p ^ f) : CFSG.Open.IsComponentOf (modOdd v J) ⊤ := by
  have hmem : IsInvolutionMember (modOdd v J) :=
    isInvolutionMember_modOdd_of_isSectionMember (isSectionMember_self_of_isClassicalMember hJ) hq
  have hsub : IsSubnormal (modOdd v J) ⊤ := by
    have h := isSubnormal_subgroupOf hJ.subnormal (Subgroup.centralizer ({v} : Set G))
    rw [Subgroup.subgroupOf_self] at h
    have hsurj : Function.Surjective (oddQuotMk v) := QuotientGroup.mk'_surjective _
    have h2 := Components.chain_map (oddQuotMk v) h
    rw [Subgroup.map_top_of_surjective _ hsurj] at h2
    exact h2
  have hO : componentClassificationOddCore ↥(modOdd v J) = ⊥ := by
    have hK : (oddCoreIn (modOdd v J)).IsSubnormal := by
      have h1 : IsSubnormal (oddCoreIn (modOdd v J)) ⊤ :=
        isSubnormal_trans (isSubnormal_oddCoreIn _) hsub
      exact (AssemblyBPredicates.isSubnormal_top_iff_mathlib _).mp
        ((AssemblyBPredicates.isSubnormal_iff_open _ _).mpr h1)
    have h2 := CFSG.Walter.eq_bot_of_isSubnormal_of_odd (pPrimeCore_oddQuot_eq_bot v) hK
      (odd_card_oddCoreIn _)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h2
  have hqs : CFSG.Open.IsQuasisimple ↥(modOdd v J) := by
    have e : (↥(modOdd v J) ⧸ componentClassificationOddCore ↥(modOdd v J)) ≃* ↥(modOdd v J) :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact Components.quasisimple_of_equiv e.symm hmem.quasisimple
  exact ⟨le_top, hsub, hqs⟩

theorem centralizes_modOdd_of_commutator_mem {J I W : Subgroup G} {v s : G}
    (hJ : IsClassicalMember p f J v) (hq : 5 ≤ p ^ f)
    (hcov : ∀ x ∈ J, ∃ i ∈ I, ∃ n ∈ oddCoreIn J, x = i * n)
    (hsC : s ∈ Subgroup.centralizer ({v} : Set G)) (hW : Odd (Nat.card W))
    (hIW : I ≤ Subgroup.normalizer (W : Set G)) (hIJ : I ≤ J) (hs : ∀ i ∈ I, ⁅s, i⁆ ∈ W) :
    ∀ y ∈ modOdd v J, oddQuotMk v ⟨s, hsC⟩ * y = y * oddQuotMk v ⟨s, hsC⟩ := by
  set C : Subgroup G := Subgroup.centralizer ({v} : Set G) with hC
  have hJC : J ≤ C := isSubnormal_le hJ.subnormal
  have hIC : I ≤ C := hIJ.trans hJC
  have hOJ : oddCoreIn J ≤ oddCoreIn C := oddCoreIn_le_of_isSubnormal hJ.subnormal
  have hQI : ∀ q ∈ modOdd v J, ∃ i ∈ I, ∃ hiC : i ∈ C, q = oddQuotMk v ⟨i, hiC⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨i, hi, n, hn, hkin⟩ := hcov (k : G) hk
    have hiC : i ∈ C := hIC hi
    have hnC : n ∈ C := oddCoreIn_le C (hOJ hn)
    refine ⟨i, hi, hiC, ?_⟩
    have e : k = ⟨i, hiC⟩ * ⟨n, hnC⟩ := Subtype.ext hkin
    rw [e, map_mul, oddQuotMk_eq_one_of_mem_oddCoreIn (hOJ hn) hnC, mul_one]
  set Wt : Subgroup (OddQuot v) := ((W ⊓ C).subgroupOf C).map (oddQuotMk v) with hWt
  have hWtodd : Odd (Nat.card Wt) := by
    have h1 : Nat.card ((W ⊓ C).subgroupOf C) = Nat.card (W ⊓ C : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : W ⊓ C ≤ C)).toEquiv
    have h2 : Odd (Nat.card ((W ⊓ C).subgroupOf C)) :=
      h1 ▸ hW.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    exact h2.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hnormW : ∀ (i : G) (hi : i ∈ I) (hiC : i ∈ C) (w : ↥C),
      w ∈ (W ⊓ C).subgroupOf C →
        (⟨i, hiC⟩ : ↥C) * w * (⟨i, hiC⟩ : ↥C)⁻¹ ∈ (W ⊓ C).subgroupOf C := by
    intro i hi hiC w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨hwW, hwC⟩ := hw
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hIW hi) (w : G)).mp hwW, ?_⟩
    exact C.mul_mem (C.mul_mem hiC hwC) (C.inv_mem hiC)
  have hQW : modOdd v J ≤ Subgroup.normalizer (Wt : Set (OddQuot v)) := by
    intro q hq
    obtain ⟨i, hi, hiC, rfl⟩ := hQI q hq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨i, hiC⟩ * w * ⟨i, hiC⟩⁻¹, hnormW i hi hiC w hw, by simp [map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwy⟩
      have hi' : i⁻¹ ∈ I := I.inv_mem hi
      have hiC' : i⁻¹ ∈ C := C.inv_mem hiC
      have hw' := hnormW i⁻¹ hi' hiC' w hw
      refine ⟨⟨i⁻¹, hiC'⟩ * w * ⟨i⁻¹, hiC'⟩⁻¹, hw', ?_⟩
      have e1 : oddQuotMk v ⟨i, hiC⟩ * y * (oddQuotMk v ⟨i, hiC⟩)⁻¹ = oddQuotMk v w := hwy.symm
      have e2 : (⟨i⁻¹, hiC'⟩ : ↥C) = (⟨i, hiC⟩ : ↥C)⁻¹ := rfl
      rw [map_mul, map_mul, map_inv, e2, map_inv, ← e1]
      group
  have hsWt : ∀ q ∈ modOdd v J, ⁅oddQuotMk v ⟨s, hsC⟩, q⁆ ∈ Wt := by
    intro q hq
    obtain ⟨i, hi, hiC, rfl⟩ := hQI q hq
    rw [← map_commutatorElement]
    refine ⟨⁅(⟨s, hsC⟩ : ↥C), ⟨i, hiC⟩⁆, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hs i hi, C.mul_mem (C.mul_mem (C.mul_mem hsC hiC) (C.inv_mem hsC)) (C.inv_mem hiC)⟩
  exact centralizes_of_isComponent_of_commutator_mem (isComponentOf_modOdd hJ hq) hWtodd hQW hsWt

theorem mem_trivialOnQuot_of_centralizes_modOdd {J : Subgroup G} {v s : G}
    (hJ : IsClassicalMember p f J v) (hcan : perfectResidualOf (J ⊔ involutionOddCore v) = J)
    (hsC : s ∈ Subgroup.centralizer ({v} : Set G))
    (hcent : ∀ y ∈ modOdd v J, oddQuotMk v ⟨s, hsC⟩ * y = y * oddQuotMk v ⟨s, hsC⟩) :
    s ∈ trivialOnQuot J := by
  rw [involutionOddCore_eq_oddCoreIn] at hcan
  set C : Subgroup G := Subgroup.centralizer ({v} : Set G) with hC
  set N : Subgroup G := oddCoreIn C with hN
  have hJC : J ≤ C := isSubnormal_le hJ.subnormal
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := hJC.trans (normalizer_oddCoreIn C)
  have hcomm : ∀ j ∈ J, ⁅s, j⁆ ∈ N := fun j hj =>
    (mk_comm_eq_iff (Y := C) hsC (hJC hj)).mp (hcent _ ⟨⟨j, hJC hj⟩, hj, rfl⟩)
  have hconj : ∀ g : G, g ∈ C → (∀ j ∈ J, ⁅g, j⁆ ∈ N) → ∀ x ∈ J ⊔ N, g * x * g⁻¹ ∈ J ⊔ N := by
    intro g hgC hg x hx
    have hx' : x ∈ (↑(J ⊔ N) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J N hJN] at hx'
    obtain ⟨j, hj, n, hn, rfl⟩ := Set.mem_mul.mp hx'
    have e : g * (j * n) * g⁻¹ = (⁅g, j⁆ * j) * (g * n * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (J ⊔ N).mul_mem ((J ⊔ N).mul_mem (Subgroup.mem_sup_right (hg j hj))
      (Subgroup.mem_sup_left hj)) (Subgroup.mem_sup_right (conj_mem_oddCoreIn hgC hn))
  have hsinv : ∀ j ∈ J, ⁅s⁻¹, j⁆ ∈ N := by
    intro j hj
    have e : ⁅s⁻¹, j⁆ = s⁻¹ * ⁅s, j⁆⁻¹ * s⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_oddCoreIn (C.inv_mem hsC) (N.inv_mem (hcomm j hj))
  have hnormJN : s ∈ Subgroup.normalizer ((J ⊔ N : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj s hsC hcomm x, fun hx => ?_⟩
    have := hconj s⁻¹ (C.inv_mem hsC) hsinv _ hx
    simpa [mul_assoc] using this
  have hnormJ : s ∈ Subgroup.normalizer (J : Set G) := by
    have := perfectResidualOf_normalizer_contains (J ⊔ N) hnormJN
    rwa [hcan] at this
  have hS : J ⊓ N ≤ oddCoreIn J := by
    refine le_oddCoreIn_of_normalizes inf_le_left ?_
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    intro y hy
    exact mem_normalizer_inf (Subgroup.le_normalizer hy) (hJN hy)
  refine ⟨hnormJ, fun x hx => hS ⟨?_, hcomm x hx⟩⟩
  have : ⁅s, x⁆ = (s * x * s⁻¹) * x⁻¹ := rfl
  rw [this]
  exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp hnormJ x).mp hx) (J.inv_mem hx)

omit [Finite G] in
theorem isPerfect_conjSub {P : Subgroup G} (hP : Group.IsPerfect ↥P) (g : G) :
    Group.IsPerfect ↥(conjSub g P) := by
  let ε : ↥P ≃* ↥(conjSub g P) :=
    Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact Group.IsPerfect.ofSurjective (f := ε.toMonoidHom) ε.surjective

theorem perfectResidualOf_conjSub (g : G) (H : Subgroup G) :
    perfectResidualOf (conjSub g H) = conjSub g (perfectResidualOf H) := by
  have key : ∀ (g : G) (H : Subgroup G),
      conjSub g (perfectResidualOf H) ≤ perfectResidualOf (conjSub g H) := fun g H =>
    le_perfectResidualOf_of_perfect (conjSub_mono (Subgroup.map_subtype_le _))
      (isPerfect_conjSub (finite_perfectResidualOf_isPerfect H) g)
  refine le_antisymm ?_ (key g H)
  have h2 := conjSub_mono (n := g) (key g⁻¹ (conjSub g H))
  rw [conjSub_conjSub_inv, conjSub_inv_conjSub] at h2
  exact h2

theorem trivialOnQuot_conjSub {J : Subgroup G} {s : G} (h : s ∈ trivialOnQuot J) (g : G) :
    g * s * g⁻¹ ∈ trivialOnQuot (conjSub g J) := by
  obtain ⟨hn, hc⟩ := h
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have e : g⁻¹ * (g * s * g⁻¹ * y * (g * s * g⁻¹)⁻¹) * g = s * (g⁻¹ * y * g) * s⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hn (g⁻¹ * y * g)
  · have hx' : g⁻¹ * x * g ∈ J := mem_conjSub_iff.mp hx
    have e : ⁅g * s * g⁻¹, x⁆ = g * ⁅s, g⁻¹ * x * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, oddCoreIn_conjSub_eq]
    exact conj_mem_conjSub (hc _ hx')

@[expose] def IsCanonical (J : Subgroup G) (v : G) : Prop :=
  perfectResidualOf (J ⊔ involutionOddCore v) = J

theorem IsCanonical.conj {J : Subgroup G} {v : G} (h : IsCanonical J v) (g : G) :
    IsCanonical (conjSub g J) (g * v * g⁻¹) := by
  unfold IsCanonical at h ⊢
  have e : conjSub g J ⊔ conjSub g (involutionOddCore v) = conjSub g (J ⊔ involutionOddCore v) :=
    (Subgroup.map_sup _ _ _).symm
  rw [involutionOddCore_conj, e, perfectResidualOf_conjSub, h]

theorem commute_of_mem_trivialOnQuot {J : Subgroup G} {x y : G} (hxJ : x ∈ trivialOnQuot J)
    (hx2 : x * x = 1) (hyJ : y ∈ J) (hy2 : y * y = 1) (hyc : ∀ k ∈ J, k * y = y * k) :
    x * y = y * x := by
  have hc : ⁅x, y⁆ ∈ oddCoreIn J := hxJ.2 y hyJ
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have ht' : x * y * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hxJ.1 y).mp hyJ
  have hcomm : (x * y * x⁻¹) * y = y * (x * y * x⁻¹) := hyc _ ht'
  have ht'2 : (x * y * x⁻¹) * (x * y * x⁻¹) = 1 := by
    calc (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y := by
      simp only [commutatorElement_def, hyi]
    rw [e]
    calc (x * y * x⁻¹) * y * ((x * y * x⁻¹) * y)
        = (x * y * x⁻¹) * (y * (x * y * x⁻¹)) * y := by group
      _ = (x * y * x⁻¹) * ((x * y * x⁻¹) * y) * y := by rw [← hcomm]
      _ = ((x * y * x⁻¹) * (x * y * x⁻¹)) * (y * y) := by group
      _ = 1 := by rw [ht'2, hy2, mul_one]
  have hodd : Odd (orderOf ⁅x, y⁆) :=
    (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn J) hc)
  have hdvd : orderOf ⁅x, y⁆ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hord : orderOf ⁅x, y⁆ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd hodd (by rw [h]; decide)
  exact (commutatorElement_eq_one_iff_mul_comm).mp (orderOf_eq_one_iff.mp hord)

theorem axisResidual_single {J : Subgroup G} {z a : G} (hJ : IsClassicalMember p f J z)
    (ha2 : a * a = 1) (haJ : a ∈ trivialOnQuot J) :
    AxisResidual J (Subgroup.zpowers a) (triangleResidual J a) z := by
  have c := isCentralInvolution_of_isClassicalMember hJ
  have h := axisResidual_perfectResidual hJ.perfect hJ.mem c.sq (fun x hx => (c.central x hx).symm)
    hJ.subnormal (isPGroup_zpowers_of_mul_self_eq_one ha2) (Subgroup.zpowers_le.mpr haJ)
  simpa only [triangleResidual, centralizer_zpowers_eq_singleton'] using h

theorem oddCoreIn_le_trivialOnQuot {K X : Subgroup G} (hKX : IsSubnormal K X)
    (hK : Group.IsPerfect ↥K) : oddCoreIn X ≤ trivialOnQuot K := by
  intro o ho
  refine ⟨oddCoreIn_le_normalizer_of_perfect_of_isSubnormal hKX hK.commutator_eq_top ho,
    fun k hk => ?_⟩
  have h := commutator_mem_oddCoreIn_of_perfect_of_isSubnormal hKX hK.commutator_eq_top hk ho
  have e : ⁅o, k⁆ = (k * o * k⁻¹ * o⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreIn K).inv_mem h

theorem triangleResidual_conjSub (J : Subgroup G) {a x : G}
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) :
    triangleResidual (conjSub x J) a = conjSub x (triangleResidual J a) := by
  unfold triangleResidual
  have h1 : conjSub x (Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({a} : Set G) :=
    conjSub_eq_self_of_mem hx
  have h2 : conjSub x (J ⊓ Subgroup.centralizer ({a} : Set G)) =
      conjSub x J ⊓ conjSub x (Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.map_inf_eq _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  rw [h1] at h2
  rw [← h2, perfectResidualOf_conjSub]

omit [Finite G] in
theorem commutator_conj_mem_oddCoreIn {a x y z : G}
    (hx : x ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)))
    (hyC : y ∈ Subgroup.centralizer ({a} : Set G)) (hzC : z ∈ Subgroup.centralizer ({a} : Set G))
    (h : ⁅y, z⁆ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G))) :
    ⁅x * y * x⁻¹, z⁆ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx
  have hx1 : oddQuotMk a ⟨x, hxC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hx hxC
  have hxyC : x * y * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem hxC hyC) (inv_mem hxC)
  refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hxyC hzC).mp ?_
  have h1 : oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a ⟨z, hzC⟩ =
      oddQuotMk a ⟨z, hzC⟩ * oddQuotMk a ⟨y, hyC⟩ :=
    (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hyC hzC).mpr h
  have e : (⟨x * y * x⁻¹, hxyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
      ⟨x, hxC⟩ * ⟨y, hyC⟩ * ⟨x, hxC⟩⁻¹ := rfl
  show oddQuotMk a ⟨x * y * x⁻¹, hxyC⟩ * oddQuotMk a ⟨z, hzC⟩ =
    oddQuotMk a ⟨z, hzC⟩ * oddQuotMk a ⟨x * y * x⁻¹, hxyC⟩
  rw [e, map_mul, map_mul, map_inv, hx1]
  simp only [one_mul, inv_one, mul_one]
  exact h1

theorem exists_axisTriangle_of_residuals_commute {M J N : Subgroup G} {a t u : G}
    (hM : IsClassicalMember p f M a) (hJ : IsClassicalMember p f J t)
    (hN : IsClassicalMember p f N u) (hq : 5 ≤ p ^ f) (hJcan : IsCanonical J t)
    (hNcan : IsCanonical N u) (htM : t ∈ trivialOnQuot M) (huM : u ∈ trivialOnQuot M)
    (haJ : a ∈ trivialOnQuot J) (haN : a ∈ trivialOnQuot N)
    (hJN : ∀ i ∈ triangleResidual J a, ∀ j ∈ triangleResidual N a,
      ⁅i, j⁆ ∈ involutionOddCore a) :
    ∃ x ∈ involutionOddCore a, AxisTriangle p f M J (conjSub x N) a t (x * u * x⁻¹) := by
  have cM := isCentralInvolution_of_isClassicalMember hM
  have cJ := isCentralInvolution_of_isClassicalMember hJ
  have cN := isCentralInvolution_of_isClassicalMember hN
  have ha2 := cM.sq
  have ht2 := cJ.sq
  have hu2 := cN.sq
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have rJ := axisResidual_single hJ ha2 haJ
  have rN := axisResidual_single hN ha2 haN
  have hIC : ∀ {K I : Subgroup G} {z : G}, AxisResidual K (Subgroup.zpowers a) I z → I ≤ C := by
    intro K I z r y hy
    have := (r.le_inf hy).2
    rwa [centralizer_zpowers_eq_singleton'] at this
  have hIJC : triangleResidual J a ≤ C := hIC rJ
  have hINC : triangleResidual N a ≤ C := hIC rN
  have htC : t ∈ C := hIJC rJ.mem
  have huC : u ∈ C := hINC rN.mem
  have hnadj : NAdj a (triangleResidual J a) (triangleResidual N a) := fun i hi j hj => by
    rw [← involutionOddCore_eq_oddCoreIn]
    exact hJN i hi j hj
  obtain ⟨x, hx, hxc⟩ := exists_conj_commute_of_nadj hnadj hIJC hINC rJ.mem rN.mem ht2 hu2
  have hx' : x ∈ involutionOddCore a := by rwa [involutionOddCore_eq_oddCoreIn]
  have hxC : x ∈ C := oddCoreIn_le _ hx
  have hN' : IsClassicalMember p f (conjSub x N) (x * u * x⁻¹) := hN.conj x
  have hN'can : IsCanonical (conjSub x N) (x * u * x⁻¹) := hNcan.conj x
  have hu'C : x * u * x⁻¹ ∈ C := mul_mem (mul_mem hxC huC) (inv_mem hxC)
  have hxM : x ∈ trivialOnQuot M := oddCoreIn_le_trivialOnQuot hM.subnormal hM.perfect hx
  have hu'M : x * u * x⁻¹ ∈ trivialOnQuot M :=
    mul_mem (mul_mem hxM huM) (inv_mem hxM)
  have haN' : a ∈ trivialOnQuot (conjSub x N) := by
    have h := trivialOnQuot_conjSub haN x
    have e : x * a * x⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxC
      calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [this]
        _ = a := by group
    rwa [e] at h
  have hcomm1 : ∀ i ∈ triangleResidual J a, ⁅x * u * x⁻¹, i⁆ ∈ oddCoreIn C := by
    intro i hi
    have h1 : ⁅u, i⁆ ∈ oddCoreIn C := by
      have := (oddCoreIn C).inv_mem
        (by rw [← involutionOddCore_eq_oddCoreIn]; exact hJN i hi u rN.mem)
      rwa [commutatorElement_inv] at this
    exact commutator_conj_mem_oddCoreIn hx huC (hIJC hi) h1
  have hu'J : x * u * x⁻¹ ∈ trivialOnQuot J := by
    have hu'Ct : x * u * x⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm
    have hJCt : J ≤ Subgroup.centralizer ({t} : Set G) := isSubnormal_le hJ.subnormal
    refine mem_trivialOnQuot_of_centralizes_modOdd hJ hJcan hu'Ct ?_
    refine centralizes_modOdd_of_commutator_mem hJ hq (I := triangleResidual J a)
      (W := involutionOddCore a ⊓ Subgroup.centralizer ({t} : Set G)) rJ.cover hu'Ct
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)) ?_
      (rJ.le_inf.trans inf_le_left) fun i hi => ?_
    · intro i hi
      exact mem_normalizer_inf (normalizer_oddCoreIn _ (hIJC hi))
        (Subgroup.le_normalizer (hJCt (rJ.le_inf hi).1))
    · refine Subgroup.mem_inf.mpr ⟨hcomm1 i hi, ?_⟩
      have hi' : i ∈ Subgroup.centralizer ({t} : Set G) := hJCt (rJ.le_inf hi).1
      exact mul_mem (mul_mem (mul_mem hu'Ct hi') (inv_mem hu'Ct)) (inv_mem hi')
  have htN' : t ∈ trivialOnQuot (conjSub x N) := by
    have htCu : t ∈ Subgroup.centralizer ({x * u * x⁻¹} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxc
    have hN'Cu : conjSub x N ≤ Subgroup.centralizer ({x * u * x⁻¹} : Set G) :=
      isSubnormal_le hN'.subnormal
    have rN' := axisResidual_single hN' ha2 haN'
    have hI'C : triangleResidual (conjSub x N) a ≤ C := hIC rN'
    refine mem_trivialOnQuot_of_centralizes_modOdd hN' hN'can htCu ?_
    refine centralizes_modOdd_of_commutator_mem hN' hq (I := triangleResidual (conjSub x N) a)
      (W := involutionOddCore a ⊓ Subgroup.centralizer ({x * u * x⁻¹} : Set G)) rN'.cover htCu
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)) ?_
      (rN'.le_inf.trans inf_le_left) fun i hi => ?_
    · intro i hi
      exact mem_normalizer_inf (normalizer_oddCoreIn _ (hI'C hi))
        (Subgroup.le_normalizer (hN'Cu (rN'.le_inf hi).1))
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [triangleResidual_conjSub N hxC] at hi
        have hi' : x⁻¹ * i * x ∈ triangleResidual N a := mem_conjSub_iff.mp hi
        have h1 : ⁅x * (x⁻¹ * i * x) * x⁻¹, t⁆ ∈ oddCoreIn C := by
          refine commutator_conj_mem_oddCoreIn hx (hINC hi') htC ?_
          have := (oddCoreIn C).inv_mem (by
            rw [← involutionOddCore_eq_oddCoreIn]; exact hJN t rJ.mem _ hi')
          rwa [commutatorElement_inv] at this
        have e : x * (x⁻¹ * i * x) * x⁻¹ = i := by group
        rw [e] at h1
        have := (oddCoreIn C).inv_mem h1
        rwa [commutatorElement_inv] at this
      · have hi' : i ∈ Subgroup.centralizer ({x * u * x⁻¹} : Set G) := hN'Cu (rN'.le_inf hi).1
        exact mul_mem (mul_mem (mul_mem htCu hi') (inv_mem htCu)) (inv_mem hi')
  refine ⟨x, hx', hM, hJ, hN', ?_, ?_, hxc, htM, hu'M, haJ, hu'J, haN', htN'⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hu'C).symm

end Local

end CFSG.ClassicalInvolution.Balance.Bootstrap
