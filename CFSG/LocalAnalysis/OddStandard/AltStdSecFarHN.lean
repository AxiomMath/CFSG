module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecWreath
public import CFSG.RankThree.PartOne.S11c.HNFiveCoverage
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarExcl
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootComp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS1
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Card

variable {A : Type*} [Group A] [Finite A]

theorem card_comap_mk' (N : Subgroup A) [N.Normal] (H : Subgroup (A ⧸ N)) :
    Nat.card (H.comap (QuotientGroup.mk' N)) = Nat.card H * Nat.card N := by
  have h1 := Subgroup.card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective N)] at h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h3, ← h2] at h1
  have h4 : Nat.card (H.comap (QuotientGroup.mk' N)) * H.index =
      (Nat.card H * Nat.card N) * H.index := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h4

end Card

section HNFact

open CFSG.RankThree.PartOne.HNRed CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore in
theorem card_centralizer_five_of_hn {W : Type*} [Group W] [Finite W]
    (e : W ≃* CFSG.Blueprint.NativeSporadic.HN) {x u : W} (hx : orderOf x = 5)
    (hu : orderOf u = 7) (hxu : x * u = u * x) :
    Nat.card (centralizer ({x} : Set W)) = 630000 := by
  let E : W ≃* ↥JH := e.trans hnEquivJ
  have hcovJ : SevenCommuteConj ↥JH := fun _ _ hf hw hfu hwu =>
    exists_conj_pow_of_commute_seven_JH hf hw hfu hwu
  obtain ⟨hcomm, -, -, hfJ5, hcardC, hcardI, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := IJ) 7 (by rw [hcardI]; norm_num)
  have hfJu : ∃ v : ↥JH, orderOf v = 7 ∧ fJ * v = v * fJ :=
    ⟨(y : ↥JH), by rw [Subgroup.orderOf_coe]; exact hy, hcomm fJ (mem_zpowers fJ) y y.2⟩
  obtain ⟨hf₁, hf₁u, hc₁⟩ :=
    @coverage_data_of_mulEquiv W (↥JH) _ inferInstance E fJ hfJ5 hfJu hcardC
  have hcovW := @sevenCommuteConj_of_mulEquiv W (↥JH) _ inferInstance E hcovJ
  obtain ⟨g, a, hga⟩ := hcovW _ x hf₁ hx hf₁u ⟨u, hu, hxu⟩
  rw [card_centralizer_eq_of_conj_pow hf₁ hx hga, hc₁]

end HNFact

section Cyc

abbrev fiveCyc : Perm (Fin 16) := swap 4 5 * swap 5 6 * swap 6 7 * swap 7 8

abbrev sevenCyc : Perm (Fin 16) :=
  swap 9 10 * swap 10 11 * swap 11 12 * swap 12 13 * swap 13 14 * swap 14 15

theorem orderOf_fiveCyc : orderOf fiveCyc = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (by decide)
  rw [show fiveCyc ^ 5 = fiveCyc * fiveCyc * fiveCyc * fiveCyc * fiveCyc by
    simp only [pow_succ, pow_zero, one_mul]]
  decide

set_option maxRecDepth 20000 in
theorem orderOf_sevenCyc : orderOf sevenCyc = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (by decide)
  rw [show sevenCyc ^ 7 = sevenCyc * sevenCyc * sevenCyc * sevenCyc * sevenCyc * sevenCyc *
    sevenCyc by simp only [pow_succ, pow_zero, one_mul]]
  decide

theorem fiveCyc_mem : fiveCyc ∈ altSub (fourSet (13 + 3))ᶜ :=
  mem_altSub.2 ⟨by decide, by decide⟩

theorem sevenCyc_mem : sevenCyc ∈ altSub (fourSet (13 + 3))ᶜ :=
  mem_altSub.2 ⟨by decide, by decide⟩

theorem fiveCyc_comm_sevenCyc : fiveCyc * sevenCyc = sevenCyc * fiveCyc := by decide

theorem fiveCyc_comm_swap : fiveCyc * swap 9 10 = swap 9 10 * fiveCyc := by decide

theorem fiveCyc_comm_tau : fiveCyc * OverData.tau 13 = OverData.tau 13 * fiveCyc := by decide

end Cyc

section SecR

variable {m : ℕ} {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

include hR in
theorem card_secR : Nat.card R = 4 := by
  have h0 : (⟨0, by omega⟩ : Fin (m + 3)) ∈ fourSet (m + 3) := by rw [mem_fourSet]; simp
  have hmaps : ∀ r ∈ R, r ⟨0, by omega⟩ ∈ fourSet (m + 3) := by
    intro r hr
    by_contra h
    have h1 : r (r ⟨0, by omega⟩) = r ⟨0, by omega⟩ :=
      hR.le hr _ (Finset.mem_compl.2 h)
    have := r.injective h1
    rw [this] at h
    exact h h0
  let ev : R → ↥(fourSet (m + 3)) := fun r => ⟨(r : Perm (Fin (m + 3))) ⟨0, by omega⟩, hmaps r r.2⟩
  have hinj : Function.Injective ev := by
    intro r s hrs
    have h1 : (r : Perm (Fin (m + 3))) ⟨0, by omega⟩ = (s : Perm (Fin (m + 3))) ⟨0, by omega⟩ :=
      congrArg Subtype.val hrs
    have h2 : ((s⁻¹ * r : R) : Perm (Fin (m + 3))) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      change (s : Perm (Fin (m + 3)))⁻¹ ((r : Perm (Fin (m + 3))) ⟨0, by omega⟩) = _
      rw [h1]
      simp
    have h3 := eq_one_of_fixes_of_transitive hR.le hR.comm hR.trans (s⁻¹ * r).2 h0 h2
    have h4 : s⁻¹ * r = 1 := Subtype.ext h3
    calc r = s * (s⁻¹ * r) := by group
      _ = s := by rw [h4, mul_one]
  have hsurj : Function.Surjective ev := by
    rintro ⟨j, hj⟩
    obtain ⟨r, hr, hrj⟩ := hR.trans _ h0 j hj
    exact ⟨⟨r, hr⟩, Subtype.ext hrj⟩
  rw [Nat.card_congr (Equiv.ofBijective ev ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe, card_fourSet (N := m + 3) (by have := hR.three_le; omega)]

end SecR

section HN

variable {G : Type} [Group G] [Finite G] {z : G} (O : OverData G z 13)
  {R : Subgroup (Perm (Fin (13 + 3)))} (hR : SecR 13 R)

theorem exists_two_subgroup_of_hn
    (hHN : HNOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ centralizer (secP O R : Set G) ∧
      T ≤ centralizer ({O.φ fiveCyc} : Set G) ∧ 2 ^ 7 ∣ Nat.card T := by
  classical
  obtain ⟨W, hWn, hWi, htW, ⟨eW⟩⟩ := hHN
  set Od := CFSG.oddCore (secQ (secP O R)) with hOd
  set π := QuotientGroup.mk' Od with hπ
  set ι := secIncl O hR _ altSub_compl_le with hι
  set ψ := π.comp ι with hψ
  have hψi : Function.Injective ψ := secLq_injective O hR (by omega)
  set f1 : secQ (secP O R) := ι ⟨fiveCyc, fiveCyc_mem⟩ with hf1
  set u1 : secQ (secP O R) := ι ⟨sevenCyc, sevenCyc_mem⟩ with hu1
  have hfb : orderOf (π f1) = 5 := by
    change orderOf (ψ ⟨fiveCyc, fiveCyc_mem⟩) = 5
    rw [orderOf_injective ψ hψi, Subgroup.orderOf_mk, orderOf_fiveCyc]
  have hub : orderOf (π u1) = 7 := by
    change orderOf (ψ ⟨sevenCyc, sevenCyc_mem⟩) = 7
    rw [orderOf_injective ψ hψi, Subgroup.orderOf_mk, orderOf_sevenCyc]
  have hfu : π f1 * π u1 = π u1 * π f1 := by
    change ψ _ * ψ _ = ψ _ * ψ _
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext fiveCyc_comm_sevenCyc)
  have hfW : π f1 ∈ W := mem_of_odd_of_index_two hWi (by rw [hfb]; decide)
  have huW : π u1 ∈ W := mem_of_odd_of_index_two hWi (by rw [hub]; decide)
  have hCW : Nat.card (centralizer ({(⟨π f1, hfW⟩ : W)} : Set W)) = 630000 :=
    card_centralizer_five_of_hn eW (u := ⟨π u1, huW⟩) (by rw [Subgroup.orderOf_mk]; exact hfb)
      (by rw [Subgroup.orderOf_mk]; exact hub) (Subtype.ext hfu)
  set C := centralizer ({π f1} : Set (secQ (secP O R) ⧸ Od)) with hC
  have hτf : (⟨OverData.tau 13, hR.tau_mem_fixSub⟩ : fixSub (fourSet (13 + 3))) *
      ⟨fiveCyc, altSub_compl_le fiveCyc_mem⟩ =
      ⟨fiveCyc, altSub_compl_le fiveCyc_mem⟩ * ⟨OverData.tau 13, hR.tau_mem_fixSub⟩ :=
    Subtype.ext fiveCyc_comm_tau.symm
  have hf1' : f1 = secIncl O hR _ le_rfl ⟨fiveCyc, altSub_compl_le fiveCyc_mem⟩ :=
    secIncl_congr O hR _ _ rfl
  have htC : (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ Od) ∈ C := by
    rw [hC, mem_centralizer_singleton_iff]
    change π (secT O hR) * π f1 = π f1 * π (secT O hR)
    rw [← map_mul, ← map_mul, secT_eq_secIncl, hf1', ← map_mul, ← map_mul, hτf]
  have hCW' : Nat.card (W.subgroupOf C) = 630000 := by
    rw [← hCW]
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨((c : C) : secQ (secP O R) ⧸ Od), c.2⟩, ?_⟩
        invFun := fun w => ⟨⟨((w : W) : secQ (secP O R) ⧸ Od), ?_⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun w => rfl }
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.1 (c : C).2
    · rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 w.2)
    · exact (w : W).2
  have hidx : (W.subgroupOf C).index = 2 := by
    have h1 : (W.subgroupOf C).index ∣ 2 := by
      have := Subgroup.relIndex_dvd_index_of_normal W C
      rwa [hWi] at this
    have h2 : (W.subgroupOf C).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      apply htW
      have : (⟨_, htC⟩ : C) ∈ W.subgroupOf C := h ▸ mem_top _
      exact this
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  have hCcard : 2 ^ 5 ∣ Nat.card C := by
    have := Subgroup.card_mul_index (W.subgroupOf C)
    rw [hCW', hidx] at this
    rw [← this]
    norm_num
  set Ch := C.comap π with hCh
  have hChcard : 2 ^ 5 ∣ Nat.card Ch := by
    rw [hCh, card_comap_mk' Od C]
    exact Dvd.dvd.mul_right hCcard _
  have h9 : (9 : Fin (13 + 3)) ∉ fourSet (13 + 3) := by decide
  have h10 : (10 : Fin (13 + 3)) ∉ fourSet (13 + 3) := by decide
  set s := secSwap O hR h9 h10 with hs
  have hsf : s * f1 = f1 * s := by
    rw [hs, hf1', secSwap, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext fiveCyc_comm_swap.symm
  have hsCh : s ∈ Ch := by
    change π s ∈ C
    rw [hC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hsf]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsp : IsPGroup 2 (zpowers (⟨s, hsCh⟩ : Ch)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext (secSwap_mul_self O hR h9 h10)
    · intro h
      have h1 : s = 1 := congrArg Subtype.val h
      have h2 : (swap (9 : Fin (13 + 3)) 10 : Perm (Fin (13 + 3))) = 1 :=
        congrArg Subtype.val (secIncl_injective O hR _ le_rfl (h1.trans (map_one _).symm))
      exact absurd h2 (by decide)
  obtain ⟨P₂, hP₂⟩ := hsp.exists_le_sylow
  have hP₂card : 2 ^ 5 ∣ Nat.card P₂ := Sylow.pow_dvd_card_of_pow_dvd_card P₂ hChcard
  set T₁ : Subgroup (secQ (secP O R)) := (P₂ : Subgroup Ch).map Ch.subtype with hT₁
  have hT₁Ch : ∀ τ ∈ T₁, τ ∈ Ch := fun τ hτ => map_subtype_le _ hτ
  have hsT : s ∈ T₁ := ⟨⟨s, hsCh⟩, hP₂ (mem_zpowers _), rfl⟩
  have hT₁p : IsPGroup 2 T₁ := P₂.isPGroup'.map _
  have hT₁card : Nat.card T₁ = Nat.card P₂ :=
    Subgroup.card_map_of_injective Ch.subtype_injective
  have hmem : ∀ τ ∈ T₁, ∀ o ∈ Od, f1⁻¹ * (τ * (f1 * o) * τ⁻¹) ∈ Od := by
    intro τ hτ o ho
    have hτC : π τ * π f1 = π f1 * π τ := mem_centralizer_singleton_iff.1 (hT₁Ch τ hτ)
    have e1 : f1⁻¹ * (τ * (f1 * o) * τ⁻¹) = (f1⁻¹ * τ * f1 * τ⁻¹) * (τ * o * τ⁻¹) := by group
    rw [e1]
    refine mul_mem ?_ ((inferInstance : Od.Normal).conj_mem _ ho τ)
    apply (QuotientGroup.eq_one_iff _).1
    change π (f1⁻¹ * τ * f1 * τ⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc (π f1)⁻¹, hτC]
    group
  let act : MulAction T₁ Od :=
    { smul := fun τ o => ⟨f1⁻¹ * ((τ : secQ (secP O R)) * (f1 * o) * (τ : secQ (secP O R))⁻¹),
        hmem τ τ.2 o o.2⟩
      one_smul := fun o => by
        apply Subtype.ext
        change f1⁻¹ * ((1 : secQ (secP O R)) * (f1 * o) * (1 : secQ (secP O R))⁻¹) = o
        group
      mul_smul := fun τ σ o => by
        apply Subtype.ext
        change f1⁻¹ * (((τ : secQ (secP O R)) * σ) * (f1 * o) * ((τ : secQ (secP O R)) * σ)⁻¹) =
          f1⁻¹ * ((τ : secQ (secP O R)) *
            (f1 * (f1⁻¹ * ((σ : secQ (secP O R)) * (f1 * o) * (σ : secQ (secP O R))⁻¹))) *
              (τ : secQ (secP O R))⁻¹)
        group }
  have hfix := hT₁p.card_modEq_card_fixedPoints Od
  have hodd : Odd (Nat.card Od) :=
    ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore (secQ (secP O R))
  have hne : Nat.card (MulAction.fixedPoints T₁ Od) ≠ 0 := by
    intro h0
    rw [h0] at hfix
    have : Nat.card Od % 2 = 0 := hfix
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨⟨o, ho⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have ho' : ∀ τ : T₁, f1⁻¹ * ((τ : secQ (secP O R)) * (f1 * o) * (τ : secQ (secP O R))⁻¹) = o :=
    fun τ => congrArg Subtype.val (ho τ)
  have ho1 : (o : secQ (secP O R)) = 1 := by
    have h1 := ho' ⟨s, hsT⟩
    have h2 : s * (f1 * o) * s⁻¹ = f1 * (s * o * s⁻¹) := by
      calc s * (f1 * o) * s⁻¹ = (s * f1) * o * s⁻¹ := by group
        _ = (f1 * s) * o * s⁻¹ := by rw [hsf]
        _ = f1 * (s * o * s⁻¹) := by group
    have h3 : s * (o : secQ (secP O R)) * s⁻¹ = (o : secQ (secP O R))⁻¹ :=
      conj_secSwap_eq_inv O hR (by norm_num) h9 h10 (by decide) o.2
    change f1⁻¹ * (s * (f1 * o) * s⁻¹) = o at h1
    rw [h2, h3, inv_mul_cancel_left] at h1
    have h4 : (o : secQ (secP O R)) ^ 2 = 1 := by
      rw [pow_two]
      calc (o : secQ (secP O R)) * o = (o : secQ (secP O R))⁻¹⁻¹ * o := by rw [inv_inv]
        _ = 1 := by rw [h1, inv_mul_cancel]
    exact eq_one_of_odd_of_sq (orderOf_odd_of_mem_oddCore o.2) h4
  have hT₁f : ∀ τ ∈ T₁, τ * f1 = f1 * τ := by
    intro τ hτ
    have h1 := ho' ⟨τ, hτ⟩
    rw [ho1, mul_one] at h1
    change f1⁻¹ * (τ * f1 * τ⁻¹) = 1 at h1
    calc τ * f1 = f1 * (f1⁻¹ * (τ * f1 * τ⁻¹)) * τ := by group
      _ = f1 * τ := by rw [h1, mul_one]
  set That := T₁.comap (QuotientGroup.mk' (secPin (secP O R))) with hThat
  set T : Subgroup G := That.map (centralizer (secP O R : Set G)).subtype with hT
  have hPin : Nat.card (secPin (secP O R)) = 4 := by
    have hPC : secP O R ≤ centralizer (secP O R : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨r', hr', rfl⟩
      rw [O.φ_comm_iff]
      exact hR.comm r' hr' r hr
    rw [secPin, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, secP,
      Subgroup.card_map_of_injective O.φ_injective, card_secR hR]
  have hTcard : Nat.card T = Nat.card T₁ * 4 := by
    rw [hT, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hThat,
      card_comap_mk' _ T₁, hPin]
  have hf5 : orderOf (O.φ fiveCyc) = 5 := by
    rw [orderOf_injective O.φ O.φ_injective, orderOf_fiveCyc]
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hT₁p.exists_card_eq
    exact IsPGroup.of_card (n := k + 2) (by rw [hTcard, hk]; ring)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hfP : O.φ fiveCyc ∈ centralizer (secP O R : Set G) :=
      fixSub_comm_secP O hR (altSub_compl_le fiveCyc_mem)
    set ff : ↥(centralizer (secP O R : Set G)) := ⟨O.φ fiveCyc, hfP⟩ with hff
    have hmk : (QuotientGroup.mk ff : secQ (secP O R)) = f1 := by
      rw [hf1, hι, secIncl_apply]
    have hy' : (QuotientGroup.mk y : secQ (secP O R)) ∈ T₁ := hy
    have h1 := hT₁f _ hy'
    rw [← hmk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    have h2 := QuotientGroup.eq.1 h1
    have h3 : ((y * ff)⁻¹ * (ff * y) : ↥(centralizer (secP O R : Set G))) ∈ secPin (secP O R) := h2
    have h4 : ((y : G) * O.φ fiveCyc)⁻¹ * (O.φ fiveCyc * y) ∈ secP O R := h3
    set p := ((y : G) * O.φ fiveCyc)⁻¹ * (O.φ fiveCyc * y) with hp
    obtain ⟨r, hr, hrp⟩ := h4
    have hp4 : p ^ 4 = 1 := by rw [← hrp, ← map_pow, hR.pow_four r hr, map_one]
    have hpf : p * O.φ fiveCyc = O.φ fiveCyc * p :=
      (mem_centralizer_iff.1 hfP p ⟨r, hr, hrp⟩)
    have e1 : (y : G)⁻¹ * O.φ fiveCyc * y = O.φ fiveCyc * p := by rw [hp]; group
    have hf55 : (O.φ fiveCyc) ^ 5 = 1 := by rw [← hf5]; exact pow_orderOf_eq_one _
    have h5 : (O.φ fiveCyc * p) ^ 5 = 1 := by
      have hc := conj_pow (a := (y : G)⁻¹) (b := O.φ fiveCyc) (i := 5)
      rw [inv_inv] at hc
      rw [← e1, hc, hf55, mul_one, inv_mul_cancel]
    rw [Commute.mul_pow (show Commute (O.φ fiveCyc) p from hpf.symm), hf55, one_mul,
      pow_succ, hp4, one_mul] at h5
    rw [h5, mul_one] at e1
    calc (y : G) * O.φ fiveCyc = y * ((y : G)⁻¹ * O.φ fiveCyc * y) := by rw [e1]
      _ = O.φ fiveCyc * y := by group
  · rw [hTcard, hT₁card]
    obtain ⟨k, hk⟩ := hP₂card
    rw [hk]
    exact ⟨k, by ring⟩

theorem not_hnOutcome_of_bound
    (hbound : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ centralizer (secP O R : Set G) →
      T ≤ centralizer ({O.φ fiveCyc} : Set G) → Nat.card T ∣ 20160) :
    ¬ HNOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) := by
  intro hHN
  obtain ⟨T, hTp, hTP, hTf, hT7⟩ := exists_two_subgroup_of_hn O hR hHN
  have h := hbound T hTp hTP hTf
  have : 2 ^ 7 ∣ 20160 := hT7.trans h
  norm_num at this

end HN

end CFSG.OddStandard.AltStdSec
