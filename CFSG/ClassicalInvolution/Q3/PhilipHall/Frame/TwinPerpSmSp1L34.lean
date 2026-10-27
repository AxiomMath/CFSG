module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Wit
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import Certificates.Certificate397505

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (qGens qCert)
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal (IsQ8Pair)
open Certificates.TwinPerpSmSp1
open CFSG.ComponentClassification

set_option linter.unusedSectionVars false

theorem l34SmallAutModel :
    CFSG.Sporadic.SmallOddCore.AutModel PSL3Four.S PSL3Four.R := by
  obtain ⟨e, he, -⟩ := PSL3Four.full_automorphism_action
  exact {
    le := PSL3Four.S_le_R
    conj_mem := fun x hx p hp => PSL3Four.conj_mem_S hx hp
    surj := fun α => by
      obtain ⟨r, rfl⟩ := e.surjective α
      exact ⟨r, r.2, fun p => he r p⟩
    inj := fun x hx hc => by
      have hmem : x ∈ Subgroup.centralizer (PSL3Four.S : Set (Equiv.Perm (Fin 42))) ⊓
          PSL3Four.R := ⟨Subgroup.mem_centralizer_iff.2 fun p hp => (hc p hp).symm, hx⟩
      rw [PSL3Four.centralizer_S_inf_R, Subgroup.mem_bot] at hmem
      exact hmem }

theorem card_l34R : 2 ^ 8 * 945 = Nat.card PSL3Four.R := by
  rw [PSL3Four.card_R]
  norm_num

theorem l34Syl_le_R :
    Subgroup.closure (permsA 42 (qGens l34Wit.syl)) ≤ PSL3Four.R := by
  refine syl_le_of_q8WitCheck l34Wit Certificates.certificate397505.2.2.1 _ fun l hl => ?_
  obtain ⟨a, ha, hT⟩ := PSL3Four.gTabs_tabs l hl
  change permOfArr 42 CFSG.PSL3Four.Native.gTabs[l]! ∈ PSL3Four.R
  rw [permOfArr_eq_of_rep fun x => hT.2 x]
  exact Subgroup.subset_closure ha

theorem l34Wit_xg_mem : ∀ l < l34Wit.xg.size, permOfArr 42 l34Wit.xg[l]! ∈ PSL3Four.S := by
  intro l hl
  obtain ⟨a, ha, hT⟩ := PSL3Four.gensS_tabs l hl
  change permOfArr 42 CFSG.PSL3Four.Native.gensS[l]! ∈ PSL3Four.S
  rw [permOfArr_eq_of_rep fun x => hT.2 x]
  exact Subgroup.subset_closure ha

theorem sq_mem_of_q8SqIn (D : Q8WitData) (hD : q8WitCheck D = true) {T : Array (Array ℕ)}
    (h : q8SqIn D.syl.n (qCert D.syl).pts ((qCert D.syl).pts.map fun y => compA D.syl.n y y) T =
      true)
    {H : Subgroup (Equiv.Perm (Fin D.syl.n))}
    (hT : ∀ k < T.size, ∀ g : Equiv.Perm (Fin D.syl.n), Rep D.syl.n T[k]! g → g ∈ H)
    {ξ η : Equiv.Perm (Fin D.syl.n)}
    (hξ : ξ ∈ Subgroup.closure (permsA D.syl.n (qGens D.syl)))
    (hη : η ∈ Subgroup.closure (permsA D.syl.n (qGens D.syl))) (hq : IsQ8Pair ξ η) :
    ξ ^ 2 ∈ H := by
  unfold q8WitCheck q8WitCheck' at hD
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hD
  obtain ⟨-, hkeys, -, hQenum, -⟩ := hD
  have hqk : ∀ p ∈ D.syl.qKeys, p < D.syl.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  obtain ⟨i, hi, hxi⟩ := enumOK_exists_rep hqk hQenum hξ
  obtain ⟨j, hj, hyj⟩ := enumOK_exists_rep hqk hQenum hη
  obtain ⟨-, -, hval⟩ := enumOK_spec hqk hQenum
  have hsqi : ((qCert D.syl).pts.map fun y => compA D.syl.n y y)[i]! =
      compA D.syl.n (qCert D.syl).pts[i]! (qCert D.syl).pts[i]! :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporE81.getElem!_map' (qCert D.syl).pts _ hi
  have hsqj : ((qCert D.syl).pts.map fun y => compA D.syl.n y y)[j]! =
      compA D.syl.n (qCert D.syl).pts[j]! (qCert D.syl).pts[j]! :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporE81.getElem!_map' (qCert D.syl).pts _ hj
  have hx2 := rep_compA hxi hxi
  have hy2 := rep_compA hyj hyj
  have hxinv : Rep D.syl.n (invCand D.syl.n (qCert D.syl).pts[i]!) ξ⁻¹ := by
    have := rep_inv_of_validA (hval i hi)
    rwa [permOfArr_eq_of_rep hxi] at this
  obtain ⟨h4, h2, hc, hne⟩ := id hq
  have hci := allLt_spec h hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hci
  rcases hci with (hc1 | hc2) | hc3
  · rw [hsqi] at hc1
    exact absurd (by rw [pow_two]; exact (eqA_iff hx2 rep_idA).1 hc1) hne
  · have h4' : ξ * ξ * (ξ * ξ) = 1 := by
      rw [← h4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [hsqi, (eqA_iff (rep_compA hx2 hx2) rep_idA).2 h4'] at hc2
    exact absurd hc2 (by decide)
  · have hcj := allLt_spec hc3 hj
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcj
    rcases hcj with (hj1 | hj2) | hj3
    · have h2' : η * η = ξ * ξ := by rw [← pow_two, ← pow_two]; exact h2
      rw [hsqi, hsqj, (eqA_iff hy2 hx2).2 h2'] at hj1
      exact absurd hj1 (by decide)
    · have hyx : η * ξ = ξ⁻¹ * η := by
        rw [← hc]
        group
      rw [(eqA_iff (rep_compA hyj hxi) (rep_compA hxinv hyj)).2 hyx] at hj2
      exact absurd hj2 (by decide)
    · obtain ⟨k, hk, hkx⟩ := PSL3Four.memTab_iff.1 hj3
      rw [hsqi] at hkx
      rw [pow_two]
      exact hT k hk _ (hkx ▸ hx2)

theorem pow_eq_one_of_centralizes_C₁
    {g : Equiv.Perm (Fin 42)} (hg : g ∈ PSL3Four.R)
    (hc : ∀ c ∈ PSL3Four.C₁, g * c = c * g) : g ^ 256 = 1 := by
  have h := Certificates.certificate397505.2.2.2.2
  unfold l34CentCheck at h
  obtain ⟨k, hk, hkg⟩ := PSL3Four.enumerates_R.exists_pos hg
  have hk' := (PSL3Four.allBelow_eq_true.1 h) k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with h1 | h1
  · exfalso
    have h2 : ¬ ∀ a < (PSL3Four.centS CFSG.PSL3Four.Native.r₁T).size,
        (CFSG.PSL3Four.Native.comp 42 (PSL3Four.centS CFSG.PSL3Four.Native.r₁T)[a]!
            PSL3Four.enumR.tabs[k]! ==
          CFSG.PSL3Four.Native.comp 42 PSL3Four.enumR.tabs[k]!
            (PSL3Four.centS CFSG.PSL3Four.Native.r₁T)[a]!) = true := by
      intro hall
      rw [PSL3Four.allBelow_eq_true.2 hall] at h1
      exact absurd h1 (by decide)
    apply h2
    intro a ha
    obtain ⟨c, hcC, hcT⟩ := PSL3Four.enumerates_C₁.exists_elt ha
    exact (PSL3Four.TabRep.beq_iff (hcT.comp hkg) (hkg.comp hcT)).2 (hc c hcC).symm
  · exact (PSL3Four.TabRep.beq_iff (hkg.pow 256) PSL3Four.TabRep.idTab).1 h1

theorem eq_one_of_odd_of_pow_two_pow {G : Type*} [Group G] {g : G} (hodd : Odd (orderOf g)) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have hdvd := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  · rw [hi, pow_succ] at hodd
    exact absurd (Even.mul_left even_two _) (Nat.not_even_iff_odd.2 hodd)

theorem oddCore_centralizer_of_l34
    {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y)
    [N.Normal] (ι : Y →* Equiv.Perm (Fin 42)) (hι : Function.Injective ι)
    (hιR : ∀ y, ι y ∈ PSL3Four.R) (hιN : ∀ m ∈ N, ι m ∈ PSL3Four.S)
    (hιN' : ∀ s ∈ PSL3Four.S, ∃ m ∈ N, ι m = s) {t : Y} (htN : t ∈ N) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hτ2 : orderOf (⟨ι t, hιR t⟩ : PSL3Four.R) = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_injective ι hι, ht]
  have hτS : ι t ∈ PSL3Four.S := hιN t htN
  obtain ⟨c, hcR, hτc⟩ : ∃ c ∈ PSL3Four.R, ι t = c * PSL3Four.r₁ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hτ2 with h1 | h1 | h1 | h1
    · exact PSL3Four.eq_conj_of_isConj h1
    · exact absurd hτS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₂)
    · exact absurd hτS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₃)
    · exact absurd hτS (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₄)
  have hci : c⁻¹ ∈ PSL3Four.R := PSL3Four.R.inv_mem hcR
  have hA : ∀ s ∈ PSL3Four.S, s * ι t = ι t * s → s ^ 64 = 1 := by
    intro s hs hst
    have hs' : c⁻¹ * s * c⁻¹⁻¹ ∈ PSL3Four.C₁ := by
      show c⁻¹ * s * c⁻¹⁻¹ ∈ Subgroup.centralizer {PSL3Four.r₁} ⊓ PSL3Four.S
      refine Subgroup.mem_inf.2 ⟨?_, PSL3Four.conj_mem_S hci hs⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hτc] at hst
      calc c⁻¹ * s * c⁻¹⁻¹ * PSL3Four.r₁ = c⁻¹ * (s * (c * PSL3Four.r₁ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * PSL3Four.r₁ * c⁻¹) * s) * c := by rw [hst]
        _ = PSL3Four.r₁ * (c⁻¹ * s * c⁻¹⁻¹) := by group
    have h64 : (c⁻¹ * s * c⁻¹⁻¹) ^ 64 = 1 := by
      have := pow_card_eq_one' (G := ↥PSL3Four.C₁) (x := ⟨_, hs'⟩)
      rw [PSL3Four.card_C₁] at this
      exact congrArg Subtype.val this
    calc s ^ 64 = c * (c⁻¹ * s ^ 64 * c⁻¹⁻¹) * c⁻¹ := by group
      _ = 1 := by rw [← conj_pow, h64]; group
  have hB : ∀ g ∈ PSL3Four.R, (∀ s ∈ PSL3Four.S, s * ι t = ι t * s → g * s = s * g) →
      g ^ 256 = 1 := by
    intro g hg hcomm
    have hg' : c⁻¹ * g * c⁻¹⁻¹ ∈ PSL3Four.R :=
      PSL3Four.R.mul_mem (PSL3Four.R.mul_mem hci hg) (PSL3Four.R.inv_mem hci)
    have key := pow_eq_one_of_centralizes_C₁ hg' fun d hd => by
      have hd' : d ∈ Subgroup.centralizer {PSL3Four.r₁} ⊓ PSL3Four.S := hd
      have hdS : c * d * c⁻¹ ∈ PSL3Four.S := PSL3Four.conj_mem_S hcR (Subgroup.mem_inf.1 hd').2
      have hdt : (c * d * c⁻¹) * ι t = ι t * (c * d * c⁻¹) := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hd').1
        rw [hτc]
        calc c * d * c⁻¹ * (c * PSL3Four.r₁ * c⁻¹) = c * (d * PSL3Four.r₁) * c⁻¹ := by group
          _ = c * (PSL3Four.r₁ * d) * c⁻¹ := by rw [h1]
          _ = c * PSL3Four.r₁ * c⁻¹ * (c * d * c⁻¹) := by group
      have h2 := hcomm _ hdS hdt
      calc c⁻¹ * g * c⁻¹⁻¹ * d = c⁻¹ * (g * (c * d * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * d * c⁻¹) * g) * c := by rw [h2]
        _ = d * (c⁻¹ * g * c⁻¹⁻¹) := by group
    calc g ^ 256 = c * (c⁻¹ * g ^ 256 * c⁻¹⁻¹) * c⁻¹ := by group
      _ = 1 := by rw [← conj_pow, key]; group
  set H := Subgroup.centralizer ({t} : Set Y) with hH
  haveI : (CFSG.oddCore ↥H).Normal := CFSG.oddCore_normal (G := ↥H)
  have hOodd : Odd (Nat.card ↥(CFSG.oddCore ↥H)) :=
    CFSG.ComponentClassification.SmallLocal.odd_card_oddCore
  have hoddo : ∀ o ∈ CFSG.oddCore ↥H, Odd (orderOf o) := fun o ho =>
    Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ ho)
  have hcommN : ∀ o ∈ CFSG.oddCore ↥H, ∀ m : ↥H, (m : Y) ∈ N → o * m = m * o := by
    intro o ho m hm
    have hqO : o * (m * o⁻¹ * m⁻¹) ∈ CFSG.oddCore ↥H :=
      Subgroup.mul_mem _ ho ((inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem _
        (Subgroup.inv_mem _ ho) m)
    have hqN : ((o * (m * o⁻¹ * m⁻¹) : ↥H) : Y) ∈ N := by
      have e : ((o * (m * o⁻¹ * m⁻¹) : ↥H) : Y) =
          ((o : Y) * (m : Y) * (o : Y)⁻¹) * (m : Y)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
      rw [e]
      exact N.mul_mem ((inferInstance : N.Normal).conj_mem _ hm _) (N.inv_mem hm)
    have hqt : ((o * (m * o⁻¹ * m⁻¹) : ↥H) : Y) * t = t * ((o * (m * o⁻¹ * m⁻¹) : ↥H) : Y) :=
      Subgroup.mem_centralizer_singleton_iff.1 (o * (m * o⁻¹ * m⁻¹)).2
    have hq64 := hA _ (hιN _ hqN) (by rw [← map_mul, ← map_mul, hqt])
    have hq1 : o * (m * o⁻¹ * m⁻¹) = 1 := by
      refine eq_one_of_odd_of_pow_two_pow (hoddo _ hqO) (k := 6) (Subtype.ext (hι ?_))
      rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
      exact hq64
    calc o * m = o * (m * o⁻¹ * m⁻¹) * (m * o) := by group
      _ = m * o := by rw [hq1, one_mul]
  rw [eq_bot_iff]
  intro o ho
  rw [Subgroup.mem_bot]
  have h256 : ι (o : Y) ^ 256 = 1 := hB _ (hιR _) fun s hs hst => by
    obtain ⟨m, hmN, rfl⟩ := hιN' s hs
    have hmt : m * t = t * m := hι (by rw [map_mul, map_mul]; exact hst)
    have hmH : m ∈ H := Subgroup.mem_centralizer_singleton_iff.2 hmt
    have h1 := congrArg (fun z : ↥H => ι (z : Y)) (hcommN o ho ⟨m, hmH⟩ hmN)
    simpa only [Subgroup.coe_mul, map_mul] using h1
  refine eq_one_of_odd_of_pow_two_pow (hoddo o ho) (k := 8) (Subtype.ext (hι ?_))
  rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
  exact h256

theorem isPGroup_core_of_l34 {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R' : Subgroup Y}
    {S : Sylow 2 R'} {t : Y} (hP : PerpHypS n Y R' S t)
    (θ : ↥(genFittingFStar Y) ≃* ↥PSL3Four.S) : IsPGroup 2 ↥(tightCore R') := by
  haveI := hP.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab
  have hM := l34SmallAutModel
  have hιinj : Function.Injective (hM.embed (genFittingFStar Y) θ) :=
    hM.embed_injective (genFittingFStar Y) θ hC
  have hιR : ∀ y, hM.embed (genFittingFStar Y) θ y ∈ PSL3Four.R :=
    hM.embed_mem (genFittingFStar Y) θ
  have hιN : ∀ m ∈ genFittingFStar Y, hM.embed (genFittingFStar Y) θ m ∈ PSL3Four.S :=
    fun m hm => by
      have := hM.embed_coe (genFittingFStar Y) θ ⟨m, hm⟩
      rw [this]
      exact (θ ⟨m, hm⟩).2
  have hιN' : ∀ s ∈ PSL3Four.S, ∃ m ∈ genFittingFStar Y,
      hM.embed (genFittingFStar Y) θ m = s := fun s hs =>
    ⟨(θ.symm ⟨s, hs⟩ : Y), (θ.symm ⟨s, hs⟩).2, by
      rw [hM.embed_coe (genFittingFStar Y) θ, MulEquiv.apply_symm_apply]⟩
  obtain ⟨r', hr', ⟨e'⟩⟩ := hP.core.datum.quat
  set S' : Subgroup Y := (S : Subgroup R').map R'.subtype with hS'
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨r', hr', ⟨(Subgroup.equivMapOfInjective (S : Subgroup R') R'.subtype
      R'.subtype_injective).symm.trans e'⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal.exists_q8Pair hQ
  have hS'2 : IsPGroup 2 ↥S' := S.isPGroup'.map R'.subtype
  have hpK : p ∈ tightCore R' := hP.core.datum.sylow_core.1 hp
  have hpt : p ^ 2 = t := by
    have hz := uniqueInv_core hP
    have h1 : p ^ 2 * p ^ 2 = 1 := by rw [← pow_add]; exact hpq.1
    rcases hz.unique (p ^ 2) ((tightCore R').pow_mem hpK 2) h1 with h2 | h2
    · exact absurd h2 hpq.2.2.2
    · exact h2
  have hS'R : S'.map (hM.embed (genFittingFStar Y) θ) ≤ PSL3Four.R := by
    rintro _ ⟨y, -, rfl⟩
    exact hιR y
  have hW := Certificates.certificate397505.2.2.1
  obtain ⟨w, hwR, hw⟩ := exists_conj_le_of_card l34Syl_le_R hS'R
    (hS'2.map (hM.embed (genFittingFStar Y) θ)) (k := 8) (m := 945)
    (card_syl_of_q8WitCheck l34Wit hW) (by decide) card_l34R
  obtain ⟨φ, hφinj, hφapp⟩ : ∃ φ : Y →* Equiv.Perm (Fin 42), Function.Injective φ ∧
      ∀ y, φ y = w * hM.embed (genFittingFStar Y) θ y * w⁻¹ :=
    ⟨(MulAut.conj w).toMonoidHom.comp (hM.embed (genFittingFStar Y) θ),
      (MulAut.conj w).injective.comp hιinj, fun y => rfl⟩
  have hx : φ p ∈ Subgroup.closure (permsA 42 (qGens l34Wit.syl)) := by
    rw [hφapp]
    exact hw _ ⟨p, hp, rfl⟩
  have hy : φ q ∈ Subgroup.closure (permsA 42 (qGens l34Wit.syl)) := by
    rw [hφapp]
    exact hw _ ⟨q, hq, rfl⟩
  have hsq := sq_mem_of_q8SqIn l34Wit hW Certificates.certificate397505.2.2.2.1
    (H := PSL3Four.S) (fun k hk g hg => by
      obtain ⟨g', hg'S, hg'T⟩ := PSL3Four.enumerates_S.exists_elt hk
      have : g = g' := Equiv.ext fun i => Fin.ext ((hg i).symm.trans (hg'T.2 i))
      rw [this]
      exact hg'S) hx hy (hpq.map φ hφinj)
  have hsq2 : φ p ^ 2 ∈ PSL3Four.S := hsq
  rw [← map_pow, hpt, hφapp] at hsq2
  have hιt : hM.embed (genFittingFStar Y) θ t ∈ PSL3Four.S := PSL3Four.conj_mem_S' hwR hsq2
  obtain ⟨m, hm, hmt⟩ := hιN' _ hιt
  have htN : t ∈ genFittingFStar Y := by
    rw [← hιinj hmt]
    exact hm
  exact isPGroup_core_of_oddCore hP (oddCore_centralizer_of_l34 (genFittingFStar Y)
    (hM.embed (genFittingFStar Y) θ) hιinj hιR hιN hιN' htN hP.core.datum.order)

theorem leaf_l34 {n : ℕ} : NoTwinS n (fun F _ => CFSG.Blueprint.LieModel F .PSL 3 2 2) := by
  have h := Certificates.certificate397505.2.2.1
  refine noTwinS_of_q8Wit l34SmallAutModel (Subgroup.closure (permsA 42 (qGens l34Wit.syl)))
    l34Syl_le_R (k := 8) (m := 945) (card_syl_of_q8WitCheck l34Wit h) (by decide) card_l34R
    (hwit_of_q8WitCheck l34Wit rfl h _ l34Wit_xg_mem) ?_
  intro Y _ _ R' S t hP hF
  obtain ⟨θ⟩ : Nonempty (↥(genFittingFStar Y) ≃* ↥PSL3Four.S) := by
    rcases hF with ⟨-, hF⟩ | ⟨hF, -⟩ | ⟨hF, -⟩ | ⟨hF, -⟩
    · exact PSL3Four.nonempty_equiv_of_stated _ hF
    all_goals exact absurd hF (by norm_num)
  exact ⟨⟨θ⟩, isPGroup_core_of_l34 hP θ⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
