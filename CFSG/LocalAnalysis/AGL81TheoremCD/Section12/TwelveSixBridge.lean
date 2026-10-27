module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt

import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.AltOddCentre
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem nonempty_alt9_of_quot_center {K : Subgroup G} (hq : CFSG.IsQuasisimple (modTwoCore K))
    (hS : Nonempty (modTwoCore K ⧸ center (modTwoCore K) ≃* alternatingGroup (Fin 9))) :
    Nonempty (modTwoCore K ≃* alternatingGroup (Fin 9)) := by
  have hO : CFSG.pCore 2 (modTwoCore K) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.F153L3C2.quot_pCore_two_eq_bot K
  have hZ : Subgroup.center (modTwoCore K) = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.altOddCentreTrivial (modTwoCore K)
      ⟨hq.1.commutator_eq_top, hq.2.1⟩
      (CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_of_pCore_eq_bot hO).not_two_dvd_nat
      9 (by norm_num) hS
  obtain ⟨e⟩ := hS
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e⟩

private theorem comap_centralizer_range_eq_center_quotient {X L : Type} [Group X] [Group L]
    (f : X →* L) :
    (Subgroup.centralizer (f.range : Set L)).comap f =
      (Subgroup.center (X ⧸ f.ker)).comap (QuotientGroup.mk' f.ker) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  have key1 : f x ∈ Subgroup.centralizer (f.range : Set L) ↔
      ∀ y : X, ⁅y, x⁆ ∈ f.ker := by
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h y
      have hy : f y * f x = f x * f y := h (f y) ⟨y, rfl⟩
      rw [MonoidHom.mem_ker, map_commutatorElement f y x,
        commutatorElement_eq_one_iff_mul_comm]
      exact hy
    · intro h y hy
      obtain ⟨z, hz⟩ := hy
      rw [← hz, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement f z x]
      exact MonoidHom.mem_ker.mp (h z)
  have key2 : (QuotientGroup.mk' f.ker x) ∈ Subgroup.center (X ⧸ f.ker) ↔
      ∀ y : X, ⁅y, x⁆ ∈ f.ker := by
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h y
      have hy : QuotientGroup.mk' f.ker y * QuotientGroup.mk' f.ker x =
          QuotientGroup.mk' f.ker x * QuotientGroup.mk' f.ker y := h _
      have hy' : ⁅QuotientGroup.mk' f.ker y, QuotientGroup.mk' f.ker x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hy
      rw [← map_commutatorElement (QuotientGroup.mk' f.ker) y x] at hy'
      exact (QuotientGroup.eq_one_iff (N := f.ker) ⁅y, x⁆).mp hy'
    · intro h y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective f.ker y
      have hz : QuotientGroup.mk' f.ker ⁅z, x⁆ = 1 :=
        (QuotientGroup.eq_one_iff (N := f.ker) ⁅z, x⁆).mpr (h z)
      rw [map_commutatorElement (QuotientGroup.mk' f.ker) z x] at hz
      exact commutatorElement_eq_one_iff_mul_comm.mp hz
  exact key1.trans key2.symm

private theorem comap_center_quotient_congr {Y : Type} [Group Y] {N M : Subgroup Y}
    [N.Normal] [M.Normal] (h : N = M) :
    (Subgroup.center (Y ⧸ N)).comap (QuotientGroup.mk' N) =
      (Subgroup.center (Y ⧸ M)).comap (QuotientGroup.mk' M) := by
  subst h
  rfl

private theorem primeComplementCore_comap_inclusion_eq {p : ℕ} (hp : p.Prime)
    {K H : Subgroup G} (hKH : K ≤ H) (hN : (K.subgroupOf H).Normal) :
    (primeComplementCore (G := ↥H) p).comap (Subgroup.inclusion hKH) =
      primeComplementCore (G := ↥K) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSchar : (primeComplementCore (G := ↥K) p).Characteristic :=
    CFSG.pPrimeCore_characteristic
  have hSmap_normal : ((primeComplementCore (G := ↥K) p).map
      (Subgroup.inclusion hKH)).Normal := by
    let e : ↥K ≃* ↥(K.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hKH).symm
    have hchar : ((primeComplementCore (G := ↥K) p).map e.toMonoidHom).Characteristic :=
      (CFSG.CGT.PushingUpLit.characteristic_map_mulEquiv_iff e).mpr hSchar
    have h := ConjAct.normal_of_characteristic_of_normal (H := K.subgroupOf H)
      (K := (primeComplementCore (G := ↥K) p).map e.toMonoidHom)
    have hcomp : (K.subgroupOf H).subtype.comp e.toMonoidHom = Subgroup.inclusion hKH := by
      ext x
      rfl
    rwa [Subgroup.map_map, hcomp] at h
  apply le_antisymm
  · have hnorm : ((primeComplementCore (G := ↥H) p).comap
        (Subgroup.inclusion hKH)).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hcop : Nat.Coprime p (Nat.card ↥((primeComplementCore (G := ↥H) p).comap
        (Subgroup.inclusion hKH))) :=
      Nat.Coprime.of_dvd_right
        (Subgroup.card_comap_dvd_of_injective (primeComplementCore (G := ↥H) p)
          (Subgroup.inclusion hKH) (Subgroup.inclusion_injective hKH))
        CFSG.pPrimeCore_coprime_card
    exact le_sSup ⟨hnorm, hcop⟩
  · intro x hx
    have hSmap_coprime : Nat.Coprime p (Nat.card ↥((primeComplementCore (G := ↥K) p).map
        (Subgroup.inclusion hKH))) := by
      rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKH)]
      exact CFSG.pPrimeCore_coprime_card
    have hle : (primeComplementCore (G := ↥K) p).map (Subgroup.inclusion hKH) ≤
        primeComplementCore (G := ↥H) p := le_sSup ⟨hSmap_normal, hSmap_coprime⟩
    exact hle (Subgroup.mem_map_of_mem (Subgroup.inclusion hKH) hx)

private theorem p_dvd_card_sSup_order_p (h : TwelveCtx G M p Q H) :
    p ∣ Nat.card ↥(sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}) := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨n, hn⟩ := h.Q_isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have hsub : Subsingleton ↥Q := (Nat.card_eq_one_iff_unique.mp hn).1
    refine h.Q_ne_bot (eq_bot_iff.mpr fun x hx => ?_)
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥Q) 1)
  have hdvdQ : p ∣ Nat.card Q := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) p hdvdQ
  have hxord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hxcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers, hxord]
  have hmem : Subgroup.zpowers (x : G) ∈ {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} :=
    ⟨Subgroup.zpowers_le.mpr (h.Q_le_H x.2), hxcard⟩
  have hle : Subgroup.zpowers (x : G) ≤
      sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} := le_sSup hmem
  simpa [hxcard] using Subgroup.card_dvd_of_le hle

private theorem p_dvd_card_of_isPComponentIn_not_le (h : TwelveCtx G M p Q H)
    {Y : Subgroup G} (hY : IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) : p ∣ Nat.card Y := by
  classical
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  have hOpM : relPPrimeCore p H ≤ M := by
    obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
    exact relPPrimeCore_le_of_gamma (Q := Q) h.p_prime (hEQ.trans h.Q_le_H) hE hEc hΓ
  by_contra hpY
  have hcop : Nat.Coprime p (Nat.card Y) := h.p_prime.coprime_iff_not_dvd.mpr hpY
  obtain ⟨K, hKcomp, hKsub, hrest⟩ := hY.2
  have hcop' : Nat.Coprime p (Nat.card ↥(Y.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY.1).toEquiv]
    exact hcop
  have hle : Y.subgroupOf H ≤ CFSG.pPrimeCore p ↥H :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hKsub hcop'
  have hleY : Y ≤ (CFSG.pPrimeCore p ↥H).map H.subtype := by
    calc Y = (Y.subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hY.1).symm
      _ ≤ _ := Subgroup.map_mono hle
  have hrel : (CFSG.pPrimeCore p ↥H).map H.subtype = relPPrimeCore p H :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      h.p_prime H).symm
  exact hYM (hrel ▸ hleY |>.trans hOpM)

private theorem p_dvd_card_kSub (h : TwelveCtx G M p Q H)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H) : p ∣ Nat.card (kSub p M H) := by
  classical
  have hKne : kSub p M H ≠ ⊥ := by
    intro hbot
    have hqO : CFSG.Open.IsQuasisimple
        (↥(kSub p M H) ⧸ pCore 2 ↥(kSub p M H)) :=
      ⟨hK.2.2.1.1.commutator_eq_top, hK.2.2.1.2.1⟩
    haveI : Nontrivial (↥(kSub p M H) ⧸ pCore 2 ↥(kSub p M H)) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hqO
    haveI : Subsingleton (↥(kSub p M H) ⧸ pCore 2 ↥(kSub p M H)) := by
      rw [hbot, QuotientGroup.subsingleton_iff, eq_top_iff']
      intro x
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
      rw [hx]
      exact one_mem _
    exact not_subsingleton (↥(kSub p M H) ⧸ pCore 2 ↥(kSub p M H)) inferInstance
  rw [kSub]
  split_ifs with hL
  · exact p_dvd_card_sSup_order_p h
  · have hne : sSup {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} ≠ ⊥ := by
      simpa only [kSub, if_neg hL] using hKne
    have hSne : ({Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} :
        Set (Subgroup G)).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      exact hne (by rw [hcon]; exact sSup_empty)
    obtain ⟨Y, hY⟩ := hSne
    exact (p_dvd_card_of_isPComponentIn_not_le h hY.1 hY.2).trans
      (Subgroup.card_dvd_of_le (le_sSup hY))

private theorem eq_top_of_map_quotient_eq_top {Y : Type} [Group Y] {N M : Subgroup Y}
    [N.Normal] (hNM : N ≤ M) (h : M.map (QuotientGroup.mk' N) = ⊤) : M = ⊤ := by
  rw [eq_top_iff]
  intro k hk
  have hmem : QuotientGroup.mk' N k ∈ M.map (QuotientGroup.mk' N) := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨o, ho, hok⟩ := Subgroup.mem_map.mp hmem
  have h1 : o⁻¹ * k ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) (o⁻¹ * k)).mp
    change QuotientGroup.mk' N (o⁻¹ * k) = 1
    rw [map_mul, map_inv, hok, inv_mul_cancel]
  have hk_eq : k = o * (o⁻¹ * k) := by group
  rw [hk_eq]
  exact M.mul_mem ho (hNM h1)

private theorem primeComplementCore_ne_top {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card K) :
    primeComplementCore (G := K) p ≠ ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro htop
  have hcard : Nat.card K = Nat.card ↥(primeComplementCore (G := K) p) := by
    rw [htop, Subgroup.card_top]
  have hcop : Nat.Coprime p (Nat.card K) := by
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hone : p = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hdvd
  exact hp.ne_one hone

private theorem comap_center_quotient_eq_of_central_proper {Y : Type} [Group Y]
    {N M : Subgroup Y} [N.Normal] [M.Normal] (hNM : N ≤ M)
    (hperf : Group.IsPerfect (Y ⧸ N))
    (hcentral : M.map (QuotientGroup.mk' N) ≤ Subgroup.center (Y ⧸ N)) :
    (Subgroup.center (Y ⧸ M)).comap (QuotientGroup.mk' M) =
      (Subgroup.center (Y ⧸ N)).comap (QuotientGroup.mk' N) := by
  haveI : Group.IsPerfect (Y ⧸ N) := hperf
  let C : Subgroup (Y ⧸ N) := M.map (QuotientGroup.mk' N)
  haveI hCnorm : C.Normal :=
    (inferInstance : M.Normal).map _ (QuotientGroup.mk'_surjective _)
  have hCpre : C.comap (QuotientGroup.mk' N) = M :=
    Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
  have hZ : (Subgroup.center ((Y ⧸ N) ⧸ C)).comap (QuotientGroup.mk' C) =
      Subgroup.center (Y ⧸ N) :=
    CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
      (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact hcentral)
  have h := (QuotientGroup.comap_comap_center (G := Y) (H₁ := N) (H₂ := C)).trans
    (comap_center_quotient_congr hCpre)
  rw [hZ] at h
  exact h.symm

private theorem xSub_subgroupOf_kSub_eq_center_complement (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) :
    (xSub p M H).subgroupOf (kSub p M H) =
      (Subgroup.center (↥(kSub p M H) ⧸
        primeComplementCore (G := ↥(kSub p M H)) p)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥(kSub p M H)) p)) := by
  classical
  let K : Subgroup G := kSub p M H
  let ι : ↥K →* ↥H := Subgroup.inclusion
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H)
  let Op : Subgroup ↥K := primeComplementCore (G := ↥K) p
  let π : ↥H →* (↥H ⧸ primeComplementCore (G := ↥H) p) :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hxsub : (xSub p M H).subgroupOf H =
      (Subgroup.centralizer (kStar p M H :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p))).comap π := by
    rw [xSub, CFSG.AGLEmbedding.d1PlusCore]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hstep : (xSub p M H).subgroupOf K =
      (Subgroup.centralizer (kStar p M H :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p))).comap (π.comp ι) := by
    rw [← Subgroup.comap_comap, ← hxsub]
    ext x
    rfl
  have hker : (π.comp ι).ker = Op := by
    have h1 : (π.comp ι).ker = (primeComplementCore (G := ↥H) p).comap ι := by
      ext x
      change π (ι x) = 1 ↔ ι x ∈ primeComplementCore (G := ↥H) p
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact primeComplementCore_comap_inclusion_eq h.p_prime
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H) hKH
  have hrange : (π.comp ι).range = kStar p M H := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hstep2 : (xSub p M H).subgroupOf K =
      (Subgroup.center (↥K ⧸ (π.comp ι).ker)).comap
        (QuotientGroup.mk' (π.comp ι).ker) := by
    rw [hstep, ← hrange]
    exact comap_centralizer_range_eq_center_quotient (f := π.comp ι)
  exact hstep2.trans (comap_center_quotient_congr hker)

private theorem center_modPrimeComplement_eq_center_modTwoCore (h : TwelveCtx G M p Q H)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    (Subgroup.center (↥(kSub p M H) ⧸
        primeComplementCore (G := ↥(kSub p M H)) p)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥(kSub p M H)) p)) =
      (Subgroup.center (modTwoCore (kSub p M H))).comap
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H))) := by
  classical
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  let K : Subgroup G := kSub p M H
  let O2 : Subgroup ↥K := pCore 2 ↥K
  let Op : Subgroup ↥K := primeComplementCore (G := ↥K) p
  have hqO : CFSG.Open.IsQuasisimple (↥K ⧸ O2) :=
    ⟨hK.2.2.1.1.commutator_eq_top, hK.2.2.1.2.1⟩
  haveI hperf : Group.IsPerfect (↥K ⧸ O2) := ⟨hqO.1⟩
  have hpdvd : p ∣ Nat.card ↥K := p_dvd_card_kSub h hK
  have hO2Op : O2 ≤ Op := by
    refine le_sSup ⟨inferInstance, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp2g : IsPGroup 2 O2 := CFSG.pCore_isPGroup
    obtain ⟨n, hn⟩ := hp2g.exists_card_eq
    rw [hn]
    have hp2 : Nat.Coprime p 2 :=
      h.p_prime.coprime_iff_not_dvd.mpr fun hd =>
        h.p_odd (Nat.prime_dvd_prime_iff_eq h.p_prime Nat.prime_two |>.mp hd)
    exact hp2.pow_right n
  have hOp_ne_top : Op ≠ ⊤ := primeComplementCore_ne_top h.p_prime hpdvd
  let C : Subgroup (↥K ⧸ O2) := Op.map (QuotientGroup.mk' O2)
  haveI hCnorm : C.Normal :=
    (inferInstance : Op.Normal).map _ (QuotientGroup.mk'_surjective _)
  have hCcentral : C ≤ Subgroup.center (↥K ⧸ O2) :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hqO C
      (fun htop => hOp_ne_top (eq_top_of_map_quotient_eq_top hO2Op htop))
  exact comap_center_quotient_eq_of_central_proper hO2Op hperf hCcentral

theorem TwelveCtx.xSub_subgroupOf_kSub_eq (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    (xSub p M H).subgroupOf (kSub p M H) =
      (center (modTwoCore (kSub p M H))).comap (QuotientGroup.mk' (pCore 2 ↥(kSub p M H))) :=
  (xSub_subgroupOf_kSub_eq_center_complement h hKH).trans
    (center_modPrimeComplement_eq_center_modTwoCore h hK)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
