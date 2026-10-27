module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.GroupTheory.Commutator.RelIndexLeFour
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueSetting
import CFSG.Sporadic.Recognition.JankoWongKleinOrder
public import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46W
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Layer0

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private lemma oddIn_le (H : Subgroup G) : oddIn H ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
private lemma oddIn_subgroupOf_eq_pPrimeCore (H : Subgroup G) :
    (oddIn H).subgroupOf H = pPrimeCore 2 ↥H := by
  rw [oddIn]
  exact Subgroup.subgroupOf_map_subtype_eq_self (pPrimeCore 2 ↥H)

private lemma l34SuzOdd_centralizer_le_normalizer (hS : L34SuzOddSetting A t) :
    centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G) :=
  fun _ hh => (CFSG.IsStandardSubgroup.standardComponentIsStandard hS.standard)
    |>.mem_normalizer_of_commute hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.mp hh)

private lemma exists_fixed_lift_centerQuotient {Y : Type} [Group Y] [Finite Y]
    (α : MulAut Y) (hα : α * α = 1)
    (hZ : Odd (Nat.card (Subgroup.center Y)))
    (β : MulAut (Y ⧸ Subgroup.center Y))
    (hβ : ∀ y : Y, β (QuotientGroup.mk' (Subgroup.center Y) y) =
      QuotientGroup.mk' (Subgroup.center Y) (α y))
    {x : Y ⧸ Subgroup.center Y} (hx : β x = x) :
    ∃ c : Y, α c = c ∧ QuotientGroup.mk' (Subgroup.center Y) c = x := by
  let N : Subgroup Y := Subgroup.center Y
  have hN : N ≤ N.comap α := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (Subgroup.centerCharacteristic (G := Y)) α
    change α z ∈ Subgroup.center Y
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨z, by simpa [N] using hz, rfl⟩
  have hα2 : ∀ y, α (α y) = y := by
    intro y
    have h := congrArg (fun f : MulAut Y => f y) hα
    simpa using h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hxmap : QuotientGroup.map N N α hN (QuotientGroup.mk' N a) =
      QuotientGroup.mk' N a := by
    change (QuotientGroup.mk' (Subgroup.center Y)) (α a) =
      (QuotientGroup.mk' (Subgroup.center Y)) a
    rw [← hβ a]
    exact hx
  exact CFSG.Sporadic.Recognition.JankoWong.KleinOrder.exists_fixed_lift
    hZ hα2 hN hxmap

private lemma eq_one_or_eq_of_mem_oddIn_sup_zpowers {H : Subgroup G} {t x : G}
    (hHt : t ∈ H) (hHct : ∀ h ∈ H, h * t = t * h) (ht : orderOf t = 2)
    (hxH : x ∈ H) (hx2 : x * x = 1)
    (hx : x ∈ oddIn H ⊔ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  let D : Subgroup ↥H := (oddIn H).subgroupOf H
  let T : Subgroup ↥H := (Subgroup.zpowers t).subgroupOf H
  have hDnorm : D.Normal := by
    rw [show D = CFSG.pPrimeCore 2 ↥H from oddIn_subgroupOf_eq_pPrimeCore H]; infer_instance
  have hsup : (oddIn H ⊔ Subgroup.zpowers t).subgroupOf H = D ⊔ T := by
    rw [Subgroup.subgroupOf_sup (oddIn_le H) (Subgroup.zpowers_le.mpr hHt)]
  have hx' : (⟨x, hxH⟩ : ↥H) ∈ D ⊔ T := by
    rw [← hsup]
    exact hx
  have : D.Normal := hDnorm
  obtain ⟨d, hd, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hxyG : (d : G) * (y : G) = x := congrArg Subtype.val hxy
  have hdO : (d : G) ∈ oddIn H := Subgroup.mem_subgroupOf.mp hd
  have hdOdd : Odd (orderOf (d : G)) :=
    Odd.of_dvd_nat (odd_card_oddIn H)
      (Subgroup.orderOf_dvd_natCard (oddIn H) hdO)
  have hyEq : (y : G) = 1 ∨ (y : G) = t :=
    CFSG.Semidihedral.EscapingCentralizer.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two
      ht (Subgroup.mem_subgroupOf.mp hy)
  have hd_comm : (d : G) * t = t * (d : G) := hHct d (oddIn_le H hdO)
  have hd_one_of_sq : (d : G) * (d : G) = 1 → (d : G) = 1 := by
    intro hdd
    have hdvd : orderOf (d : G) ∣ 2 := by
      simpa [pow_two] using orderOf_dvd_of_pow_eq_one (show (d : G) ^ 2 = 1 by
        simpa [pow_two] using hdd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_right.mpr hdOdd) (dvd_refl _) hdvd)
  rcases hyEq with hy1 | hyt
  · left
    have hx_d : x = (d : G) := by rw [← hxyG, hy1, mul_one]
    rw [hx_d]
    apply hd_one_of_sq
    simpa [hx_d] using hx2
  · right
    have hx_dt : x = (d : G) * t := by rw [← hxyG, hyt]
    rw [hx_dt] at hx2
    have hx2' : ((d : G) * t) * ((d : G) * t) = 1 := by
      simpa [hx_dt] using hx2
    have htt : t * t = 1 := by simpa [pow_two, ht] using pow_orderOf_eq_one t
    have hdd : (d : G) * (d : G) = 1 := by
      calc (d : G) * (d : G)
          = ((d : G) * t) * ((d : G) * t) := by
            rw [show (d : G) * (d : G) = ((d : G) * t) * ((d : G) * t) by
              rw [mul_assoc, ← mul_assoc t (d : G) t, ← hd_comm, mul_assoc, htt, mul_one]]
        _ = 1 := hx2'
    rw [hd_one_of_sq hdd, one_mul] at hx_dt
    exact hx_dt

private lemma even_card_of_isSporadic_suz
    {Y : Type} [Group Y] (h : Blueprint.NativeSporadic.IsSporadic Y .Suz) :
    Even (Nat.card Y) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Even (Nat.card Blueprint.NativeSporadic.Suz)
  rw [CFSG.Sporadic.Suz.card_Suz]
  norm_num

private lemma oddIn_le_centralizer_of_quasisimple {H A : Subgroup G}
    (hAH : A ≤ H) (hHN : H ≤ Subgroup.normalizer (A : Set G))
    (hqA : IsQuasisimple A) (hAnotOdd : ¬ Odd (Nat.card ↥A)) :
    oddIn H ≤ Subgroup.centralizer (A : Set G) := by
  let D : Subgroup G := oddIn H
  have hDH : D ≤ H := oddIn_le H
  have hDnorm : (D.subgroupOf H).Normal := by
    rw [oddIn_subgroupOf_eq_pPrimeCore]
    infer_instance
  have : (D.subgroupOf H).Normal := hDnorm
  have hHN_D : H ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hDH
  have hAN_D : A ≤ Subgroup.normalizer (D : Set G) := hAH.trans hHN_D
  have hDN_A : D ≤ Subgroup.normalizer (A : Set G) := hDH.trans hHN
  have hcommD : ⁅D, A⁆ ≤ D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAN_D
  have hcommA : ⁅D, A⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hDN_A
  have hcomm : ⁅D, A⁆ ≤ D ⊓ A := le_inf hcommD hcommA
  have hDodd : Odd (Nat.card D) := odd_card_oddIn H
  have hIodd : Odd (Nat.card ↥(D ⊓ A)) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le (K := D) inf_le_left)
  have hnormInf : ((D ⊓ A).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    refine (le_inf hAN_D Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain htop | hle := CFSG.LocalCores.quasisimple_normal_subgroups hqA hnormInf
  · exfalso
    have hcard : Nat.card ↥((D ⊓ A).subgroupOf A) = Nat.card ↥(D ⊓ A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [htop, Subgroup.card_top] at hcard
    exact hAnotOdd (hcard ▸ hIodd)
  have hleZ : D ⊓ A ≤ (Subgroup.center ↥A).map A.subtype := by
    have hmap := Subgroup.map_mono (f := A.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at hmap
  have hcommZ : ⁅D, A⁆ ≤ (Subgroup.center ↥A).map A.subtype := hcomm.trans hleZ
  have hcenter_le : (Subgroup.center ↥A).map A.subtype ≤
      Subgroup.centralizer (A : Set G) := by
    rintro z ⟨z₀, hz₀, rfl⟩ a ha
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨a, ha⟩)
  have hdouble : ⁅⁅A, D⁆, A⁆ = ⊥ := by
    have h1 : ⁅⁅A, D⁆, A⁆ ≤ ⁅((Subgroup.center ↥A).map A.subtype), A⁆ := by
      rw [Subgroup.commutator_comm A D]
      exact Subgroup.commutator_mono hcommZ le_rfl
    have h2 : ⁅((Subgroup.center ↥A).map A.subtype), A⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcenter_le
    exact le_antisymm (h2 ▸ h1) bot_le
  have hperfA : Group.IsPerfect ↥A := hqA.1
  have hADbot : ⁅A, D⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hperfA hdouble
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hADbot

private lemma not_odd_card_of_isSporadic_suz
    {Y : Type} [Group Y] [Finite Y]
    (h : Blueprint.NativeSporadic.IsSporadic (Y ⧸ Subgroup.center Y) .Suz) :
    ¬ Odd (Nat.card Y) := by
  intro hodd
  have hquot : Odd (Nat.card (Y ⧸ Subgroup.center Y)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)] at hodd
    exact Nat.Odd.of_mul_left hodd
  exact (Nat.not_odd_iff_even.mpr (even_card_of_isSporadic_suz h)) hquot

private lemma card_outer_le_two_of_isSporadic_suz
    {Y : Type} [Group Y] [Finite Y] (hq : IsQuasisimple Y)
    (h : Blueprint.NativeSporadic.IsSporadic (Y ⧸ Subgroup.center Y) .Suz) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ≤ 2 := by
  have : Group.IsPerfect Y := hq.1
  have hinj : Function.Injective
      (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom Y) :=
    CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective Y
  have hcard := Nat.card_le_card_of_injective
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom Y) hinj
  have hcardQ : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    have hdvd : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (Y ⧸ Subgroup.center Y)).index ∣ 2 := by
      simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner,
        CFSG.EvenSporadicStandard.Finkelstein77.innAut] using
        CFSG.EvenSporadicStandard.TwoSuz.index_dvd_two_of_isSporadic_suz h
    have hEq : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Y ⧸ Subgroup.center Y)) =
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (Y ⧸ Subgroup.center Y)).index :=
      (Subgroup.index_eq_card
        (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
          (Y ⧸ Subgroup.center Y))).symm
    rw [hEq]
    exact Nat.le_of_dvd (by norm_num) hdvd
  exact hcard.trans hcardQ

private lemma l34SuzOdd_oddCore_index_two_centralizer (hS : L34SuzOddSetting A t) :
    ∃ M : Subgroup ↥(centralizer (A : Set G)),
      M.Normal ∧ M.index = 2 ∧
        M = CFSG.pPrimeCore 2 ↥(centralizer (A : Set G)) ∧
        (⟨t, hS.t_mem⟩ : ↥(centralizer (A : Set G))) ∉ M ∧
        M ⊔ Subgroup.zpowers (⟨t, hS.t_mem⟩ : ↥(centralizer (A : Set G))) = ⊤ := by
  classical
  let X : Subgroup G := centralizer (A : Set G)
  let S : Sylow 2 ↥X := Classical.choice Sylow.nonempty
  have hScard : Nat.card (S : Subgroup ↥X) = 2 := hS.card_sylow S
  obtain ⟨-, M, hMnorm, hModd, hMindex, hMeq⟩ :=
    CFSG.Semidihedral.EscapingCentralizer.odd_core_index_two_of_sylow_two_card_two S hScard
  have htX_notM : (⟨t, hS.t_mem⟩ : ↥X) ∉ M := by
    intro hmem
    have hdvd : orderOf (⟨t, hS.t_mem⟩ : ↥X) ∣ Nat.card ↥M :=
      Subgroup.orderOf_dvd_natCard M hmem
    have hord : orderOf (⟨t, hS.t_mem⟩ : ↥X) = 2 := by
      simpa using hS.orderOf_t
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hModd) (even_iff_two_dvd.mpr hdvd)
  have : M.Normal := hMnorm
  have htopX : M ⊔ Subgroup.zpowers (⟨t, hS.t_mem⟩ : ↥X) = ⊤ :=
    CFSG.Fischer.eq_top_of_index_two hMindex le_sup_left
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (⟨t, hS.t_mem⟩ : ↥X))) htX_notM
  exact ⟨M, hMnorm, hMindex, hMeq, htX_notM, htopX⟩

private lemma l34SuzOdd_centralizer_eq_oddIn_sup_zpowers (hS : L34SuzOddSetting A t)
    {M : Subgroup ↥(centralizer (A : Set G))}
    (hMeq : M = CFSG.pPrimeCore 2 ↥(centralizer (A : Set G)))
    (htop : M ⊔ Subgroup.zpowers (⟨t, hS.t_mem⟩ : ↥(centralizer (A : Set G))) = ⊤) :
    centralizer (A : Set G) = oddIn (centralizer (A : Set G)) ⊔ Subgroup.zpowers t := by
  let X : Subgroup G := centralizer (A : Set G)
  have hmap := congrArg (fun P : Subgroup ↥X => P.map X.subtype) htop
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hMeq, Subgroup.map_top,
    Subgroup.range_subtype] at hmap
  simpa [oddIn, X] using hmap.symm

private lemma l34SuzOdd_oddIn_inf_centralizer_eq
    (hS : L34SuzOddSetting A t)
    {M : Subgroup ↥(centralizer (A : Set G))} (hMnorm : M.Normal)
    (hMindex : M.index = 2)
    (hMeq : M = CFSG.pPrimeCore 2 ↥(centralizer (A : Set G))) :
    oddIn (centralizer (A : Set G)) ⊓ centralizer ({t} : Set G) =
      oddIn (centralizer ({t} : Set G)) := by
  classical
  let X : Subgroup G := centralizer (A : Set G)
  let H : Subgroup G := centralizer ({t} : Set G)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem a ha
  have hHnorm : H ≤ Subgroup.normalizer (A : Set G) :=
    l34SuzOdd_centralizer_le_normalizer hS
  have hAnotOdd : ¬ Odd (Nat.card ↥A) :=
    not_odd_card_of_isSporadic_suz hS.suz
  have hDleX : oddIn H ≤ X :=
    oddIn_le_centralizer_of_quasisimple hA_le_H hHnorm hS.standard.1 hAnotOdd
  have hHNX : H ≤ Subgroup.normalizer (X : Set G) :=
    hHnorm.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A)
  have : M.Normal := hMnorm
  have hDleOX : oddIn H ≤ oddIn X := by
    intro d hd
    have hdX : d ∈ X := hDleX hd
    have hodd : Odd (orderOf d) :=
      Odd.of_dvd_nat (odd_card_oddIn H) (Subgroup.orderOf_dvd_natCard (oddIn H) hd)
    have hgord : Odd (orderOf (⟨d, hdX⟩ : ↥X)) := by simpa using hodd
    have hdM : (⟨d, hdX⟩ : ↥X) ∈ M :=
      CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_two_pow_index M
        ⟨1, by rw [hMindex]; norm_num⟩ hgord
    rw [oddIn]
    exact ⟨⟨d, hdX⟩, by rwa [hMeq] at hdM, rfl⟩
  have hKnorm : ((oddIn X ⊓ H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    have h1 : H ≤ Subgroup.normalizer (oddIn X : Set G) :=
      hHNX.trans (CFSG.ComponentClassification.GrSLit.GrS5.normalizer_le_normalizer_oddIn X)
    have h2 : H ≤ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKodd : Odd (Nat.card ↥(oddIn X ⊓ H)) :=
    Odd.of_dvd_nat (odd_card_oddIn X)
      (Subgroup.card_dvd_of_le (H := oddIn X ⊓ H) (K := oddIn X) inf_le_left)
  have hOeq : oddIn X ⊓ H = oddIn H := by
    refine le_antisymm ?_ ?_
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact subgroupOf_le_pPrimeCore_map (p := 2) inf_le_right
        (Nat.coprime_two_left.mpr hKodd)
    · intro d hd
      exact ⟨hDleOX hd, oddIn_le H hd⟩
  exact hOeq

private lemma l34SuzOdd_mem_sup_of_notMem_oddCore (hS : L34SuzOddSetting A t)
    {M : Subgroup ↥(centralizer (A : Set G))} (hMnorm : M.Normal)
    (hMindex : M.index = 2)
    (hMeq : M = CFSG.pPrimeCore 2 ↥(centralizer (A : Set G)))
    (htX_notM : (⟨t, hS.t_mem⟩ : ↥(centralizer (A : Set G))) ∉ M)
    {x : G} (hxX : x ∈ centralizer (A : Set G))
    (hxH : x ∈ centralizer ({t} : Set G))
    (hxM : (⟨x, hxX⟩ : ↥(centralizer (A : Set G))) ∉ M) :
    x ∈ (oddIn (centralizer (A : Set G)) ⊓ centralizer ({t} : Set G)) ⊔
      Subgroup.zpowers t := by
  classical
  let X : Subgroup G := centralizer (A : Set G)
  let H : Subgroup G := centralizer ({t} : Set G)
  have : M.Normal := hMnorm
  let q : ↥X →* ↥X ⧸ M := QuotientGroup.mk' M
  have hQcard : Nat.card (↥X ⧸ M) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hMindex
  have huniq := (Nat.card_eq_two_iff' (1 : ↥X ⧸ M)).mp hQcard
  obtain ⟨y, hy, hyuniq⟩ := huniq
  have ht_sq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.orderOf_t, pow_two] at h
    exact h
  have htx_sq : (⟨t, hS.t_mem⟩ : ↥X) * (⟨t, hS.t_mem⟩ : ↥X) = 1 := by
    apply Subtype.ext
    simpa using ht_sq
  have hqne : q (⟨t, hS.t_mem⟩ : ↥X) ≠ 1 := by
    rw [show q (⟨t, hS.t_mem⟩ : ↥X) = QuotientGroup.mk (⟨t, hS.t_mem⟩ : ↥X) from rfl,
      Ne, QuotientGroup.eq_one_iff]
    exact htX_notM
  have hqt : q (⟨t, hS.t_mem⟩ : ↥X) = y := hyuniq _ hqne
  have hqxne : q (⟨x, hxX⟩ : ↥X) ≠ 1 := by
    rw [show q (⟨x, hxX⟩ : ↥X) = QuotientGroup.mk (⟨x, hxX⟩ : ↥X) from rfl,
      Ne, QuotientGroup.eq_one_iff]
    exact hxM
  have hqx : q (⟨x, hxX⟩ : ↥X) = y := hyuniq _ hqxne
  have hxtM : (⟨x, hxX⟩ : ↥X) * (⟨t, hS.t_mem⟩ : ↥X) ∈ M := by
    have hq1 : q ((⟨x, hxX⟩ : ↥X) * (⟨t, hS.t_mem⟩ : ↥X)) = 1 := by
      rw [map_mul, hqx, hqt, ← hqt, ← map_mul, htx_sq, map_one]
    exact (QuotientGroup.eq_one_iff _).mp (by
      change q ((⟨x, hxX⟩ : ↥X) * (⟨t, hS.t_mem⟩ : ↥X)) = 1
      exact hq1)
  have hxtH : x * t ∈ H :=
    mul_mem hxH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hxtO : x * t ∈ oddIn X := by
    rw [oddIn]
    exact ⟨(⟨x, hxX⟩ : ↥X) * (⟨t, hS.t_mem⟩ : ↥X), by rwa [hMeq] at hxtM, rfl⟩
  have hmem : x * t ∈ oddIn X ⊓ H := ⟨hxtO, hxtH⟩
  have hxeq : x = (x * t) * t := by
    rw [mul_assoc, ht_sq, mul_one]
  rw [hxeq]
  exact mul_mem (Subgroup.mem_sup_left hmem)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

private lemma l34SuzOdd_sup_inf_centralizer_eq (hS : L34SuzOddSetting A t)
    {M : Subgroup ↥(centralizer (A : Set G))} (hMnorm : M.Normal)
    (hMindex : M.index = 2)
    (hMeq : M = CFSG.pPrimeCore 2 ↥(centralizer (A : Set G)))
    (htX_notM : (⟨t, hS.t_mem⟩ : ↥(centralizer (A : Set G))) ∉ M) :
    (oddIn (centralizer (A : Set G)) ⊔ Subgroup.zpowers t) ⊓ centralizer ({t} : Set G) =
      (oddIn (centralizer (A : Set G)) ⊓ centralizer ({t} : Set G)) ⊔ Subgroup.zpowers t := by
  classical
  let X : Subgroup G := centralizer (A : Set G)
  let H : Subgroup G := centralizer ({t} : Set G)
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxAB, hxH⟩
    have hxX : x ∈ X := (sup_le (oddIn_le X) (Subgroup.zpowers_le.mpr hS.t_mem)) hxAB
    by_cases hxM : (⟨x, hxX⟩ : ↥X) ∈ M
    · have hxO : x ∈ oddIn X := by
        rw [oddIn]
        exact ⟨⟨x, hxX⟩, by rwa [hMeq] at hxM, rfl⟩
      have hx1 : x = x * 1 := by simp
      rw [hx1]
      exact mul_mem (Subgroup.mem_sup_left ⟨hxO, hxH⟩)
        (Subgroup.mem_sup_right (Subgroup.one_mem _))
    · exact l34SuzOdd_mem_sup_of_notMem_oddCore hS hMnorm hMindex hMeq htX_notM hxX hxH hxM
  · refine sup_le ?_ ?_
    · exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
    · exact le_inf le_sup_right (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl))

theorem centralizer_inf_centralizer_eq_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) :
    centralizer ({t} : Set G) ⊓ centralizer (A : Set G) =
      oddIn (centralizer ({t} : Set G)) ⊔ zpowers t := by
  classical
  let X : Subgroup G := centralizer (A : Set G)
  let H : Subgroup G := centralizer ({t} : Set G)
  obtain ⟨M, hMnorm, hMindex, hMeq, htX_notM, htop⟩ :=
    l34SuzOdd_oddCore_index_two_centralizer hS
  have hXeq : X = oddIn X ⊔ Subgroup.zpowers t :=
    l34SuzOdd_centralizer_eq_oddIn_sup_zpowers hS hMeq htop
  have hOeq : oddIn X ⊓ H = oddIn H :=
    l34SuzOdd_oddIn_inf_centralizer_eq hS hMnorm hMindex hMeq
  have hstep : (oddIn X ⊔ Subgroup.zpowers t) ⊓ H =
      (oddIn X ⊓ H) ⊔ Subgroup.zpowers t :=
    l34SuzOdd_sup_inf_centralizer_eq hS hMnorm hMindex hMeq htX_notM
  calc
    centralizer ({t} : Set G) ⊓ centralizer (A : Set G) = X ⊓ H := by rw [inf_comm]
    _ = (oddIn X ⊔ Subgroup.zpowers t) ⊓ H := by
      conv_lhs => rw [hXeq]
    _ = (oddIn X ⊓ H) ⊔ Subgroup.zpowers t := hstep
    _ = oddIn H ⊔ Subgroup.zpowers t := by rw [hOeq]

private lemma l34SuzOdd_notMem_sup_oddIn (hS : L34SuzOddSetting A t)
    (hDcentA : oddIn (centralizer ({t} : Set G)) ≤ Subgroup.centralizer (A : Set G)) :
    t ∉ A ⊔ oddIn (centralizer ({t} : Set G)) := by
  let H : Subgroup G := centralizer ({t} : Set G)
  let D : Subgroup G := oddIn H
  intro htAD
  obtain ⟨a, ha, d, hd, htk⟩ :=
    CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hDcentA htAD
  have hdC : d ∈ Subgroup.centralizer (A : Set G) := hDcentA hd
  have haC : a ∈ Subgroup.centralizer (A : Set G) := by
    have haeq : a = t * d⁻¹ := by rw [htk]; group
    rw [haeq]
    exact mul_mem hS.t_mem (inv_mem hdC)
  have haZ : a ∈ (Subgroup.center ↥A).map A.subtype := by
    rw [CFSG.EvenSporadicStandard.map_center_eq_inf_centralizer]
    exact ⟨ha, haC⟩
  obtain ⟨z, hz, hza⟩ := haZ
  have haOdd : Odd (orderOf a) := by
    rw [← hza]
    have hzdvd : orderOf (A.subtype z) ∣ Nat.card ↥(Subgroup.center ↥A) := by
      simpa using Subgroup.orderOf_dvd_natCard (Subgroup.center ↥A) hz
    exact Odd.of_dvd_nat hS.odd_card_center hzdvd
  have hdOdd : Odd (orderOf d) :=
    Odd.of_dvd_nat (odd_card_oddIn H) (Subgroup.orderOf_dvd_natCard D hd)
  have hcomm : Commute a d := Subgroup.mem_centralizer_iff.mp hdC a ha
  have htodd : Odd (orderOf t) := by
    rw [htk]
    exact Odd.of_dvd_nat (Odd.mul haOdd hdOdd) hcomm.orderOf_mul_dvd_mul_orderOf
  rw [hS.orderOf_t] at htodd
  rcases htodd with ⟨k, hk⟩
  omega

private lemma l34SuzOdd_relIndex_sup_oddIn_le_two
    (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    (houter : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥A) ≤ 2) :
    (A ⊔ (oddIn (centralizer ({t} : Set G)) ⊔ Subgroup.zpowers t)).relIndex
      (centralizer ({t} : Set G)) ≤ 2 := by
  let H : Subgroup G := centralizer ({t} : Set G)
  let D : Subgroup G := oddIn H
  have hEq : H ⊓ (A ⊔ Subgroup.centralizer (A : Set G)) =
      A ⊔ (D ⊔ Subgroup.zpowers t) := by
    rw [CFSG.EvenSporadicStandard.centralizer_singleton_inf_sup_centralizer
      (L := A) hS.t_mem]
    have hinf : Subgroup.centralizer (A : Set G) ⊓ H = D ⊔ Subgroup.zpowers t := by
      rw [inf_comm]
      exact centralizer_inf_centralizer_eq_of_l34SuzOdd hS
    rw [hinf]
  rw [← hEq]
  have hdvd := CFSG.AGLEmbedding.relIndex_sup_centralizer_dvd_card_outer
    (L := A) (U := H) hHnorm
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans houter

private lemma l34SuzOdd_relIndex_sup_oddIn_eq_two (hS : L34SuzOddSetting A t)
    (hHNK : centralizer ({t} : Set G) ≤ Subgroup.normalizer
      ((A ⊔ oddIn (centralizer ({t} : Set G)) : Subgroup G) : Set G))
    (htK : t ∉ A ⊔ oddIn (centralizer ({t} : Set G))) :
    (A ⊔ oddIn (centralizer ({t} : Set G))).relIndex
      ((A ⊔ oddIn (centralizer ({t} : Set G))) ⊔ Subgroup.zpowers t) = 2 := by
  let H : Subgroup G := centralizer ({t} : Set G)
  let D : Subgroup G := oddIn H
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htN_K : t ∈ Subgroup.normalizer ((A ⊔ D : Subgroup G) : Set G) := hHNK htH
  have hcard_sup :=
    CFSG.ComponentClassification.GrSLit.GrS4.card_sup_mul_inf_eq_mul_of_normalizes
      (H := Subgroup.zpowers t) (K := A ⊔ D)
      (Subgroup.zpowers_le.mpr htN_K)
  have hinf_bot : (A ⊔ D) ⊓ Subgroup.zpowers t = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x = 1 ∨ x = t :=
      CFSG.Semidihedral.EscapingCentralizer.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two
        hS.orderOf_t hx.2
    rcases hx' with h1 | ht
    · rw [h1]
      exact Subgroup.one_mem ⊥
    · rw [ht] at hx
      exact absurd hx.1 htK
  have hcardL : Nat.card ↥((A ⊔ D) ⊔ Subgroup.zpowers t) =
      Nat.card ↥(A ⊔ D) * 2 := by
    have h := hcard_sup
    rw [inf_comm, sup_comm (Subgroup.zpowers t) (A ⊔ D), hinf_bot, Subgroup.card_bot,
      mul_one, Nat.card_zpowers, hS.orderOf_t, mul_comm] at h
    exact h
  have hrelK : (A ⊔ D).relIndex ((A ⊔ D) ⊔ Subgroup.zpowers t) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := A ⊔ D)
      (K := (A ⊔ D) ⊔ Subgroup.zpowers t)
    rw [inf_eq_left.mpr le_sup_left] at h1
    rw [hcardL] at h1
    have h1' : (A ⊔ D).relIndex ((A ⊔ D) ⊔ Subgroup.zpowers t) *
        Nat.card ↥(A ⊔ D) = 2 * Nat.card ↥(A ⊔ D) := by
      rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1'
  exact hrelK

theorem not_mem_commutator_centralizer_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) :
    t ∉ ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  let D : Subgroup G := oddIn H
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem a ha
  have hHnorm : H ≤ Subgroup.normalizer (A : Set G) :=
    l34SuzOdd_centralizer_le_normalizer hS
  have hAnotOdd : ¬ Odd (Nat.card ↥A) :=
    not_odd_card_of_isSporadic_suz hS.suz
  have hDcentA : D ≤ Subgroup.centralizer (A : Set G) :=
    oddIn_le_centralizer_of_quasisimple hA_le_H hHnorm hS.standard.1 hAnotOdd
  have hDnormH : (D.subgroupOf H).Normal := by
    rw [oddIn_subgroupOf_eq_pPrimeCore]
    infer_instance
  have : (D.subgroupOf H).Normal := hDnormH
  have hHN_D : H ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (oddIn_le H)
  have hK_le_H : A ⊔ D ≤ H := sup_le hA_le_H (oddIn_le H)
  have hHNK : H ≤ Subgroup.normalizer ((A ⊔ D : Subgroup G) : Set G) :=
    (le_inf hHnorm hHN_D).trans (Subgroup.inf_normalizer_le_normalizer_sup A D)
  have htK : t ∉ A ⊔ D := l34SuzOdd_notMem_sup_oddIn hS hDcentA
  have houter : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥A) ≤ 2 :=
    card_outer_le_two_of_isSporadic_suz hS.standard.1 hS.suz
  have hrelsup : (A ⊔ (D ⊔ Subgroup.zpowers t)).relIndex H ≤ 2 :=
    l34SuzOdd_relIndex_sup_oddIn_le_two hS hHnorm houter
  have hrelK : (A ⊔ D).relIndex ((A ⊔ D) ⊔ Subgroup.zpowers t) = 2 :=
    l34SuzOdd_relIndex_sup_oddIn_eq_two hS hHNK htK
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKleL : A ⊔ D ≤ (A ⊔ D) ⊔ Subgroup.zpowers t := le_sup_left
  have hLleH : (A ⊔ D) ⊔ Subgroup.zpowers t ≤ H :=
    sup_le hK_le_H (Subgroup.zpowers_le.mpr htH)
  have hrel4 : (A ⊔ D).relIndex H ≤ 4 := by
    have htower := (Subgroup.relIndex_mul_relIndex (A ⊔ D)
      ((A ⊔ D) ⊔ Subgroup.zpowers t) H hKleL hLleH).symm
    rw [htower, hrelK, sup_assoc]
    omega
  have hcomm_le : ⁅H, H⁆ ≤ A ⊔ D :=
    CFSG.GroupTheory.commutator_le_of_relIndex_le_four hHNK hrel4
  intro ht'
  exact htK (hcomm_le (by simpa [H] using ht'))

omit [Finite G] in
private lemma l34SuzOdd_centralizer_map_centerQuotient
    (hZ : Odd (Nat.card (Subgroup.center ↥A))) {v : G} (hv : v ∈ A)
    (hv2 : v * v = 1) :
    (Subgroup.centralizer ({⟨v, hv⟩} : Set ↥A)).map
        (QuotientGroup.mk' (Subgroup.center ↥A)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (Subgroup.center ↥A) ⟨v, hv⟩} :
          Set (↥A ⧸ Subgroup.center ↥A)) := by
  classical
  let vA : ↥A := ⟨v, hv⟩
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  have hvA2 : vA * vA = 1 := by
    apply Subtype.ext
    exact hv2
  refine le_antisymm ?_ ?_
  · have h := Subgroup.map_centralizer_le_centralizer_image ({vA} : Set ↥A) q
    simpa [q, vA] using h
  · have h := CFSG.Walter.Suzuki.centralizer_mk_le_map (O := Subgroup.center ↥A)
      hZ hvA2
    change Subgroup.centralizer
      ({(↑vA : ↥A ⧸ Subgroup.center ↥A)} : Set (↥A ⧸ Subgroup.center ↥A)) ≤
        (Subgroup.centralizer ({vA} : Set ↥A)).map
          (QuotientGroup.mk' (Subgroup.center ↥A))
    exact h

omit [Finite G] in
private lemma l34SuzOdd_image_perfect (hD : L34SuzOddData A V K y) (hKA : K ≤ A) :
    Group.IsPerfect ↥((K.subgroupOf A).map (QuotientGroup.mk' (Subgroup.center ↥A))) := by
  classical
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  let Kbar : Subgroup (↥A ⧸ Subgroup.center ↥A) := (K.subgroupOf A).map q
  have hKsub_perf : Group.IsPerfect ↥(K.subgroupOf A) := by
    have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hD.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKA).symm.surjective
  let f : ↥(K.subgroupOf A) →* (↥A ⧸ Subgroup.center ↥A) :=
    q.comp (K.subgroupOf A).subtype
  have hrange : ((⊤ : Subgroup ↥(K.subgroupOf A)).map f) = Kbar := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨(x : ↥A), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have h := Group.IsPerfect.map (H := (⊤ : Subgroup ↥(K.subgroupOf A))) (f := f)
  rwa [hrange] at h

omit [Finite G] in
private lemma l34SuzOdd_image_le_centralizer (hD : L34SuzOddData A V K y) {v : G}
    (hv : v ∈ V) (hKleCGV : K ≤ Subgroup.centralizer (V : Set G)) :
    (K.subgroupOf A).map (QuotientGroup.mk' (Subgroup.center ↥A)) ≤
      Subgroup.centralizer
        ({QuotientGroup.mk' (Subgroup.center ↥A) ⟨v, hD.le_A hv⟩} :
          Set (↥A ⧸ Subgroup.center ↥A)) := by
  rintro y ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← map_mul, ← map_mul]
  congr 1
  have hxv : (x : ↥A) * ⟨v, hD.le_A hv⟩ = ⟨v, hD.le_A hv⟩ * x := by
    apply Subtype.ext
    have hk : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    have hcomm : (x : G) * v = v * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp (hKleCGV hk) v hv).symm
    simpa using hcomm
  exact hxv

private lemma l34SuzOdd_suzPair_centerQuotient (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hKA : K ≤ A) (hKleCGV : K ≤ Subgroup.centralizer (V : Set G)) :
    CFSG.EvenSporadicStandard.Solomon78.SuzPair (↥A ⧸ Subgroup.center ↥A) ⊤
      ((K.subgroupOf A).map (QuotientGroup.mk' (Subgroup.center ↥A)))
      (QuotientGroup.mk' (Subgroup.center ↥A) ⟨v, hD.le_A hv⟩) := by
  classical
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  let vA : ↥A := ⟨v, hD.le_A hv⟩
  have hvA2 : vA * vA = 1 := by
    apply Subtype.ext
    exact hD.mul_self v hv
  have hvA_ne : vA ≠ 1 := by
    intro h
    exact hv1 (congrArg Subtype.val h)
  have hvAord : orderOf vA = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hvA2) hvA_ne
  have hq_ne : q vA ≠ 1 := by
    rw [show q vA = QuotientGroup.mk vA from rfl, Ne, QuotientGroup.eq_one_iff]
    intro hmem
    have hdvd : orderOf vA ∣ Nat.card ↥(Subgroup.center ↥A) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥A) hmem
    rw [hvAord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hS.odd_card_center) (even_iff_two_dvd.mpr hdvd)
  have hqv_ord : orderOf (q vA) = 2 := by
    have hq2 : q vA * q vA = 1 := by
      rw [← map_mul, hvA2, map_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hq2) hq_ne
  refine ⟨Subgroup.mem_top _, hqv_ord, le_top, ?_,
    l34SuzOdd_image_perfect hD hKA, hD.card_image⟩
  intro k hk
  have h := l34SuzOdd_image_le_centralizer hD hv hKleCGV hk
  rwa [Subgroup.mem_centralizer_singleton_iff] at h

private lemma l34SuzOdd_mem_commutator_of_mem_map (hS : L34SuzOddSetting A t)
    {v : G} (hv : v ∈ A) (hv2 : v * v = 1)
    (hvinMap : QuotientGroup.mk' (Subgroup.center ↥A) ⟨v, hv⟩ ∈
      (⁅Subgroup.centralizer ({⟨v, hv⟩} : Set ↥A),
        Subgroup.centralizer ({⟨v, hv⟩} : Set ↥A)⁆).map
        (QuotientGroup.mk' (Subgroup.center ↥A))) :
    ⟨v, hv⟩ ∈ ⁅Subgroup.centralizer ({⟨v, hv⟩} : Set ↥A),
        Subgroup.centralizer ({⟨v, hv⟩} : Set ↥A)⁆ := by
  classical
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  let vA : ↥A := ⟨v, hv⟩
  let CA : Subgroup ↥A := Subgroup.centralizer ({vA} : Set ↥A)
  have hvA2 : vA * vA = 1 := by
    apply Subtype.ext
    exact hv2
  have hvinMap' : q vA ∈ (⁅CA, CA⁆).map q := by
    simpa only [q, vA, CA] using hvinMap
  obtain ⟨w, hw, hqw⟩ := Subgroup.mem_map.mp hvinMap'
  let zA : ↥A := w⁻¹ * vA
  have hzq : q zA = 1 := by
    change q (w⁻¹ * vA) = 1
    rw [map_mul, map_inv, hqw, inv_mul_cancel]
  have hzmem : zA ∈ Subgroup.center ↥A :=
    (QuotientGroup.eq_one_iff zA).mp hzq
  have hzodd : Odd (orderOf zA) :=
    Odd.of_dvd_nat hS.odd_card_center
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥A) hzmem)
  have hvAeq : vA = w * zA := by
    simp only [zA]
    group
  have hcomm_wz : Commute w zA :=
    Subgroup.mem_center_iff.mp hzmem w
  obtain ⟨m, hm⟩ := hzodd
  have hwpow : w ^ orderOf zA = vA := by
    have hvAsq : vA ^ 2 = 1 := by simpa [pow_two] using hvA2
    have h1 : (w * zA) ^ orderOf zA = vA := by
      rw [← hvAeq]
      rw [show orderOf zA = 2 * m + 1 by omega, pow_succ, pow_mul, hvAsq, one_pow,
        one_mul]
    rw [hcomm_wz.mul_pow, pow_orderOf_eq_one, mul_one] at h1
    exact h1
  have hvA_comm : vA ∈ ⁅CA, CA⁆ := by
    rw [← hwpow]
    exact Subgroup.pow_mem _ hw (orderOf zA)
  simpa only [q, vA, CA] using hvA_comm

theorem mem_commutator_centralizer_of_l34SuzOdd
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    v ∈ ⁅centralizer ({v} : Set G), centralizer ({v} : Set G)⁆ := by
  classical
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  let vA : ↥A := ⟨v, hD.le_A hv⟩
  have hKA : K ≤ A := by
    rw [hD.K_eq]
    exact (CFSG.Walter.Bender35.commutator_self_le
      (A ⊓ Subgroup.centralizer (V : Set G))).trans inf_le_left
  have hKleCGV : K ≤ Subgroup.centralizer (V : Set G) := by
    rw [hD.K_eq]
    exact (CFSG.Walter.Bender35.commutator_self_le
      (A ⊓ Subgroup.centralizer (V : Set G))).trans inf_le_right
  let CA : Subgroup ↥A := Subgroup.centralizer ({vA} : Set ↥A)
  let R : Subgroup (↥A ⧸ Subgroup.center ↥A) :=
    Subgroup.centralizer ({q vA} : Set (↥A ⧸ Subgroup.center ↥A))
  have hRmap : CA.map q = R :=
    l34SuzOdd_centralizer_map_centerQuotient hS.odd_card_center (hD.le_A hv)
      (hD.mul_self v hv)
  have hpair : CFSG.EvenSporadicStandard.Solomon78.SuzPair
      (↥A ⧸ Subgroup.center ↥A) ⊤ ((K.subgroupOf A).map q) (q vA) :=
    l34SuzOdd_suzPair_centerQuotient hS hD hv hv1 hKA hKleCGV
  have hvinR : q vA ∈ ⁅R, R⁆ :=
    CFSG.EvenSporadicStandard.Induction.suz_involutionPerfect
      (↥A ⧸ Subgroup.center ↥A) hS.suz ((K.subgroupOf A).map q) (q vA) hpair
  have hCAcomm_map : (⁅CA, CA⁆).map q = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, hRmap]
  have hvinMap : q vA ∈ (⁅CA, CA⁆).map q := by
    rw [hCAcomm_map]
    exact hvinR
  have hvA_comm : vA ∈ ⁅CA, CA⁆ :=
    l34SuzOdd_mem_commutator_of_mem_map hS (hD.le_A hv) (hD.mul_self v hv) hvinMap
  have hvinMapA : v ∈ (⁅CA, CA⁆).map A.subtype := ⟨vA, hvA_comm, rfl⟩
  have hmap_le : (⁅CA, CA⁆).map A.subtype ≤
      ⁅Subgroup.centralizer ({v} : Set G), Subgroup.centralizer ({v} : Set G)⁆ := by
    rw [Subgroup.map_commutator]
    have hle : CA.map A.subtype ≤ Subgroup.centralizer ({v} : Set G) := by
      rintro x ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hy
      simpa using congrArg A.subtype h
    exact Subgroup.commutator_mono hle hle
  exact hmap_le hvinMapA

theorem conj_ne_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (g : G) : g * t * g⁻¹ ≠ v := by
  intro hgt
  have hvmem : v ∈ ⁅centralizer ({v} : Set G), centralizer ({v} : Set G)⁆ :=
    mem_commutator_centralizer_of_l34SuzOdd hS hD hv hv1
  have hCmap : (Subgroup.centralizer ({v} : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom = Subgroup.centralizer ({t} : Set G) := by
    rw [CFSG.Walter.map_conj_centralizer_singleton]
    congr 1
    rw [show g⁻¹ * v * (g⁻¹)⁻¹ = t by rw [inv_inv, ← hgt]; group]
  have hmapcomm : (⁅centralizer ({v} : Set G), centralizer ({v} : Set G)⁆).map
      (MulAut.conj g⁻¹).toMonoidHom =
      ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
    rw [Subgroup.map_commutator, hCmap]
  have htmem : t ∈ ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
    rw [← hmapcomm]
    refine Subgroup.mem_map.mpr ⟨v, hvmem, ?_⟩
    show g⁻¹ * v * (g⁻¹)⁻¹ = t
    rw [inv_inv, ← hgt]
    group
  exact not_mem_commutator_centralizer_of_l34SuzOdd hS htmem

omit [Finite G] in
private lemma l34SuzOdd_conjAut_sq
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b) :
    CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ = 1 := by
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rwa [hb, pow_two] at h
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  calc b * (b * (a : G) * b⁻¹) * b⁻¹
      = (b * b) * (a : G) * (b⁻¹ * b⁻¹) := by group
    _ = (a : G) := by rw [hb2, hbinv, hb2]; simp

omit [Finite G] in
private lemma l34SuzOdd_centerQuotientAut_sq
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ = 1 := by
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rwa [hb, pow_two] at h
  have hbH2 : (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ :
      ↥(centralizer ({t} : Set G))) = 1 := by
    ext
    simpa using hb2
  rw [← map_mul, hbH2, map_one]

omit [Finite G] in
private lemma l34SuzOdd_centerQuotientAut_sigma_sq
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {s : G} (hs : orderOf s = 2) (hst : s * t = t * s) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ *
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ = 1 := by
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs, pow_two] at h
  have hsH2 : (⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ *
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ :
      ↥(centralizer ({t} : Set G))) = 1 := by
    ext
    simpa using hs2
  rw [← map_mul, hsH2, map_one]

omit [Finite G] in
private lemma l34SuzOdd_centerQuotientAut_comm
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b s : G} (hbt : b * t = t * b) (hst : s * t = t * s) (hsb : s * b = b * s) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ =
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ *
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ := by
  have hcommH : (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ :
      ↥(centralizer ({t} : Set G))) =
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ *
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ := by
    ext
    exact hsb.symm
  rw [← map_mul, ← map_mul, hcommH]

private lemma l34SuzOdd_centerQuotientAut_ne_one (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hbt : b * t = t * b) (hbA : b ∉ centralizer (A : Set G)) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ ≠ 1 := by
  intro hβ1
  have hmem := (CFSG.normalizerToCenterQuotientAut_eq_one_iff hS.standard.1.1 hHnorm
    ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩).mp hβ1
  exact hbA hmem.2

omit [Finite G] in
private lemma l34SuzOdd_centerQuotientAut_compat
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hbt : b * t = t * b) (y : ↥A) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩
        (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y) :=
  (CFSG.normalizerConjAutOfMem_comp_mk A (centralizer ({t} : Set G)) hHnorm
    ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y).symm

omit [Finite G] in
private lemma l34SuzOdd_oddIn_comap_le_fixSubgroup
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hbt : b * t = t * b)
    {β : MulAut (↥A ⧸ Subgroup.center ↥A)}
    (hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y)) :
    ((oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G))).comap A.subtype).map
        (QuotientGroup.mk' (Subgroup.center ↥A)) ≤
      CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β := by
  rintro y ⟨k, hk, rfl⟩
  have hkOdd : (k : G) ∈ oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)) :=
    Subgroup.mem_comap.mp hk
  have hkJ : (k : G) ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G) :=
    oddIn_le _ hkOdd
  have hkcomm : (k : G) * b = b * (k : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hkJ.2
  have hbkb : b * (k : G) * b⁻¹ = (k : G) := by
    rw [← hkcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hαk : CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
      ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ k = k := by
    apply Subtype.ext
    simpa [CFSG.normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe]
      using hbkb
  change β (QuotientGroup.mk' (Subgroup.center ↥A) k) =
    QuotientGroup.mk' (Subgroup.center ↥A) k
  rw [hβcompat k, hαk]

private lemma l34SuzOdd_oddIn_comap_card_odd {b : G} :
    Odd (Nat.card ↥(((oddIn (centralizer ({t} : Set G) ⊓
      centralizer ({b} : Set G))).comap A.subtype).map
        (QuotientGroup.mk' (Subgroup.center ↥A)))) := by
  let J : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)
  let KA : Subgroup ↥A := (oddIn J).comap A.subtype
  have h1 : Nat.card ↥(KA.map (QuotientGroup.mk' (Subgroup.center ↥A))) ∣ Nat.card ↥KA :=
    Subgroup.card_map_dvd KA _
  have h2 : Nat.card ↥KA ∣ Nat.card ↥(oddIn J) := by
    rw [show KA = (oddIn J).comap A.subtype from rfl, Subgroup.comap_subtype]
    have hcard : Nat.card ↥((oddIn J).subgroupOf A) = Nat.card ↥(oddIn J ⊓ A) := by
      rw [← Subgroup.inf_subgroupOf_right (oddIn J) A]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat (odd_card_oddIn J) (h1.trans h2)

private lemma l34SuzOdd_fixSubgroup_map_eq (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b)
    {β : MulAut (↥A ⧸ Subgroup.center ↥A)}
    (hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y)) :
    (CFSG.EvenSporadicStandard.Solomon78.fixSubgroup
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩)).map
        (QuotientGroup.mk' (Subgroup.center ↥A)) =
      CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β := by
  have hαb2 : CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ = 1 :=
    l34SuzOdd_conjAut_sq hHnorm hb hbt
  refine le_antisymm ?_ ?_
  · rintro y ⟨c', hc', rfl⟩
    have hαc' : CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ c' = c' := hc'
    change β (QuotientGroup.mk' (Subgroup.center ↥A) c') =
      QuotientGroup.mk' (Subgroup.center ↥A) c'
    rw [hβcompat c', hαc']
  · intro y hy
    obtain ⟨c', hc', hq'⟩ :=
      exists_fixed_lift_centerQuotient
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩) hαb2
        hS.odd_card_center β hβcompat hy
    exact ⟨c', hc', hq'⟩

private lemma l34SuzOdd_oddIn_comap_conj (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b) :
    ∀ c' ∈ CFSG.EvenSporadicStandard.Solomon78.fixSubgroup
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩),
      ∀ k ∈ ((oddIn (centralizer ({t} : Set G) ⊓
        centralizer ({b} : Set G))).comap A.subtype),
        c' * k * c'⁻¹ ∈ ((oddIn (centralizer ({t} : Set G) ⊓
          centralizer ({b} : Set G))).comap A.subtype) := by
  let H : Subgroup G := centralizer ({t} : Set G)
  let J : Subgroup G := H ⊓ centralizer ({b} : Set G)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem a ha
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rwa [hb, pow_two] at h
  have hJN : J ≤ Subgroup.normalizer (oddIn J : Set G) := by
    have hJnorm : ((oddIn J).subgroupOf J).Normal := by
      rw [oddIn_subgroupOf_eq_pPrimeCore]
      infer_instance
    have : ((oddIn J).subgroupOf J).Normal := hJnorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (oddIn_le J)
  intro c' hc' k hk
  have hkOdd : (k : G) ∈ oddIn J := Subgroup.mem_comap.mp hk
  have hc'A : (c' : G) ∈ A := c'.2
  have hc'α : CFSG.normalizerConjAutOfMem A H hHnorm
      ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ c' = c' := hc'
  have hc'b : b * (c' : G) * b⁻¹ = (c' : G) := by
    have h := congrArg Subtype.val hc'α
    simpa [CFSG.normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe]
      using h
  have hc'bc : b * (c' : G) = (c' : G) * b := by
    have h := congrArg (fun z : G => z * b) hc'b
    simpa [mul_assoc, hb2] using h
  have hc'J : (c' : G) ∈ J :=
    ⟨hA_le_H hc'A, Subgroup.mem_centralizer_singleton_iff.mpr hc'bc.symm⟩
  have hconjOdd : (c' : G) * (k : G) * (c' : G)⁻¹ ∈ oddIn J :=
    (Subgroup.mem_normalizer_iff.mp (hJN hc'J) (k : G)).mp hkOdd
  exact Subgroup.mem_comap.mpr (by simpa using hconjOdd)

private lemma l34SuzOdd_oddIn_comap_normal (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b)
    {β : MulAut (↥A ⧸ Subgroup.center ↥A)}
    (hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y))
    (hKA_conj : ∀ c' ∈ CFSG.EvenSporadicStandard.Solomon78.fixSubgroup
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩),
      ∀ k ∈ ((oddIn (centralizer ({t} : Set G) ⊓
        centralizer ({b} : Set G))).comap A.subtype),
        c' * k * c'⁻¹ ∈ ((oddIn (centralizer ({t} : Set G) ⊓
          centralizer ({b} : Set G))).comap A.subtype))
    :
    (((oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G))).comap
        A.subtype).map (QuotientGroup.mk' (Subgroup.center ↥A))).subgroupOf
      (CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β) |>.Normal := by
  let J : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)
  let KA : Subgroup ↥A := (oddIn J).comap A.subtype
  let P : Subgroup (↥A ⧸ Subgroup.center ↥A) :=
    KA.map (QuotientGroup.mk' (Subgroup.center ↥A))
  have hmap : (CFSG.EvenSporadicStandard.Solomon78.fixSubgroup
      (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩)).map
      (QuotientGroup.mk' (Subgroup.center ↥A)) =
      CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β :=
    l34SuzOdd_fixSubgroup_map_eq hS hHnorm hb hbt hβcompat
  constructor
  intro p hp f
  have hpP : (p : ↥A ⧸ Subgroup.center ↥A) ∈ P := hp
  obtain ⟨k, hk, hqk⟩ := Subgroup.mem_map.mp hpP
  have hfpre : (f : ↥A ⧸ Subgroup.center ↥A) ∈
      (CFSG.EvenSporadicStandard.Solomon78.fixSubgroup
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩)).map
        (QuotientGroup.mk' (Subgroup.center ↥A)) := by
    rw [hmap]
    exact f.2
  obtain ⟨c', hc', hq'⟩ := Subgroup.mem_map.mp hfpre
  have hck : c' * k * c'⁻¹ ∈ KA := hKA_conj c' hc' k hk
  have hqck : QuotientGroup.mk' (Subgroup.center ↥A) (c' * k * c'⁻¹) =
      (f : ↥A ⧸ Subgroup.center ↥A) * p *
        (f : ↥A ⧸ Subgroup.center ↥A)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hq', hqk]
  refine Subgroup.mem_subgroupOf.mpr ?_
  change (f : ↥A ⧸ Subgroup.center ↥A) * p *
    (f : ↥A ⧸ Subgroup.center ↥A)⁻¹ ∈ P
  rw [← hqck]
  exact Subgroup.mem_map.mpr ⟨c' * k * c'⁻¹, hck, rfl⟩

private lemma l34SuzOdd_oddIn_comap_map_eq_bot
    (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : orderOf b = 2) (hbt : b * t = t * b)
    {β : MulAut (↥A ⧸ Subgroup.center ↥A)}
    (hβne : β ≠ 1) (hβ2 : β * β = 1)
    (hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y)) :
    ((oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G))).comap
        A.subtype).map (QuotientGroup.mk' (Subgroup.center ↥A)) = ⊥ := by
  let J : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)
  let KA : Subgroup ↥A := (oddIn J).comap A.subtype
  let P : Subgroup (↥A ⧸ Subgroup.center ↥A) :=
    KA.map (QuotientGroup.mk' (Subgroup.center ↥A))
  have hPle : P ≤ CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β :=
    l34SuzOdd_oddIn_comap_le_fixSubgroup hHnorm hbt hβcompat
  have hPodd : Odd (Nat.card ↥P) := l34SuzOdd_oddIn_comap_card_odd
  have hKA_conj := l34SuzOdd_oddIn_comap_conj hS hHnorm hb hbt
  have hPnorm : (P.subgroupOf (CFSG.EvenSporadicStandard.Solomon78.fixSubgroup β)).Normal :=
    l34SuzOdd_oddIn_comap_normal hS hHnorm hb hbt hβcompat hKA_conj
  exact CFSG.EvenSporadicStandard.Induction.suz_autOddCoreTrivial hS.suz β hβne hβ2 P
    hPle hPnorm hPodd

private lemma l34SuzOdd_fixed_point_of_centerQuotient
    (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b s : G} (hb : orderOf b = 2) (hbt : b * t = t * b) (hst : s * t = t * s)
    (hsJ : ∀ g ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G),
      s * g * s⁻¹ * g⁻¹ ∈ oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)))
    {β : MulAut (↥A ⧸ Subgroup.center ↥A)}
    (hβne : β ≠ 1) (hβ2 : β * β = 1)
    (hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A)
        (CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
          ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ y))
    (hαb2 : CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ *
      CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩ = 1)
    {x : ↥A ⧸ Subgroup.center ↥A} (hx : β x = x) :
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ x = x := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  let J : Subgroup G := H ⊓ centralizer ({b} : Set G)
  let q : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
  have hA_le_H : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem a ha
  have hsH : s ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hst
  obtain ⟨c, hcα, hcq⟩ :=
    exists_fixed_lift_centerQuotient
      (CFSG.normalizerConjAutOfMem A H hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩) hαb2
      hS.odd_card_center β hβcompat hx
  have hcA : (c : G) ∈ A := c.2
  have hcb : b * (c : G) * b⁻¹ = (c : G) := by
    have h := congrArg Subtype.val hcα
    simpa [CFSG.normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  have hb2 : b * b = 1 := by simpa [pow_two, hb] using pow_orderOf_eq_one b
  have hcbc : b * (c : G) = (c : G) * b := by
    have h := congrArg (fun z : G => z * b) hcb
    simpa [mul_assoc, hb2] using h
  have hcH : (c : G) ∈ H := hA_le_H hcA
  have hcJ : (c : G) ∈ J :=
    ⟨hcH, Subgroup.mem_centralizer_singleton_iff.mpr hcbc.symm⟩
  let u : G := s * (c : G) * s⁻¹ * (c : G)⁻¹
  have huJ : u ∈ oddIn J := hsJ (c : G) hcJ
  have hsN : s ∈ Subgroup.normalizer (A : Set G) := hHnorm hsH
  have hscA : s * (c : G) * s⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hsN (c : G)).mp hcA
  have huA : u ∈ A := A.mul_mem hscA (A.inv_mem hcA)
  have hPbot : ((oddIn J).comap A.subtype).map q = ⊥ :=
    l34SuzOdd_oddIn_comap_map_eq_bot hS hHnorm hb hbt hβne hβ2 hβcompat
  have huP : q ⟨u, huA⟩ ∈ ((oddIn J).comap A.subtype).map q :=
    Subgroup.mem_map.mpr ⟨⟨u, huA⟩, Subgroup.mem_comap.mpr huJ, rfl⟩
  have hqu : q ⟨u, huA⟩ = 1 := by
    rw [hPbot] at huP
    exact huP
  have hαs_eq : (CFSG.normalizerConjAutOfMem A H hHnorm ⟨s, hsH⟩) c =
      ⟨u * (c : G), A.mul_mem huA hcA⟩ := by
    apply Subtype.ext
    change s * (c : G) * s⁻¹ = u * (c : G)
    simp only [u]
    group
  rw [← hcq, ← CFSG.normalizerConjAutOfMem_comp_mk A H hHnorm ⟨s, hsH⟩ c, hαs_eq]
  change q ((⟨u, huA⟩ : ↥A) * c) = q c
  rw [map_mul, hqu, one_mul]

private lemma l34SuzOdd_eq_t_of_centerQuotientAut_eq_one
    (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {s : G} (hs : orderOf s = 2) (hst : s * t = t * s)
    (hσ1 : CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ = 1) :
    s = t := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  have hsH : s ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hst
  have hqA : Group.IsPerfect ↥A := hS.standard.1.1
  have hsC : s ∈ Subgroup.centralizer (A : Set G) := by
    have hmem := (CFSG.normalizerToCenterQuotientAut_eq_one_iff hqA hHnorm ⟨s, hsH⟩).mp hσ1
    exact hmem.2
  have hsInf : s ∈ H ⊓ Subgroup.centralizer (A : Set G) := ⟨hsH, hsC⟩
  rw [centralizer_inf_centralizer_eq_of_l34SuzOdd hS] at hsInf
  have hHct : ∀ h ∈ H, h * t = t * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp hh
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs, pow_two] at h
  have hsne : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs
    norm_num at hs
  exact (eq_one_or_eq_of_mem_oddIn_sup_zpowers
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hHct hS.orderOf_t hsH hs2
    hsInf).resolve_left hsne

private lemma l34SuzOdd_eq_b_or_eq_tb_of_centerQuotientAut_eq
    (hS : L34SuzOddSetting A t)
    (hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    {b s : G} (hb : orderOf b = 2) (hs : orderOf s = 2)
    (hbt : b * t = t * b) (hst : s * t = t * s) (hsb : s * b = b * s)
    (hσβ : CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩ =
      CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
        ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩) :
    s = b ∨ s = t * b := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  have hbH : b ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hbt
  have hsH : s ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hst
  have hqA : Group.IsPerfect ↥A := hS.standard.1.1
  have hb2 : b * b = 1 := by simpa [pow_two, hb] using pow_orderOf_eq_one b
  have hs2 : s * s = 1 := by simpa [pow_two, hs] using pow_orderOf_eq_one s
  have hβ2 : CFSG.normalizerToCenterQuotientAut A H hHnorm ⟨b, hbH⟩ *
      CFSG.normalizerToCenterQuotientAut A H hHnorm ⟨b, hbH⟩ = 1 :=
    l34SuzOdd_centerQuotientAut_sq hHnorm hb hbt
  have hsbC : s * b ∈ Subgroup.centralizer (A : Set G) := by
    have hsbH : s * b ∈ H := H.mul_mem hsH hbH
    have hσβ1 : CFSG.normalizerToCenterQuotientAut A H hHnorm ⟨s, hsH⟩ *
        CFSG.normalizerToCenterQuotientAut A H hHnorm ⟨b, hbH⟩ = 1 := by
      rw [hσβ, hβ2]
    have hmem := (CFSG.normalizerToCenterQuotientAut_eq_one_iff hqA hHnorm
      ⟨s * b, hsbH⟩).mp ?_
    exact hmem.2
    change (CFSG.normalizerToCenterQuotientAut A H hHnorm)
      ((⟨s, hsH⟩ : ↥H) * ⟨b, hbH⟩) = 1
    rw [map_mul]
    exact hσβ1
  have hsbInv : s * b * (s * b) = 1 := by
    calc s * b * (s * b) = s * (b * s) * b := by group
      _ = s * (s * b) * b := by rw [← hsb]
      _ = (s * s) * (b * b) := by group
      _ = 1 := by rw [hs2, hb2]; simp
  have hsbInf : s * b ∈ H ⊓ Subgroup.centralizer (A : Set G) :=
    ⟨H.mul_mem hsH hbH, hsbC⟩
  rw [centralizer_inf_centralizer_eq_of_l34SuzOdd hS] at hsbInf
  have hHct : ∀ h ∈ H, h * t = t * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp hh
  rcases eq_one_or_eq_of_mem_oddIn_sup_zpowers
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hHct hS.orderOf_t
    (H.mul_mem hsH hbH) hsbInv hsbInf with h1 | h2
  · left
    calc s = s * 1 := by rw [mul_one]
      _ = s * (b * b) := by rw [hb2]
      _ = (s * b) * b := by group
      _ = b := by rw [h1, one_mul]
  · right
    rw [← h2, mul_assoc, hb2, mul_one]

theorem eq_of_commutator_mem_oddIn_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) {b s : G}
    (hb : orderOf b = 2) (hbt : b * t = t * b) (hbA : b ∉ centralizer (A : Set G))
    (hs : orderOf s = 2) (hst : s * t = t * s) (hsb : s * b = b * s)
    (hsJ : ∀ g ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G),
      s * g * s⁻¹ * g⁻¹ ∈ oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G))) :
    s = t ∨ s = b ∨ s = t * b := by
  classical
  have hHnorm : centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    l34SuzOdd_centralizer_le_normalizer hS
  let αb : MulAut ↥A := CFSG.normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm
    ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩
  let β : MulAut (↥A ⧸ Subgroup.center ↥A) :=
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
      ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩
  let σ : MulAut (↥A ⧸ Subgroup.center ↥A) :=
    CFSG.normalizerToCenterQuotientAut A (centralizer ({t} : Set G)) hHnorm
      ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩
  have hαb2 : αb * αb = 1 := l34SuzOdd_conjAut_sq hHnorm hb hbt
  have hβ2 : β * β = 1 := l34SuzOdd_centerQuotientAut_sq hHnorm hb hbt
  have hσ2 : σ * σ = 1 := l34SuzOdd_centerQuotientAut_sigma_sq hHnorm hs hst
  have hβσ : β * σ = σ * β := l34SuzOdd_centerQuotientAut_comm hHnorm hbt hst hsb
  have hβne : β ≠ 1 := l34SuzOdd_centerQuotientAut_ne_one hS hHnorm hbt hbA
  have hβcompat : ∀ y : ↥A, β (QuotientGroup.mk' (Subgroup.center ↥A) y) =
      QuotientGroup.mk' (Subgroup.center ↥A) (αb y) :=
    fun y => l34SuzOdd_centerQuotientAut_compat hHnorm hbt y
  have hfix : ∀ x : ↥A ⧸ Subgroup.center ↥A, β x = x → σ x = x :=
    fun x hx => l34SuzOdd_fixed_point_of_centerQuotient hS hHnorm hb hbt hst hsJ
      hβne hβ2 hβcompat hαb2 hx
  have hACC := CFSG.EvenSporadicStandard.Solomon78.suz_autCenterCond_of_isSporadic hS.suz
  rcases hACC β σ hβ2 hσ2 hβσ hfix with hσ1 | hσβ
  · left
    exact l34SuzOdd_eq_t_of_centerQuotientAut_eq_one hS hHnorm hs hst hσ1
  · rcases l34SuzOdd_eq_b_or_eq_tb_of_centerQuotientAut_eq hS hHnorm hb hs hbt hst hsb
      hσβ with h | h
    · right
      left
      exact h
    · right
      right
      exact h

end CFSG.ComponentClassification.GrSLit.L34Sec5S
