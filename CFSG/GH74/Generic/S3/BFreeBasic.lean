module

public import CFSG.GH74.Generic.S3.J2Star
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.GLS.C3.Layer1.St1RigOrd
public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Back91Core
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

theorem two_le_pRank_of_commuting_involutions {P : Type*} [Group P] [Finite P] {a b : P}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b) (hc : Commute a b) :
    2 ≤ CFSG.pRank 2 P := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have hZa : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha2
  have hZb : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  have hbc : zpowers b ≤ centralizer ((zpowers a : Subgroup P) : Set P) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hc.zpow_left k).eq
  have hE : IsElementaryAbelian 2 ↥(zpowers a ⊔ zpowers b) :=
    have := hZa
    have := hZb
    IsElementaryAbelian.sup_of_le_centralizer hbc
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 ↥(zpowers a ⊔ zpowers b)).exists_card_eq
  have hle : zpowers a ≤ zpowers a ⊔ zpowers b := le_sup_left
  have hcard_a : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ha]
  have h2 : 2 ≤ Nat.card ↥(zpowers a ⊔ zpowers b) := by
    rw [← hcard_a]; exact Subgroup.card_le_of_le hle
  have hne2 : Nat.card ↥(zpowers a ⊔ zpowers b) ≠ 2 := by
    intro h
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_a, h])
    have hbmem : b ∈ zpowers a ⊔ zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rw [← heq] at hbmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbmem
    have : a ^ k = 1 ∨ a ^ k = a := by
      rcases Int.even_or_odd' k with ⟨l, rfl | rfl⟩
      · left; rw [zpow_mul]; simp [ha2]
      · right; rw [zpow_add, zpow_mul]; simp [ha2]
    rcases this with h1 | h1
    · exact hb1 (hk ▸ h1)
    · exact hne (hk ▸ h1).symm
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m ≤ 1 := by omega
    have hle2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    rw [hm] at h2 hne2
    omega
  exact hm2.trans (le_pRank_of_card' one_lt_two _ hE hm)

theorem exists_twoComponent_over {G : Type} [Group G] [Finite G] {x : G}
    {K : Subgroup (CentralizerBar x)} (hK : IsComponent K) :
    ∃ M : Subgroup G, GLS.IsPCompIn 2 (centralizer ({x} : Set G)) M ∧ imgBar x M = K := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let S : Set (Subgroup ↥C) :=
    {J | J.IsSubnormal ∧ J.map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) = K}
  have hne : S.Nonempty :=
    ⟨K.comap (QuotientGroup.mk' (pPrimeCore 2 ↥C)), hK.2.comap _,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _⟩
  obtain ⟨J, hJS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup ↥C)) S hne
  refine ⟨J.map C.subtype, ⟨Subgroup.map_subtype_le J, ?_⟩, ?_⟩
  · have hsub : (J.map C.subtype).subgroupOf C = J :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
    rw [hsub]
    exact ⟨K, hK, hJS.1, hJS.2, fun J' hlt hJ'sub hJ'map => hmin J' ⟨hJ'sub, hJ'map⟩ hlt⟩
  · unfold imgBar
    have hsub : (J.map C.subtype).subgroupOf C = J :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
    rw [hsub]
    exact hJS.2

theorem onlyInvX_of_pRank_CxK {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} {M : Subgroup G}
    (hM : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) M) (himg : imgBar x M = K)
    (h1 : pRank 2 ↥(GLS.CxK x M) ≤ 1) : OnlyInvX x K := by
  intro u hu hu2
  have hu' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  obtain ⟨w, hw, hw2, hwu⟩ := exists_involution_lift x hu'
  have hwC : w ∈ CxK x M := by
    refine C3.Layer1.PumpRigid.mem_CxK_of_centralizes hM hw (fun y hy => ?_)
    have hbar : C3.Layer1.PumpCalc.sbar w hw = u := hwu
    rw [hbar]
    have hyK : y ∈ K := by rw [← himg]; exact hy
    have hcomm : y * u = u * y := Subgroup.mem_centralizer_iff.1 hu y hyK
    calc u * y * u⁻¹ = y * u * u⁻¹ := by rw [hcomm]
      _ = y := by group
  have hxC : x ∈ CxK x M := C3.Layer1.PumpRigid.x_mem_CxK hM.1
  by_cases hwx : w = x
  · subst hwx
    rw [← hwu]
    rfl
  · exfalso
    have hw1 : w ≠ 1 := by
      intro h1'
      subst h1'
      have : u = 1 := by rw [← hwu]; rfl
      rw [this, orderOf_one] at hu2
      omega
    have hw2' : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
    have hr : 2 ≤ CFSG.pRank 2 ↥(CxK x M) :=
      two_le_pRank_of_commuting_involutions (a := (⟨w, hwC⟩ : ↥(CxK x M))) (b := (⟨x, hxC⟩ : ↥(CxK x M)))
        (by rw [Subgroup.orderOf_mk]; exact hw2') (by rw [Subgroup.orderOf_mk]; exact hx)
        (fun h => hwx (congrArg Subtype.val h))
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hw))
    omega

theorem liftCentralAt_of_quasisimple {G : Type} [Group G] [Finite G] {x : G} (_hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hK : IsComponent K) {M : Subgroup G}
    (hM : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) M) (himg : imgBar x M = K)
    (hq : IsQuasisimple ↥M) : LiftCentralAt x K := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Mc : Subgroup ↥C := M.subgroupOf C with hMc
  set O : Subgroup ↥C := pPrimeCore 2 ↥C with hO
  have hMcq : IsQuasisimple ↥Mc :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hM.1).symm hq
  obtain ⟨K', hK'c, hMcsub, hmap, -⟩ := hM.2
  have hMcmap : Mc.map (proj x) = K := himg
  have hMcperf : ⁅Mc, Mc⁆ = Mc := Subgroup.isPerfect_iff.mp hMcq.1
  have hMcomp : IsComponent Mc := ⟨hMcq, hMcsub⟩
  have hOn : O.Normal := pPrimeCore_normal
  have hcomm : ⁅Mc, O⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hMcomp hOn.isSubnormal with h | h
    · exfalso
      have hbot : K = ⊥ := by
        rw [← hMcmap, eq_bot_iff]
        rintro _ ⟨m, hm, rfl⟩
        have : m ∈ O := h hm
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff m).2 this
      have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      rw [hbot] at this
      exact (not_nontrivial_iff_subsingleton.2 inferInstance) this
    · exact h
  have hcomm' : ∀ m ∈ Mc, ∀ o ∈ O, m * o = o * m := by
    intro m hm o ho
    have h1 : ⁅m, o⁆ ∈ ⁅Mc, O⁆ := Subgroup.commutator_mem_commutator hm ho
    rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h1
    calc m * o = (m * o * m⁻¹ * o⁻¹) * (o * m) := by group
      _ = o * m := by rw [h1, one_mul]
  set Pre : Subgroup ↥C := K.comap (proj x) with hPre
  have hPreMc : ∀ q ∈ Pre, ∃ m ∈ Mc, ∃ o ∈ O, q = m * o := by
    intro q hq'
    have : proj x q ∈ Mc.map (proj x) := by rw [hMcmap]; exact hq'
    obtain ⟨m, hm, hmq⟩ := this
    refine ⟨m, hm, m⁻¹ * q, ?_, by group⟩
    show m⁻¹ * q ∈ pPrimeCore 2 ↥C
    rw [← QuotientGroup.eq_one_iff]
    change proj x (m⁻¹ * q) = 1
    rw [map_mul, map_inv, hmq]
    group
  have hMcPre : Mc ≤ Pre := by
    intro m hm
    have : proj x m ∈ Mc.map (proj x) := Subgroup.mem_map_of_mem _ hm
    rw [hMcmap] at this
    exact this
  have hOPre : O ≤ Pre := by
    intro o ho
    show proj x o ∈ K
    have : proj x o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [this]
    exact one_mem K
  set N₀ : Subgroup ↥Pre := Mc.subgroupOf Pre with hN₀
  have hN₀n : N₀.Normal := by
    refine ⟨fun a ha b => ?_⟩
    obtain ⟨m₁, hm₁, o₁, ho₁, hb⟩ := hPreMc b.1 b.2
    have ha' : (a : ↥C) ∈ Mc := ha
    have hb' : (b : ↥C) = m₁ * o₁ := hb
    show (b : ↥C) * (a : ↥C) * (b : ↥C)⁻¹ ∈ Mc
    rw [hb']
    have h2 : m₁ * o₁ * (a : ↥C) * (m₁ * o₁)⁻¹ = m₁ * (a : ↥C) * m₁⁻¹ := by
      have e1 : o₁ * (a : ↥C) = (a : ↥C) * o₁ := (hcomm' a ha' o₁ ho₁).symm
      calc m₁ * o₁ * (a : ↥C) * (m₁ * o₁)⁻¹ = m₁ * (o₁ * (a : ↥C)) * o₁⁻¹ * m₁⁻¹ := by group
        _ = m₁ * ((a : ↥C) * o₁) * o₁⁻¹ * m₁⁻¹ := by rw [e1]
        _ = m₁ * (a : ↥C) * m₁⁻¹ := by group
    rw [h2]
    exact Mc.mul_mem (Mc.mul_mem hm₁ ha') (Mc.inv_mem hm₁)
  have hOsolv : Group.IsSolvable ↥O := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    exact (Nat.coprime_two_left.1 this)
  let g : ↥O →* ↥Pre ⧸ N₀ :=
    (QuotientGroup.mk' N₀).comp (Subgroup.inclusion hOPre)
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, o, ho, hb⟩ := hPreMc b.1 b.2
    refine ⟨⟨o, ho⟩, ?_⟩
    show (QuotientGroup.mk (⟨o, hOPre ho⟩ : ↥Pre) : ↥Pre ⧸ N₀) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    show ((⟨o, hOPre ho⟩ : ↥Pre)⁻¹ * b : ↥Pre).1 ∈ Mc
    have : ((⟨o, hOPre ho⟩ : ↥Pre)⁻¹ * b : ↥Pre).1 = o⁻¹ * (m * o) := by
      show o⁻¹ * (b : ↥C) = o⁻¹ * (m * o)
      rw [hb]
    rw [this]
    have e1 : o⁻¹ * (m * o) = m := by
      have := hcomm' m hm o ho
      calc o⁻¹ * (m * o) = o⁻¹ * (o * m) := by rw [this]
        _ = m := by group
    rw [e1]
    exact hm
  have hQsolv : Group.IsSolvable (↥Pre ⧸ N₀) := Group.isSolvable_of_surjective hgs
  set P : Subgroup ↥C := S1.liftL x K with hP
  have hPperf : ⁅P, P⁆ = P := S1.perfectResidualOf_perfect _
  have hPPre : P ≤ Pre := S1.liftL_le x K
  have hPMc : P ≤ Mc := by
    let h : ↥P →* ↥Pre ⧸ N₀ := (QuotientGroup.mk' N₀).comp (Subgroup.inclusion hPPre)
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
    have hrp : Group.IsPerfect ↥h.range := Group.IsPerfect.range h
    have hrs : Group.IsSolvable ↥h.range := inferInstance
    have hsub : Subsingleton ↥h.range := by
      by_contra hns
      have : Nontrivial ↥h.range := not_subsingleton_iff_nontrivial.1 hns
      have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥h.range
      rw [hrp.commutator_eq_top] at h1
      exact lt_irrefl _ h1
    intro p hp
    have h1 : h ⟨p, hp⟩ = 1 := by
      have := Subsingleton.elim (⟨h ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩⟩ : ↥h.range) 1
      exact congrArg Subtype.val this
    have h2 : ((Subgroup.inclusion hPPre) ⟨p, hp⟩ : ↥Pre) ∈ N₀ := by
      have := h1
      simpa [h, QuotientGroup.eq_one_iff] using this
    exact h2
  have hMcP : Mc ≤ P := S1.perfect_le_liftL hMcPre hMcperf
  have hPeq : P = Mc := le_antisymm hPMc hMcP
  intro n hn hn1 l hl
  have hnO : n ∈ O := (QuotientGroup.eq_one_iff n).1 hn1
  have hlMc : l ∈ Mc := hPMc hl
  exact (hcomm' l hlMc n hnO).symm

theorem exists_two_involutions_of_two_le_pRank {P : Type*} [Group P] [Finite P]
    (h : 2 ≤ CFSG.pRank 2 P) : ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  classical
  obtain ⟨A, hAab, hAcard⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥A := by rw [hAcard]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 h2
  have hnle : ¬ (A ≤ zpowers (a : P)) := by
    intro hle
    have hz : zpowers (a : P) ≤ A := Subgroup.zpowers_le.2 a.2
    have heq : zpowers (a : P) = A := le_antisymm hz hle
    have hc : Nat.card ↥(zpowers (a : P)) = 2 := by
      rw [Nat.card_zpowers]
      rw [Subgroup.orderOf_coe, ha]
    rw [heq, hAcard] at hc
    omega
  obtain ⟨b, hbA, hbz⟩ := Set.not_subset.1 hnle
  have hsq : ∀ g ∈ A, g ^ 2 = 1 := fun g hg => hAab.2 g hg
  have hb1 : b ≠ 1 := fun hb => hbz (hb ▸ one_mem _)
  have hbne : (a : P) ≠ b := fun hab => hbz (hab ▸ Subgroup.mem_zpowers _)
  refine ⟨(a : P), b, ?_, ?_, hbne, ?_⟩
  · rw [Subgroup.orderOf_coe, ha]
  · exact orderOf_eq_prime (by rw [sq] at *; simpa [sq] using hsq b hbA) hb1
  · exact hAab.1.is_comm.comm ⟨(a : P), a.2⟩ ⟨b, hbA⟩ |> fun h => by
      have := congrArg Subtype.val h
      exact this

theorem pRank_CxK_le_one_of_onlyInvX {G : Type} [Group G] [Finite G] {x : G} (_hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} {M : Subgroup G}
    (hM : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) M) (himg : imgBar x M = K)
    (h : OnlyInvX x K) : pRank 2 ↥(GLS.CxK x M) ≤ 1 := by
  by_contra hlt
  have h2 : 2 ≤ CFSG.pRank 2 ↥(CxK x M) := by omega
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ := exists_two_involutions_of_two_le_pRank h2
  have key : ∀ e : ↥(CxK x M), orderOf e = 2 → proj x ⟨(e : G), e.2.1⟩ = xbar x := by
    intro e he
    have heC : (e : G) ∈ centralizer ({x} : Set G) := e.2.1
    have heo : orderOf (e : G) = 2 := (Subgroup.orderOf_coe e).trans he
    have hcent := C3.Layer1.PumpRigid.centralizes_of_mem_CxK hM heC e.2
    have hu : C3.Layer1.PumpCalc.sbar (e : G) heC ∈ centralizer (K : Set (CentralizerBar x)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [← himg] at hk
      have h1 := hcent k hk
      calc k * C3.Layer1.PumpCalc.sbar (e : G) heC
          = (C3.Layer1.PumpCalc.sbar (e : G) heC * k * (C3.Layer1.PumpCalc.sbar (e : G) heC)⁻¹) *
              C3.Layer1.PumpCalc.sbar (e : G) heC := by rw [h1]
        _ = C3.Layer1.PumpCalc.sbar (e : G) heC * k := by group
    exact h _ hu (C3.Layer1.PumpCalc.orderOf_sbar heo heC)
  have ha' := key a ha
  have hb' := key b hb
  have hao : (a : G) * a = 1 := by
    have h1 := pow_orderOf_eq_one a
    rw [ha, pow_two] at h1
    simpa using congrArg Subtype.val h1
  have hbo : (b : G) * b = 1 := by
    have h1 := pow_orderOf_eq_one b
    rw [hb, pow_two] at h1
    simpa using congrArg Subtype.val h1
  set a' : ↥(centralizer ({x} : Set G)) := ⟨(a : G), a.2.1⟩ with ha'def
  set b' : ↥(centralizer ({x} : Set G)) := ⟨(b : G), b.2.1⟩ with hb'def
  have hcomm' : a' * b' = b' * a' := Subtype.ext (by simpa using congrArg Subtype.val hcomm.eq)
  have hn1 : proj x (a'⁻¹ * b') = 1 := by
    rw [map_mul, map_inv, ha', hb']
    group
  have hodd := proj_odd x _ hn1
  have hsqn : (a'⁻¹ * b') * (a'⁻¹ * b') = 1 := by
    have hao' : a' * a' = 1 := Subtype.ext hao
    have hbo' : b' * b' = 1 := Subtype.ext hbo
    have ha'inv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right hao'
    rw [ha'inv]
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [hcomm']
      _ = (a' * a') * (b' * b') := by group
      _ = 1 := by rw [hao', hbo', one_mul]
  have hne1 : a'⁻¹ * b' ≠ 1 := by
    intro h1
    apply hab
    have : (a' : ↥(centralizer ({x} : Set G))) = b' := inv_mul_eq_one.1 h1
    have h3 := congrArg Subtype.val this
    exact Subtype.ext h3
  have hord2 : orderOf (a'⁻¹ * b') = 2 := orderOf_eq_prime (by rw [sq]; exact hsqn) hne1
  rw [hord2] at hodd
  exact absurd hodd (by decide)

theorem depthOfG_eq_of_ilog2 {G : Type} [Group G] [Finite G] {x : G} {M : Subgroup G}
    (hILoG2 : IsILoG2 x M) {D : ℕ} (hdM : d2 (↥M ⧸ pPrimeCore 2 ↥M) = D)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → D ≤ d2 ↥L) :
    depthOfG G = D := by
  refine le_antisymm (hdM ▸ Nat.sInf_le ⟨x, M, hILoG2, rfl⟩) (le_csInf ⟨_, x, M, hILoG2, hdM⟩ ?_)
  rintro d ⟨y, M', h, rfl⟩
  obtain ⟨L, hL, ⟨e'⟩⟩ := g2pair_of_iloG2 h
  rw [d2_congr e']
  exact hmin y L hL

theorem exists_ilo_over {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) :
    ∃ M : Subgroup G, IsILo 2 x M ∧ imgBar x M = K ∧
      Nonempty ((↥M ⧸ pPrimeCore 2 ↥M) ≃* ↥K) := by
  obtain ⟨M, hM, himg⟩ := exists_twoComponent_over hKc
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hr
  have hILo : IsILo 2 x M :=
    ⟨hx, by simpa [oBound] using TwoThin.rankThreeCentralizers G hs hn h3 x hx, hM⟩
  have hbar : C3.Layer1.PumpCalc.bar x M = K := himg
  obtain ⟨e⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hM
  exact ⟨M, hILo, himg, ⟨e.trans (MulEquiv.subgroupCongr hbar)⟩⟩

theorem depthOfG_eq_of_mindepth {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G) (_hK : KGH G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L) :
    depthOfG G = d2 ↥K := by
  obtain ⟨M, hILo, -, ⟨eMK⟩⟩ := exists_ilo_over hs hn hr hx hKc
  exact depthOfG_eq_of_ilog2 ⟨hILo, inG2_of_mulEquiv eMK.symm hg2⟩ (d2_congr eMK) hmin

theorem exists_isJ2_of_onlyInvX {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G) (hK : KGH G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L)
    (hOnly : OnlyInvX x K) : ∃ M : Subgroup G, IsJ2 x M ∧ imgBar x M = K := by
  obtain ⟨M, hILo, himg, ⟨eMK⟩⟩ := exists_ilo_over hs hn hr hx hKc
  have hILoG2 : IsILoG2 x M := ⟨hILo, inG2_of_mulEquiv eMK.symm hg2⟩
  have hdepth := depthOfG_eq_of_mindepth hs hn hr hK hx hKc hg2 hmin
  have hdM : d2 (↥M ⧸ pPrimeCore 2 ↥M) = d2 ↥K := d2_congr eMK
  have hT : IsTwoTerminal x M :=
    C3.Layer1.PumpH1.isTwoTerminal_of_pRank_le_one hILo
      (pRank_CxK_le_one_of_onlyInvX hx hILo.2.2 himg hOnly)
  exact ⟨M, ⟨hILoG2, hdM.trans hdepth.symm, hT⟩, himg⟩

end CFSG.GH74.Generic.S3
