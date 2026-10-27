module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Families
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.L227
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.StronglyEmbedded
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.Walter.ReeOrder.JT.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)
open scoped MatrixGroups

section K3

theorem pRank_centralizer_eq_two_of_sylow {X : Type} [Group X] [Finite X] {S : Sylow 3 X}
    (hS : 3 ≤ CFSG.Open.pRank 3 (S : Subgroup X)) {x : X} (hxS : x ∈ (S : Subgroup X))
    (hx : orderOf x = 3) (hle : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) ≤ 2) :
    CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 := by
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hPg : IsPGroup 3 ↥(S : Subgroup X) := S.isPGroup'
  obtain ⟨z, hzS, hzc, hz3⟩ := exists_central_order_three hPg hxS hxne
  have hzz : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have h2 : 2 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
    by_cases hxz : x ∈ zpowers z
    ·
      exfalso
      have hSC : (S : Subgroup X) ≤ centralizer ({x} : Set X) := by
        intro y hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
        have hzy : Commute z y := hzc y hy
        apply Subgroup.mem_centralizer_singleton_iff.2
        rw [← hk]
        exact ((hzy.zpow_left k).eq).symm
      have hle' := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hSC
      omega
    ·
      have hzx : Commute z x := hzc x hxS
      have hxZ : x ∈ centralizer ((zpowers z : Subgroup X) : Set X) := by
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (show h ∈ zpowers z from hh)
        exact (hzx.zpow_left k).eq
      have hcomm_x : ∀ e ∈ zpowers z, e * x = x * e := fun e he =>
        Subgroup.mem_centralizer_iff.1 hxZ e he
      haveI hiz : CFSG.IsElementaryAbelian 3 ↥(zpowers z) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzz
      haveI hix : CFSG.IsElementaryAbelian 3 ↥(zpowers x) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
      haveI hiA : CFSG.IsElementaryAbelian 3 ↥(zpowers z ⊔ zpowers x) :=
        CFSG.IsElementaryAbelian.sup_of_le_centralizer (Subgroup.zpowers_le.2 hxZ)
      have hA9 : Nat.card ↥(zpowers z ⊔ zpowers x) = 9 := by
        rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z) hx3 hxz
          hcomm_x, Nat.card_zpowers, hz3] <;> norm_num
      have hVprop : CFSG.Open.IsElemAbelian 3 (zpowers z ⊔ zpowers x) :=
        ⟨hiA.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
      have hAC : zpowers z ≤ centralizer ({x} : Set X) := fun e he =>
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm_x e he)
      have hxC : zpowers x ≤ centralizer ({x} : Set X) :=
        Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
      have hVle : zpowers z ⊔ zpowers x ≤ centralizer ({x} : Set X) := sup_le hAC hxC
      have hk : 3 ^ 2 ≤ Nat.card ↥(zpowers z ⊔ zpowers x) := by
        rw [hA9] <;> norm_num
      exact le_pRank_of_isElemAbelian_card Nat.prime_three hVle hVprop hk
  omega

end K3

section K3Big

theorem k3_mem_zpowers_nine {W : Type*} [Group W] [Finite W] [IsCyclic W] {a b : W}
    (ha : a ^ 9 = 1) (hb : orderOf b = 9) : a ∈ Subgroup.zpowers b := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  by_contra hna
  have hb9 : b ^ 9 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  obtain ⟨F, hF⟩ : ∃ F : Finset W, F = (Finset.range 9).image (fun i : ℕ => b ^ i) :=
    ⟨_, rfl⟩
  have hinj : Set.InjOn (fun i : ℕ => b ^ i) (Finset.range 9 : Set ℕ) := by
    rw [Finset.coe_range, ← hb]
    exact pow_injOn_Iio_orderOf
  have hFcard : F.card = 9 := by
    rw [hF, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hanot : a ∉ F := by
    intro haF
    rw [hF, Finset.mem_image] at haF
    obtain ⟨i, _, hi⟩ := haF
    apply hna
    rw [← hi]
    exact pow_mem (Subgroup.mem_zpowers b) i
  have hsub : insert a F ⊆ Finset.univ.filter (fun x : W => x ^ 9 = 1) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    rcases hx with rfl | hx
    · exact ha
    · rw [hF, Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [← pow_mul, mul_comm, pow_mul, hb9, one_pow]
  have h1 : (insert a F).card ≤ (Finset.univ.filter (fun x : W => x ^ 9 = 1)).card :=
    Finset.card_le_card hsub
  have h2 : (insert a F).card = F.card + 1 := Finset.card_insert_of_notMem hanot
  have h3 : (Finset.univ.filter (fun x : W => x ^ 9 = 1)).card ≤ 9 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  omega

theorem k3_mem_zpowers_of_mem {N : Subgroup K3.W3} [Finite K3.W3] [IsCyclic N] {m : N}
    (hm : orderOf m = 9) {y : K3.W3} (hyN : y ∈ N) (hy : y ^ 9 = 1) :
    y ∈ Subgroup.zpowers (m : K3.W3) := by
  have h := k3_mem_zpowers_nine (a := (⟨y, hyN⟩ : N)) (b := m)
    (Subtype.ext (by simpa using hy)) hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem W3_no_normal_cyclic_big {N : Subgroup K3.W3} [N.Normal] (hc : IsCyclic N)
    (h9 : 9 ≤ Nat.card N) : False := by
  have hcard : Nat.card K3.W3 = 81 := CFSG.RankThree.PartTwo.Sec11.card_wreath
  haveI : Finite K3.W3 := Nat.finite_of_card_ne_zero (by omega)
  have hdvd81 : Nat.card N ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← hcard]
    exact Subgroup.card_subgroup_dvd_card N
  have h9dvd : 9 ∣ Nat.card N := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd81
    rw [hkeq] at h9 ⊢
    interval_cases k <;> (try norm_num at h9) <;> norm_num
  obtain ⟨g, hgord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥N)
  have hm9 : orderOf (g ^ (Nat.card N / 9)) = 9 := by
    have h1 : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have h2 : 9 ∣ orderOf g := by rw [hgord]; exact h9dvd
    have h3 := orderOf_pow_orderOf_div h1 h2
    rw [hgord] at h3
    exact h3
  obtain ⟨m, hm⟩ : ∃ m : N, orderOf m = 9 := ⟨g ^ (Nat.card N / 9), hm9⟩
  have hm' : orderOf (m : K3.W3) = 9 := by
    rw [Subgroup.orderOf_coe]
    exact hm
  have hmpow : (m : K3.W3) ^ 9 = 1 := by
    have := pow_orderOf_eq_one (m : K3.W3)
    rwa [hm'] at this
  have hM9 : Nat.card (Subgroup.zpowers (m : K3.W3)) = 9 := by
    rw [Nat.card_zpowers, hm']
  have hMN : Subgroup.zpowers (m : K3.W3) ≤ N := Subgroup.zpowers_le.mpr m.2
  have hMexp : ∀ n ∈ Subgroup.zpowers (m : K3.W3), n ^ 9 = 1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hmpow, one_zpow]
  have hMnorm : (Subgroup.zpowers (m : K3.W3)).Normal := by
    refine ⟨fun n hn h => ?_⟩
    have hnN : n ∈ N := hMN hn
    have hyN : h * n * h⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hnN h
    have hy9 : (h * n * h⁻¹) ^ 9 = 1 := by
      rw [conj_pow, hMexp n hn]
      simp
    exact k3_mem_zpowers_of_mem hm hyN hy9
  have hMeq : Subgroup.zpowers (m : K3.W3) = ⁅(⊤ : Subgroup K3.W3), (⊤ : Subgroup K3.W3)⁆ :=
    CFSG.RankThree.PartTwo.KFacts.eq_commutator_of_normal_of_card_nine hMnorm hM9
  have hmcomm : (m : K3.W3) ∈ ⁅(⊤ : Subgroup K3.W3), (⊤ : Subgroup K3.W3)⁆ := by
    rw [← hMeq]
    exact Subgroup.mem_zpowers _
  have hmB : (m : K3.W3) ∈ CFSG.RankThree.PartTwo.KFacts.wreathBase :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.wc_commutator_le_base hmcomm
  have hm3 : (m : K3.W3) ^ 3 = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.wreath_ker_isElemAbelian.2 _ hmB
  have hdvd : orderOf (m : K3.W3) ∣ 3 := orderOf_dvd_of_pow_eq_one hm3
  rw [hm'] at hdvd
  omega

end K3Big

section K3

theorem exists_normal_index_three_of_hom {G B : Type*} [Group G] [Finite G] [Group B]
    (hB : ∀ a b : B, a * b = b * a) (f : G →* B) {y : G} (hy : IsPGroup 3 (zpowers y))
    (h1 : f y ≠ 1) : ∃ N : Subgroup G, N.Normal ∧ N.index = 3 := by
  classical
  haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hy ⟨y, Subgroup.mem_zpowers y⟩
  have hyk : y ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hmem : f y ∈ f.range := MonoidHom.mem_range.2 ⟨y, rfl⟩
  have hd : orderOf (f y) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hyk, map_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply h1
    exact orderOf_eq_one_iff.1 (by simpa using hj)
  have h3 : 3 ∣ orderOf (f y) := by
    rw [hj]
    exact dvd_pow_self 3 hj0
  have hdvd : 3 ∣ Nat.card f.range := by
    have h := orderOf_dvd_natCard (⟨f y, hmem⟩ : f.range)
    rw [Subgroup.orderOf_mk] at h
    exact h3.trans h
  letI : CommGroup f.range :=
    { (inferInstance : Group f.range) with
      mul_comm := fun a b => Subtype.ext (hB a.1 b.1) }
  obtain ⟨ι, hι, n, -, ⟨ψ⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite f.range
  have hcard : Nat.card f.range = ∏ i, n i := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact Nat.card_zmod (n i)
  have h3prod : 3 ∣ ∏ i, n i := by
    rw [← hcard]
    exact hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).1 h3prod
  let c : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod 3) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hi (ZMod 3)).toAddMonoidHom
  let π : f.range →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp ψ.toMonoidHom
  let φ : G →* Multiplicative (ZMod 3) := c.comp (π.comp f.rangeRestrict)
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective hi (Multiplicative.toAdd z)
    exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩
  have hπ : Function.Surjective π := by
    intro a
    refine ⟨ψ.symm (Pi.mulSingle i a), ?_⟩
    simp [π, Pi.mulSingle_eq_same]
  have hφ : Function.Surjective φ := hc.comp (hπ.comp f.rangeRestrict_surjective)
  refine ⟨φ.ker, inferInstance, ?_⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hφ, Subgroup.card_top]
  exact Nat.card_zmod 3

end K3

section ComponentCore

theorem k3_eq_bot_of_coprime {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hZ : IsPGroup 3 ↥(center K)) (h3 : 3 ∣ Nat.card K)
    (N : Subgroup K) [N.Normal] (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK N with hle | htop
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    have hdvd : Nat.card N ∣ 3 ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hle
    have h1 : Nat.card N = 1 := (Nat.Coprime.pow_right k hcop.symm).eq_one_of_dvd hdvd
    exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    rw [htop, Subgroup.card_top] at hcop
    have h31 : 3 = 1 := Nat.Coprime.eq_one_of_dvd hcop h3
    norm_num at h31

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.gLAPPrimeCore_eq_bot (h : T29Setup X L x) :
    CFSG.Open.GLAPPrimeCore 3 ↥L = ⊥ :=
  k3_eq_bot_of_coprime h.comp.2.2 h.center_isPGroup
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.three_dvd_card_component h.core h.comp)
    (CFSG.Open.GLAPPrimeCore 3 ↥L)
    (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥L) 3)

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem exists_normal_index_three_of_field (h : T29Setup X L x)
    (hT : IsLThreeEps (↥L ⧸ center ↥L)) {y : X} (hy : IsPGroup 3 (zpowers y))
    (hfield : InducesNontrivialFieldAut L y) : ∃ N : Subgroup X, N.Normal ∧ N.index = 3 := by
  haveI : L.Normal := h.normal
  have hq : CFSG.Open.IsQuasisimple ↥L := h.comp.2.2
  have hT3 := isThreeType_of_isLThreeEps hT
  obtain ⟨hn, hf, h1⟩ := hfield
  have hcore : CFSG.Open.GLAPPrimeCore 3 ↥L = ⊥ := h.gLAPPrimeCore_eq_bot
  let eL : ↥L ⧸ CFSG.Open.GLAPPrimeCore 3 ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have heL : ∀ w : ↥L, eL (QuotientGroup.mk w) = w := fun w => rfl
  have hkey : MulAut.congr eL (barAut 3 L ⟨y, hn⟩) = MulAut.conjNormal y := by
    refine MulEquiv.ext fun w => ?_
    show eL (barAut 3 L ⟨y, hn⟩ (eL.symm w)) = MulAut.conjNormal y w
    have hsymm : eL.symm w = QuotientGroup.mk w := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hsymm, barAut_mk, heL]
    have hval : ((L.normalizerMonoidHom ⟨y, hn⟩ w : ↥L) : X) = y * (w : X) * y⁻¹ := rfl
    apply Subtype.ext
    rw [hval, MulAut.conjNormal_apply]
  have hf' : IsFieldAutThree (MulAut.conjNormal y : MulAut ↥L) := by
    rw [← hkey]
    exact Lemma511Ns.isFieldAutThree_of_mulEquiv eL hf
  have h1' : (MulAut.conjNormal y : MulAut ↥L) ≠ 1 := by
    intro hc
    apply h1
    apply (MulAut.congr eL).injective
    rw [map_one, hkey]
    exact hc
  have hyc := not_mem_commutator_of_fieldAut hq hT3 hf' h1'
  have hab : (Abelianization.of : X →* Abelianization X) y ≠ 1 := by
    intro h0
    apply hyc
    rw [← Abelianization.ker_of X, MonoidHom.mem_ker]
    exact h0
  exact exists_normal_index_three_of_hom (B := Abelianization X)
    (fun a b => mul_comm a b) Abelianization.of hy hab

end ComponentCore

theorem k3_three_le_pRank_of_wreath {X : Type} [Group X] [Finite X] (S : Sylow 3 X)
    (e : (S : Subgroup X) ≃* K3.W3) : 3 ≤ CFSG.Open.pRank 3 (S : Subgroup X) := by
  let B : Subgroup K3.W3 := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  let f : K3.W3 →* X := (S : Subgroup X).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hel : CFSG.Open.IsElemAbelian 3 (B.map f) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.wreath_ker_isElemAbelian.map f
  have hcard : Nat.card (B.map f) = 27 := by
    rw [Subgroup.card_map_of_injective hf]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_ker
  refine le_pRank_of_isElemAbelian_card Nat.prime_three ?_ hel (k := 3) ?_
  · rintro _ ⟨b, -, rfl⟩
    exact (e.symm b).2
  · rw [hcard]
    norm_num

theorem k3_center_eq_bot_of_psl227 {L : Type} [Group L] (hcomm : commutator L = ⊤)
    (e : L ≃* PSL(2, GaloisField 3 3)) : Subgroup.center L = ⊥ := by
  have h4 : 4 ≤ Nat.card (GaloisField 3 3) := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup PSL(2, GaloisField 3 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  haveI : IsSimpleGroup L := e.isSimpleGroup
  rcases (inferInstance : (Subgroup.center L).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have h1 : commutator L = ⊥ := (commutator_eq_bot_iff_center_eq_top L).mpr h
    rw [h1] at hcomm
    exact bot_ne_top hcomm

theorem k3_false_of_pCore_big {X : Type} [Group X] [Finite X] (S : Sylow 3 X)
    (e : (S : Subgroup X) ≃* K3.W3) (hc : IsCyclic ↥(CFSG.pCore 3 X))
    (h9 : 9 ≤ Nat.card ↥(CFSG.pCore 3 X)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hn : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal (p := 3) (G := X)
  have hle : CFSG.pCore 3 X ≤ (S : Subgroup X) := pCore_le_sylow S
  let N₀ : Subgroup (S : Subgroup X) := (CFSG.pCore 3 X).subgroupOf (S : Subgroup X)
  haveI hN₀ : N₀.Normal := hn.subgroupOf (S : Subgroup X)
  let N : Subgroup K3.W3 := N₀.map e.toMonoidHom
  haveI hN : N.Normal := hN₀.map e.toMonoidHom e.surjective
  let φ : ↥(CFSG.pCore 3 X) ≃* ↥N :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (Subgroup.equivMapOfInjective N₀ e.toMonoidHom e.injective)
  have hcyc : IsCyclic ↥N := isCyclic_of_surjective φ.toMonoidHom φ.surjective
  have hcard : Nat.card ↥N = Nat.card ↥(CFSG.pCore 3 X) := (Nat.card_congr φ.toEquiv).symm
  exact W3_no_normal_cyclic_big hcyc (hcard ▸ h9)

theorem kfactConstraintCore_of_T29 (hT : GL83I291Three) : K3.KFactConstraintCore := by
  intro X _ _ hcat hcore L hLc huniq S hSW hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hSW
  obtain ⟨x, hxS, hx1, hx3, hxr⟩ := hx
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hSrank : 3 ≤ CFSG.Open.pRank 3 (S : Subgroup X) := k3_three_le_pRank_of_wreath S e
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    hSrank.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top)
  have hcent : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 :=
    pRank_centralizer_eq_two_of_sylow hSrank hxS hxord hxr
  have hsetup : T29Setup X L x := ⟨hcat, hcore, hLc, huniq, hrank, hxord, hcent⟩
  obtain ⟨hcyc, -, -, hconc⟩ := hT X hcat hcore L hLc huniq hrank x hxord hcent
  rcases hconc with ⟨hLε, -, -, -, hfield | h9⟩ | hb
  · obtain ⟨y, hy, hyf⟩ := hfield
    exact exists_normal_index_three_of_field hsetup hLε hy hyf
  · exact (k3_false_of_pCore_big S e hcyc h9).elim
  · obtain ⟨e', -, -⟩ := id hb
    have hZ : center ↥L = ⊥ := k3_center_eq_bot_of_psl227 hLc.2.2.1 e'
    have hC : centralizer (L : Set X) = ⊥ := hsetup.centralizer_eq_bot hZ
    haveI : L.Normal := hsetup.normal
    exact K2.exists_index_three_normal hsetup.normal ⟨e'⟩ hC (index_eq_of_fieldAut_L227 hC hb)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
