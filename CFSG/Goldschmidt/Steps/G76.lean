module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.StrongClosure
import CFSG.Goldschmidt.Steps.G76Basic
import CFSG.Goldschmidt.Steps.G76L2
import CFSG.Goldschmidt.Steps.G76TypeI
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Goldschmidt.Steps.G74Basic
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.Goldschmidt.Steps.G36
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Goldschmidt.Steps.G3NewPair
import CFSG.Goldschmidt.Steps.PaperClosure
import CFSG.Goldschmidt.Steps.G3aFStar
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S3.FStar
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.Walter.Bender1970.S2.Layer
import CFSG.Walter.Bender1970.S2.Subnormal
import CFSG.Walter.Bender1970.S38.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3
import CFSG.Walter.Bender1970.S38
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Goldschmidt

open CFSG.Open G76

private theorem eq_one_or_eq_of_card_eq_two {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : Nat.card X = 2) {a : G} (ha : a ∈ X) (ha1 : a ≠ 1) {c : G} (hc : c ∈ X) :
    c = 1 ∨ c = a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hc1, hca⟩ := h
  have : Fintype X := Fintype.ofFinite _
  have h3 : 3 ≤ Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    let s : Finset X := {1, ⟨a, ha⟩, ⟨c, hc⟩}
    have hs : s.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        exact hca (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
          fun h => hc1 (congrArg Subtype.val h).symm⟩
    rw [← hs]
    exact Finset.card_le_univ s
  omega

theorem G76_of'
    (h31 : S_G31) (h64 : S_G64) (h74 : S_G74) (h75 : S_G75) : S_G76 := by
  intro G _ _ S A hG h8 hE
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isSimpleGroup
  have h36 := G36_of G32 GNewPair h31
  obtain ⟨hA8, hidx, -⟩ := h75 G S A hG h8 hE
  obtain ⟨a₀, -, -, H, hH₀, K, hK, h1, h2a, h2b, h3, -⟩ := h74 G S A hG h8 hE
  set C := A ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hC2 : Nat.card C = 2 := by
    rw [hA8] at h2b
    have : Nat.card C ≤ 2 := by nlinarith
    omega
  obtain ⟨⟨a, haC⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot C).mp (by omega))
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haA : a ∈ A := haC.1
  have haK : a ∈ Subgroup.centralizer (K : Set G) := haC.2
  have hCa : ∀ c ∈ C, c = 1 ∨ c = a := fun c hc =>
    eq_one_or_eq_of_card_eq_two hC2 haC ha1' hc
  have hH : H ∈ CFSG.Walter.benderM a := by rw [h1 a haC ha1']; rfl
  have hS := G73.isSStarIn_of_mem_benderM hG haA hH
  have hAH : A ≤ H := G73.le_of_mem_benderM hG haA hH
  have hHco := CFSG.Walter.isCoatom_of_mem_benderM hH
  have hCH : Subgroup.centralizer ({a} : Set G) ≤ H := CFSG.Walter.centralizer_le_of_mem_benderM hH
  set Q := normalClosureIn H A with hQdef
  have hQH : Q ≤ H := G73.normalClosureIn_le H A
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := G73.le_normalizer_normalClosureIn H A
  have hAQ : A ≤ Q := (le_inf le_rfl hAH).trans (G73.inf_le_normalClosureIn H A)
  have hKH' := G73.isComponentOf_of_normalClosureIn hK
  have hKH : K ≤ H := hKH'.1
  have huniq : ∀ L : Subgroup G, GorensteinWalter.IsComponentOf L Q → L = K := by
    intro L hL
    by_contra hLK
    have hLC : L ≤ Subgroup.centralizer (K : Set G) :=
      CFSG.Walter.le_centralizer_of_isComponentOf_ne hL hK hLK
    have hAL : A ⊓ L ≤ C := fun x hx => ⟨hx.1, hLC hx.2⟩
    have hcardAL : Nat.card (A ⊓ L : Subgroup G) ≤ 2 := hC2 ▸ Subgroup.card_le_of_le hAL
    have h4 := G74.four_mul_card_inf_centralizer_le h31 h36 hG haA hH hL
    have hdec := G73.eq_inf_sup_inf_centralizer h31 hS hG.elem hL
    have hle : Nat.card A ≤ Nat.card (A ⊓ L : Subgroup G) *
        Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
      calc Nat.card A = Nat.card (A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set G) :
            Subgroup G) := by rw [← hdec]
        _ ≤ _ := G74.card_sup_le hG.elem.1 inf_le_left inf_le_left
    have hpos : 0 < Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
      Nat.card_pos
    nlinarith
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haK k hk)
  have hJa : ∀ J : Subgroup G, GorensteinWalter.IsComponentOf J H →
      J ≤ Subgroup.centralizer ({a} : Set G) := by
    intro J hJ
    rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot hJ hQH hHQ with hJQ | hJQ
    · rw [huniq J (CFSG.Walter.isComponentOf_of_le hJ hJQ hQH)]
      exact hKa
    · refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJQ).trans
        (Subgroup.centralizer_le ?_)
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hAQ haA
  have haE : a ∈ Subgroup.centralizer (GorensteinWalter.componentLayerOf H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp ((sSup_le hJa) hx))
  have haF : a ∈ CFSG.fittingSubgroupOf H :=
    CFSG.Walter.generalizedFittingSubgroupOf_inf_centralizer_le H
      ⟨(h64 G S A hG a haA ha1' H hH).1, haE⟩
  have hza : IsPGroup 2 (Subgroup.zpowers a) :=
    G76.isPGroup_zpowers_of_pow_eq_one (e := 1) (by rw [pow_one]; exact hG.elem.2 a haA)
  have ha2 : a ∈ GorensteinWalter.qCoreOf H 2 :=
    CFSG.Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two
      (Subgroup.zpowers_le.mpr haF) hza (Subgroup.mem_zpowers a)
  have hO2K : GorensteinWalter.qCoreOf H 2 ≤ Subgroup.centralizer (K : Set G) := by
    have hp := GorensteinWalter.qCoreOf_isPGroup H 2
    have : Group.IsNilpotent (GorensteinWalter.qCoreOf H 2) := hp.isNilpotent
    have h := CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hKH' inferInstance
      (GorensteinWalter.qCoreOf_le H 2)
      (GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.qCoreOf_normal_in H 2))
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hHa : H ≤ Subgroup.centralizer ({a} : Set G) := by
    intro h hh
    have hO : h⁻¹ * a * h ∈ GorensteinWalter.qCoreOf H 2 := by
      have := (GorensteinWalter.qCoreOf_normal_in H 2).2 h⁻¹ (H.inv_mem hh) a ha2
      simpa using this
    have hR : IsPGroup 2 (A ⊔ GorensteinWalter.qCoreOf H 2 : Subgroup G) :=
      (G73.isPGroup hG).to_sup_of_normal_right' (GorensteinWalter.qCoreOf_isPGroup H 2)
        (hAH.trans (GorensteinWalter.le_normalizer_of_isNormalIn
          (GorensteinWalter.qCoreOf_normal_in H 2)))
    obtain ⟨T, hRT, hTcl⟩ := stronglyClosed_of_le_pGroup S hG.closed hR le_sup_left
    have hA' : h⁻¹ * a * h ∈ A := hTcl a haA h (hRT (Subgroup.mem_sup_right hO))
    have hC' : h⁻¹ * a * h ∈ C := ⟨hA', hO2K hO⟩
    rcases hCa _ hC' with h0 | h0
    · exfalso
      apply ha1'
      calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
        _ = 1 := by rw [h0]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * a = h * (h⁻¹ * a * h) := by rw [h0]
        _ = a * h := by group
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
    CFSG.Walter.map_conj_eq_iff_mem_normalizer.mp
      (huniq _ (CFSG.Walter.isComponentOf_map_conj hK (hHQ hh)))
  have hdecK := G73.eq_inf_sup_inf_centralizer h31 hS hG.elem hK
  have hAKa : A ≤ K ⊔ Subgroup.zpowers a := by
    rw [hdecK]
    refine sup_le (inf_le_right.trans le_sup_left) fun c hc => ?_
    rcases hCa c hc with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hKaH : K ⊔ Subgroup.zpowers a ≤ H :=
    sup_le hKH (Subgroup.zpowers_le.mpr (CFSG.Walter.mem_of_mem_benderM hH))
  have hHKa : H ≤ Subgroup.normalizer ((K ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro h hh
    rw [← CFSG.Walter.map_conj_eq_iff_mem_normalizer, Subgroup.map_sup,
      CFSG.Walter.map_conj_eq_iff_mem_normalizer.mpr (hHK hh), MonoidHom.map_zpowers]
    have hc : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.mp (hHa hh)
    have hca : (MulAut.conj h).toMonoidHom a = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hc]
      group
    rw [hca]
  have hFrat : H ≤ K ⊔ Subgroup.zpowers a ⊔ Subgroup.normalizer (A : Set G) :=
    G74.le_sup_normalizer hG.le hG.closed hKaH hHKa hAKa
  set N := Subgroup.normalizer (A : Set G) with hNdef
  set W : Subgroup G := ⨆ n : N, K.map (MulAut.conj (n : G)).toMonoidHom with hWdef
  have hKW : K ≤ W := by
    refine le_trans ?_ (le_iSup (fun n : N => K.map (MulAut.conj (n : G)).toMonoidHom) 1)
    intro k hk
    exact ⟨k, hk, by simp⟩
  have hNW : N ≤ Subgroup.normalizer (W : Set G) := by
    intro m hm
    have hle : W.map (MulAut.conj m).toMonoidHom ≤ W := by
      rw [hWdef, Subgroup.map_iSup]
      refine iSup_le fun n => ?_
      rw [CFSG.Walter.map_conj_map_conj]
      exact le_iSup (fun n : N => K.map (MulAut.conj (n : G)).toMonoidHom)
        ⟨m * n, N.mul_mem hm n.2⟩
    exact CFSG.Walter.mem_normalizer_of_conj_mem' fun x hx => hle ⟨x, hx, rfl⟩
  have haN : a ∈ N := Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
    fun x hx => congrArg Subtype.val (hG.elem.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := by
    refine hFrat.trans (sup_le (sup_le (hKW.trans Subgroup.le_normalizer) ?_) hNW)
    rw [Subgroup.zpowers_le]
    exact hNW haN
  have hWtop : W = ⊤ := by
    have hNWtop : Subgroup.normalizer (W : Set G) = ⊤ := by
      rcases eq_or_lt_of_le hHW with heq | hlt
      · exact absurd (hNW.trans heq.symm.le) h3
      · exact hHco.2 _ hlt
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp hNWtop
    rcases hWn.eq_bot_or_eq_top with h0 | h0
    · exfalso
      exact CFSG.Walter.ne_bot_of_isComponentOf hK (le_bot_iff.mp (h0 ▸ hKW))
    · exact h0
  have hSA : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) :=
    G76.le_centralizer_of_odd_index hG (by rw [hidx]; decide)
  obtain ⟨-, T₀, hT₀, htype⟩ := exists_g36Hyp h31 hS hG.elem hK
  have hKq : CFSG.Open.IsQuasisimple K := hT₀.quasisimple
  rcases htype with hI | hII
  · exact (G76.false_of_typeI hG hA8 haA hKq hI ⟨T₀, hT₀⟩ hC2 hdecK (hCH.trans hHK)
      hSA).elim
  have hAT : A.subgroupOf K = (T₀ : Subgroup K) := G76.eq_sylow_of_typeII hT₀ hII
  have hT₀ab : IsMulCommutative (T₀ : Subgroup K) := by
    have := hG.elem.1
    rw [← hAT]
    exact Subgroup.comap_injective_isMulCommutative (H := A) K.subtype_injective
  have hacts : ∀ w ∈ Subgroup.centralizer (A : Set G), IsPGroup 2 (Subgroup.zpowers w) →
      ∃ b ∈ (T₀ : Subgroup K), ∀ k ∈ K, w * k * w⁻¹ = (b : G) * k * (b : G)⁻¹ := by
    intro w hwA hw
    refine G76.exists_acts_of_sylow hKq T₀ hT₀ab hw (fun p hp => ?_) (hHK (hCH ?_))
    · rw [← hAT] at hp
      exact (Subgroup.mem_centralizer_iff.mp hwA p (Subgroup.mem_subgroupOf.mp hp)).symm
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA) hwA
  have hSab : IsMulCommutative (S : Subgroup G) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    set z := (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ with hz
    have hzW : W ≤ Subgroup.centralizer ({z} : Set G) := by
      refine iSup_le fun n => ?_
      rintro _ ⟨k, hk, rfl⟩
      have hconjA : ∀ s ∈ (S : Subgroup G), (n : G)⁻¹ * s * n ∈
          Subgroup.centralizer (A : Set G) := by
        intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have hnc : (n : G) * c * (n : G)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp n.2 c).mp hc
        have h1 := Subgroup.mem_centralizer_iff.mp (hSA hs) _ hnc
        calc c * ((n : G)⁻¹ * s * n) = (n : G)⁻¹ * (((n : G) * c * (n : G)⁻¹) * s) * n := by
              group
          _ = (n : G)⁻¹ * (s * ((n : G) * c * (n : G)⁻¹)) * n := by rw [h1]
          _ = (n : G)⁻¹ * s * n * c := by group
      have hconj2 : ∀ s ∈ (S : Subgroup G), IsPGroup 2
          (Subgroup.zpowers ((n : G)⁻¹ * s * n)) := by
        intro s hs
        obtain ⟨e, he⟩ := S.isPGroup' ⟨s, hs⟩
        apply G76.isPGroup_zpowers_of_pow_eq_one (e := e)
        have hs2 : s ^ 2 ^ e = 1 := by
          have := congrArg Subtype.val he
          simpa using this
        have e1 : (n : G)⁻¹ * s * n = (n : G)⁻¹ * s * ((n : G)⁻¹)⁻¹ := by rw [inv_inv]
        rw [e1, conj_pow, hs2]
        group
      obtain ⟨b, hb, hbx⟩ := hacts _ (hconjA x x.2) (hconj2 x x.2)
      obtain ⟨c, hc, hcy⟩ := hacts _ (hconjA y y.2) (hconj2 y y.2)
      have hbc : (b : G) * c = c * b := congrArg Subtype.val
        (congrArg Subtype.val (hT₀ab.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩))
      have hz' := G76.commutator_acts_trivially b.2 c.2 hbx hcy hbc k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e1 : (n : G)⁻¹ * x * n * ((n : G)⁻¹ * y * n) * ((n : G)⁻¹ * x * n)⁻¹ *
          ((n : G)⁻¹ * y * n)⁻¹ = (n : G)⁻¹ * z * n := by rw [hz]; group
      rw [e1] at hz'
      calc (n : G) * k * (n : G)⁻¹ * z = (n : G) * (k * ((n : G)⁻¹ * z * n)) * (n : G)⁻¹ := by
            group
        _ = (n : G) * (((n : G)⁻¹ * z * n) * k) * (n : G)⁻¹ := by rw [hz']
        _ = z * ((n : G) * k * (n : G)⁻¹) := by group
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({z} : Set G) := hzW (hWtop ▸ Subgroup.mem_top g)
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hZ : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨u, v, huv⟩ := hG.nonabelian
        exact huv (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top v) u)
    rw [hZ, Subgroup.mem_bot] at hzc
    rw [hz] at hzc
    have : (x : G) * y = y * x := by
      calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hzc, one_mul]
    exact this
  exact G76.isTypeJR_of_isMulCommutative hG hA8 hSab

theorem G76_of
    (h37 : S_G37) (h311 : S_G311) : S_G76 :=
  G76_of' G31 (G64_of_steps h37 h311) (G74_of_steps h37 h311) (G75_of_steps h37 h311)

end CFSG.Goldschmidt
