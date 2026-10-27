module

public import CFSG.GH74.GLS.Bg.Iii2.ExtBasic
public import CFSG.GH74.GLS.NT44.RigidActor
public import CFSG.GH74.GLS.NT44.GammaProperness
public import CFSG.GH74.GLS.NT44.ProductDisconnection
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt

import CFSG.GH74.GLS.NT44.RigidSeed
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.RigidExhaustion
import CFSG.GH74.GLS.NT44.L34SylowCentralizer
import CFSG.GH74.GLS.Stage1.Thm4.P92Pump
import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.LocalAnalysis.OddStandard.HigherRank.BlowUpACentre
import CFSG.Holt.General.BasicComponents
import CFSG.GH74.GLS.NT44.ConjugateClosure
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.GLS.Bg.Iii2 CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem exists_rigid_selection_of_center_card_sixteen
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (x0 : G) (K0 : Subgroup G)
    (hterm : IsTwoTerminal x0 K0)
    (hL34 : IsL34Quotient (kBar K0))
    (h16 : Nat.card (center (kBar K0)) = 16) :
    ∃ (z : G) (T : Subgroup G),
      orderOf z = 2 ∧
      (RigidSet (kBar K0) z).Nonempty ∧
      (∀ s : G, orderOf s = 2 →
        (RigidSet (kBar K0) s).ncard ≤ (RigidSet (kBar K0) z).ncard) ∧
      (∀ s : G, orderOf s = 2 →
        (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) z).ncard →
        cLog s ≤ cLog z) ∧
      (∀ s : G, orderOf s = 2 →
        (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) z).ncard →
        cLog s = cLog z →
        s ∈ Kz (kBar K0) s → z ∈ Kz (kBar K0) z) ∧
      IsSylowOf 2 T (centralizer ({z} : Set G)) ∧
      IsSylowOf 2 T ⊤ ∧
      z ∈ T ∧
      T ≤ centralizer ({z} : Set G) ∧
      z ∈ zStar (Kz (kBar K0) z) := by
  classical
  clear _hKP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have h3 : 3 ≤ pRank 2 G := by
    have h1 : IsILo 2 x0 K0 := hterm.1
    have h2 : oBound 2 ≤ pRank 2 ↥(centralizer ({x0} : Set G)) := h1.2.1
    have h3' : oBound 2 = 3 := by simp [oBound]
    exact (h3' ▸ h2).trans (CFSG.GH74.GLS.Bg.pRank_subgroup_le (by norm_num) _)
  have hRank : ∀ u : G, orderOf u = 2 → 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    fun u hu => CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G
      (inferInstance : IsSimpleGroup G) hnonab h3 u hu
  obtain ⟨zSeed, JSeed, hSeed⟩ :=
    exists_rigidSeed_of_center_card_sixteen hnonab hterm h16
  have hSeedord : orderOf zSeed = 2 := hSeed.1.1.1
  have hSeedmem : JSeed ∈ RigidSet (kBar K0) zSeed := hSeed
  have hSnonempty : {s : G | orderOf s = 2}.Nonempty := ⟨zSeed, hSeedord⟩
  obtain ⟨x, hxS, hmax⟩ :=
    exists_lex_max (S := {s : G | orderOf s = 2}) hSnonempty
      (fun s : G => (RigidSet (kBar K0) s).ncard)
      (fun s : G => cLog s)
      (fun s : G => if s ∈ Kz (kBar K0) s then 1 else 0)
  have hx2 : orderOf x = 2 := hxS
  have hCountMax : ∀ s : G, orderOf s = 2 →
      (RigidSet (kBar K0) s).ncard ≤ (RigidSet (kBar K0) x).ncard :=
    fun s hs => (hmax s hs).1
  have hcLogMax : ∀ s : G, orderOf s = 2 →
      (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) x).ncard →
      cLog s ≤ cLog x :=
    fun s hs hc => ((hmax s hs).2 hc).1
  have hThird : ∀ s : G, orderOf s = 2 →
      (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) x).ncard →
      cLog s = cLog x →
      s ∈ Kz (kBar K0) s → x ∈ Kz (kBar K0) x := by
    intro s hs hcount hcl hsKz
    by_contra hxKz
    have hle := ((hmax s hs).2 hcount).2 hcl
    have hs1 : (if s ∈ Kz (kBar K0) s then 1 else 0) = 1 := if_pos hsKz
    have hx0 : (if x ∈ Kz (kBar K0) x then 1 else 0) = 0 := if_neg hxKz
    rw [hs1, hx0] at hle
    omega
  have hposSeed : 0 < (RigidSet (kBar K0) zSeed).ncard :=
    (Set.ncard_pos (s := RigidSet (kBar K0) zSeed) (Set.toFinite _)).mpr
      ⟨JSeed, hSeedmem⟩
  have hposx : 0 < (RigidSet (kBar K0) x).ncard :=
    lt_of_lt_of_le hposSeed (hCountMax zSeed hSeedord)
  have hxFamilyNonempty : (RigidSet (kBar K0) x).Nonempty :=
    (Set.ncard_pos (s := RigidSet (kBar K0) x) (Set.toFinite _)).mp hposx
  obtain ⟨T, hT, hxT⟩ := exists_sylow_mem hx2
  have hTcard : Nat.card ↥T = 2 ^ cLog x := hT.card_eq
  have l34_of_mem : ∀ {K : Subgroup G}, K ∈ RigidSet (kBar K0) x →
      IsL34Quotient (kBar K) := by
    intro K hK
    obtain ⟨e⟩ := hK.2
    exact CFSG.GH74.GLS.TwoThin.isL34Quotient_of_mulEquiv e.symm hL34
  have centre16_of_mem : ∀ {K : Subgroup G}, K ∈ RigidSet (kBar K0) x →
      Nat.card (center (kBar K)) = 16 := by
    intro K hK
    obtain ⟨e⟩ := hK.2
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact h16
  have pumpFact : ∀ y : G, orderOf y = 2 → (∀ t ∈ T, t * y = y * t) →
      ∃ J : Subgroup G → Subgroup G,
        (∀ K ∈ RigidSet (kBar K0) x, PumpUpLT 2 x K y (J K)) ∧
        (∀ K ∈ RigidSet (kBar K0) x, IsRigidOfType (kBar K0) y (J K)) ∧
        (RigidSet (kBar K0) y = J '' RigidSet (kBar K0) x) ∧
        (∀ K ∈ RigidSet (kBar K0) x, x ∈ normalizer (J K : Set G)) ∧
        (RigidSet (kBar K0) y).ncard = (RigidSet (kBar K0) x).ncard := by
    intro y hyo hyT
    have hyX : y ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hyT x hxT).symm
    have hxY : x ∈ centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hyT x hxT)
    have hpoint : ∀ K ∈ RigidSet (kBar K0) x,
        ∃ M : Subgroup G, PumpUpLT 2 x K y M := by
      intro K hK
      have hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hK.1.1.2.2
      have hKperf : ⁅K, K⁆ = K :=
        CFSG.GH74.GLS.TwoThin.commutator_self_of_isTwoComponent hKpc.1
          (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hKpc).2
      have hperfK : Group.IsPerfect (kBar K) :=
        (CFSG.GH74.GLS.TwoThin.isQuasisimple_hat hKpc).1
      have hnotEA : ¬ IsElementaryAbelian 2 ↥(center (kBar K)) :=
        CFSG.OddStandard.HigherRank.not_isElementaryAbelian_center_of_isL34Quotient
          (Q := kBar K) hperfK (l34_of_mem hK) (centre16_of_mem hK)
      have hZ : ∃ c ∈ center (kBar K), c * c ≠ 1 := by
        by_contra h
        have hsq : ∀ c : kBar K, c ∈ center (kBar K) → c * c = 1 := by
          intro c hc
          by_contra hc1
          exact h ⟨c, hc, hc1⟩
        apply hnotEA
        refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
        intro a
        apply Subtype.ext
        simpa [pow_two] using hsq (a : kBar K) a.2
      have hP : IsSylowOf 2 (T ⊓ K) K :=
        CFSG.GH74.GLS.Stage1.Thm4.P92.sylow_inf (Lh := kBar K0) hK hT
      let X : Subgroup G := centralizer ({x} : Set G)
      have hyX' : y ∈ X := hyX
      let yX : X := ⟨y, hyX'⟩
      let B : Subgroup X := K.subgroupOf X
      have hBpc : IsPComponent 2 B := hKpc.2
      obtain ⟨Sx, hSx⟩ := hT.exists_sylow_eq_subgroupOf
      have hSx_le : (Sx : Subgroup X) ≤ Subgroup.centralizer ({yX} : Set X) := by
        intro p hp
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (by
          simpa using hyT (p : G) (by
            have hp' : p ∈ T.subgroupOf X := by
              rw [← hSx]
              exact hp
            exact Subgroup.mem_subgroupOf.mp hp'))
      have hyXn : yX ∈ Subgroup.normalizer (B : Set X) :=
        CFSG.Holt.General.mem_normalizer_of_isPComponent_of_le_centralizer hSx_le hBpc
      have hyN : y ∈ normalizer (K : Set G) := by
        have h : yX ∈ (Subgroup.normalizer (K : Set G)).subgroupOf X := by
          rw [Subgroup.subgroupOf_normalizer_eq hKpc.1]
          exact hyXn
        simpa using Subgroup.mem_subgroupOf.mp h
      have hycs : y ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
        mem_centralizerSection_of_centralizes_sylow_of_isL34Quotient K (T ⊓ K) y
          hKperf (l34_of_mem hK) hZ hP hyN (fun p hp => (hyT p hp.1).symm)
      obtain ⟨M, hlt⟩ :=
        CFSG.GH74.GLS.TwoThin.exists_pumpup_of_involution hx2 hyo hKpc hyX hycs
          hK.1.1 (hRank y hyo)
      exact ⟨M, hlt⟩
    choose! J hJ using hpoint
    obtain ⟨hinj, hrig, hEq, hvert⟩ :=
      rigid_pump_exhaustion (fullQ := kBar K0) J hxY hJ (hCountMax y hyo)
    exact ⟨J, hJ, hrig, hEq, fun K hK => (hvert K hK).1,
      by rw [hEq, hinj.ncard_image]⟩
  obtain ⟨Q, hQ⟩ := hT.isPGroup.exists_le_sylow
  have hSp : IsPGroup 2 ↥(Q : Subgroup G) := Q.isPGroup'
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hSne : (Q : Subgroup G) ≠ ⊥ := by
    intro h
    have hxQ : x ∈ (Q : Subgroup G) := hQ hxT
    rw [h, Subgroup.mem_bot] at hxQ
    exact hx1 hxQ
  obtain ⟨y, hyQ, hyo, hycent⟩ := exists_involution_normal hSp le_rfl
    (fun s hs p hp => (Q : Subgroup G).mul_mem
      ((Q : Subgroup G).mul_mem hs hp) ((Q : Subgroup G).inv_mem hs)) hSne
  have hyT : ∀ t ∈ T, t * y = y * t := fun t ht => hycent t (hQ ht)
  obtain ⟨J, hJ, hrig, hEq, hvert, hcount⟩ := pumpFact y hyo hyT
  have hcl : cLog y ≤ cLog x := hcLogMax y hyo hcount
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
  have hSC : (Q : Subgroup G) ≤ centralizer ({y} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hycent s hs).symm
  have hTS : T = (Q : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge hQ
    rw [hk, hTcard]
    exact Nat.pow_le_pow_right (by norm_num) ((pow_le_cLog hSC hk).trans hcl)
  have hTsyl : IsSylowOf 2 T ⊤ := by
    apply isSylowOf_of_card le_top
    rw [hTS, Subgroup.card_top]
    exact Q.card_eq_multiplicity
  obtain ⟨K₁, hK₁⟩ := hxFamilyNonempty
  have hP₁ : IsSylowOf 2 (T ⊓ K₁) K₁ :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.sylow_inf (Lh := kBar K0) hK₁ hT
  have h2dvdK₁ : 2 ∣ Nat.card K₁ := by
    have h16dvd : 16 ∣ Nat.card (kBar K₁) := by
      have h := Subgroup.card_subgroup_dvd_card (center (kBar K₁))
      rwa [centre16_of_mem hK₁] at h
    have h2dvdbar : 2 ∣ Nat.card (kBar K₁) :=
      (show 2 ∣ 16 by norm_num).trans h16dvd
    simpa [kBar] using
      h2dvdbar.trans (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K₁))
  have hfac : 0 < (Nat.card K₁).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2dvdK₁
  have hPcard : Nat.card ↥(T ⊓ K₁) = 2 ^ (Nat.card K₁).factorization 2 := hP₁.card_eq
  have hPne : T ⊓ K₁ ≠ ⊥ := by
    intro h
    have h1 : 1 = 2 ^ (Nat.card K₁).factorization 2 := by
      rw [← hPcard, h, Subgroup.card_bot]
    have hgt : 1 < 2 ^ (Nat.card K₁).factorization 2 :=
      Nat.one_lt_pow (by omega) (by norm_num)
    omega
  let U : Subgroup G :=
    ⨆ (K : Subgroup G) (_ : K ∈ RigidSet (kBar K0) x), T ⊓ K
  have hUT : U ≤ T := iSup₂_le fun K _ => inf_le_left
  have hK₁le : T ⊓ K₁ ≤ U := fun p hp =>
    Subgroup.mem_iSup_of_mem K₁ (Subgroup.mem_iSup_of_mem hK₁ hp)
  have hUne : U ≠ ⊥ := by
    intro h
    have hle : T ⊓ K₁ ≤ (⊥ : Subgroup G) := by
      rw [← h]
      exact hK₁le
    exact hPne (le_bot_iff.mp hle)
  have hUnormal : ∀ t ∈ T, ∀ p ∈ U, t * p * t⁻¹ ∈ U := by
    intro t ht
    have hle : U ≤ U.comap (MulAut.conj t).toMonoidHom := by
      refine iSup₂_le fun K hK => ?_
      intro p hp
      have hK' : IsRigidOfType (kBar K0) x (cmap t K) := by
        have h := isRigidOfType_conj (Q := kBar K0) hK t
        rwa [conj_fix_of_mem_centralizer (hT.le ht)] at h
      have hmem : t * p * t⁻¹ ∈ T ⊓ cmap t K := by
        refine ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), mem_cmap.2 ?_⟩
        have e : t⁻¹ * (t * p * t⁻¹) * t = p := by group
        rw [e]
        exact hp.2
      exact Subgroup.mem_iSup_of_mem (cmap t K) (Subgroup.mem_iSup_of_mem hK' hmem)
    exact fun p hp => hle hp
  obtain ⟨yU, hyU, hyUo, hyUT⟩ :=
    exists_involution_normal hT.isPGroup hUT hUnormal hUne
  obtain ⟨J₂, hJ₂, hrig₂, hEq₂, hvert₂, hcount₂⟩ := pumpFact yU hyUo hyUT
  have hcl₂ : cLog yU ≤ cLog x := hcLogMax yU hyUo hcount₂
  have hTCyU : T ≤ centralizer ({yU} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hyUT t ht)
  have hclx : cLog x ≤ cLog yU := pow_le_cLog hTCyU hTcard
  have hcleq : cLog yU = cLog x := le_antisymm hcl₂ hclx
  have hUKz : U ≤ Kz (kBar K0) yU := by
    refine iSup₂_le fun K hK => ?_
    intro p hp
    have hpT : p ∈ T := hp.1
    have hpK : p ∈ K := hp.2
    have hpY : p ∈ centralizer ({yU} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hyUT p hpT)
    have hxY₂ : x ∈ centralizer ({yU} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hyUT x hxT)
    have h2el : ∃ m : ℕ, p ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hT.isPGroup.exists_pow_pow_eq_one ⟨p, hpT⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hpJ : p ∈ J₂ K :=
      CFSG.GH74.GLS.Stage1.Thm4.P92.mem_pumpUp hK.1 (hJ₂ K hK) hxY₂
        (hvert₂ K hK) hpK hpY h2el
    have hleJ : J₂ K ≤ Kz (kBar K0) yU := le_sSup (hrig₂ K hK)
    exact hleJ hpJ
  have hyKz : yU ∈ Kz (kBar K0) yU := hUKz hyU
  have hxKz : x ∈ Kz (kBar K0) x := hThird yU hyUo hcount₂ hcleq hyKz
  have hxZstar : x ∈ zStar (Kz (kBar K0) x) :=
    CFSG.GH74.GLS.Stage1.Thm4.Alt51.z_mem_zStar
      (K := Kz (kBar K0) x) (z := x)
      (by simpa using (kz_le_centralizer (Q := kBar K0) (z := x))) hxKz
  exact ⟨x, T, hx2, ⟨K₁, hK₁⟩, hCountMax, hcLogMax, hThird,
    hT, hTsyl, hxT, hT.le, hxZstar⟩

theorem exists_rigid_actor_of_center_card_sixteen
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (x0 : G) (K0 : Subgroup G)
    (hterm : IsTwoTerminal x0 K0)
    (hL34 : IsL34Quotient (kBar K0))
    (h16 : Nat.card (center (kBar K0)) = 16) :
    ∃ (x v : G) (J T : Subgroup G),
      orderOf x = 2 ∧
      J ∈ RigidSet (kBar K0) x ∧
      (∀ s : G, orderOf s = 2 →
        Nat.card ↥(RigidSet (kBar K0) s) ≤ Nat.card ↥(RigidSet (kBar K0) x)) ∧
      (∀ s : G, orderOf s = 2 →
        (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) x).ncard →
        cLog s ≤ cLog x) ∧
      (∀ s : G, orderOf s = 2 →
        (RigidSet (kBar K0) s).ncard = (RigidSet (kBar K0) x).ncard →
        cLog s = cLog x →
        s ∈ Kz (kBar K0) s → x ∈ Kz (kBar K0) x) ∧
      IsSylowOf 2 T (centralizer ({x} : Set G)) ∧
      IsSylowOf 2 T ⊤ ∧
      x ∈ T ∧ T ≤ centralizer ({x} : Set G) ∧
      x ∈ zStar (Kz (kBar K0) x) ∧
      v ∈ T ∧ orderOf v = 2 ∧ IsConj x v ∧ v * x = x * v ∧
      v ∈ normalizer (J : Set G) ∧
      v ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, T, hx2, hfamily, hCountMax, hcLogMax, hThird,
      hTsylowC, hTsylowG, hxT, hTle, hxZstar⟩ :=
    exists_rigid_selection_of_center_card_sixteen
      (G := G) hnonab hKP x0 K0 hterm hL34 h16
  obtain ⟨J, hJ⟩ := hfamily
  set B : Subgroup G := Subgroup.closure {y : G | y ∈ T ∧ IsConj x y} with hBdef
  set P : Subgroup G := Kz (kBar K0) x with hPdef
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  have hCardMax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet (kBar K0) s) ≤ Nat.card ↥(RigidSet (kBar K0) x) := by
    intro s hs
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact hCountMax s hs
  have hBnot : ¬ (B ≤ zStar P) := by
    intro hB
    have hBT : B ≤ T := by
      rw [hBdef]
      exact (Subgroup.closure_le T).mpr (fun a ha => ha.1)
    have hBW : B ≤ T ⊓ zStar P := le_inf hBT hB
    set W : Subgroup G := T ⊓ zStar P with hWdef
    have hPleC : P ≤ C := by
      rw [hPdef, hCdef]
      exact kz_le_centralizer (Q := kBar K0) (z := x)
    have hzStar_le_C : zStar P ≤ C := (show zStar P ≤ P from inf_le_left).trans hPleC
    have hC_le_N : C ≤ normalizer (zStar P : Set G) := by
      intro c hc
      have hcN : c ∈ normalizer (P : Set G) := by
        rw [hCdef] at hc
        rw [hPdef]
        exact centralizer_le_normalizer_kz (Q := kBar K0) (z := x) hc
      exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_normalizer_zStar hcN
    have hW : IsSylowOf 2 W (zStar P) := by
      have h1 : IsSylowOf 2 (T ⊓ zStar P) (zStar P) :=
        hTsylowC.inf_of_le_normalizer hzStar_le_C hC_le_N
      rw [hWdef]
      exact h1
    have hWT : W ≤ T := by
      rw [hWdef]
      exact inf_le_left
    have hZW : B ≤ W := by
      rw [hWdef]
      exact hBW
    have hBclosure : Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤ T ⊓ zStar P := by
      rw [← hBdef]
      exact hBW
    obtain ⟨hZel, hZrank⟩ :=
      elementary_rank_conjugate_closure_of_le_zStar
        (P := P) (T := T) (x := x) hnonab hTsylowG hx2 hBclosure
    have hGamma : gammaK 2 B 1 ≠ ⊤ := by
      have h := gammaK_conjugate_closure_ne_top_of_le_rigid_center_sylow
        (fullQ := kBar K0) (T := T) (W := W) (J := J) (x := x)
        hnonab hL34 hx2 hCountMax hJ h16 hTsylowG hxT hTle hW hWT hZW
      simpa [hBdef] using h
    have hPD : CFSG.GH74.Uniqueness.IsProductDisconnected (conjugatesOf x) (gammaK 2 B 1) := by
      have h := isProductDisconnected_conjugatesOf_of_gammaK_conjugate_closure_ne_top
        (T := T) (x := x) hTsylowG hx2 hxT hTle hZel hZrank
        (by simpa [hBdef] using hGamma)
      simpa [hBdef] using h
    have hInv : CFSG.GH74.Uniqueness.IsInvariantInvolutionSet (conjugatesOf x) := by
      refine ⟨?_, ?_⟩
      · intro z hz
        exact hz.orderOf_eq.symm.trans hx2
      · intro z hz g
        exact hz.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    obtain ⟨-, S, hM_eq⟩ :=
      CFSG.GH74.Uniqueness.S_CorZD_unconditional G inferInstance hnonab
        (conjugatesOf x) (gammaK 2 B 1) hInv hPD
    have hMsol : Group.IsSolvable ↥(gammaK 2 B 1) := by
      rw [hM_eq]
      exact CFSG.GH74.GLS.C3.Layer1.U1a.isSolvable_normalizer_sylow_two S
    have hx_B : x ∈ B := by
      rw [hBdef]
      exact Subgroup.subset_closure ⟨hxT, IsConj.refl x⟩
    have hC_le_M : C ≤ gammaK 2 B 1 := by
      rw [hCdef]
      exact CFSG.GH74.GLS.C3.Layer1.U1a.centralizer_le_gammaK (Q := B) hx_B hx2
    have hJ_le_C : J ≤ C := by
      rw [hCdef]
      exact hJ.1.1.2.2.1
    have hJ_le_M : J ≤ gammaK 2 B 1 := hJ_le_C.trans hC_le_M
    have hJsol : Group.IsSolvable ↥J :=
      @Group.isSolvable_of_isSolvable_injective ↥J ↥(gammaK 2 B 1) _ _
        (Subgroup.inclusion hJ_le_M) (Subgroup.inclusion_injective hJ_le_M) hMsol
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.not_isSolvable_of_isPCompIn
      (H := C) (J := J) hJ.1.1.2.2 hJsol
  obtain ⟨v, hvT, hvconj, hv2, hvN, hvact⟩ :=
    exists_conjugate_normalizing_not_mem_cSec_of_not_closure_le_zStar
      (fullQ := kBar K0) (x := x) (K := J) (T := T)
      hJ hTsylowC hL34 h16 hxZstar hCountMax hBnot
  exact ⟨x, v, J, T, hx2, hJ, hCardMax, hcLogMax, hThird,
    hTsylowC, hTsylowG, hxT, hTle, hxZstar, hvT, hv2, hvconj,
    Subgroup.mem_centralizer_singleton_iff.mp (hTle hvT), hvN, hvact⟩

end CFSG.GH74.GLS.NT44
