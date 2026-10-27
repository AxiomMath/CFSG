module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem520
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

theorem stmt5_1_20_of_sqtk_F4
    (h5114 : Stmt5_1_14_first_F4) (h331 : Stmt3_3_1_F4) (h510 : Stmt5_1_10_F4)
    (h512 : Stmt5_1_2_F4) (h518 : Stmt5_1_18_F4) (h519 : Stmt5_1_19_F4) (hE54 : E54L34FactSQTK)
    (hH11 : H11ThreeFact) (hGal : OrthOddGalFact) : Stmt5_1_20_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK hnot D₃ hD₃ h3
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have hh := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.isUniqueM_F4 h5114
  suffices hD₃M : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) by
    refine ⟨hD₃M, ?_⟩
    by_contra hne
    apply hD₃M
    rw [sup_comm] at hne
    exact le_of_pCoreOf_sup_ne_bot hU hne
  intro hD₃M

  rcases h519 G T M L V H B D n hyp hN hV hK hnot D₃ hD₃ h3 with
    ⟨hn, -⟩ | ⟨-, -, hn⟩ | ⟨hmod, hgt, h3n, hD₃B, -, horth⟩
  · exact hn hD₃M
  · exact hn hD₃M
  obtain ⟨m, hnm, -⟩ := id horth
  have hn6 : n ≠ 6 := fun h6 => h3n (by rw [h6]; norm_num)
  have hm5 : 5 ≤ m := by omega
  have horth' : IsOrthCh5 L V (2 * m) := hnm ▸ horth
  set K := oTwoUpper H with hKdef
  have hTH : T ≤ H := hyp.hStar.1.1
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H

  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdBorel : d ∈ borelL T L := hN.2.1.1 (hD₃ hdD₃)
  have hdL : d ∈ L := hdBorel.1

  have hred := hV.isTwoReducedIn
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hVT : V ≤ T := hh.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hCLT : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
    hh.inf_centralizer_le_T hred.2.1 hV.2.2
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n hyp hN hV hK).2.2
  have hVne : V ≠ ⊥ := by
    intro hb
    apply hV.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp

  obtain ⟨-, hZD₃⟩ := h518 G T M L V H B D n hyp hN hV hK D₃ hD₃ h3 hD₃M
  have hdfix : ∀ z ∈ quasithinOmegaOneCenter T, d * z * d⁻¹ = z := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (D₃ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZD₃ hz
    rw [Subgroup.mem_centralizer_iff.mp hzC d hdD₃, mul_assoc, mul_inv_cancel, mul_one]

  obtain ⟨hJ, -, -, hUJ, -⟩ :
      thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
        L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
        L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) ∧
        IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M ∧
        IsUniqueM (Subgroup.normalizer (baum T : Set G)) M := by
    rcases h512 G T M L V n hh hV with h1 | ⟨-, hquot⟩ | ⟨-, hn2, -⟩
    · exact h1
    · exfalso
      have hTC : T ≤ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        le_normalizer_inf hTV (le_normalizer_centralizer_of_le_normalizer hh.T_le_normalizer)
      have hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
        by_contra hne
        obtain ⟨c, hc, hc1, hcZ⟩ :=
          exists_mem_omegaOneCenter hT2 hred.2.2.1 inf_le_left hVT hTC hne
        have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hcZ, hc.2⟩
        rw [hZL, Subgroup.mem_bot] at this
        exact hc1 this
      have hnat := isNatModCh5_of_isNatQuotCh5 hquot hC
      obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl hVT hTV hVne
      exact hh.conj_ne_of_isNatModCh5 hnat hdL hd3 hd1 hzV hz1 (hdfix z hzZ)
    · omega

  set QL := T ⊓ Subgroup.centralizer (V : Set G) with hQLdef
  set S := (T ⊓ L) ⊔ QL with hSdef
  have hQLeq : QL = pCoreOf 2 (L ⊔ T) := hh.centralizer_eq_pCoreOf hV
  have hST : S ≤ T := sup_le inf_le_left inf_le_left
  have hTQL : T ≤ Subgroup.normalizer (QL : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer_of_le_normalizer hTV)
  have hTTL : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer hh.T_le_normalizer
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hle : S ≤ S.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTTL ht) y).mp hy)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTQL ht) y).mp hy)
    exact hle hx
  have hVS : V ≤ S := by
    intro v hv
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hVT hv, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact comm_of_mem_of_isElemAbelian hred.2.2.1 hw hv
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJS : thompsonJ T ≤ S :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hJT hx, (hJ hx).2⟩)

  have hpR : 4 < CFSG.Open.pRank 2 S := by

    have hTLC : ¬ T ⊓ L ≤ Subgroup.centralizer (V : Set G) := by
      intro hle
      have h1 : T ⊓ L ≤ pCoreOf 2 L := fun x hx => hh.inf_centralizer_le hLV hV.2.2 ⟨hx.2, hle hx⟩
      have h2 : pCoreOf 2 L ≤ T ⊓ L := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS
      have heq : T ⊓ L = pCoreOf 2 L := le_antisymm h1 h2
      have hodd := hS.2.2
      have he : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
        exact map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥L)
      rw [heq, he, Subgroup.index, card_of_lieModel_L2 (by omega) hh.lie] at hodd
      apply hodd
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    obtain ⟨x, hxTL, hxC⟩ : ∃ x ∈ T ⊓ L, x ∉ Subgroup.centralizer (V : Set G) := by
      by_contra hall
      push Not at hall
      exact hTLC hall
    have hex : ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
      obtain ⟨j, hj⟩ := hT2 ⟨x, hxTL.1⟩
      refine ⟨j, ?_⟩
      have : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      rw [this]
      exact Subgroup.one_mem _
    classical
    set k := Nat.find hex with hkdef
    have hk : x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, pow_one] at hk
      exact hxC hk
    set y := x ^ 2 ^ (k - 1) with hydef
    have hyC : y ∉ Subgroup.centralizer (V : Set G) := Nat.find_min hex (by omega)
    have hy2 : y ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      have e : y ^ 2 = x ^ 2 ^ k := by
        rw [hydef, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      rw [e]; exact hk
    have hyTL : y ∈ T ⊓ L := (T ⊓ L).pow_mem hxTL _

    have hA₀N : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr (hTV hyTL.1)
    have hA₀L : autOn (Subgroup.zpowers y) V ≤ autOn L V :=
      autOn_le_autOn V (Subgroup.zpowers_le.mpr hyTL.2)
    have hA₀el : IsElemAbelian 2 (autOn (Subgroup.zpowers y) V) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun φ hφ => ?_⟩
      · obtain ⟨g, hg, hga⟩ := mem_autOn_iff.mp a.2
        obtain ⟨g', hg', hgb⟩ := mem_autOn_iff.mp b.2
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg'
        have hc : g * g' = g' * g := Subtype.ext (by
          show (g : G) * g' = g' * g
          rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])
        apply Subtype.ext
        show (a : MulAut ↥V) * b = b * a
        rw [← hga, ← hgb, ← map_mul, ← map_mul, hc]
      · obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.mp hφ
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [← map_pow]
        apply A4.conjAct_eq_one_iff.mpr
        have e : ((g ^ 2 : Subgroup.normalizer (V : Set G)) : G) = (y ^ 2) ^ i := by
          rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
            mul_comm]
        rw [e]
        exact Subgroup.zpow_mem _ hy2 i
    have hA₀C : ¬ Subgroup.zpowers y ≤ Subgroup.centralizer (V : Set G) := fun hle =>
      hyC (hle (Subgroup.mem_zpowers y))
    have hineq := hH11 G L V (Subgroup.zpowers y) m horth' (by omega) hA₀N hA₀L hA₀el hA₀C
    have hpos : 0 < (Subgroup.zpowers y ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (Subgroup.zpowers y) := relIndex_pos' _ _
    have hidx : (V ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)).relIndex V ≤
        Nat.card V := by
      have := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) V
      have hc : 0 < Nat.card ↥((V ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) ⊓ V) :=
        Nat.card_pos
      nlinarith
    have hV32 : 2 ^ m ≤ Nat.card V := by nlinarith
    obtain ⟨k', hk'⟩ := (IsPGroup.iff_card).mp (isPGroup_of_isElemAbelian hred.2.2.1)
    have hk'5 : 5 ≤ k' := by
      by_contra hlt
      have : 2 ^ k' < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
      omega
    exact lt_of_lt_of_le (by omega) (CFSG.SectionRank.le_pRank (by norm_num) hVS hred.2.2.1 hk')
  have hpRT : 4 < CFSG.Open.pRank 2 T :=
    lt_of_lt_of_le hpR (CFSG.SectionRank.pRank_mono (by norm_num) hST)

  have hJST : thompsonJ T = thompsonJ S := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    refine thompsonJi_eq_of_le (by omega) ?_ hST
    rw [← thompsonJ_eq_thompsonJi_zero]
    exact hJS

  obtain ⟨-, -, hBorel, -, -⟩ := h510 G T M L H B D n hyp hN
  have hTK := hyp.inf_oTwoUpper_eq hBorel
  have hdMH : d ∈ M ⊓ H := hN.1.1 (hD₃B ▸ hdD₃)
  have hdTK : d ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [hKdef, ← hTK]
    exact le_normalizer_inf (le_normalizer_pCoreOf 2 _) (inf_le_right.trans hHK) hdMH
  have hTKS : T ⊓ K ≤ S := hGal G L T V (T ⊓ K) n d horth hmod hT2 hh.T_le_normalizer hTV hS
    hCLT hdBorel hord inf_le_left hdTK

  set X := K ⊔ S with hXdef
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := (hST.trans hTH).trans hHK
  have hXH : X ≤ H := sup_le hKH (hST.trans hTH)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (hh.isSylowTwoOf hTH)]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => ?_
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hle : X ≤ X.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHK (hTH ht)) y).mp hy)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTS ht) y).mp hy)
    exact hle hx
  have hTX : T ⊓ X = S := by
    refine le_antisymm (fun x hx => ?_) (le_inf hST le_sup_right)
    have hset : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSK
    have hx' : x ∈ (K : Set G) * (S : Set G) := by rw [← hset]; exact hx.2
    obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    have hkT : k ∈ T := by
      have : k = k * s * s⁻¹ := by group
      rw [this]
      exact T.mul_mem hx.1 (T.inv_mem (hST hs))
    exact S.mul_mem (hTKS ⟨hkT, hk⟩) hs
  have hSX : IsSylowTwoOf S X := by
    rw [← hTX]
    exact A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf hTH) hXH hHX
  have hcharH : CharTwo H := charTwo_of_inH' hh.qtke hh.sylow hyp.hStar.1
  have hcharX : CharTwo X :=
    CharTwo.of_normal hcharH hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)
  have hXC : X ⊓ centralizerModO2 K ≤ pCoreOf 2 X := by
    have h1 : X ⊓ centralizerModO2 K ≤ pCoreOf 2 H ⊓ X :=
      fun x hx => ⟨h.inf_centralizerModO2_le ⟨hXH hx.1, hx.2⟩, hx.1⟩
    refine h1.trans (le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left))
    exact le_normalizer_inf (hXH.trans (le_normalizer_pCoreOf 2 H)) Subgroup.le_normalizer

  have hKM : ¬ K ≤ M := by
    intro hKM
    apply hyp.hStar.2.1
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (hh.isSylowTwoOf hTH)]
    exact sup_le hKM hh.T_le
  have hSQX : SQTKGroup ↥X := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hh.qtke hh.simple hh.nonabelian hyp.hStar.1.2) hXH
  rcases hE54 G X K S hSQX hcharX hSX le_sup_left (hXH.trans hHK) hK rfl hXC with hJn | hEn
  ·
    rw [← hJST] at hJn
    exact hKM ((le_sup_left.trans hJn).trans hUJ.1.2)

  set E := CFSG.Quasithin.omegaOneCenterOf (thompsonJi S 4) with hEdef
  have hJ4S : thompsonJi S 4 ≤ S := iSup₂_le fun _ hA => hA.1
  have hJne : thompsonJi S 4 ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
    have hc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    rw [pow_zero, mul_one] at hc
    have hAJ : A ≤ thompsonJi S 4 := by
      refine le_trans ?_ (thompsonJi_mono (Nat.zero_le 4) hpR)
      exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsElemAbelianCorank S 0 B) => B) A
        (isMaxElemAbelian_iff_corank_zero.mp hA) le_rfl
    intro hb
    rw [hb, le_bot_iff] at hAJ
    rw [hAJ, Subgroup.card_bot] at hc
    have : (2 : ℕ) ^ 0 < 2 ^ CFSG.Open.pRank 2 S := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hEne : E ≠ ⊥ :=
    omegaOneCenterOf_ne_bot ((hT2.to_le hST).to_le hJ4S) hJne
  have hE2 : IsPGroup 2 E := (hT2.to_le hST).to_le
    ((Subgroup.closure_le _).mpr (fun x hx => hJ4S hx.1.1))

  have hJ4C : ¬ thompsonJi S 4 ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have hle' : thompsonJi S 4 ≤ QL := le_inf (hJ4S.trans hST) hle
    have heq : thompsonJi S 4 = thompsonJi QL 4 :=
      thompsonJi_eq_of_le hpR hle' (le_sup_right : QL ≤ S)
    have hLTE : L ⊔ T ≤ Subgroup.normalizer (E : Set G) := by
      rw [hEdef, heq]
      refine le_trans ?_ (normalizer_le_normalizer_omegaOneCenterOf _)
      refine le_trans ?_ (normalizer_le_normalizer_thompsonJi QL 4)
      rw [hQLeq]
      exact le_normalizer_pCoreOf 2 _
    have hloc : IsTwoLocal (Subgroup.normalizer (E : Set G)) := ⟨E, hEne, hE2, rfl⟩
    obtain ⟨M', hM', hle''⟩ := exists_maxTwoLocal_ge hloc
    have hM'eq : M' = M := (hh.isUniqueM_F4 h331).2 M' ⟨hM', hLTE.trans hle''⟩
    exact hKM (((le_sup_left : K ≤ X).trans hEn).trans (hM'eq ▸ hle''))

  obtain ⟨A, hA, hAC⟩ : ∃ A, IsElemAbelianCorank S 4 A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    exact hJ4C (iSup₂_le fun A hA => hall A hA)
  have hB24 := card_le_relIndex_mul_card_mul_two_pow hred.2.2.1 hVS hA
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := (hA.1.trans hST).trans hTV
  have hAL : autOn A V ≤ autOn L V := by
    refine (autOn_le_of_le_sup (X := T ⊓ L) (Q := QL) ?_ inf_le_right ?_).trans
      (autOn_le_autOn V inf_le_right)
    · rw [sup_comm]; exact hA.1
    · exact inf_le_left.trans hTQL
  have hH := hH11 G L V A m horth' (by omega) hAN hAL (isElemAbelian_autOn hA.2.1) hAC

  have hcard := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rw [inf_of_le_left inf_le_left] at hcard
  have hpos1 : 0 < (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A :=
    relIndex_pos' _ _
  have hpos2 : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h16 : 2 ^ m ≤ 2 ^ 4 := by
    have h1 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A * 2 ^ m *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
        (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ 4 := by
      calc _ ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
            Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.mul_le_mul_right _ hH
        _ = Nat.card V := hcard
        _ ≤ _ := hB24
    have h2 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ m ≤
        (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ 4 := by
      calc _ = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A * 2 ^ m *
            Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by ring
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hpos1 hpos2)
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h16
  omega

end CFSG.Quasithin.H13
