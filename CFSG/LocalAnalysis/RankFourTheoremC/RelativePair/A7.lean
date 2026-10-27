module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Main
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Frame
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Block
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Module
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Normal
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Three
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Offender
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Split
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Facts
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Cover
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_RankGrp
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairTwoCore
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Setting

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup Equiv CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem KFactSetting.exists_a7Frame {n : ℕ} {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : KFactSetting n G) (hd : MaximalRelativePair p P M D R T)
    (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) (hp3 : p = 3)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H))
    (hn : ∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
      p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G)) :
    ∃ ι : ↥H →* Perm (Fin 7), A7Frame D H V ι := by
  subst hp3
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hDp : IsPGroup 3 D := P.isPGroup'.to_le hd.ext.obstruction.2.1
  have hDcard : Nat.card D = 9 := by
    have := (hd.ext.isElemAbelian_of_isMulCommutative Nat.prime_three hd.abelian).2
    simpa using this
  obtain ⟨ι, hker, hA7, hDι, hVι⟩ := a7f_exists_hom (primeComplementCore_coprime 3)
    (fun N hN hc => normal_coprime_le_primeComplementCore 3 N hN hc)
    (by exact hfacts.pCore_quotient)
    (a7f_card_le_nine hfacts.pRank_eq) ((CFSG.isComponent_iff_open L).mpr hL) e
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hDcard)
    (hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm)
    (invariantTwoMaximalWithin_internal_global D H V hDH hfacts.maximal)
  have hH : H ≠ ⊤ := by
    have := hS.simple
    exact twoLocal_ne_top hS.nonab H hopt.pair.cand.twoLocal
  refine ⟨ι,
    { D_le := hDH, V_le := hVH, S_le := hfacts.pCore_le, V_two := hfacts.maximal.2.1
      D_norm := hfacts.maximal.2.2.1, D_three := hDp, D_card := hDcard
      H_norm := hfacts.normalizer_pCore, charTwo := hS.obstruction.charTwo H hopt.pair.cand.twoLocal
      sylow := hfacts.sylow, K_coprime := ?_, card_V := hcard, ker_eq := hker, A7_le := hA7
      D_img := hDι, V_img := hVι, kGroup := fun X hXH => a7f_isKGroup hS.kProper hH hXH
      noCover := ?_, exists_n := hn }⟩
  · rw [a7K, Subgroup.card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime 3
  · intro Y hYV hY1 hY hcov
    obtain ⟨n, hnH, hnD, hjoin⟩ := hn
    have hle := a7f_map_conj_le hVH (hVι.le.trans vOne_le_alternatingGroup) hcov hnH
    rw [hker] at hle
    exact hopt.not_map_conj_le_of_normalizer hd hfacts rfl hYV hY1 hY hnH hnD hjoin hle

theorem KFactSetting.gl83RelPair2A7Module_proved
    {n : ℕ} (hS : KFactSetting n G) :
    GL83RelPair2A7Module G := by
  intro p hp P M D R T H V hd hopt hfacts hp3 L hL hLA hcard hn
  obtain ⟨e⟩ := hLA
  obtain ⟨ι, hF⟩ := hS.exists_a7Frame hd hopt hfacts hp3 hL e hcard hn
  obtain ⟨Y, hYI, hYs, hYx, -⟩ := hF.exists_block
  obtain ⟨Y₁, hY₁Y, hY₁n, hperf, hι, hYK, hVY⟩ := hF.exists_perfect_normal hYI hYs hYx
  have hY₁I : Y₁ ≤ a7I H ι := hY₁Y.trans hYI
  obtain ⟨hRW, hR0, hRY⟩ := hF.exists_module hYI hYx hY₁Y hY₁n hperf hι
  obtain ⟨hJH, hHJ, -, hJι, -, hJKS, hDJ, hVJ, hY₁J⟩ := hF.exists_J_core hY₁I hperf hι hYK hVY
  have hthree := hF.exists_J_three hJH hJι hDJ
  obtain ⟨A, hA, hAι⟩ := hF.exists_offender hRW fun a haV ha2 haS =>
    hF.rank_ge_four hY₁I hY₁n hperf hι hVY hRW hR0 hRY haV ha2 haS
  have hbound := hF.card_a7W_le hJH hJι hJKS hVJ hA hAι
  have hWel : IsElemAbelian 2 (a7W H) := B2F.isElemAbelian_omegaOneCenterOf _
  have hWn : H ≤ normalizer (a7W H : Set G) := by
    have := CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H)
    rw [hF.H_norm] at this
    exact this
  have hJW : ∀ j ∈ a7J H Y₁, (a7W H).map (MulAut.conj j).toMonoidHom = a7W H := fun j hj =>
    mem_normalizer_iff_map_conj_eq.mp (hWn (hJH hj))
  have hker : ∀ j : ↥H, (j : G) ∈ a7J H Y₁ → ι j = 1 → ∀ w ∈ a7W H,
      (j : G) * w * (j : G)⁻¹ = w := by
    intro j hjJ hj1 w hw
    have hjK : (j : G) ∈ a7K H := by
      have : j ∈ ι.ker := hj1
      rw [hF.ker_eq] at this
      exact ⟨j, this, rfl⟩
    have hjS : (j : G) ∈ pCoreOf 2 H := hJKS ⟨hjJ, hjK⟩
    have hc := Subgroup.mem_centralizer_iff.mp (a7main_W_le_centralizer H hw) j hjS
    rw [hc]
    group
  have hX₀W : a7J H ⁅pCoreOf 2 H, Y₁⁆ ≤ a7W H := a7main_J_le_of_normalizer hRW hWn
  have hX₀J : ∀ j ∈ a7J H Y₁, (a7J H ⁅pCoreOf 2 H, Y₁⁆).map (MulAut.conj j).toMonoidHom =
      a7J H ⁅pCoreOf 2 H, Y₁⁆ := fun j hj =>
    mem_normalizer_iff_map_conj_eq.mp (a7main_le_normalizer_J (hJH hj))
  have hX₀ne : a7J H ⁅pCoreOf 2 H, Y₁⁆ ≠ ⊥ := fun h => hR0 (le_bot_iff.mp (a7main_le_J.trans h.le))
  have hX₀c : ⁅a7J H ⁅pCoreOf 2 H, Y₁⁆, a7J H Y₁⁆ = a7J H ⁅pCoreOf 2 H, Y₁⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx j hj
      have hjn := a7main_le_normalizer_J (X := ⁅pCoreOf 2 H, Y₁⁆) (hJH hj)
      have h1 : j * x⁻¹ * j⁻¹ ∈ a7J H ⁅pCoreOf 2 H, Y₁⁆ := by
        have := (mem_normalizer_iff.mp hjn x⁻¹).mp ((Subgroup.inv_mem _) hx)
        exact this
      have : x * (j * x⁻¹ * j⁻¹) ∈ a7J H ⁅pCoreOf 2 H, Y₁⁆ := Subgroup.mul_mem _ hx h1
      rw [commutatorElement_def]
      convert this using 1
      group
    · refine iSup₂_le fun h hh => ?_
      have h1 : (⁅pCoreOf 2 H, Y₁⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom =
          ⁅(⁅pCoreOf 2 H, Y₁⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom,
            Y₁.map (MulAut.conj h).toMonoidHom⁆ := by
        conv_lhs => rw [← hRY]
        exact Subgroup.map_commutator _ _ _
      rw [h1]
      exact Subgroup.commutator_mono (a7main_map_conj_le_J hh |>.trans' le_rfl)
        (a7main_map_conj_le_J hh)
  obtain ⟨U, hUW, hU16, hUC, hWU, hUJ, hUc, hUmax⟩ := exists_a7_natural_module (H := H)
    (ι := ι) hJH hJW hWel hJι hker hbound hX₀W hX₀J hX₀ne hX₀c
  have hUn : H ≤ normalizer (U : Set G) := by
    intro h hh
    have hh' : (h⁻¹ : G) ∈ H := H.inv_mem hh
    have hJh : (a7J H Y₁).map (MulAut.conj h).toMonoidHom = a7J H Y₁ :=
      mem_normalizer_iff_map_conj_eq.mp (hHJ hh)
    have hUh : U.map (MulAut.conj h).toMonoidHom ≤ U := by
      refine hUmax _ ?_ ?_ ?_
      · calc U.map (MulAut.conj h).toMonoidHom ≤ (a7W H).map (MulAut.conj h).toMonoidHom :=
            Subgroup.map_mono hUW
          _ = a7W H := mem_normalizer_iff_map_conj_eq.mp (hWn hh)
      · intro j hj
        have hj' : h⁻¹ * j * h ∈ a7J H Y₁ := by
          have := (mem_normalizer_iff.mp (hHJ hh') j).mp hj
          simpa [mul_assoc] using this
        have h1 := hUJ _ hj'
        rw [Subgroup.map_map]
        have : (MulAut.conj j).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
            (MulAut.conj h).toMonoidHom.comp (MulAut.conj (h⁻¹ * j * h)).toMonoidHom := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [this, ← Subgroup.map_map, h1]
      · have h1 := Subgroup.map_commutator U (a7J H Y₁) (MulAut.conj h).toMonoidHom
        rw [hJh, hUc] at h1
        exact h1.symm
    have hcard : Nat.card (U.map (MulAut.conj h).toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    have hUeq : U.map (MulAut.conj h).toMonoidHom = U :=
      Subgroup.eq_of_le_of_card_ge hUh (by rw [hcard])
    exact mem_normalizer_iff_map_conj_eq.mpr hUeq
  have hUS : U ≤ centralizer (pCoreOf 2 H : Set G) := hUW.trans (a7main_W_le_centralizer H)
  have hUel : IsElemAbelian 2 U := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hWel.2 x (hUW hx)⟩
    exact Subtype.ext (by
      have := hWel.1.is_comm.comm ⟨x, hUW x.2⟩ ⟨y, hUW y.2⟩
      simp at this ⊢
      exact this)
  have hcomm : ∀ s ∈ pCoreOf 2 H, ∀ j ∈ a7J H Y₁, s * j * s⁻¹ * j⁻¹ ∈ U := by
    let Z₀ : Subgroup G :=
      { carrier := {j | j ∈ H ∧ ∀ s ∈ pCoreOf 2 H, s * j * s⁻¹ * j⁻¹ ∈ U}
        one_mem' := ⟨H.one_mem, fun s _ => by simp⟩
        mul_mem' := fun {a b} ha hb => by
          refine ⟨H.mul_mem ha.1 hb.1, fun s hs => ?_⟩
          have h1 := ha.2 s hs
          have h2 := (mem_normalizer_iff.mp (hUn ha.1) _).mp (hb.2 s hs)
          have := U.mul_mem h1 h2
          convert this using 1
          group
        inv_mem' := fun {a} ha => by
          refine ⟨H.inv_mem ha.1, fun s hs => ?_⟩
          have h1 := (mem_normalizer_iff.mp (hUn (H.inv_mem ha.1)) _).mp
            (U.inv_mem (ha.2 s hs))
          convert h1 using 1
          group }
    have hHS : H ≤ normalizer (pCoreOf 2 H : Set G) := hF.H_norm.ge
    have hY₁Z : Y₁ ≤ Z₀ := by
      intro y hy
      refine ⟨(hY₁I.trans (a7I_le H ι)) hy, fun s hs => ?_⟩
      have h1 : s * y * s⁻¹ * y⁻¹ ∈ ⁅pCoreOf 2 H, Y₁⁆ :=
        Subgroup.commutator_mem_commutator hs hy
      exact hUmax _ hX₀W hX₀J hX₀c (a7main_le_J h1)
    have hconj : ∀ h ∈ H, ∀ z ∈ Z₀, h * z * h⁻¹ ∈ Z₀ := by
      intro h hh z hz
      refine ⟨H.mul_mem (H.mul_mem hh hz.1) (H.inv_mem hh), fun s hs => ?_⟩
      have hs' : h⁻¹ * s * h ∈ pCoreOf 2 H := by
        have := (mem_normalizer_iff.mp (hHS (H.inv_mem hh)) s).mp hs
        simpa [mul_assoc] using this
      have h1 := hz.2 _ hs'
      have h2 := (mem_normalizer_iff.mp (hUn hh) _).mp h1
      convert h2 using 1
      group
    have hZ₀n : H ≤ normalizer (Z₀ : Set G) := by
      intro h hh
      refine mem_normalizer_iff.mpr fun x => ⟨fun hx => hconj h hh x hx, fun hx => ?_⟩
      have := hconj h⁻¹ (H.inv_mem hh) _ hx
      simpa [mul_assoc] using this
    have hJZ : a7J H Y₁ ≤ Z₀ := a7main_J_le_of_normalizer hY₁Z hZ₀n
    exact fun s hs j hj => (hJZ hj).2 s hs
  obtain ⟨hcent, hquad, hidx⟩ := hF.module_facts hJH hJι hUJ hUel hU16 hUC
    (fun j hj h1 u hu => hker j hj h1 u (hUW hu)) hVJ hUS
  refine ⟨a7J H Y₁, U, ?_⟩
  exact
    { U_le := hUW.trans (a7main_W_le H)
      U_central := hUS
      U_exp := fun u hu => hWel.2 u (hUW hu)
      card_U := hU16
      U_normal := hUn
      J₁_le := hJH
      D_le := hDJ
      V_le := hVJ
      comm := hcomm
      split := fun w hwS hwC hw2 =>
        (sup_le_sup_left (inf_le_inf_right _ (a7main_W_le H)) U) (hWU (a7main_mem_W_of hwS hwC hw2))
      inter := hUC
      cent := hcent
      quad := hquad
      idx := hidx
      three := hthree }

theorem ObstructionSetting.not_invariantTwoMaximalWithin_of_module {p : ℕ}
    (hS : ObstructionSetting G) (hD1 : TheoremD1 G) (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D R T H V : Subgroup G} (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hd : MaximalRelativePair p P M D R T) (hfacts : OptimalRelPairFacts p M D H V)
    (hp3 : p = 3) {J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H)) :
    ¬ invariantTwoMaximalWithin D M V := by
  intro hmax
  subst hp3
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, -, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hd.ext hd.not_le_normalizer hR h13
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hMmax := hd.ext.obstruction.1
  have hPM := hS.sylow_le hp hMmax
  have hDM : D ≤ M := hd.ext.obstruction.2.1.trans hPM
  obtain ⟨n, hnP, hnN, hnC⟩ :=
    hS.exists_mem_normalizer_not_mem_centralizer hD1 hp hd.ext hd.not_le_normalizer hDab hCD
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  have hnord : ∃ k : ℕ, n ^ (3 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨e, heD, hez⟩ : ∃ e ∈ D, e ∉ zpowers z := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show D ≤ zpowers z from fun x hx => h x hx)
    rw [hDc, Nat.card_zpowers, orderOf_eq_prime hzp hz1] at this
    norm_num at this
  have hezc : e * z = z * e := congrArg Subtype.val (hDab.is_comm.comm ⟨e, heD⟩ ⟨z, hzD⟩)
  obtain ⟨b, hb0, hneb⟩ :=
    exists_transvection_exponent hDe hDc hzD hz1 hnord hnN hnz hnC heD hez
  obtain ⟨a, c, haM, hcM, hzac, hza, hzc'⟩ : ∃ a c : G, a ∈ M ∧ c ∈ M ∧
      z = a * c * a⁻¹ * c⁻¹ ∧ z * a = a * z ∧ z * c = c * z := by
    rcases eq_commutator_or_eq_commutator_of_exponent hzp hezc hb0 hneb with h | h
    · exact ⟨n, e, hPM hnP, hDM heD, h, hnz.symm, hezc.symm⟩
    · exact ⟨e, n, hDM heD, hPM hnP, h, hezc.symm, hnz.symm⟩
  have hX2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hMX : M ≤ normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 M
  have hznc : ∃ x ∈ pCoreOf 2 M, z * x ≠ x * z := by
    by_contra hcon
    push Not at hcon
    have hzC : z ∈ centralizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun x hx => (hcon x hx).symm
    have hzX : z ∈ pCoreOf 2 M := hS.charTwo M hMmax.1.1 ⟨hDM hzD, hzC⟩
    obtain ⟨k, hk⟩ := hX2 ⟨z, hzX⟩
    have hzk : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact hz1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hzk) (orderOf_dvd_of_pow_eq_one hzp)))
  have hXV : pCoreOf 2 M ≤ V := invariantTwoMaximalWithin_contains_normal_two_subgroup D M V
    (pCoreOf 2 M) hDM hmax (pCoreOf_le 2 M) (pCoreOf_normal 2 M) hX2
  have hVH : V ≤ H := hfacts.maximal.1
  have hHS : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H
  have hzJ : z ∈ J₁ := hdata.D_le hzD
  have hidx : (pCoreOf 2 H).relIndex (pCoreOf 2 M) ≤ 4 := by
    rw [← relIndex_eq_four_of_card hfacts.pCore_le hcard]
    exact Subgroup.relIndex_le_of_le_right hXV Subgroup.index_ne_zero_of_finite
  obtain ⟨hidx4, -, hcent⟩ := rank_step hX2 hMX (hDM hzD) haM hcM hzac hzp hza hzc' hznc
    (hHS (hdata.J₁_le hzJ)) hdata.U_le (fun s hs => hdata.comm s hs z hzJ) hidx hdata.card_U
    (fun x hx => hdata.U_normal (hVH (hXV hx)))
  have hVeq : pCoreOf 2 M ⊔ pCoreOf 2 H = V :=
    sup_eq_of_relIndex_eq hXV hfacts.pCore_le hcard hidx4
  have hVU : V ≤ centralizer (U : Set G) := by
    rw [← hVeq]
    refine sup_le (fun x hx => mem_centralizer_iff.mpr fun u hu => hcent x hx u hu)
      (fun s hs => mem_centralizer_iff.mpr fun u hu => ?_)
    exact (mem_centralizer_iff.mp (hdata.U_central hu) s hs).symm
  have hVS : V ≤ pCoreOf 2 H := hdata.cent ▸ le_inf le_rfl hVU
  have hle := Subgroup.card_le_of_le hVS
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  omega

theorem ObstructionSetting.gl83RelPair2A7B_of_module (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hM : GL83RelPair2A7Module G) : GL83RelPair2A7B G := by
  intro p hp P M D R T H V hd hopt hfacts hp3 L hL hLA hcard
  obtain ⟨e⟩ := hLA
  obtain ⟨-, n, hnH, hnD, hjoin⟩ := hopt.a7_structure hd hfacts hp3 hL e
  obtain ⟨J₁, U, hdata⟩ := hM p hp P M D R T H V hd hopt hfacts hp3 L hL ⟨e⟩ hcard
    ⟨n, hnH, hnD, hjoin⟩
  have hnotmax := hS.not_invariantTwoMaximalWithin_of_module hD1 hp hR h13 hd hfacts hp3 hdata
    hcard
  obtain ⟨-, _, -, -, -, -, -, -, hglob⟩ := hS.transitivity_data hD1 hp hd.ext
    hd.not_le_normalizer hR h13
  obtain ⟨T'', hVT'', hT''max⟩ := exists_invariantTwoMaximalWithin_containing D M V hfacts.le_M
    hfacts.maximal.2.1 hfacts.maximal.2.2.1
  have hlt : V < T'' := lt_of_le_of_ne hVT'' fun h => hnotmax (h ▸ hT''max)
  have hel : IsElemAbelian 2 (pCoreOf 2 H) := by
    subst hp3
    exact hopt.isElemAbelian_pCoreOf hfacts hdata hcard hT''max.1 hT''max.2.1 hT''max.2.2.1 hlt
  have hVn : V ≤ normalizer (pCoreOf 2 H : Set G) :=
    hfacts.maximal.1.trans hfacts.normalizer_pCore.ge
  obtain ⟨S₁, hS₁⟩ := a7_orbit_pCore_le_two hdata hfacts.pCore_le hel hcard hVn
  exact ⟨⟨T'', (hglob T'' hT''max).1, hlt⟩, S₁, hS₁⟩

end CFSG.LocalAnalysis.RankFourTheoremC
