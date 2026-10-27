module

public import CFSG.Quasithin.EmptyFaithful.SzMSC12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P5Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153DC27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.S152Y

section C134

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_c134Case_of_c27_corr_F4 (hMS : MS93.AS_C_1_34_corr_F4) {H R M K V : Subgroup G}
    (hq : IsLnTwoQuot K 3) (hC : C27Concl H R M K V) (hK : K ∈ cComp H)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) :
    ∃ i : ℕ, MS93.IsC134CaseCorr i (K ⊔ R) R K := by
  have hMSp : IsMSPair (K ⊔ R) R := SBd5.c27_caseG hq hC
  have hcomp : K ∈ cComp (K ⊔ R) := SBd5.mem_cComp_sup' hK hRN
  have hset : ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K R hRN
  obtain ⟨e⟩ := hq
  let α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hα : IsModO2Surj K α := by
    refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).ker = CFSG.pCore 2 ↥K
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  exact hMS G (K ⊔ R) R K hMSp hcomp hset ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

section Main

variable {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}

theorem card_conjClosure_K_le_corr_F4 (hC27 : ASC27Statement_F4 G) (hMS : MS93.AS_C_1_34_corr_F4)
    (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) K) ≤ 2 ^ 3 := by
  have S : Setting146 G T M := c.setting
  obtain ⟨hRad, hSyl⟩ := c23_of_facts c hsyl hLT
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  set R₁ : Subgroup G := pCoreOf 2 (i1Of1469 T M I) with hR₁
  have hKI : K ≤ I := hK.le
  have hKN : I ≤ Subgroup.normalizer (K : Set G) := hK.normal
  have hRN : R₁ ≤ Subgroup.normalizer (K : Set G) := hRad.1.trans hKN
  obtain ⟨e⟩ := exists_mulEquiv_of_isPSL hL32
  have hq : IsLnTwoQuot K 3 :=
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩
  have hqs : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (H13.isQuasisimple_sl_zmod_two (by norm_num)).1
  have hKc : K ∈ cComp I := mem_cComp_of_eq_oTwoUpper hK.eq_residual hqs
  have hct : CharTwo K := CharTwo.of_normal c.c4 hKI
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hKN)
  have hnot : ¬ K ≤ M ⊓ I := by
    intro hKM
    apply c.hI.1.2.2
    calc I = K ⊔ (T ⊓ I) := hK.eq_sup
      _ ≤ M := sup_le (hKM.trans inf_le_left) (inf_le_left.trans hTM)
  have hSQ := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.2
  have hyp : HypC23 I R₁ (M ⊓ I) :=
    { sqtk := (show SQTKGroup ↥I from ⟨hSQ.2, hSQ.1⟩)
      radical := hRad
      le := inf_le_right
      cgs := cgsIn_le_of_CGS_le' c.c1
      sylow := hSyl }
  have hC : C27Concl I R₁ (M ⊓ I) K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R₁))) :=
    c27Concl_of_statement_F4 hC27 hyp hKc hqs hct hnot hRN rfl
  obtain ⟨i, hi⟩ := exists_c134Case_of_c27_corr_F4 hMS hq hC hKc hRN
  obtain ⟨y, hyK, hyN, hyfpf, -⟩ := Setting146.exists_y_fpf c.toHyp14610 hLT
  have hyK' : y ∈ K := by rw [hK.eq_residual]; exact hyK
  have hS : IsSylowTwoOf ((T ⊓ I) ⊓ K) K := A4.isSylowTwoOf_inf_normal hsyl hKI hKN
  have hvd : GVData K (VZ T M) ((T ⊓ I) ⊓ K) y :=
    { card := S.hyp.rank_two
      S_le := inf_le_right
      S_norm := fun s hs => hMV (hTM hs.1.1)
      y_mem := hyK'
      y_norm := hyN
      y_fpf := hyfpf }
  have hAP : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 (K ⊔ R₁) :=
    (A4.omegaOneCenterOf_le _).trans (pCoreOf_le_pCoreOf_sup hRN)
  have d : L32Data K R₁ (VZ T M) (wOf1469 K) ((T ⊓ I) ⊓ K) y :=
    { hq := hq
      vd := hvd
      hS := hS
      hVW := hK.v_le_w
      WQ := Subgroup.commutator_mono hAP le_rfl
      Wsq := fun a ha => wOf1469_sq ha
      Wnorm := le_normalizer_wOf1469 K
      Wtriv := fun k hk x hx => wOf1469_comm_pCore hk hx
      Wcent := fun a ha q hq' => by
        have hqO : q ∈ pCoreOf 2 K := commutator_pCore_le hRN hq'
        have h := wOf1469_comm_pCore hqO ha
        exact (mul_inv_eq_iff_eq_mul.mp h).symm }
  calc Nat.card (conjClosure (VZ T M) K) ≤ 8 := card_le_of_c134_corr d hi
    _ = 2 ^ 3 := by norm_num

end Main

end C134

end CFSG.Quasithin.S152Y

namespace CFSG.Quasithin

section Setting

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M : Subgroup G}

theorem Setting146.card_conjClosure_K_le_corr_F4 (hC27 : ASC27Statement_F4 G)
    (hMS : MS93.AS_C_1_34_corr_F4)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) K) ≤ 2 ^ 3 :=
  S152Y.card_conjClosure_K_le_corr_F4 hC27 hMS c hsyl hLT hK hL32

theorem Setting146.facts14610_L32_proved_corr_F4 (hC27 : ASC27Statement_F4 G)
    (hMS : MS93.AS_C_1_34_corr_F4)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 :=
  le_antisymm
    ((Subgroup.card_le_of_le (Setting146.conjClosure_I₂_le_conjClosure_K c.toHyp14610 hK)).trans
      (Setting146.card_conjClosure_K_le_corr_F4 hC27 hMS c hsyl hLT hK hL32))
    (Setting146.eight_le_card_conjClosure_I₂ c.toHyp14610)

end Setting

section Stage

open CFSG.Open CFSG.QuasithinUnique

theorem stage14610FiveW_of_narrow_inputs_H_corr_F4
    (h9 : Stage1469W) (hF618 : F6.TheoremF618Cat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hMS : MS93.AS_C_1_34_corr_F4)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three) (h4 : Stage1463Four)
    (i11 : Input14610ListN)
    (i16a : Input14610PermFixedA6)
    (i16b : Input14610PermFixedA7) (i17c : Input14610PermA7Fixed) : Stage14610FiveW_F4 := by
  have i13 : Input14610Hat6 := input14610Hat6_proved
  have i16 : Input14610PermFixed := input14610PermFixed_of_narrow i16a i16b
  intro G _ _ T M H u S hH hu I hI hbig hrank I₂ hle hI₂ hs3 hgen hcent
  have c : Hyp14610 T M H u I I₂ :=
    ⟨S, hH, hu, hI, hbig, hrank, hle, hI₂, hs3, hgen, hcent⟩
  have hidx := (h1 G T M S H hH u hu).2.1
  have hN0 := h2 G T M S H hH u hu
  have hNu := (h4 G T M S H hH u hu).1
  obtain ⟨hsyl, hcases⟩ := isIStar_sylow_cases S hu hidx hN0 hNu hI
  have hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) :=
    h9 G T M H u S hH hu I hI hbig hrank
  have hN : tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) := (h1 G T M S H hH u hu).2.2.1
  have hV3 : ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G)) := (h3 G T M S H hH u hu).1
  have hc1 := S.facts14610_c1 hI hsyl hLT
  have hc2 := S.facts14610_c2 hI hsyl hgen hc1
  have hc3 := fun P hPI hPinv => Setting146.facts14610_c3 h9 h3 c hsyl hLT P hPI hPinv
  have hc4 := Setting146.facts14610_c4 hF618 input14610Four_proved c hsyl hLT hc2
  let cF : Facts14610 T M H u I I₂ := { c with c1 := hc1, c2 := hc2, c3 := hc3, c4 := hc4 }
  have hT := S.isGoldschmidtTripleIn_14610 c hsyl hLT
  have hF := S.f618Cat_14610 hF618 c hsyl hLT hc2
  have hK : Concl14610List T M I I₂ (oTwoUpper I) :=
    concl14610List_of_core cF hsyl hLT hT (i11 G T M H u I I₂ (hC27 G) cF hsyl hLT hT hF)
  rcases hK.shape with ⟨hL32, -⟩ | ⟨-, hHat | hG2 | hA6 | hA7⟩
  · exact Setting146.facts14610_L32_proved_corr_F4 (hC27 G) hMS cF hsyl hLT hK hL32
  · exact (Setting146.facts14610_hat6 i13 cF hK hHat.1).elim
  · exact Setting146.facts14610_G22_of_sylow cF hsyl hLT hK hG2.1
  · rcases hA6.2.2 with hW | hW
    · exact Setting146.facts14610_rank4_of_sylow cF hK hsyl (Or.inl hA6.1) hW
    · exact Setting146.facts14610_perm_of_sylow' i16 i17c cF hsyl hcases hLT hN hV3 hK
        (Or.inl ⟨hA6.1, hW⟩)
  · rcases hA7.2.2 with hW | hW
    · exact Setting146.facts14610_rank4_of_sylow cF hK hsyl (Or.inr hA7.1) hW
    · exact Setting146.facts14610_perm_of_sylow' i16 i17c cF hsyl hcases hLT hN hV3 hK
        (Or.inr ⟨hA7.1, hW⟩)

end Stage

section Proved

open CFSG.Open CFSG.QuasithinUnique

theorem stage14610FiveW_proved_corr_F4
    (h9 : Stage1469W) (hF618 : F6.TheoremF618Cat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hMS : MS93.AS_C_1_34_corr_F4) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) : Stage14610FiveW_F4 :=
  stage14610FiveW_of_narrow_inputs_H_corr_F4 h9 hF618 hC27 hMS stage1463_one_proof h2 h3 h4
    (input14610ListN_of_listW input14610ListW_holds) input14610PermFixedA6_holds
    input14610PermFixedA7_holds input14610PermA7Fixed_holds

end Proved

section NoE9

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.E9P2L
open CFSG.Quasithin.EmptyFaithfulMultiple

theorem noE9Z4LargeBig_proved_corr_F4
    (h35 : Lemma1435) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (hD36 : D36)
    (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hcab : GoldschmidtCentralAbelianBound) (hE22 : E2.E22StatementNoN)
    (hF618 : F6.TheoremF618Cat) (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hMS : MS93.AS_C_1_34_corr_F4) (h2' : Stage1463Two) (h3 : Stage1463Three) (h4 : Stage1463Four) :
    NoE9Z4LargeBig_F4 :=
  have h9 : Stage1469W := stage1469W_proved hA37 hA38 hA39 hE22 h2' h3 h4
  have hL := input14614ListsE9_of_prop134 h35 hA37 hA38 hD36 hD37 hD321 hI5 hD310 hD391 hI4
    prop134E9He_holds
  noE9Z4LargeBig_of_parts_F4 h35 stage1461Five stage1461Two
    (e9Fstar_of_inputs h35 H13.VolI.a36ForSQTK_holds hA37 sqtkList3Dvd_proved
      S146zT.input14614NoSz_proved hL)
    (e9Normalizer_of_inputs h35 H13.VolI.a36ForSQTK_holds hA37 sqtkList3Dvd_proved
      S146zT.input14614NoSz_proved hL)
    hcab h9 (stage14610FiveW_proved_corr_F4 h9 hF618 hC27 hMS h2' h3 h4) stage1463_one_proof h2' h3 h4

end NoE9

end CFSG.Quasithin
