module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23SettingProof
import CFSG.Quasithin.Vol2.Ch5Sec3Lemma531
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.Quasithin.Vol2.Ch1Unique
import CFSG.Quasithin.Vol2.Ch1A3Cat
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
import CFSG.Quasithin.Background.KnownMultTypes
import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Stmt5_2_8_Q_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (K' : Subgroup G),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → oTwoUpper H < K' →
    quasithinIsMaximalLocal T K' → CFSG.Quasithin.IsExcA7Block K' →
      IsElemAbelian 2 (pCoreOf 2 K') ∧ Nat.card (pCoreOf 2 K') = 16 ∧ T ≤ K'

variable {G : Type} [Group G]

theorem stmt5_2_11_four_of_F4
    (h39 : Vol2Native.A39ForSQTKCat) (hQ : Stmt5_2_8_Q_F4) :
    Stmt5_2_11_four_F4 := by
  intro G _ _ T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc
  obtain ⟨hUab, hU16, hTK⟩ := hQ G T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved
    Vol2Native.a37ForSQTKCat_proved)
  have h39' : A39ForSQTK := a39ForSQTK_of_cat h39
  have hTN : T ≤ Subgroup.normalizer (K' : Set G) := hTK.trans Subgroup.le_normalizer

  have hUM := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39' hyp.sylow hmax
  rw [conjClosure_eq_self_of_le_normalizer hTN] at hUM
  set M0 := Subgroup.normalizer (K' : Set G) with hM0
  have hKM0 : K' ≤ M0 := Subgroup.le_normalizer
  have hTM0 : T ≤ M0 := hTK.trans hKM0
  suffices hMK : M0 = K' by
    refine ⟨?_, hTK⟩
    have := hUM.1.1
    rwa [hMK] at this

  set U := pCoreOf 2 K' with hUdef
  have hUK : U ≤ K' := CFSG.LieType.BorelTits.pCoreOf_le 2 K'
  have hUM0' : U ≤ M0 := hUK.trans hKM0
  have hUN : M0 ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K'
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K'
  have hTs : IsSylowTwoOf T M0 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM0
  have hO : pCoreOf 2 M0 = U := le_antisymm (pCoreOf_le_pCoreOf_of_sylow hTs hTK hKM0)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUM0' hUN hU2)
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hU16
    norm_num at hU16
  have hCT : CharTwo M0 := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTM0, by rw [hO]; exact hUne⟩
  have hC : M0 ⊓ Subgroup.centralizer (U : Set G) ≤ U := by
    have h := hCT
    unfold CharTwo at h
    rwa [hO] at h

  have hU'n : (U.subgroupOf M0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM0').mpr hUN
  set φ : M0 →* MulAut (U.subgroupOf M0) := MulAut.conjNormal
  have hker : φ.ker = U.subgroupOf M0 :=
    le_antisymm (ker_conjNormal_le hUM0' hC) (le_ker_conjNormal hUab.1)
  have hcardU' : Nat.card (U.subgroupOf M0) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM0').toEquiv, hU16]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := U.subgroupOf M0)
    (fun a b => by
      have := hUab.1.is_comm.comm ⟨(a : M0), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : M0), Subgroup.mem_subgroupOf.mp b.2⟩
      have h' : ((a : M0) : G) * ((b : M0) : G) = ((b : M0) : G) * ((a : M0) : G) :=
        congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext h'))
    (fun a => by
      apply Subtype.ext; apply Subtype.ext
      exact hUab.2 _ (Subgroup.mem_subgroupOf.mp a.2))
    hcardU'
  set eGL := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  have hfin : Finite (MulAut (U.subgroupOf M0)) := Finite.of_equiv _ eGL.symm.toEquiv
  have hsimp : IsSimpleGroup (MulAut (U.subgroupOf M0)) := by
    have := isSimpleGroup_GL_four_two
    exact eGL.isSimpleGroup
  have hcardS : Nat.card (MulAut (U.subgroupOf M0)) = 20160 := by
    rw [Nat.card_congr eGL.toEquiv, card_GL_four_two]

  set ψ : K' →* MulAut (U.subgroupOf M0) := φ.comp (Subgroup.inclusion hKM0)
  obtain ⟨-, ⟨α, hαs, hαk⟩, -⟩ := hexc
  have hψk : ψ.ker = α.ker := by
    ext k
    rw [MonoidHom.mem_ker, hαk, CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore]
    change Subgroup.inclusion hKM0 k ∈ φ.ker ↔ _
    rw [hker, Subgroup.mem_subgroupOf]
    change ((k : G) ∈ (CFSG.Open.pCore 2 K').map K'.subtype) ↔ _
    constructor
    · intro h
      obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp h
      have : k' = k := Subtype.ext hkk'
      rw [← this]
      exact hk'
    · intro h
      exact Subgroup.mem_map.mpr ⟨k, h, rfl⟩
  have hcardA : Nat.card ψ.range = 2520 := by
    rw [← Subgroup.index_ker, hψk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hαs,
      Subgroup.card_top, card_alternatingGroup_seven]
  have hAeq : ψ.range = (K'.subgroupOf M0).map φ := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKM0 k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hKn : (K'.subgroupOf M0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM0).mpr le_rfl
  have hAn : (((K'.subgroupOf M0).map φ).subgroupOf φ.range).Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨k, hk, hka⟩ := ha
    obtain ⟨m, hm⟩ := x.2
    refine ⟨m * k * m⁻¹, hKn.conj_mem k hk m, ?_⟩
    simp only [map_mul, map_inv, hm, hka, Subgroup.coe_mul, Subgroup.coe_inv]
  have hEq := eq_of_normal_card_of_simple hcardS (Subgroup.map_le_range φ _) hAn
    (by rw [← hAeq]; exact hcardA)

  refine le_antisymm (fun m hm => ?_) hKM0
  have hmr : φ ⟨m, hm⟩ ∈ (K'.subgroupOf M0).map φ := by
    rw [hEq]; exact ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨k, hk, hkm⟩ := hmr
  have hker' : k⁻¹ * ⟨m, hm⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkm, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hkK : (k : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  have hmk : m = (k : G) * ((k⁻¹ * ⟨m, hm⟩ : M0) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [hmk]
  exact mul_mem hkK (hUK hker')

end CFSG.Quasithin.H13
