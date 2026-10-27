module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain
public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Assembly
public import CFSG.HardMathSupport.Curtis.Coordinator.FFToralAction
import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Lift
import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3NatDiag
import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Diag2
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeBlock
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusAssembly
import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open scoped commutatorElement
open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.Proving

theorem exists_cube_root {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : Even f) : ∃ ω : F, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd (K := F) (d := 3)
    (by rw [hF]; exact three_dvd_two_pow_sub_one hf)
  exact ⟨ω, hω.ne_one (by norm_num), hω.pow_eq_one⟩

theorem ff_toral_main
    (hZ : KFactFixCensusCenter) (h51 : AsB51)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) : CitedBlockToralCenterFF := by
  intro G _ _ M S L hK hA hL h93 hX hS hcyc h3A6 ζ hζL hζC hζ3 hζ1 u hu hu3 huC hfix X hX3 hXL
    hXS hXu hX81 hmax hc1 e he1 hel he3
  obtain ⟨f, ψ, d, hfe, hf2, hCP, hpc, cfg⟩ :=
    toral_setup hZ hA hL h93 hX hS hcyc h3A6 hζL hζC hζ3 hζ1 hu hu3 huC hfix
  obtain ⟨hk, ω, hω1, hω3⟩ := field_facts hfe hf2
  have : NeZero f := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h9 : 9 ∣ Nat.card (GaloisField 2 f) - 1
  ·
    have hab := toral_c1_nine cfg hω1 hω3 h9 (blockPL_le_normalizer hA) hX3 hXL hXS hXu hX81 hmax
    have hbot : ⁅X, X⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (fun a ha b hb => hab b hb a ha)
    rw [hbot] at he1
    exact Subgroup.mem_bot.mp he1
  · have h3f : ¬ 3 ∣ f := fun h3 => h9 (by rw [hk]; exact nine_dvd_two_pow_sub_one hfe h3)
    have hf1 : 1 ≤ f := by omega
    have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hK hA hL
    have hSM : S ≤ M := hA.twoRadical.1
    have hO2 : pCoreOf 2 M ≤ S := hA.twoCore_le
    have hLM : L ≤ M := hL.le
    obtain ⟨R, hR3, hRX⟩ := exists_isPGroup_map_eq (CFSG.pCore 2 ↥M) hX3
    let Q : Subgroup G := R.map M.subtype
    have hQM : Q ≤ M := Subgroup.map_subtype_le R
    have hQ3 : IsPGroup 3 Q := hR3.map _
    have hQX : ∀ q : ↥Q, QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M) ∈ X := by
      rintro ⟨_, r, hr, rfl⟩
      rw [← hRX]
      exact ⟨r, hr, rfl⟩
    have hQL : Q ≤ Subgroup.normalizer (L : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact mem_normalizer_of_mk_mem_barM hL.toIsTwoPrimeComponent r.2
        (hXL (hQX ⟨_, r, hr, rfl⟩))
    have hQS : Q ≤ Subgroup.normalizer (S : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact mem_normalizer_of_mk_mem_barM_normalizer hSM hO2 r.2 (hXS (hQX ⟨_, r, hr, rfl⟩))
    have hQV : Q ≤ Subgroup.normalizer (blockV S L : Set G) := le_normalizer_blockV_of hQL hQS
    have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) := le_normalizer_blockV_of_sub S L
    let φ : ↥Q →* ↥M ⧸ CFSG.pCore 2 ↥M :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hQM)
    have hφX : φ.range = X := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact hQX q
      · intro hx
        rw [← hRX] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨⟨(r : G), r, hr, rfl⟩, rfl⟩
    let _ : CommGroup ↥(blockV S L) := blockVCommGroup S L
    have hVsq : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
      Subtype.ext
        ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v v.2)
    obtain ⟨h, hs, hker0, hcompat, hB⟩ := block_b51_setup h51 hbridge hK hA hL hSL hfe
      (by omega) ψ
    have hhb : Function.Bijective h := ⟨(MonoidHom.ker_eq_bot_iff h).mp hker0, hs⟩
    have hperf : ⁅(⊤ : Subgroup ↥(barM M L)), (⊤ : Subgroup ↥(barM M L))⁆ = ⊤ := by
      rw [← commutator_def]
      exact hL.component.2.2.1
    have hker : h.ker ≤ Subgroup.center ↥(barM M L) := by rw [hker0]; exact bot_le
    have hPSLK : IsPSL 3 2 f (↥(autOn L (blockV S L)) ⧸ Subgroup.center ↥(autOn L (blockV S L))) :=
      isPSL_quot_of_sl3_cover hf1 ψ h hs hker hperf
    have hmat : ∀ (F' : Type) [Field F'] [Finite F']
        (π : ↥(StatedSL 3 F') →* ↥(autOn L (blockV S L))), Nat.card F' = 2 ^ f →
        Function.Bijective π →
        ∃ A : MulAut ↥(blockV S L) → GL (Fin 3) F',
          (∀ p ∈ (Setup.rho (blockV S L) Q hQV).range,
            ∀ γ γ' : ↥(StatedSL 3 F'), (γ' : GL (Fin 3) F') = A p * (γ : GL (Fin 3) F') * (A p)⁻¹ →
              p * (π γ : MulAut ↥(blockV S L)) * p⁻¹ = (π γ' : MulAut ↥(blockV S L))) ∧
          ∀ p ∈ (Setup.rho (blockV S L) Q hQV).range, ∀ p' ∈ (Setup.rho (blockV S L) Q hQV).range,
            A p * A p' = A p' * A p := by
      intro F' _ _ π hF' hπb
      have : CharP F' 2 := FFC.charP_two_of_card_pow hF'
      obtain ⟨g', d', hd', hJ'⟩ := exists_setup' hCP (natCoord h hhb π hπb)
      have cfg' : ToralCfg (barM M L) (blockPL M S L)
          ((natCoord h hhb π hπb).trans (MulAut.conj g'⁻¹)) d' u :=
        ⟨hd', hJ', cfg.hu, cfg.hu3, cfg.huC, cfg.hfix⟩
      obtain ⟨ω', hω1', hω3'⟩ := exists_cube_root hF' hfe
      have h9' : ¬ 9 ∣ Nat.card F' - 1 := by rw [hF', ← hk]; exact h9
      obtain ⟨bb, hbb, hdiag⟩ := toral_diag_key cfg' hω1' hω3' hf1 hF' h3f h9'
        (fun x hxQ hxL j hj => blockPL_conj_mem hA hxL hxQ j hj) hX3 hXL hXS hXu
      exact exists_matrices hL hQM hQL hQS h hhb hcompat π hπb g' hbb fun q =>
        let hx := hXL (hQX q)
        let ⟨A, a, h1, h2⟩ := hdiag _ (hQX q)
        ⟨hx, A, a, h1, h2⟩
    let ρQ := Setup.rho (blockV S L) Q hQV
    let ρL := Setup.rho (blockV S L) L hLV
    rw [← hφX, MonoidHom.range_eq_map, ← Subgroup.map_commutator] at he1
    obtain ⟨c₀, hc₀, rfl⟩ := he1
    obtain ⟨l', hl', hl'x⟩ := hel
    let lL : ↥L := ⟨(l' : G), Subgroup.mem_subgroupOf.mp hl'⟩
    have heq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨c₀, hQM c₀.2⟩ : ↥M) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨lL, hLM lL.2⟩ : ↥M) := hl'x.symm
    have hzeq : ρQ c₀ = ρL lL := rho_eq_of_mk_eq hA hQM hLM hQL hQS c₀ lL heq
    have hzP : ρQ c₀ ∈ ⁅ρQ.range, ρQ.range⁆ := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      exact Subgroup.mem_map.mpr ⟨c₀, hc₀, rfl⟩
    have hzK : ρQ c₀ ∈ autOn L (blockV S L) := by
      rw [hzeq, ← Setup.range_rho hLV]
      exact ⟨lL, rfl⟩
    obtain ⟨k, hk3⟩ := hQ3 c₀
    have hzm : (ρQ c₀) ^ 3 ^ k = 1 := by rw [← map_pow, hk3, map_one]
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have hz1 : ρQ c₀ = 1 := by
      rcases core_classify h51 hVsq hB hPSLK with
        ⟨F', _, _, π, hF', hbij, hπ⟩ | ⟨F', _, _, π, I, hF', hbij, hind, hsup, hreal⟩
      · obtain ⟨A, hA1, hA2⟩ := hmat F' π hF' hbij
        exact eq_one_of_trivial_on_commV hVsq hzK hodd hzm
          (fun u hu => commutator_trivial_of_natural_diag π hπ A hA1 hA2 _ hzP u hu)
      · obtain ⟨A, hA1, hA2⟩ := hmat F' π hF' hbij
        refine eq_one_of_trivial_on_commV hVsq hzK hodd hzm (fun u hu => ?_)
        rw [commutator_trivial_of_case1ii_diag π hind hsup hreal A hA1 hA2 _ hzP hzK _ hodd hzm
          u hu, mul_inv_cancel]
        exact one_mem _
    have hlL1 : ρL lL = 1 := hzeq ▸ hz1
    let y : ↥(barM M L) := toBar hL.le lL
    have hyx : (y : ↥M ⧸ CFSG.pCore 2 ↥M) = φ c₀ := hl'x
    have hyker : y ∈ h.ker := by
      rw [MonoidHom.mem_ker, hcompat]
      exact Subtype.ext hlL1
    have hy1 : y = 1 := by
      have := hker0 ▸ hyker
      exact Subgroup.mem_bot.mp this
    rw [← hyx, hy1]
    rfl

theorem citedBlockToralCenterFF_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : CitedBlockToralCenterFF :=
  ff_toral_main (CFSG.AGLEmbedding.kFactFixCensusCenter_holds hGA)
    CFSG.Quasithin.B5.asB51_holds CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge

end CFSG.HardMathSupport.Curtis.Coordinator
