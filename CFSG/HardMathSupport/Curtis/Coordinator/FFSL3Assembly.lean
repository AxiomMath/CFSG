module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Kernel
public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Setup
import CFSG.Quasithin.EmptyFaithful.S153MAR

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G] [Finite G] {M S L Q : Subgroup G}

theorem block_b51_setup
    (h51 : AsB51) (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {f : ℕ} (hf : Even f) (hf1 : 1 ≤ f)
    (e : ↥(barM M L) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f)) :
    ∃ h : ↥(barM M L) →* ↥(autOn L (blockV S L)), Function.Surjective h ∧
      h.ker = ⊥ ∧ (∀ l : ↥L, h (toBar hL.le l) = toAut S L l) ∧
      (letI := blockVCommGroup S L;
        B51Hyp (ffJ (autOn (L ⊔ S) (blockV S L))) (autOn L (blockV S L))) := by
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) := le_normalizer_blockV_of_sub S L
  let _ : CommGroup ↥(blockV S L) := blockVCommGroup S L
  have hVsq : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
    Subtype.ext
      ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v v.2)
  obtain ⟨h, hs, hker, hcompat⟩ := exists_central_factor_blockV hA hL hSL
  have hperf : ⁅(⊤ : Subgroup ↥(barM M L)), (⊤ : Subgroup ↥(barM M L))⁆ = ⊤ := by
    rw [← commutator_def]
    exact hL.component.2.2.1
  have hcat : CatalogSimpleSections ↥(autOn L (blockV S L)) :=
    (((catalogSimpleSections_of_isKGroup hK).quotient (CFSG.pCore 2 ↥M)).subgroup
      (barM M L)).of_surjective h hs
  have hSQTK : SQTKGroup ↥(autOn L (blockV S L)) :=
    sqtkGroup_of_sl3_cover hf1 e h hs hker hbridge hcat
  have hB : B51Hyp (ffJ (autOn (L ⊔ S) (blockV S L))) (autOn L (blockV S L)) :=
    (S153M.le_ffJ_of_ffModule hVsq (InternalSec.autOn_le_autOn_of_le le_sup_left)
      (InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hSL))
      (InternalSec.autOn_two_of hLV fun y hy => by
        obtain ⟨e, he⟩ := exists_pow_mem_sup hA.twoRadical.isPGroup hSL hy
        exact ⟨e, Subgroup.mem_sup_left he⟩)
      (isQuasisimple_autOn hA hL hSL) hSQTK (pCoreOf_autOn_sup_eq_bot hA hL hSL)
      (isFFModule_autOn_blockV hA hL hSL)).2
  have hker0 : h.ker = ⊥ := by
    have := ker_inf_center_eq_bot h51 hVsq hB hf hf1 e h hs hker hperf
    rw [← inf_eq_left.mpr hker]
    exact this
  exact ⟨h, hs, hker0, hcompat, hB⟩

theorem commutator_inf_center_eq_bot_of_sl3
    (h51 : AsB51) (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {f : ℕ} (hf : Even f) (hf1 : 1 ≤ f)
    (e : ↥(barM M L) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))
    (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q) (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (hQC : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ⁅barM M Q, barM M Q⁆ ⊓
      (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥ := by
  have hLM : L ≤ M := hL.le
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) := le_normalizer_blockV_of_sub S L
  have hQV : Q ≤ Subgroup.normalizer (blockV S L : Set G) := le_normalizer_blockV_of hQL hQS
  let _ : CommGroup ↥(blockV S L) := blockVCommGroup S L
  have hVsq : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
    Subtype.ext
      ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v v.2)
  obtain ⟨h, hs, hker0, hcompat, hB⟩ := block_b51_setup h51 hbridge hK hA hL hSL hf hf1 e
  let ρQ := Setup.rho (blockV S L) Q hQV
  let ρL := Setup.rho (blockV S L) L hLV
  let φ : ↥Q →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hQM)
  have hbarQ : barM M Q = φ.range := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨Subgroup.inclusion hQM q, Subgroup.mem_subgroupOf.mpr q.2, rfl⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxBC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hxBC
  rw [hbarQ, MonoidHom.range_eq_map, ← Subgroup.map_commutator] at hxQ
  obtain ⟨c₀, hc₀, rfl⟩ := hxQ
  obtain ⟨l', hl', hl'x⟩ := hxL
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
  have hP : ρQ.range ≤ Subgroup.centralizer (autOn L (blockV S L) : Set (MulAut ↥(blockV S L))) := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← Setup.range_rho hLV] at hk
    obtain ⟨l, rfl⟩ := hk
    exact (rho_mul_comm hA hQM hLM hQL hQS hQC q l).symm
  obtain ⟨k, hk⟩ := hQ3 c₀
  have hzm : (ρQ c₀) ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hz1 : ρQ c₀ = 1 :=
    core_eq_one h51 hVsq hB hP hzP hzK (Odd.pow (by decide)) hzm
  have hlL1 : ρL lL = 1 := hzeq ▸ hz1
  let y : ↥(barM M L) := toBar hL.le lL
  have hyx : (y : ↥M ⧸ CFSG.pCore 2 ↥M) = φ c₀ := hl'x
  have hyker : y ∈ h.ker := by
    rw [MonoidHom.mem_ker, hcompat]
    exact Subtype.ext hlL1
  have hycen : y ∈ Subgroup.center ↥(barM M L) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hxC b b.2
    rw [← hyx] at this
    exact this
  have hy1 : y = 1 := by
    have := hker0 ▸ hyker
    exact Subgroup.mem_bot.mp this
  rw [Subgroup.mem_bot, ← hyx, hy1]
  rfl

end CFSG.HardMathSupport.Curtis.Coordinator
