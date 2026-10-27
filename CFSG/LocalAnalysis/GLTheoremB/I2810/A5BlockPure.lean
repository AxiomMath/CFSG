module

import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Pure

theorem card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem not_isPGroup_alt5 : ¬ IsPGroup 2 ↥(alternatingGroup (Fin 5)) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [card_alt5] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem oTwo_of_hom_aux {X : Type} [Group X] [Finite X] {I N : Subgroup X} (hNI : N ≤ I)
    (hN : IsPGroup 2 ↥N) (φ : ↥I →* ↥(alternatingGroup (Fin 5))) (hφ : Function.Surjective φ)
    (hker : ∀ x : ↥I, φ x = 1 ↔ (x : X) ∈ N) :
    pCoreOf 2 I = N ∧ Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(alternatingGroup (Fin 5))) := by
  have hker' : φ.ker = N.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  haveI : (N.subgroupOf I).Normal := hker' ▸ MonoidHom.normal_ker φ
  have hP : IsPGroup 2 ↥(N.subgroupOf I) :=
    hN.comap_of_injective I.subtype I.subtype_injective
  have hle1 : N.subgroupOf I ≤ CFSG.pCore 2 ↥I := s0_le_pCore_of_normal _ hP
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hle2 : CFSG.pCore 2 ↥I ≤ N.subgroupOf I := by
    rw [← hker']
    haveI hPn : ((CFSG.pCore 2 ↥I).map φ).Normal := (CFSG.pCore_normal (p := 2) (G := ↥I)).map φ hφ
    have hP2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥I).map φ) := CFSG.pCore_isPGroup.map φ
    have hbot : (CFSG.pCore 2 ↥I).map φ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥I).map φ) with h | h
      · exact h
      · exfalso
        rw [h] at hP2
        exact not_isPGroup_alt5 (hP2.of_equiv Subgroup.topEquiv)
    intro x hx
    have : φ x ∈ (CFSG.pCore 2 ↥I).map φ := Subgroup.mem_map_of_mem φ hx
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have heq : CFSG.pCore 2 ↥I = N.subgroupOf I := le_antisymm hle2 hle1
  refine ⟨?_, ⟨?_⟩⟩
  · rw [CFSG.openPCoreOf_eq_map_pCore, heq, Subgroup.map_subgroupOf_eq_of_le hNI]
  · exact (QuotientGroup.quotientMulEquivOfEq (heq.trans hker'.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Pure
