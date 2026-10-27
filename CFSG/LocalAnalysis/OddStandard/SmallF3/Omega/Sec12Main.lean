module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Close

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem aschOmega5_of_inputs (i : Asc82Omega5Inputs) : AschOmega5 := by
  intro G _ _ t L hS hpsp
  exfalso
  have hp := asc82Pre11_of_inputs i
  have hS10 : Sec10Setting G t L := { toSec3SettingLB := hS, psp4 := hpsp }
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(centralizer ({t} : Set G))) := inferInstance
  obtain ⟨S, hSyl⟩ : ∃ S : Subgroup G, IsSylow2Of S (centralizer ({t} : Set G)) :=
    ⟨_, isSylow2Of_map_sylow P⟩
  obtain ⟨z, hz⟩ := i.zExists G t L hS S hSyl
  have hZ : Sec10Z G t L S z := { toSec10Setting := hS10, toAsc82Notation := hz }
  have hLpsp : IsPSp43 L := (hp.basic G t L S z hZ).1
  obtain ⟨K1, K2, hK1, hK2, hne, -⟩ := hp.facts.pockets5 G L hLpsp z hz.pocket
  have hctx : Sec10Ctx G t L S z K1 K2 :=
    { toSec10Z := hZ, pocket1 := hK1, pocket2 := hK2, ne := hne }
  have h1112 := asc82Lemma1112_of_pre hp i.corIII i.toAsc82Inputs11
  have halt1 : Sec1011Alt1 t S L := by
    rcases hp.r10.l1011 G t L S z K1 K2 hctx with h | h
    · exact h
    · exact ((h1112 G t L S z K1 K2 hctx).1 h.1).elim
  obtain ⟨E, hE⟩ := asc82Lemma12E_of hp G t L S z K1 K2 hctx halt1
  exact asc82Lemma1210_of_inputs i G t L S z K1 K2 E hE
    (mem_oTwoRes_top_of_sec3Setting hS.toSec3Setting t)

end CFSG.OddStandard.SmallF3.Omega
