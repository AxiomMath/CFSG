module

public import Certificates.Certificate27820
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def baseList : List (Fin 128) := [32, 64, 1, 2, 15, 22]

@[expose] def levelsPg : Array Level := rawLevels 128 sgsArr baseArr

@[expose] def groupsPg : List (List ℕ) := [[0], [1], [2], [3], [4], [5]]

@[expose] def blocksPg : List (Array (Array ℕ)) := blocksOf 128 levelsPg groupsPg

@[expose] def inPg (g : Array ℕ) : Bool := siftA 128 levelsPg baseArr 0 g

@[expose] noncomputable def QPg : RawSchreierDatum 128 :=
  RawSchreierDatum.ofArrays 128 (by norm_num) sgsArr 36 (by decide) baseList (by decide) wordsArr

@[expose] noncomputable def Pg : Subgroup (Equiv.Perm (Fin 128)) := QPg.originalSubgroup

theorem baseArr_eq : (baseList.map Fin.val).toArray = baseArr := by decide

theorem chain_check :
    rawChainOK 128 (sgsArr.extract 0 36) sgsArr baseArr wordsArr 4 = true := by
  have h := Certificates.certificate27820.2.2.1
  simp only [chainCheck, Bool.and_eq_true] at h
  exact h.1

theorem orbit_prod :
    (rawOrbitSizes 128 sgsArr baseArr).prod = 3317760 := by
  have h := Certificates.certificate27820.2.2.1
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem chainArrays :
    ChainArrays QPg (sgsArr.extract 0 36) sgsArr baseArr wordsArr :=
  chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv

theorem inPg_iff {g : Array ℕ} {G : Equiv.Perm (Fin 128)}
    (hG : Rep 128 g G) : inPg g = true ↔ G ∈ Pg :=
  siftA_iff_mem_originalSubgroup chainArrays (by norm_num) chain_check hG

theorem groupsPg_flatten : groupsPg.flatten = List.range QPg.baseCount := rfl

theorem card_Pg : Nat.card Pg = 3317760 := by
  have h := card_originalSubgroup_of_chainOK chainArrays (by norm_num) chain_check
  rw [orbit_prod] at h
  exact h

theorem card_eq_countW_Pg {f : List (Array ℕ) → Bool}
    {Pr : Equiv.Perm (Fin 128) → Prop} [DecidablePred Pr]
    (hfP : ∀ w g, RepW 128 w g → g ∈ Pg → (f w = true ↔ Pr g)) :
    Nat.card {x : Pg // Pr x} = countW f blocksPg [] :=
  card_eq_countW chainArrays (by norm_num) chain_check groupsPg_flatten hfP

end CFSG.EvenSporadicStandard.Fin76b.W16
