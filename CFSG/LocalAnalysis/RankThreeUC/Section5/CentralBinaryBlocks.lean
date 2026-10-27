module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsElemAbelianOfBinaryRankCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section3.OmegaOneCenter.OmegaOneZ
public import CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary.FaithfulPImageVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem prime (hc : BinaryActionRankCounterexample G p P T B e ρ) : p.Prime := hc.oddPrimeClassTwoAction.setting.prime

theorem elemAbelian (hc : BinaryActionRankCounterexample G p P T B e ρ) : CFSG.Open.IsElemAbelian p P :=
  isElemAbelian_of_binary_rank_counterexample hc

set_option warn.classDefReducibility false in
@[expose] noncomputable def pCommGroup (hc : BinaryActionRankCounterexample G p P T B e ρ) : CommGroup ↥P :=
  { (inferInstance : Group ↥P) with
    mul_comm := fun a b => (elemAbelian hc).1.is_comm.comm a b }

theorem pExp (hc : BinaryActionRankCounterexample G p P T B e ρ) : ∀ x : ↥P, x ^ p = 1 := fun x =>
  Subtype.ext (by simpa using (elemAbelian hc).2 x x.2)

@[expose] def Space (_hc : BinaryActionRankCounterexample G p P T B e ρ) : Type := Additive ↥P

noncomputable instance (hc : BinaryActionRankCounterexample G p P T B e ρ) : AddCommGroup (Space hc) :=
  @Additive.addCommGroup _ (pCommGroup hc)

noncomputable instance (hc : BinaryActionRankCounterexample G p P T B e ρ) : Module (ZMod p) (Space hc) :=
  haveI : Fact p.Prime := ⟨prime hc⟩
  letI := pCommGroup hc
  moduleOf (pExp hc)

instance (hc : BinaryActionRankCounterexample G p P T B e ρ) : Finite (Space hc) :=
  inferInstanceAs (Finite (Additive ↥P))

@[expose] def Space.mk (hc : BinaryActionRankCounterexample G p P T B e ρ) : ↥P → Space hc := Additive.ofMul

@[expose] def Space.val {hc : BinaryActionRankCounterexample G p P T B e ρ} : Space hc → ↥P := Additive.toMul

@[expose] noncomputable def sigma (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Representation (ZMod p) (MulAut ↥P) (Space hc) where
  toFun φ := AddMonoidHom.toZModLinearMap p
    (show Space hc →+ Space hc from MonoidHom.toAdditive φ.toMonoidHom)
  map_one' := by ext v : 1; rfl
  map_mul' a b := by ext v : 1; rfl

theorem sigma_apply (hc : BinaryActionRankCounterexample G p P T B e ρ) (φ : MulAut ↥P) (v : Space hc) :
    (sigma hc φ v).val = φ v.val := rfl

@[expose] noncomputable def Y (hc : BinaryActionRankCounterexample G p P T B e ρ) : Subgroup (MulAut ↥P) :=
  Section3.OmegaOneCenter.omegaOneZ 2 (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal))

@[expose] noncomputable def X (hc : BinaryActionRankCounterexample G p P T B e ρ) : Subgroup (MulAut ↥P) :=
  ⁅Y hc, Bstar P B⁆

@[expose] noncomputable def E (hc : BinaryActionRankCounterexample G p P T B e ρ) (K : Subgroup (MulAut ↥P)) :
    Submodule (ZMod p) (Space hc) :=
  BinaryRepresentations.fixedSpace (sigma hc) K

@[expose] noncomputable def Qline (hc : BinaryActionRankCounterexample G p P T B e ρ) : Submodule (ZMod p) (Space hc) :=
  E hc (Bstar P B)

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks
