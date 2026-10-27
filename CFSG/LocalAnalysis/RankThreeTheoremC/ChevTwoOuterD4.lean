module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterSylow
public import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem isPByAbelian_outer_of_twistedChevalleyModel {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hm : TwistedChevalleyModel X .D4 (2 ^ f)) (p : ℕ) : IsPByAbelian p (Outer X) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hm
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hker' : Θ.ker = inner C := hker
  set Φ := QuotientGroup.lift (inner C) Θ hker'.ge
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have hΦ : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hΦker
  have hcomm : ∀ x y : Outer C, x * y = y * x := fun x y =>
    hΦ (by rw [map_mul, map_mul]; exact ringAut_mul_comm K _ _)
  exact (IsPByAbelian.of_commutative hcomm).map_equiv (equivalence e).symm

theorem isPByAbelian_outer_trialityD4 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq : q.p = 2) (hd : d.1 = .trialityD4 q) (p : ℕ) :
    IsPByAbelian p (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := hd
  have hm := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq (by decide) (MulEquiv.refl _)
  rw [hq] at hm
  exact isPByAbelian_outer_of_twistedChevalleyModel q.exponent_pos hm p

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter
