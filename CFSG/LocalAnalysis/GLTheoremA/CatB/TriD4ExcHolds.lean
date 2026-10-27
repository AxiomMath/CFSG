module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4ExcComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (PerfectInLayer)


private theorem triD4_exc_core {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hbr : CFSG.TauCetiBridge.Even.UntwistedBridgeEven τ c)
    (hfam : ∀ q, CFSG.Yardstones.Md42047359a2a.lieFamily (c q) = .exceptional)
    (hchar : ∀ q, (c q).characteristic = q.p) (hfs : ∀ q, KD264Lie.fieldSize (c q) = q.card) :
    TriD4No fun d => ∃ q, d = c q := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α _ _ hα3 hα1 _ _ _ J hJ hT _
  have hp : q.p = 2 := (hchar q).symm.trans hc
  have hq : q.card = 2 := (hfs q).symm.trans hf
  have hlayer : PerfectInLayer α :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional S hS hnc
      ⟨c q, hv⟩ (hfam q) ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (by show (3 : ℕ) ≠ (c q).characteristic; rw [hc]; norm_num) α hα3 hα1
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨eB⟩ := hbr q hv hp (GaloisField 2 1) (by rw [hK, hq])
  have hZ : Subgroup.center ↥(adjointGroup τ (GaloisField 2 1)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e' : S ≃* ↥(adjointGroup τ (GaloisField 2 1)) :=
    e.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hα3' : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  exact (false_of_componentsNoD4 hlayer
    (ComponentsNoD4.of_congr e' (componentsNoD4_adjointGroup hτ hK hα3')) hJ hT).elim

theorem triD4NoE6_holds : TriD4NoE6 :=
  triD4_exc_core (c := TauCeti.LieTypeIndex.E6) (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 (fun _ => rfl)
    TauCeti.LieTypeIndex.characteristic_E6 (fun _ => rfl)

theorem triD4NoF4_holds : TriD4NoF4 :=
  triD4_exc_core (c := TauCeti.LieTypeIndex.F4) (Or.inl rfl)
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 (fun _ => rfl)
    TauCeti.LieTypeIndex.characteristic_F4 (fun _ => rfl)

theorem triD4NoE78_holds : TriD4NoE78 := by
  have h7 : TriD4No fun d => ∃ q, d = .E7 q :=
    triD4_exc_core (c := TauCeti.LieTypeIndex.E7) (Or.inr (Or.inr (Or.inl rfl)))
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 (fun _ => rfl)
      TauCeti.LieTypeIndex.characteristic_E7 (fun _ => rfl)
  have h8 : TriD4No fun d => ∃ q, d = .E8 q :=
    triD4_exc_core (c := TauCeti.LieTypeIndex.E8) (Or.inr (Or.inr (Or.inr rfl)))
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 (fun _ => rfl)
      TauCeti.LieTypeIndex.characteristic_E8 (fun _ => rfl)
  intro S _ _ hS hnc d hd hc hf hSd α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ
  obtain ⟨q, hq | hq⟩ := hd
  · exact h7 S hS hnc d ⟨q, hq⟩ hc hf hSd α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ
  · exact h8 S hS hnc d ⟨q, hq⟩ hc hf hSd α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
