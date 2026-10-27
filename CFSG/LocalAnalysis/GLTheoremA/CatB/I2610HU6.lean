module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Facts
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HQuot
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HLift
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HCore
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HL2
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9

private theorem nonempty_mulEquiv_S6_of_catalogIs {S : Type} [Group S]
    (h : catalogIs S isU6two) : Nonempty (S ≃* LevelLieU6.S6) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isU6two, onLie] at hi
  | alternating n hn => simp [isU6two, onLie] at hi
  | sporadic s => simp [isU6two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [isU6two, onLie] at hi
      exact LevelLieU6.bridge_u6two_stated hv ((TauCeti.PrimePower.card_def q).trans hi) e
    | _ => simp [isU6two, onLie] at hi

theorem i2610FactU6_holds : I2610FactU6 := by
  intro Γ _ _ K W hK hcat hWN hW hW27 hWK J hJ
  obtain ⟨eS⟩ := nonempty_mulEquiv_S6_of_catalogIs hcat
  obtain ⟨A, hA, h9, I, hI, ⟨e₁⟩⟩ := exists_quot_component hK hWN hW hW27 hWK eS hJ
  obtain ⟨X, Y, hX3, hY3, hXY, hXs, hYX, J', hJ', ⟨e₂⟩⟩ :=
    exists_pair_of_elemAbelian_nine hA h9 hI
  apply not_catalogIs_isL2prime_of_card_eq
  rw [Nat.card_congr (e₁.trans e₂).toEquiv]
  exact card_pSimple_of_pair X Y hX3 hY3 hXY hXs hYX hJ'

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
