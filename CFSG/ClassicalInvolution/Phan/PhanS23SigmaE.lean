module

public import CFSG.ClassicalInvolution.Phan.PhanS23SigmaC
public import CFSG.ClassicalInvolution.Phan.PhanS23SigmaD

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open Descent

theorem sigmaWitt_family (hW : FamilyWitt7) {ι : Type} [Fintype ι] (v w : ι → Vec GF49)
    (hbf : ∀ i j, bf m0 (v i) (v j) = bf m0 (w i) (w j))
    (hher : ∀ i j, her m0 (v i) (v j) = her m0 (w i) (w j))
    (hrel : ∀ c d : ι → GF49, ∑ i, c i • v i + ∑ i, d i • tauV m0 (v i) = 0 ↔
      ∑ i, c i • w i + ∑ i, d i • tauV m0 (w i) = 0) :
    ∃ g : SigmaIso m0, ∀ i, g.toLinearEquiv (v i) = w i := by
  obtain ⟨E, hE1, hE2, hE3⟩ := descent_witt hW (fun i => gammaEquiv.symm (v i))
    (fun i => gammaEquiv.symm (w i))
    (fun i j => by rw [polarK_symm, polarK_symm]; exact hbf i j)
    (fun i j => by rw [polarK_starV_symm, polarK_starV_symm]; exact hher i j)
    (fun c d => by rw [rel_symm, rel_symm]; exact hrel c d)
  refine ⟨⟨gammaEquiv.symm.trans (E.trans gammaEquiv), ?_, ?_⟩, ?_⟩
  · intro x y
    simp only [LinearEquiv.trans_apply, bf_gammaEquiv, hE1]
    exact polarK_symm x y
  · intro x
    simp only [LinearEquiv.trans_apply, tauV_symm, hE2, tauV_gammaEquiv]
  · intro i
    simp only [LinearEquiv.trans_apply, hE3]
    exact gammaEquiv.apply_symm_apply (w i)

theorem sigmaWitt_of_familyWitt7 (hW : FamilyWitt7) : SigmaWitt :=
  fun v w h1 h2 h3 => sigmaWitt_family hW v w h1 h2 h3

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
