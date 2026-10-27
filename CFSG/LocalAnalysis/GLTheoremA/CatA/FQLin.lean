module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open

section SL

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem sl_map_subtype_iff (σ : K ≃+* K) (A : GL (Fin d) (fixF σ)) :
    Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ LargeEvenSLGroup (Fin d) K ↔
      A ∈ LargeEvenSLGroup (Fin d) (fixF σ) := by
  rw [mem_LargeEvenSL_iff, mem_LargeEvenSL_iff]
  have h : ((Matrix.GeneralLinearGroup.map (fixF σ).subtype A : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = (fixF σ).subtype (A : Matrix (Fin d) (Fin d) (fixF σ)).det := by
    rw [RingHom.map_det]
    rfl
  rw [h]
  constructor
  · intro h1
    apply (fixF σ).subtype.injective
    rw [h1, map_one]
  · intro h1
    rw [h1, map_one]

theorem stOrderBody_linear (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (I : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))) :
    StOrderBody p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  refine stOrderBody_of_matrix hm hK (LargeEvenSLGroup (Fin d) K)
    (fun σ h hh => sl_map_mem σ h hh) (fun _ => True) (fun _ _ _ => trivial)
    (u := d * (d - 1) / 2) (v := 1) ?_ one_pos ?_ ?_ hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) I
  · have : 2 ≤ d * (d - 1) := calc 2 = 2 * 1 := rfl
      _ ≤ d * (d - 1) := Nat.mul_le_mul hd (by omega)
    exact Nat.div_pos this (by norm_num)
  · rw [pow_one]
    exact twoPart_card_SL hd hm hK
  · intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_eq_of_iff σ _ (LargeEvenSLGroup (Fin d) (fixF σ)) (sl_map_subtype_iff σ)]
    exact twoPart_card_SL hd (one_le_of_card_fixed he) hk

end SL

end FQ

end CFSG.LocalAnalysis.GLTheoremA
