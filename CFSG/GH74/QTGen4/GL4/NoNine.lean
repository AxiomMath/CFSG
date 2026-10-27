module

public import CFSG.LargeExtraspecial.O62SL4

public section

namespace CFSG.GH74.QTGen4

open scoped Matrix

theorem GL4_two_pow_nine {g : GL (Fin 4) (ZMod 2)} (h : g ^ 9 = 1) : g ^ 3 = 1 := by
  have hm : ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 9) = 1 := by
    have := congrArg (fun u : GL (Fin 4) (ZMod 2) => (u : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    simpa [Units.val_pow_eq_pow_val] using this
  apply Units.ext
  have := CFSG.LargeExtraspecial.O62.matrix_pow_three_eq_one_of_pow_nine _ hm
  simpa [Units.val_pow_eq_pow_val] using this

theorem orderOf_ne_nine_of_injective {Q : Type} [Group Q] (ψ : Q →* GL (Fin 4) (ZMod 2))
    (hψ : Function.Injective ψ) (q : Q) : orderOf q ≠ 9 := by
  intro hq
  have h9 : q ^ 9 = 1 := by
    rw [← hq]
    exact pow_orderOf_eq_one q
  have hg : ψ q ^ 9 = 1 := by
    rw [← map_pow, h9, map_one]
  have h3 := GL4_two_pow_nine hg
  have hq3 : q ^ 3 = 1 := by
    apply hψ
    rw [map_pow, h3, map_one]
  have hdvd : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  rw [hq] at hdvd
  norm_num at hdvd

end CFSG.GH74.QTGen4

end
