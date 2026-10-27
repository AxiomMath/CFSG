module

public import CFSG.LieType.Universal.Spin.Twisted.Weyl
public import CFSG.LieType.Universal.Spin.Twisted.Generation
public import CFSG.LieType.Universal.Spin.Twisted.Commutator
public import CFSG.LieType.Universal.Spin.Twisted.Bruhat
public import CFSG.LieType.Universal.Spin.Twisted.Torus
public import CFSG.LieType.Steinberg.Conclusion

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

universe w

variable (n : ℕ) {K : Type} [Field K] [Finite K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem minusDatum_isCTGroupDatum (hn : 4 ≤ n) :
    IsCTGroupDatum (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum n hirr).isFiniteType) (minusDatum n hirr).roots
      (minusDatum n hirr).rootGroup (minusWeyl n hirr) (minusTorus n hirr) where
  n_mem := minusDatum_n_mem n hirr
  conj_mem := minusDatum_conj_mem n hirr
  braid := minusDatum_braid n hirr
  H_le := minusDatum_H_le n hirr
  sq_mem := minusDatum_sq_mem n hirr
  H_conj_mem := minusDatum_H_conj_mem n hirr
  conj_H_mem := minusDatum_conj_H_mem n hirr
  le_rankOne := minusDatum_le_rankOne n hirr
  iSup_eq_top := minusDatum_iSup_eq_top n hirr hn

theorem minusDatum_steinbergExtras :
    SteinbergExtras (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) where
  ne_bot := minusDatum_ne_bot n hirr
  two_smul_le := minusDatum_two_smul_le n hirr
  commutator_mem := minusDatum_commutator_mem n hirr
  prodInjective_pos L hL hmem hsort := by
    refine minusDatum_prodInjective n hirr 1 L hL (fun γ hγ => ((hmem γ).1 hγ).1)
      (fun γ hγ => ?_) (hsort.imp fun {γ δ} h => ?_)
    · have h : 0 < ht (ι := Fin (n - 1)) γ := ((hmem γ).1 hγ).2.1
      omega
    · have h' : ht (ι := Fin (n - 1)) γ ≤ ht (ι := Fin (n - 1)) δ := h
      omega
  prodInjective_neg L hL hmem hsort := by
    refine minusDatum_prodInjective n hirr (-1) L hL (fun γ hγ => ((hmem γ).1 hγ).1)
      (fun γ hγ => ?_) (hsort.imp fun {γ δ} h => ?_)
    · have h : ht (ι := Fin (n - 1)) γ < 0 := ((hmem γ).1 hγ).2.1
      omega
    · have h' : ht (ι := Fin (n - 1)) δ ≤ ht (ι := Fin (n - 1)) γ := h
      omega
  posPart_inf_negPart := minusDatum_posPart_inf_negPart n hirr
  rankOne_bruhat := minusDatum_rankOne_bruhat n hirr
  eq_one_of_mem_normalizer := minusDatum_eq_one_of_mem_normalizer n hirr
  torus_commute := minusDatum_torus_commute n hirr
  torus_iSupIndep := minusDatum_torus_iSupIndep n hirr
  torus_inf_posPart := minusDatum_torus_inf_posPart n hirr

theorem minusDatum_conclusionA (hn : 4 ≤ n) : ConclusionA.{0, w} (minusDatum n hirr) :=
  conclusionA_of (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)

end CFSG.LieType.Universal.Spin.Twisted
