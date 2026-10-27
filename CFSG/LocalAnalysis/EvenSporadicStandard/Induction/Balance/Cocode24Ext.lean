module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Weight
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayBasic

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open CFSG.EvenSporadicStandard.Wong77.Module (golayCode golayRow coordSum coordSum_apply)

abbrev WWord : Type := CFSG.EvenSporadicStandard.Wong77.Module.Word

@[expose] def res : Word →ₗ[ZMod 2] WWord := LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.castSucc

@[simp] theorem res_apply (v : Word) (i : Fin 23) : res v i = v i.castSucc := rfl

theorem res_rowWord (k : Fin 12) : res (rowWord k) = golayRow k := by
  revert k
  decide

theorem parity_rowWord (k : Fin 12) :
    rowWord k (Fin.last 23) = ∑ i : Fin 23, golayRow k i := by
  revert k
  decide

theorem ext_of_mem_golay {v : Word} (hv : v ∈ golay) :
    res v ∈ golayCode ∧ v (Fin.last 23) = ∑ i : Fin 23, v i.castSucc := by
  rw [golay_eq_span] at hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [res_rowWord]
      exact Submodule.subset_span ⟨k, rfl⟩
    · rw [parity_rowWord]
      simp only [← res_apply, res_rowWord]
  · exact ⟨Submodule.zero_mem _, by simp⟩
  · rintro x y - - ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨by rw [map_add]; exact Submodule.add_mem _ hx1 hy1, ?_⟩
    simp only [Pi.add_apply, hx2, hy2, Finset.sum_add_distrib]
  · rintro a x - ⟨hx1, hx2⟩
    refine ⟨by rw [map_smul]; exact Submodule.smul_mem _ _ hx1, ?_⟩
    simp only [Pi.smul_apply, hx2, Finset.smul_sum]

theorem mem_golay_iff_ext (v : Word) :
    v ∈ golay ↔ res v ∈ golayCode ∧ v (Fin.last 23) = ∑ i : Fin 23, v i.castSucc := by
  refine ⟨ext_of_mem_golay, ?_⟩
  rintro ⟨h1, h2⟩
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 h1
  have hw : (∑ k, m k • rowWord k) ∈ golay :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (rowWord_mem k)
  have hres : res (∑ k, m k • rowWord k) = res v := by
    rw [map_sum]
    simp only [map_smul, res_rowWord]
    exact hm
  obtain ⟨-, hw2⟩ := ext_of_mem_golay hw
  have hvw : v = ∑ k, m k • rowWord k := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [h2, hw2]
      exact Finset.sum_congr rfl fun j _ => (congrFun hres j).symm
    · exact (congrFun hres j).symm
  rw [hvw]
  exact hw

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
