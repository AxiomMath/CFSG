module

public import CFSG.ClassicalInvolution.Q3.Q3URPhanA3
public import CFSG.ClassicalInvolution.Phan.Coherent
public import CFSG.ClassicalInvolution.Phan.Phan3AKernel

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Q3.Q3W

theorem phanA3Completion3_of_cert : PhanA3Completion3 := by
  intro X _ U W hW
  obtain ⟨F, hFι, -, -⟩ := coherent_family card_K9 (n := 3) (by norm_num) hW
  refine ⟨PhanA3Group, inferInstance, phanP, famHom F, phanV, phanP_surjective, phanP_ker,
    fun a => ?_, fun a => ?_⟩
  · exact map_phanV (standardFamily K9 3 1 3) a
  · rw [map_phanV F a, hFι a]

end CFSG.ClassicalInvolution.Phan.Q3G
