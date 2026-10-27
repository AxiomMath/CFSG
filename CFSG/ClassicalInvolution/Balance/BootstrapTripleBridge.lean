module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type*} [Group G]

private theorem conj_inv_apply (g x : G) : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
  simp

theorem exists_exactTriple_of_distinctCentralTriple {z : G} {J : Subgroup G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzJ : z ∈ J) (hJ : J ≤ Subgroup.centralizer {z})
    (h : DistinctCentralTriple z J) :
    ∃ g : Fin 3 → G, ExactTriple (J.map (MulAut.conj (g 0)⁻¹).toMonoidHom)
      (J.map (MulAut.conj (g 1)⁻¹).toMonoidHom) (J.map (MulAut.conj (g 2)⁻¹).toMonoidHom)
      ((g 0)⁻¹ * z * g 0) ((g 1)⁻¹ * z * g 1) ((g 2)⁻¹ * z * g 2) := by
  obtain ⟨g, hcomm, hinj⟩ := h
  have hmem : ∀ i, (g i)⁻¹ * z * g i ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom := fun i =>
    Subgroup.mem_map.mpr ⟨z, hzJ, conj_inv_apply _ _⟩
  have hcent : ∀ i, ∀ k ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom,
      k * ((g i)⁻¹ * z * g i) = ((g i)⁻¹ * z * g i) * k := by
    intro i k hk
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hk
    have hjz : j * z = z * j := Subgroup.mem_centralizer_singleton_iff.mp (hJ hj)
    rw [conj_inv_apply]
    calc (g i)⁻¹ * j * g i * ((g i)⁻¹ * z * g i) = (g i)⁻¹ * (j * z) * g i := by group
      _ = (g i)⁻¹ * (z * j) * g i := by rw [hjz]
      _ = (g i)⁻¹ * z * g i * ((g i)⁻¹ * j * g i) := by group
  have hsq : ∀ i, (g i)⁻¹ * z * g i * ((g i)⁻¹ * z * g i) = 1 := by
    intro i
    calc (g i)⁻¹ * z * g i * ((g i)⁻¹ * z * g i) = (g i)⁻¹ * (z * z) * g i := by group
      _ = 1 := by rw [hz2]; group
  have hne1 : ∀ i, (g i)⁻¹ * z * g i ≠ 1 := by
    intro i hi
    apply hz1
    calc z = g i * ((g i)⁻¹ * z * g i) * (g i)⁻¹ := by group
      _ = 1 := by rw [hi]; group
  have hdist : ∀ i j, i ≠ j → (g i)⁻¹ * z * g i ≠ (g j)⁻¹ * z * g j := fun i j hij heq =>
    hij (hinj heq)
  exact ⟨g, hmem 0, hmem 1, hmem 2, hcent 0, hcent 1, hcent 2, hsq 0, hsq 1, hsq 2, hne1 0,
    hne1 1, hne1 2, hcomm 0 1 (by decide), hcomm 0 2 (by decide), hcomm 1 2 (by decide),
    hdist 0 1 (by decide), hdist 0 2 (by decide), hdist 1 2 (by decide)⟩

end CFSG.ClassicalInvolution.Balance.Bootstrap
