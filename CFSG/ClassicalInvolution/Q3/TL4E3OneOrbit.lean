module

public import CFSG.ClassicalInvolution.Q3.TL4E3Z2
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.le_centralizer_of_mem_omegaNbr (hF : E3Frame n R S t J u) {M P : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hP : P ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) {v : Y}
    (hv : IsUniqueInvolution M v) : P ≤ Subgroup.centralizer ({v} : Set Y) := by
  obtain ⟨m, hm'⟩ := hM
  have hm : conjSub m (tightCore R) = M := hm'
  have hd := hF.large.datum
  obtain ⟨S', hd', -⟩ := hd.conj m
  have hcore : tightCore (conjSub m R) = M := by rw [← conjSub_tightCore, hm]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub m R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hα := hF.alpha.conj m
  have hP' : P ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub m R)))
      (tightCore (conjSub m R)) := by
    rw [hfam, hcore]
    exact hP
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hP.1
  have hvt : m * t * m⁻¹ = v := by
    have h1 := hd.isUniqueInvolution_core.conj m
    rw [hm] at h1
    exact h1.eq hv
  have h2 := edge_le_centralizer_of_alpha hd' hP' hw (hα P hP' w hw)
  rwa [hvt] at h2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
