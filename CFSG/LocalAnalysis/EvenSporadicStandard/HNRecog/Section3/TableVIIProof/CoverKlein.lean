module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv

open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y] {w : Y} {π : Y →* Perm (Fin 5)}

theorem tableVII_cover_klein (hC : TableVIICover Y w π) {x : Y} (hx : x ∈ commutator Y)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxw : x ≠ w) :
    ∃ x₂ : Y, x₂ ∈ commutator Y ∧ x₂ ^ 2 = 1 ∧ x * x₂ = x₂ * x ∧ π x₂ ≠ 1 ∧ π x₂ ≠ π x := by
  have hxsign : Perm.sign (π x) = 1 := (tableVII_cover_mem_comm hC).mp hx
  have hv2 : π x * π x = 1 := by
    have h : (π x) ^ 2 = 1 := by simpa using congrArg π hx2
    simpa [pow_two] using h
  have hv1 : π x ≠ 1 := by
    intro h
    rcases (tableVII_cover_pi_eq_one hC).mp h with h' | h'
    · exact hx1 h'
    · exact hxw h'
  obtain ⟨g, hgcomm, hgne, hgstep⟩ := tableVII_perm_klein (π x) hv2 hv1 hxsign
  obtain ⟨ĝ, hĝ⟩ := hC.surj g
  let x₂ : Y := ĝ * x * ĝ⁻¹
  have hπx2 : π x₂ = g * π x * g⁻¹ := by
    change π (ĝ * x * ĝ⁻¹) = g * π x * g⁻¹
    simp only [map_mul, map_inv, hĝ]
  have hx₂mem : x₂ ∈ commutator Y := by
    change ĝ * x * ĝ⁻¹ ∈ commutator Y
    exact (inferInstance : (commutator Y).Normal).conj_mem x hx ĝ
  have hx₂sq : x₂ ^ 2 = 1 := by
    change (ĝ * x * ĝ⁻¹) ^ 2 = 1
    rw [conj_pow, hx2]
    simp
  have hxinv : x⁻¹ = x := by
    have h : x * x = 1 := by simpa [pow_two] using hx2
    exact inv_eq_of_mul_eq_one_right h
  have hx₂inv : x₂⁻¹ = x₂ := by
    have h : x₂ * x₂ = 1 := by simpa [pow_two] using hx₂sq
    exact inv_eq_of_mul_eq_one_right h
  refine ⟨x₂, hx₂mem, hx₂sq, ?_, ?_, ?_⟩
  · have hπc : π (x * x₂ * x⁻¹ * x₂⁻¹) = 1 := by
      change π ⁅x, x₂⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hπx2]
      exact hgcomm.symm
    rcases (tableVII_cover_pi_eq_one hC).mp hπc with hc | hc
    · calc x * x₂ = (x * x₂ * x⁻¹ * x₂⁻¹) * (x₂ * x) := by group
        _ = 1 * (x₂ * x) := by rw [hc]
        _ = x₂ * x := one_mul _
    · exfalso
      have hy2 : (x * x₂) ^ 2 = w := by
        have h : x * x₂ * x⁻¹ * x₂⁻¹ = (x * x₂) ^ 2 := by
          rw [pow_two, hxinv, hx₂inv]
          group
        rw [← h, hc]
      let x₃ : Y := ĝ * x₂ * ĝ⁻¹
      have hx₃sq : x₃ ^ 2 = 1 := by
        change (ĝ * x₂ * ĝ⁻¹) ^ 2 = 1
        rw [conj_pow, hx₂sq]
        simp
      have hπx₃ : π x₃ = g * (g * π x * g⁻¹) * g⁻¹ := by
        change π (ĝ * x₂ * ĝ⁻¹) = g * (g * π x * g⁻¹) * g⁻¹
        simp only [map_mul, map_inv, hĝ, hπx2]
      have hπy : π (x * x₂) = π x * (g * π x * g⁻¹) := by
        rw [map_mul, hπx2]
      have hπr : π (x₃ * (x * x₂)⁻¹) = 1 := by
        rw [map_mul, map_inv, hπx₃, hπy, hgstep]
        group
      rcases (tableVII_cover_pi_eq_one hC).mp hπr with hr | hr
      · have hx3eq : x₃ = x * x₂ := by
          calc x₃ = x₃ * (x * x₂)⁻¹ * (x * x₂) := by group
            _ = 1 * (x * x₂) := by rw [hr]
            _ = x * x₂ := one_mul _
        have hx3w : x₃ ^ 2 = w := by rw [hx3eq, hy2]
        exact hC.ne_one (by rw [← hx3w, hx₃sq])
      · have hx3eq : x₃ = w * (x * x₂) := by
          calc x₃ = x₃ * (x * x₂)⁻¹ * (x * x₂) := by group
            _ = w * (x * x₂) := by rw [hr]
        have hx3w : x₃ ^ 2 = w := by
          rw [hx3eq, pow_two]
          calc (w * (x * x₂)) * (w * (x * x₂))
              = w * ((x * x₂) * w) * (x * x₂) := by group
            _ = w * (w * (x * x₂)) * (x * x₂) := by
                  rw [← tableVII_cover_central hC (x * x₂)]
            _ = w * w * ((x * x₂) * (x * x₂)) := by group
            _ = w := by
                  have hww : w * w = 1 := by simpa [pow_two] using hC.sq
                  rw [hww, one_mul]
                  simpa [pow_two] using hy2
        exact hC.ne_one (by rw [← hx3w, hx₃sq])
  · intro h
    have h1 : g * π x * g⁻¹ = 1 := by rw [← hπx2, h]
    exact hv1 (by
      calc π x = g⁻¹ * (g * π x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
  · intro h
    exact hgne (by rw [← hπx2]; exact h)

end CFSG.EvenSporadicStandard.HNRecog.Section3