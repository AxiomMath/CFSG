module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Graph
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Field
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3GField
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.KGroups.L3Eps

section Assembly

variable {F : Type} [Field F] [Finite F]

theorem kaAll_L3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card F = p ^ f)
    (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  have hodd : Odd (Nat.card F) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ Nat.card F := by
    rw [hK]
    calc 3 ≤ p := by have := hp.two_le; omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have h2 : (2 : F) ≠ 0 := kaL3_two_ne_zero hodd
  rcases linear3_involution_cases h2 α hα hα1 with
    ⟨y, hy2, hy1, hαy⟩ | ⟨A, σ, hσ, hαeq⟩ | ⟨B, hB, hαeq⟩ | ⟨A, σ, hσ, hαeq⟩
  · obtain ⟨e', he'⟩ := exists_equiv_tInv h2 (MulEquiv.refl (projectiveSL 3 F)) hy2 hy1
    have ht : KAAll (MulAut.conj (tInv : projectiveSL 3 F)) := by
      by_cases h3' : Nat.card F = 3
      · exact kaL3_inner_three h3'
      · exact kaL3_inner_five hodd (by obtain ⟨k, hk⟩ := hodd; omega)
    have h := KAAll.of_mulEquiv e'.symm ht
    have hc : MulAut.congr e'.symm (MulAut.conj (tInv : projectiveSL 3 F)) = MulAut.conj y := by
      ext x
      have : e'.symm tInv = y := by rw [← he']; exact e'.symm_apply_apply y
      simp [MulAut.congr_apply, MulAut.conj_apply, this]
    rw [hc] at h
    rw [hαy]
    exact h
  · rw [hαeq]
    exact kaL3_field hp hf hK A σ hσ (by rw [sq, ← hαeq]; exact hα)
  · rw [hαeq]
    exact kaL3_graph hodd h3 B hB
  · rw [hαeq]
    exact kaL3_gfield hp hp2 hf hK A σ hσ (by rw [sq, ← hαeq]; exact hα)

end Assembly

theorem kay_L3 : KAY FL3 := by
  intro Y _ _ hY _ α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  obtain ⟨p0, f0, hp0, hf0, hp02, hlie⟩ := hY
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
  have hα2' : MulAut.congr e α * MulAut.congr e α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hα1' : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hK := KAAll.of_mulEquiv e.symm (kaAll_L3 hp0 hp02 hf0 hFcard _ hα2' hα1')
  have hc : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [hc] at hK
  have hc := hK p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
