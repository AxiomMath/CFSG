module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem rk2_isLabel_norm {X : Type} [Group X] {lab : GLALabel} (h : Rk2IsLabel X lab) :
    Rk2IsLabel X (rk2Norm lab) := by
  by_cases hC : lab.tag = .C
  · obtain ⟨t, ℓ, n⟩ := lab
    simp only at hC
    subst hC
    obtain ⟨hX, lab', hlab', hraw⟩ := h
    obtain ⟨R, _, I, F, hs, hna, θ, hlabeq⟩ := rk2_rawDatum_exists hraw
    subst hlabeq
    exact ⟨hX, ⟨.B, ℓ, n⟩, hlab', rk2_rawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  · rw [rk2Norm_of_ne hC]
    exact h

theorem i162At_of_tables (hInn : Rk2InnRank) (hLow : Rk2Lower) (G : Type) [Group G] [Finite G] :
    I162At G := by
  intro p hp hp2 B K k hB hBK hk3 hek hcard
  obtain ⟨lab, hLab, hlab, hkr⟩ := rk2_inn_bound hInn hp hp2 k hB hBK hcard
  have hE := hLow K lab hLab
  have hhalf := rk2_half_of_rank hlab hp hp2 (c := Subgroup.center ↥K = ⊥) (e := evenRank ↥K)
    (by omega) hE (by omega)
  exact ⟨rk2Norm lab, rk2_isLabel_norm hLab, hhalf⟩

end CFSG.LocalAnalysis.GLTheoremA
