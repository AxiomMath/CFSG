module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscClaims
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc



section Finite

theorem swap3_no_comm (a b : Equiv.Perm (Fin 3)) (ha : a.IsSwap) (hb : b.IsSwap) (hab : a ≠ b) :
    a * b ≠ b * a := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨x', y', hxy', rfl⟩ := hb
  revert x y x' y'
  decide

theorem swap4_no_three (a b c : Equiv.Perm (Fin 4)) (ha : a.IsSwap) (hb : b.IsSwap)
    (hc : c.IsSwap) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : a * b = b * a)
    (h2 : a * c = c * a) (h3 : b * c = c * b) : False := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨x', y', hxy', rfl⟩ := hb
  obtain ⟨x'', y'', hxy'', rfl⟩ := hc
  revert x y x' y' x'' y''
  decide

end Finite

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_three_commuting (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    {M₁ M₂ M₃ : Subgroup G} (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h₁ : ρ₁.K = M₁) (h₂ : ρ₂.K = M₂)
    (h₃ : ρ₃.K = M₃) (h12 : M₂ ∈ omegaNbr Ω M₁) (h13 : M₃ ∈ omegaNbr Ω M₁)
    (h23 : M₃ ∈ omegaNbr Ω M₂) :
    ∃ x ∈ muDelta Ω W, ∃ y ∈ muDelta Ω W, ∃ w ∈ muDelta Ω W, x ≠ y ∧ x ≠ w ∧ y ≠ w ∧
      x * y = y * x ∧ x * w = w * x ∧ y * w = w * y := by
  subst h₁ h₂ h₃
  have ne12 : ρ₁.K ≠ ρ₂.K := fun e => h12.2.1 e.symm
  have ne13 : ρ₁.K ≠ ρ₃.K := fun e => h13.2.1 e.symm
  have ne23 : ρ₂.K ≠ ρ₃.K := fun e => h23.2.1 e.symm
  refine ⟨MuTab.muTabElt ρ₁, MuTab.muTabElt_mem ρ₁, MuTab.muTabElt ρ₂, MuTab.muTabElt_mem ρ₂,
    MuTab.muTabElt ρ₃, MuTab.muTabElt_mem ρ₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => ne12 ((Q3T6.Mu.muTabElt_eq_iff hP hW ρ₁ ρ₂).mp h)
  · exact fun h => ne13 ((Q3T6.Mu.muTabElt_eq_iff hP hW ρ₁ ρ₃).mp h)
  · exact fun h => ne23 ((Q3T6.Mu.muTabElt_eq_iff hP hW ρ₂ ρ₃).mp h)
  · exact (Q3T6.Mu.muTab_commute_iff hP hW ρ₁ ρ₂ ne12).mpr h12
  · exact (Q3T6.Mu.muTab_commute_iff hP hW ρ₁ ρ₃ ne13).mpr h13
  · exact (Q3T6.Mu.muTab_commute_iff hP hW ρ₂ ρ₃ ne23).mpr h23

end Members

section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem disc12_of_setting (s : Setting n R S t₀ K K' z u J t W) :
    dComp (CoreAssembly.conjClass (tightCore R)) K =
        dstarComp (CoreAssembly.conjClass (tightCore R)) K ∨
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact Or.inl heq
  right
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have hf := s.data.frame
  have hW : W ∈ WSet Ω := s.data.hW
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hnc : ¬ DbarConnected Ω W := Q3T6.Mu.thompsonGraphAll hP hK heq hW
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ₁, h₁⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hK hf.hz s.data.hzW
  obtain ⟨ρ₂, h₂⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hK'Ω hzK' s.data.hzW
  obtain ⟨ρ₃, h₃⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hf.hJ.1 hf.ht s.data.htW
  have h12 : K' ∈ omegaNbr Ω K :=
    Q3.Q3CL.T3.twin_mem_omegaNbr hP.hyp hK hK'Ω hf.hne hf.hz hzK'
  have h13 : J ∈ omegaNbr Ω K := hf.hJ.2 K (mem_twinSet_self hK hf.hz)
  have h23 : J ∈ omegaNbr Ω K' := hf.hJ.2 K' hf.hK'
  obtain ⟨x, hx, y, hy, w, hw, hxy, hxw, hyw, c1, c2, c3⟩ :=
    exists_three_commuting hP hW ρ₁ ρ₂ ρ₃ h₁ h₂ h₃ h12 h13 h23
  have hcube : Q3T8.Asc77.ThompsonCube := fun _ _ _ _ hP' => Q3CL.thompsonCube hP'
  rcases Q3T8.Asc77.Thompson.muDelta_classification hcube Q3T8.Asc77.thompsonStar
      Q3T8.Asc77.thompsonClique hP hW hnc with ⟨e, he⟩ | ⟨e, he⟩ | h
  · exact absurd (by rw [← map_mul, ← map_mul, c1]) (swap3_no_comm (e x) (e y)
      ((he x).mp hx) ((he y).mp hy) (fun h => hxy (e.injective h)))
  · exact (swap4_no_three (e x) (e y) (e w) ((he x).mp hx) ((he y).mp hy) ((he w).mp hw)
      (fun h => hxy (e.injective h)) (fun h => hxw (e.injective h)) (fun h => hyw (e.injective h))
      (by rw [← map_mul, ← map_mul, c1]) (by rw [← map_mul, ← map_mul, c2])
      (by rw [← map_mul, ← map_mul, c3])).elim
  · exact h

theorem disc12 (n : ℕ) : Disc12 n := by
  intro Y _ _ R S t₀ K K' z u J t W s
  exact disc12_of_setting s

end Main

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
