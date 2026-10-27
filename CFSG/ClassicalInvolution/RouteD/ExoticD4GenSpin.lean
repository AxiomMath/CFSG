module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenPos
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourPair
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem finrank_quadPlus_four : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem exists_frame_span_eq_perp (hodd : Odd (Nat.card F)) (fr : OFrame (quadPlus 4 F)) :
    ∃ frY : OFrame (quadPlus 4 F), frY.span = fr.perp := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hn3 : 3 ≤ 4 := by norm_num
  let a₀ : Fin 4 := ⟨0, by omega⟩
  let a₁ : Fin 4 := ⟨1, by omega⟩
  let a₂ : Fin 4 := ⟨2, by omega⟩
  let a₃ : Fin 4 := ⟨3, by omega⟩
  have h01 : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrArg Fin.val h
  have h23 : a₂ ≠ a₃ := fun h => by simpa [a₂, a₃] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [a₀, a₂] using congrArg Fin.val h
  have h03 : a₀ ≠ a₃ := fun h => by simpa [a₀, a₃] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [a₁, a₂] using congrArg Fin.val h
  have h13 : a₁ ≠ a₃ := fun h => by simpa [a₁, a₃] using congrArg Fin.val h
  set std₁ : OFrame (quadPlus 4 F) := (plusFrame 4 F hn3).toFrame h01 true true with hstd₁
  set std₂ : OFrame (quadPlus 4 F) := (plusFrame 4 F hn3).toFrame h23 true true with hstd₂
  have hstd : ∀ X Y, polar (quadPlus 4 F) (std₁.incl X) (std₂.incl Y) = 0 := fun X Y =>
    Balance.Bootstrap.polar_incl_toFrame_of_disjoint (plusFrame 4 F hn3) h01 h23 h02 h03 h12 h13
      true true true true X Y
  obtain ⟨g, hg, hgi⟩ := exists_isometry_incl_eq std₁ fr
  refine ⟨std₂.map hg, ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro y ⟨Z, rfl⟩
    rw [fr.mem_perp_iff_forall_incl]
    intro Y
    rw [Frame.map_incl, ← hgi Y, polar_map_of_mem hg]
    rw [polar_comm]
    exact hstd Y Z
  · rw [Frame.finrank_span, finrank_perp_eq_four finrank_quadPlus_four]

theorem D4Facts.exists_mem_fund (hF : D4Facts F) : ∃ R, R ∈ fundD4 F :=
  ⟨_, 1, Pi.single (⟨0, by norm_num⟩ : Fin 4) 1, Or.inl (hF.long _), rfl⟩

theorem D4Facts.exists_fund_of_frame (hF : D4Facts F) (fr : OFrame (quadPlus 4 F)) :
    ∃ S ∈ fundD4 F, S.map (spinAction (quadPlus 4 F)) = fr.La.range := by
  have h2 := hF.two_ne_zero
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQnd : (polarBilin (quadPlus 4 F)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 F
  obtain ⟨R₀, hR₀⟩ := hF.exists_mem_fund
  obtain ⟨fr₀, hfr₀⟩ := hF.exists_frame hR₀
  have hperp : 2 ≤ Module.finrank F fr₀.perp := by
    rw [finrank_perp_eq_four finrank_quadPlus_four]
    norm_num
  obtain ⟨x₀, hx₀⟩ := exists_spin_conj hF.odd hQnd fr₀ fr hperp
  refine ⟨conjSub x₀ R₀, conjSub_mem_fundamentalSubgroups hR₀ x₀, ?_⟩
  show (R₀.map (MulAut.conj x₀).toMonoidHom).map _ = _
  rw [map_conj_map, hfr₀]
  exact (La_range_eq_map_conj hx₀).symm

theorem D4Facts.commutes_of_map_commute (hF : D4Facts F)
    {S R : Subgroup (spinGroup (quadPlus 4 F))} (hR : R ∈ fundD4 F)
    (h : ∀ a ∈ S.map (spinAction (quadPlus 4 F)), ∀ b ∈ R.map (spinAction (quadPlus 4 F)),
      a * b = b * a) : Commutes S R := by
  intro x hx y hy
  have hmem : x ∈ Subgroup.centralizer (R : Set (spinGroup (quadPlus 4 F))) :=
    Models.Transfer.mem_centralizer_of_map (ker_spinAction_le_center _) (hF.perf R hR) (g := x)
      (by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (h _ ⟨x, hx, rfl⟩ b hb).symm)
  exact (Subgroup.mem_centralizer_iff.mp hmem y hy).symm

end CFSG.ClassicalInvolution.RouteD.Exotic
