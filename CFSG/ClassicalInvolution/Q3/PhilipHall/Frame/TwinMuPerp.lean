module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfMu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Mu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Asc77.Thompson

section Gen


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem conj_mem_omegaNbr' (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (h : J ∈ omegaNbr Ω K) (g : G) :
    conjSub g J ∈ omegaNbr Ω (conjSub g K) := by
  obtain ⟨hJ, hne, R, hR, hRJ, hRN⟩ := h
  refine ⟨hΩ.conjInvariant g J hJ, fun e => hne ((conjSub_injective g) e), conjSub g R,
    RSet.conj hΩ.conjInvariant hR g, conjSub_mono hRJ, ?_⟩
  intro x hx
  have hx' : g⁻¹ * x * g ∈ R := mem_conjSub_iff.mp hx
  have hn : g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) := hRN hx'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have e : g⁻¹ * (x * h * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * h * g) * (g⁻¹ * x * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hn (g⁻¹ * h * g)

open Classical in
theorem dbarConnected_of_not_wyl (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hμ : ¬ MuIsoWylD4 Ω W) : DbarConnected Ω W := by
  by_contra hnc
  have hΩ : HypOmegaGen Ω := hP.hyp
  set S : Finset (Subgroup G) := {K, K', K₃} with hSdef
  have hS : ∀ M ∈ S, M ∈ twinSet Ω K := by
    intro M hM
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · exact mem_twinSet_self hd.mem hd.hz
    · exact hd.hK'
    · exact hd.hK₃
  have hKS : K ∈ S := by simp [hSdef]
  obtain ⟨R, hRs, -, hRP⟩ := Q3T8.Asc77.T7V.exists_sylow_family hΩ hd.hz S hS
  obtain ⟨g, hg⟩ := Q3T6.Mu.exists_rep_of_member_sylow (ι := ↥S) hP hW (fun i => i.1)
    (fun i => R i.1) (fun i => (hS i.1 i.2).1) (fun i => hRs i.1 i.2) (⨆ M ∈ S, R M) hRP
    (fun i => le_iSup₂_of_le i.1 i.2 le_rfl)
  obtain ⟨ρ₁, h₁⟩ := hg ⟨K, hKS⟩
  obtain ⟨ρ₂, h₂⟩ := hg ⟨K', by simp [hSdef]⟩
  obtain ⟨ρ₃, h₃⟩ := hg ⟨K₃, by simp [hSdef]⟩
  have a12 : K' ∈ omegaNbr Ω K := adj_of_twins' hd hperp (mem_twinSet_self hd.mem hd.hz) hd.hK' hd.hne
  have a13 : K₃ ∈ omegaNbr Ω K :=
    adj_of_twins' hd hperp (mem_twinSet_self hd.mem hd.hz) hd.hK₃ hd.hK₃K
  have a23 : K₃ ∈ omegaNbr Ω K' := adj_of_twins' hd hperp hd.hK' hd.hK₃ hd.hK₃K'
  have h₁' : ρ₁.K = conjSub g K := h₁
  have h₂' : ρ₂.K = conjSub g K' := h₂
  have h₃' : ρ₃.K = conjSub g K₃ := h₃
  have h12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K := by
    rw [h₁', h₂']; exact conj_mem_omegaNbr' hΩ a12 g
  have h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K := by
    rw [h₁', h₃']; exact conj_mem_omegaNbr' hΩ a13 g
  have h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K := by
    rw [h₂', h₃']; exact conj_mem_omegaNbr' hΩ a23 g
  obtain ⟨x, hx, y, hy, w, hw', hxy, hxw, hyw, c1, c2, c3⟩ :=
    exists_three_commuting hP hW ρ₁ ρ₂ ρ₃ rfl rfl rfl h12 h13 h23
  have hcube : Q3T8.Asc77.ThompsonCube := fun _ _ _ _ hP' => Q3CL.thompsonCube hP'
  rcases Q3T8.Asc77.Thompson.muDelta_classification hcube Q3T8.Asc77.thompsonStar
      Q3T8.Asc77.thompsonClique hP hW hnc with ⟨e, he⟩ | ⟨e, he⟩ | h
  · exact absurd (by rw [← map_mul, ← map_mul, c1]) (swap3_no_comm (e x) (e y)
      ((he x).mp hx) ((he y).mp hy) (fun h => hxy (e.injective h)))
  · exact (swap4_no_three (e x) (e y) (e w) ((he x).mp hx) ((he y).mp hy) ((he w).mp hw')
      (fun h => hxy (e.injective h)) (fun h => hxw (e.injective h)) (fun h => hyw (e.injective h))
      (by rw [← map_mul, ← map_mul, c1]) (by rw [← map_mul, ← map_mul, c2])
      (by rw [← map_mul, ← map_mul, c3])).elim
  · exact hμ h

theorem dstarComp_subset_twinSet_of_not_wyl (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hμ : ¬ MuIsoWylD4 Ω W) :
    ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K := by
  have hconn := dbarConnected_of_not_wyl hP hd hperp hW hμ
  have heq : dComp Ω K = dstarComp Ω K := by
    by_contra hne
    exact Q3T6.Mu.thompsonGraphAll hP hd.mem hne hW hconn
  intro J hJ
  rw [← heq] at hJ
  exact A7T22.dComp_subset_twinSet hd.hyp hd.mem hd.hz hperp hJ

end Gen

section Named


theorem v3Sigma_proved (n : ℕ) : V3Sigma n := by
  intro Y _ _ R S t h h3 hE K K' K₃ u₁ u₂ u₃ hd hμ J hJ
  have hC := CoreData.of_S h.core
  have hPG := hC.partIHypG
  have hperp := kPerp_datum h hd.mem hd.hz
  push Not at hμ
  obtain ⟨W, hW, hnW⟩ := hμ
  exact dstarComp_subset_twinSet_of_not_wyl hPG hd hperp hW hnW J hJ

end Named

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
