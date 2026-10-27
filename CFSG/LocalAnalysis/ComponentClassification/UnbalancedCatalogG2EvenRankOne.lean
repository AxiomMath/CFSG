module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] def g2RankOne (K : Type) [Field K] (i : Fin Tag.G2.rank) : Subgroup (ModGL .G2 K) :=
  Subgroup.closure (Set.range (xUnit .G2 K i) ∪ Set.range (yUnit .G2 K i))

theorem xUnit_mem_g2RankOne (i : Fin Tag.G2.rank) (c : K) : xUnit .G2 K i c ∈ g2RankOne K i :=
  Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem yUnit_mem_g2RankOne (i : Fin Tag.G2.rank) (c : K) : yUnit .G2 K i c ∈ g2RankOne K i :=
  Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem weylElt_mem_g2RankOne (i : Fin Tag.G2.rank) (t : Kˣ) :
    weylElt .G2 K i t ∈ g2RankOne K i := by
  rw [weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (xUnit_mem_g2RankOne i _) (yUnit_mem_g2RankOne i _))
    (xUnit_mem_g2RankOne i _)

theorem torusElt_mem_g2RankOne (i : Fin Tag.G2.rank) (t : Kˣ) :
    torusElt .G2 K i t ∈ g2RankOne K i :=
  mul_mem (weylElt_mem_g2RankOne i t) (weylElt_mem_g2RankOne i (-1))

theorem g2RankOne_le_adjointGroup (i : Fin Tag.G2.rank) : g2RankOne K i ≤ adjointGroup .G2 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_adjointGroup i c
  · exact yUnit_mem_adjointGroup i c

theorem weylElt_mul_self [CharP K 2] (i : Fin Tag.G2.rank) :
    weylElt .G2 K i 1 * weylElt .G2 K i 1 = 1 := by
  have h := weylElt_one_sq (τ := .G2) (R := K) i
  have hneg : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [sq, hneg, torusElt_one] at h
  exact h

theorem weylElt_inv [CharP K 2] (i : Fin Tag.G2.rank) :
    (weylElt .G2 K i 1)⁻¹ = weylElt .G2 K i 1 :=
  inv_eq_of_mul_eq_one_right (weylElt_mul_self i)

theorem g2_rank_one [CharP K 2] (i : Fin Tag.G2.rank) :
    ∃ ρ : SL2 K →* ModGL .G2 K,
      (∀ c, ρ (uSL c) = xUnit .G2 K i c) ∧ (∀ c, ρ (vSL c) = yUnit .G2 K i c) ∧
      (∀ t, ρ (HSL t) = torusElt .G2 K i t) ∧ ρ WSL = weylElt .G2 K i 1 ∧
      ρ.range = g2RankOne K i ∧ Function.Injective ρ ∧
      (∀ (g : SL2 K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0),
        ρ g = torusElt .G2 K i (Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)) *
          xUnit .G2 K i ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
            (g : Matrix (Fin 2) (Fin 2) K) 0 0)) ∧
      ∀ (g : SL2 K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0),
        ρ g = xUnit .G2 K i ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
            (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
          torusElt .G2 K i (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
            (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) * weylElt .G2 K i 1 *
          xUnit .G2 K i ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
            (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  obtain ⟨ρ, hu, hv, hH, hW, hrange, hker, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image .G2 K i
  have hn2 : weylElt .G2 K i 1 ^ 2 = torusEltHom .G2 K i (-1) := weylElt_one_sq .G2 K i
  obtain ⟨ρ', ⟨hu', hH', hW'⟩, huniq, -, -, -, hcell0, hcell⟩ :=
    exceptional_rank_one_Gaussian_realization (xUnitHom .G2 K i) (torusEltHom .G2 K i)
      (weylElt .G2 K i 1) (fun t s => torusElt_mul_xUnit_mul_inv i t s) hn2
      (fun t => weylElt_mul_torusElt_mul_inv i t)
      (fun s hs => weylElt_mul_xUnit_mul_weylElt i hs)
  have hρ : ρ = ρ' := huniq ρ (fun s => hu s) (fun t => hH t) hW
  refine ⟨ρ, hu, hv, hH, hW, hrange, ?_, fun g hc => ?_, fun g hc => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl, hgl⟩ := hker g hg
    have hl1 : (l : K) = 1 := by
      have h' : ((l : K) - 1) ^ 2 = 0 := by
        linear_combination hl + (1 - (l : K)) * (CharTwo.two_eq_zero (R := K))
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
    refine Subtype.ext ?_
    rw [hgl, hl1, one_smul]
    rfl
  · rw [hρ, hcell0 g hc]
    rfl
  · rw [hρ, hcell g hc]
    rfl

end CFSG.ComponentClassification.UnbalancedCatalog
