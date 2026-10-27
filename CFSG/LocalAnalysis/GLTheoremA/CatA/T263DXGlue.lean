module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Quot
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]

theorem open_of_native_dx {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).2 h

theorem native_of_open_dx {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    CFSG.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).1 h

theorem exists_two_of_act_open {X₀ J P B : Subgroup Ω} (hJX : J ≤ X₀)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hP2 : IsPGroup 2 ↥P) (hPX : P ≤ X₀)
    (hinn : P ≤ J ⊔ (X₀ ⊓ Subgroup.centralizer (J : Set Ω))) (hact : ⁅P, J⁆ ≠ ⊥)
    (hBX : B ≤ Subgroup.normalizer (X₀ : Set Ω)) (hBJ : B ≤ Subgroup.normalizer (J : Set Ω))
    (hBP : B ≤ Subgroup.normalizer (P : Set Ω)) :
    ∃ T'' : Subgroup Ω, T'' ≤ J ∧ IsPGroup 2 ↥T'' ∧ B ≤ Subgroup.normalizer (T'' : Set Ω) ∧
      ¬ T'' ≤ Subgroup.centralizer (J : Set Ω) :=
  exists_two_of_act hJX (by first | exact hJ | exact native_of_open_dx hJ) hP2 hPX hinn hact hBX
    hBJ hBP

private theorem mem_normalizer_commutator_dx {H K : Subgroup Ω} {g : Ω}
    (hH : g ∈ Subgroup.normalizer (H : Set Ω)) (hK : g ∈ Subgroup.normalizer (K : Set Ω)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

theorem norm_data_dx {S B B₀ T' : Subgroup Ω} {x : Ω} (hSn : S.Normal)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB₀ : B₀ ≤ B) (hxB : x ∈ B₀)
    (hT'B : B ≤ Subgroup.normalizer (T' : Set Ω)) :
    B ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({x} : Set Ω) : Subgroup Ω) : Set Ω) ∧
      B ≤ Subgroup.normalizer
        ((⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) : Set Ω) ∧
      (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤ T' := by
  have hcomm : ∀ g ∈ B, g ∈ Subgroup.centralizer ({x} : Set Ω) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hBab g hg x (hB₀ hxB))
  have hBT'x : B ≤ Subgroup.normalizer
      ((T' ⊓ Subgroup.centralizer ({x} : Set Ω) : Subgroup Ω) : Set Ω) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hT'B hg, Subgroup.le_normalizer (hcomm g hg)⟩
  have hBB₀n : B ≤ Subgroup.normalizer (B₀ : Set Ω) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg k hk
    rw [hBab g hg k (hB₀ hk), mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  refine ⟨fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨by rw [Subgroup.normalizer_eq_top_iff.2 hSn]; exact Subgroup.mem_top g,
        Subgroup.le_normalizer (hcomm g hg)⟩,
    fun g hg => mem_normalizer_commutator_dx (hBB₀n hg) (hBT'x hg), ?_⟩
  exact (Subgroup.le_normalizer_iff_commutator_le_right.1 (hB₀.trans hBT'x)).trans inf_le_left

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
