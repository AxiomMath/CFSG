module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.ClassicalInvolution.Generic.LineModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Cover

variable {G C : Type*} [Group G] [Group C]

theorem LayerAt.of_central_cover (θ : G →* C) (hker : θ.ker ≤ Subgroup.center G)
    {Fund : Set (Subgroup G)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : G, R' = conjSub g R) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ Fund) (hR₀perf : R₀ ≤ ⁅R₀, R₀⁆) {L : Subgroup C} (hLθ : L ≤ θ.range)
    (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hLC : L ≤ Subgroup.centralizer ((R₀.map θ : Subgroup C) : Set C))
    (hLP : ∀ P : Subgroup C, P ≤ θ.range →
      P ≤ Subgroup.centralizer ((R₀.map θ : Subgroup C) : Set C) → P ≤ ⁅P, P⁆ → P ≤ L)
    (hcard : Nat.card ↥L ≠ Nat.card ↥(R₀.map θ)) : LayerAt Fund R₀ := by
  classical
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := ⟨hLq.1⟩
    exact Subgroup.isPerfect_iff.mp this
  set M := L.comap θ with hM
  set N := ⁅M, M⁆ with hN
  have hmapM : M.map θ = L := by
    rw [hM, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hLθ
  have hmapN : N.map θ = L := by
    rw [hN, Subgroup.map_commutator, hmapM, hLperf]
  have hNM : N ≤ M := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hNq : CFSG.Open.IsQuasisimple ↥N := by
    have hL' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf θ.range) :=
      (open_isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hLθ)).2 hLq
    have hker' : θ.rangeRestrict.ker ≤ Subgroup.center G := by
      rwa [MonoidHom.ker_rangeRestrict]
    have hcomap : (L.subgroupOf θ.range).comap θ.rangeRestrict = M := by
      ext x
      rfl
    have := isQuasisimple_commutator_comap θ.rangeRestrict θ.rangeRestrict_surjective hker' hL'
    rwa [hcomap] at this
  have hMC : M ≤ Subgroup.centralizer (R₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcomm : ∀ r ∈ R₀, ⁅x, r⁆ ∈ Subgroup.center G := by
      intro r hr
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have h1 : θ r ∈ R₀.map θ := Subgroup.mem_map_of_mem θ hr
      have h2 := Subgroup.mem_centralizer_iff.mp (hLC hx) (θ r) h1
      rw [commutatorElement_def]
      calc θ x * θ r * (θ x)⁻¹ * (θ r)⁻¹ = (θ r * θ x) * (θ x)⁻¹ * (θ r)⁻¹ := by rw [h2]
        _ = 1 := by group
    exact (commutes_of_commutator_mem_center hR₀perf hcomm r hr).symm
  refine ⟨N, hNq, hNM.trans hMC, ?_, ?_⟩
  · intro P hPC hPperf
    have h1 : P.map θ ≤ Subgroup.centralizer ((R₀.map θ : Subgroup C) : Set C) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hPC hx) r hr]
    have h2 : P.map θ ≤ ⁅P.map θ, P.map θ⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hPperf
    have h3 : P ≤ M := fun x hx =>
      hLP _ (Subgroup.map_le_range θ P) h1 h2 (Subgroup.mem_map_of_mem θ hx)
    exact hPperf.trans (Subgroup.commutator_mono h3 h3)
  · intro hmem
    obtain ⟨g, hg⟩ := hsingle R₀ hR₀ N hmem
    apply hcard
    rw [← hmapN, hg, ← conjSub_map θ g R₀]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj (θ g)).toMonoidHom
      (MulAut.conj (θ g)).injective).toEquiv).symm

end Cover

end CFSG.ClassicalInvolution.RouteD.Exotic
