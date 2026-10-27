module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (commutatorElement_mul_mul')
open scoped commutatorElement

theorem exists_central_preimage {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) (hperf : commutator X = ⊤)
    {y : Y} (hy : y ∈ Subgroup.center Y) : ∃ x ∈ Subgroup.center X, f x = y := by
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨x, ?_, rfl⟩
  have hc : ∀ g : X, ⁅x, g⁆ ∈ Subgroup.center X := by
    intro g
    apply hker
    rw [MonoidHom.mem_ker, commutatorElement_def]
    have h1 := Subgroup.mem_center_iff.1 hy (f g)
    simp only [map_mul, map_inv]
    rw [← h1]
    group
  have hcc : ∀ {z : X}, z ∈ Subgroup.center X → ∀ g : X, Commute z g :=
    fun hz g => (Subgroup.mem_center_iff.1 hz g).symm
  have hconj : ∀ u v : X, x * ⁅u, v⁆ * x⁻¹ = ⁅u, v⁆ := by
    intro u v
    have hu : x * u * x⁻¹ = u * ⁅x, u⁆ := by
      rw [← (hcc (hc u) u).eq, commutatorElement_def]
      group
    have hv : x * v * x⁻¹ = v * ⁅x, v⁆ := by
      rw [← (hcc (hc v) v).eq, commutatorElement_def]
      group
    have h2 : x * ⁅u, v⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * v * x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h2, hu, hv]
    exact commutatorElement_mul_mul' (hcc (hc u) v) (hcc (hc u) _) (hcc (hc v) u)
  have hle : commutator X ≤ Subgroup.centralizer {x} := by
    refine Subgroup.commutator_le.2 fun u _ v _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hconj u v
    calc ⁅u, v⁆ * x = x * ⁅u, v⁆ * x⁻¹ * x := by rw [this]
      _ = x * ⁅u, v⁆ := by group
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have hg : g ∈ Subgroup.centralizer {x} := hle (hperf ▸ Subgroup.mem_top g)
  exact Subgroup.mem_centralizer_singleton_iff.1 hg

theorem card_center_pQuot_dvd {p : ℕ} (hp : p.Prime) {A B : Type} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f)
    (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hB : Nontrivial (B ⧸ GLAPPrimeCore p B)) :
    Nat.card (Subgroup.center (B ⧸ GLAPPrimeCore p B)) ∣
      Nat.card (Subgroup.center (A ⧸ GLAPPrimeCore p A)) := by
  have hg : Function.Surjective (pQuotMapOfSurjective hp f hf) :=
    pQuotMapOfSurjective_surjective hp f hf
  have hker := ker_pQuotMapOfSurjective_le_center hp f hf hA hB
  have hle : Subgroup.center (B ⧸ GLAPPrimeCore p B) ≤
      (Subgroup.center (A ⧸ GLAPPrimeCore p A)).map (pQuotMapOfSurjective hp f hf) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_central_preimage _ hg hker hA.1 hy
    exact Subgroup.mem_map_of_mem _ hx
  rw [le_antisymm hle (Subgroup.map_center_le_center hg)]
  exact Subgroup.card_map_dvd _ _

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
