module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.KInftyFacts2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.KInftyFacts

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Max

variable {G : Type} [Group G] [Finite G]

theorem maximal_centralizer_le {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p ↥P) {B : Subgroup G}
    (hB : B ∈ ⋂ i : ℕ, Kfam P (2 * i))
    (hmax : ∀ B' ∈ (⋂ i : ℕ, Kfam P (2 * i)), B ≤ B' → B' = B) : P ⊓ centralizer (B : Set G) ≤ B := by
  by_contra hC
  have hB0 : B ∈ Kfam P (2 * 0) := Set.mem_iInter.mp hB 0
  have hBP : B ≤ P := le_of_mem_Kfam hB0
  obtain ⟨x, hxC, hxB, hxN⟩ := exists_central_ext hp hP hBP hC
  have hx : ∀ b ∈ B, b * x = x * b := fun b hb => Subgroup.mem_centralizer_iff.mp hxC.2 b hb
  have hBstar : Bstar B x hx ∈ ⋂ i : ℕ, Kfam P (2 * i) := by
    rw [Set.mem_iInter]
    intro i
    cases i with
    | zero => exact Bstar_classTwo hB0 hxC.1
    | succ m =>
      have hBm : B ∈ Kfam P (2 * (m + 1)) := Set.mem_iInter.mp hB (m + 1)
      have e : Kfam P (2 * (m + 1)) = Kup P (gen (Kfam P (2 * m + 1))) := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring]
        show (if Even (2 * m + 1) then Klow P (gen (Kfam P (2 * m + 1))) else Kup P (gen (Kfam P (2 * m + 1)))) = _
        simp only [Nat.not_even_two_mul_add_one m, ↓reduceIte]
      rw [e] at hBm ⊢
      refine Bstar_mem_Kup hBm hxC.1 (fun q hq => ?_)
      have hqP : q ∈ P := gen_Kfam_le P _ hq
      have hqN : q ∈ normalizer (B : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun b hb => ?_
        have h1 : ⁅b, q⁆ ∈ zOf B := hBm.2 (Subgroup.commutator_mem_commutator hb hq)
        have h2 : ⁅b, q⁆⁻¹ ∈ B := inv_mem h1.1
        have e2 : q * b * q⁻¹ = ⁅b, q⁆⁻¹ * b := by simp only [commutatorElement_def]; group
        rw [e2]
        exact mul_mem h2 hb
      exact hxN q ⟨hqP, hqN⟩
  have h1 := hmax _ hBstar le_Bstar
  exact hxB (h1 ▸ x_mem_Bstar)

theorem zOf_le_kInfty {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p ↥P) : zOf P ≤ kInfty P := by
  have hfin : (⋂ i : ℕ, Kfam P (2 * i)).Finite := Set.toFinite _
  have hne : (⋂ i : ℕ, Kfam P (2 * i)).Nonempty :=
    ⟨⊥, Set.mem_iInter.mpr fun i => bot_mem_Kfam P _⟩
  obtain ⟨B, hBmax⟩ := hfin.exists_maximal hne
  have hB : B ∈ ⋂ i : ℕ, Kfam P (2 * i) := hBmax.1
  have hmax : ∀ B' ∈ (⋂ i : ℕ, Kfam P (2 * i)), B ≤ B' → B' = B :=
    fun B' h1 h2 => le_antisymm (hBmax.2 h1 h2) h2
  have h1 := maximal_centralizer_le hp hP hB hmax
  have hBP : B ≤ P := le_of_mem_Kfam (Set.mem_iInter.mp hB 0)
  intro w hw
  have hwB : w ∈ B := h1 ⟨hw.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBP) hw.2⟩
  unfold kInfty gen
  exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨B, hB, hwB⟩)

theorem kInfty_facts_thm : KInfty_facts :=
  fun _ _ _ _ hp P hP => ⟨kInfty_le P, zOf_le_kInfty hp hP⟩

end Max

end CFSG.GH74.GLS.Stage2.Bender.Thm2
