module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.InnerModel

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

section Certified

theorem twoSuz_not_standard_of_layer0
    (hOuter : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
      centralizer (L : Set G) = zpowers z → ∀ y : G, y ∈ centralizer ({z} : Set G) →
        orderOf y = 2 → y ∉ L → ∃ P : Subgroup G,
          P ≤ centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ∧ P ≤ ⁅P, P⁆ ∧ z ∈ P)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Suz)
    (hlayer0 : ∃ z : G, orderOf z = 2 ∧ (center L).map L.subtype = zpowers z ∧
      centralizer (L : Set G) = zpowers z ∧ L ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ∧
      L.relIndex (centralizer ({z} : Set G)) ∣ 2) : False := by
  obtain ⟨z, hz2, hZz, hCz, hLz, hN, hidx⟩ := hlayer0
  have hset : Setup G L z := ⟨hz2, hZz, h2, h.standard.1.1, hQ, hLz, hN, hidx⟩
  have := h.simple
  have hO : TwoSuzNoSwapOuter' := by
    refine twoSuzNoSwapOuter'_of_perfect ?_
    intro G' _ _ L' z' hs' hC' y hyD hy2 hyz
    by_cases hyL : y ∈ L'
    · have hy1 : y ≠ 1 := fun h1 => by simp [h1] at hy2
      have hyy : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hy2, sq] at this
      obtain ⟨P, hPL, hPy, hP, hzP⟩ := exists_perfect_of_innerData (card_of_setup hs') hs'
        (innerData_of_setup hs') hyL hyy hy1 hyz
      exact ⟨P, le_inf (fun p hp => mem_centralizer_singleton_iff.2
        (hs'.mul_comm_of_mem (hPL hp))) hPy, hP, hzP⟩
    · exact hOuter G' L' z' hs' hC' y hyD hy2 hyL
  obtain ⟨g, hne, hcomm, hx2, hz'2, hne', hcomm'⟩ := exists_swap h.nonabelian hz2
  have hxD : g * z * g⁻¹ ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 hcomm
  have hz'D : g⁻¹ * z * g ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 hcomm'
  have hxx : g * z * g⁻¹ ∈ centralizer ({z} : Set G) ⊓ centralizer ({g * z * g⁻¹} : Set G) :=
    mem_comm_pair.2 ⟨hcomm, rfl⟩
  have hzx : z ∈ centralizer ({z} : Set G) ⊓ centralizer ({g * z * g⁻¹} : Set G) :=
    mem_comm_pair.2 ⟨rfl, hcomm.symm⟩
  have hns : NoSwap z (g * z * g⁻¹) (g⁻¹ * z * g) := by
    by_cases hin : g * z * g⁻¹ ∈ L ∧ g⁻¹ * z * g ∈ L
    · exact twoSuzNoSwapInner G L z hset _ _ hin.1 hin.2 hxD hz'D hx2 hz'2 hne hne'
    · exact hO G L z hset hCz _ _ hin hxD hz'D hx2 hz'2 hne hne'
  refine hns (swapEquiv z g) hxx hzx ?_ rfl
  show g⁻¹ * (g * z * g⁻¹) * g = z
  group

end Certified

end CFSG.EvenSporadicStandard.TwoSuz
