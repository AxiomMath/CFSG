module

public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {Ω : Type} [Group Ω]

private theorem charPair_omegaOneCenterOf_le (X : Subgroup Ω) : omegaOneCenterOf X ≤ X :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

private theorem charPair_le_normalizer_of_le_centralizer {Ω' : Type} [Group Ω'] {K X : Subgroup Ω'}
    (h : K ≤ Subgroup.centralizer (X : Set Ω')) : K ≤ Subgroup.normalizer (X : Set Ω') := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hc : x * g = g * x := Subgroup.mem_centralizer_iff.mp (h hg) x hx
    rw [← hc, mul_inv_cancel_right]
    exact hx
  · have h2 : g * x * g⁻¹ * g⁻¹ = g⁻¹ * (g * x * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (h (K.inv_mem hg)) _ hx
    have h3 : g * x * g⁻¹ = x := by
      have h2' : g * x * g⁻¹ * g⁻¹ = x * g⁻¹ := by
        rw [h2]
        group
      exact mul_right_cancel h2'
    rw [← h3]
    exact hx

private theorem charPair_map_le_omegaOneCenterOf {Ω' : Type} [Group Ω'] {T C : Subgroup Ω}
    (hC : C ≤ omegaOneCenterOf T) (ι : ↥T →* Ω') :
    (C.subgroupOf T).map ι ≤ omegaOneCenterOf ι.range := by
  have key : ∀ x, x ∈ Subgroup.closure {x | x ∈ centerOf T ∧ x ^ 2 = 1} → ∀ hxT : x ∈ T,
      ι ⟨x, hxT⟩ ∈ omegaOneCenterOf ι.range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hxT
      apply Subgroup.subset_closure
      refine ⟨⟨⟨⟨x, hxT⟩, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
      · rintro _ ⟨t, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.1.2 t t.2)
      · rw [← map_pow]
        have : (⟨x, hxT⟩ : ↥T) ^ 2 = 1 := Subtype.ext hx.2
        rw [this, map_one]
    | one =>
      intro h1
      have : (⟨1, h1⟩ : ↥T) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxyT
      have := Subgroup.mul_mem _ (ihx (charPair_omegaOneCenterOf_le T hx) )
        (ihy (charPair_omegaOneCenterOf_le T hy))
      rw [← map_mul] at this
      exact this
    | inv x hx ihx =>
      intro hxT
      have := Subgroup.inv_mem _ (ihx (charPair_omegaOneCenterOf_le T hx))
      rw [← map_inv] at this
      exact this
  rintro _ ⟨⟨c, hcT⟩, hc, rfl⟩
  exact key c (hC (Subgroup.mem_subgroupOf.mp hc)) hcT

theorem exists_isGomiCharPairGN [Finite Ω] (T : Subgroup Ω) (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    (hK : baum T = T) : ∃ T₁ T₂ : Subgroup Ω, IsGomiCharPairGN T T₁ T₂ := by
  obtain ⟨C₁, C₂, hC1, hC1Z, hC1c, hC2, hC2B, hC2c, hall⟩ := theoremC118 Ω T hT hT0
  rw [hK] at hC2B hC2c hall
  refine ⟨C₁, C₂, ⟨hC1Z.trans (charPair_omegaOneCenterOf_le T), hC1c, hC2B, hC2c, ?_⟩,
    hC1, hC2, hC1Z⟩
  intro Ω' _ _ G ι hι hQ
  by_cases hcent : G ≤ Subgroup.centralizer (((C₁.subgroupOf T).map ι : Subgroup Ω') : Set Ω')
  · exact Or.inl (charPair_le_normalizer_of_le_centralizer hcent)
  · have hZ : ¬ G ≤ Subgroup.centralizer (omegaOneCenterOf ι.range : Set Ω') := fun h' =>
      hcent (h'.trans (Subgroup.centralizer_le (charPair_map_le_omegaOneCenterOf hC1Z ι)))
    rcases hall Ω' G ι hι (hQ.inClassG hZ) with h1 | h2 | h3
    · refine Or.inl (charPair_le_normalizer_of_le_centralizer fun g hg => ?_)
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      exact ((Subgroup.mem_centralizer_iff.mp (h1 hx).2) g hg).symm
    · exact Or.inr h2
    · exact absurd h3 hQ.not_isL2OrA3Block

end CFSG.GroupTheory

end
