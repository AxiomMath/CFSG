module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.Open

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem eq_bot_of_normal_subgroup (hO2 : ∀ P : Subgroup K, P.Normal → IsPGroup 2 P → P = ⊥)
    {N : Subgroup K} [hN : N.Normal] (P : Subgroup N) (hP : P.Normal) (hP2 : IsPGroup 2 P) :
    P = ⊥ := by
  have hle : P ≤ CFSG.pCore 2 N := le_sSup ⟨hP, hP2⟩
  have hC : (CFSG.pCore 2 N).map N.subtype = ⊥ := by
    refine hO2 _ ⟨fun c hc x => ?_⟩ (CFSG.pCore_isPGroup.map _)
    obtain ⟨p, hp, rfl⟩ := hc
    have hφ : MulAut.conjNormal x p ∈ CFSG.pCore 2 N := by
      have hfix := (CFSG.pCore_characteristic (p := 2) (G := N)).fixed
        (MulAut.conjNormal x).symm
      rw [← hfix, mem_comap]
      simpa using hp
    exact ⟨_, hφ, by simp [MulAut.conjNormal_apply]⟩
  have hbot : CFSG.pCore 2 N = ⊥ := by
    rw [← map_eq_bot_iff_of_injective _ N.subtype_injective]
    exact hC
  exact le_bot_iff.mp (hbot ▸ hle)

omit [Finite K] in
theorem commutatorElement_mul_central {a b z : K} (hz : z ∈ center K) :
    a * z * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hz' := mem_center_iff.mp hz b
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite K] in
theorem commutatorElement_mul_central_right {a b z : K} (hz : z ∈ center K) :
    a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hz' := mem_center_iff.mp hz a⁻¹
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite K] in
theorem le_center_of_normal_of_ne_top (hK : commutator K = ⊤)
    (hs : IsSimpleGroup (K ⧸ center K)) {N : Subgroup K} [hN : N.Normal] (hne : N ≠ ⊤) :
    N ≤ center K := by
  have hmapN : (N.map (QuotientGroup.mk' (center K))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hmapN with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (center K) x ∈ N.map (QuotientGroup.mk' (center K)) :=
      ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact (QuotientGroup.eq_one_iff x).mp ((mem_bot).mp hx')
  · exfalso
    apply hne
    have hsup : N ⊔ center K = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (center K))) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    have hdec : ∀ a : K, ∃ n ∈ N, ∃ z ∈ center K, n * z = a := fun a => by
      have ha : a ∈ ((N ⊔ center K : Subgroup K) : Set K) := by rw [hsup]; trivial
      rw [Subgroup.mul_normal] at ha
      exact Set.mem_mul.mp ha
    refine eq_top_iff.mpr (hK ▸ ?_)
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
    rw [commutatorElement_def, commutatorElement_mul_central hz₁,
      commutatorElement_mul_central_right hz₂]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

end CFSG.LargeExtraspecial.S9
