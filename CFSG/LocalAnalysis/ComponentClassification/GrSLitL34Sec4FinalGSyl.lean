module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGL1

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup

theorem card_eq_card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (K : Subgroup X) : Nat.card K = Nat.card (K.map f) * Nat.card (K ⊓ f.ker : Subgroup X) := by
  let ψ : K →* Y := f.comp K.subtype
  have hrange : ψ.range = K.map f := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (K ⊓ f.ker : Subgroup X) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : K) : X), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

theorem card_sylow_GL (Q : Sylow 2 (GL (Fin 3) (ZMod 2))) : Nat.card Q = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity,
    LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.card_GL_three_two,
    show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]

namespace Data

variable {G : Type} [Group G] [Finite G] (D : Data G)

abbrev P₁ : Subgroup G := D.S ⊓ D.L₁

theorem P₁_le_S : D.P₁ ≤ D.S := inf_le_left

theorem P₁_le_L₁ : D.P₁ ≤ D.L₁ := inf_le_right

theorem sylow_P₁ : IsSylowTwoIn D.P₁ D.L₁ :=
  GrS4.isSylowTwoIn_inf_of_normal (J := D.T) D.sylow_L (oddGen_le D.L) (le_normalizer_oddGen D.L)

noncomputable def φ₁ : ↥D.L₁ →* GL (Fin 3) (ZMod 2) := D.φ.comp (inclusion (oddGen_le D.L))

theorem φ₁_surjective : Function.Surjective D.φ₁ := by
  intro M
  have hM : M ∈ (D.L₁.subgroupOf D.L).map D.φ := by
    rw [D.map_L₁_eq_top]
    exact mem_top M
  obtain ⟨x, hx, rfl⟩ := hM
  exact ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩

theorem relIndex_T₁ : D.T₁.relIndex D.T = 2 := by
  refine relIndex_eq_two_iff.mpr ⟨D.c, D.c_mem_T, fun b hb => ?_⟩
  by_cases hbT : b ∈ D.T₁
  · refine Or.inr ⟨hbT, fun h => D.c_not_mem_T₁ ?_⟩
    have := mul_mem (inv_mem hbT) h
    rwa [inv_mul_cancel_left] at this
  · exact Or.inl ⟨(D.mem_T hb).resolve_left hbT, hbT⟩

theorem card_T : Nat.card D.T = 128 := by
  have h := relIndex_mul_card D.T₁ D.T
  rw [D.relIndex_T₁, inf_eq_left.mpr D.T₁_le_T, D.card_T₁] at h
  omega

theorem mem_L₁_or {s : G} (hs : s ∈ D.S) : s ∈ D.L₁ ∨ s * D.c ∈ D.L₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Q, hQ⟩ := D.sylow_P₁
  set Q' := Q.mapSurjective D.φ₁_surjective with hQ'
  have hS2 : IsPGroup 2 (D.S.subgroupOf D.L) :=
    D.isPGroup_S.of_equiv (subgroupOfEquivOfLe D.S_le_L).symm
  have hle : (Q' : Subgroup (GL (Fin 3) (ZMod 2))) ≤ (D.S.subgroupOf D.L).map D.φ := by
    rw [hQ', Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    have hyP : (y : G) ∈ D.P₁ := by
      have h1 : y ∈ (Q : Subgroup ↥D.L₁) := hy
      rw [hQ] at h1
      exact mem_subgroupOf.mp h1
    exact ⟨inclusion (oddGen_le D.L) y, mem_subgroupOf.mpr hyP.1, rfl⟩
  have heq := Q'.is_maximal' (hS2.map D.φ) hle
  have hmem : D.φ ⟨s, D.S_le_L hs⟩ ∈ (Q' : Subgroup (GL (Fin 3) (ZMod 2))) := by
    rw [← heq]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr hs)
  rw [hQ', Sylow.coe_mapSurjective] at hmem
  obtain ⟨y, hy, hyφ⟩ := hmem
  have hyP : (y : G) ∈ D.P₁ := by
    have h1 : y ∈ (Q : Subgroup ↥D.L₁) := hy
    rw [hQ] at h1
    exact mem_subgroupOf.mp h1
  have hker : (inclusion (oddGen_le D.L) y)⁻¹ * ⟨s, D.S_le_L hs⟩ ∈ D.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (D.φ₁ y)⁻¹ * _ = 1
    rw [hyφ, inv_mul_cancel]
  rw [D.φ_ker, mem_subgroupOf] at hker
  have hT : (y : G)⁻¹ * s ∈ D.T := mem_inf.mpr ⟨mul_mem (inv_mem hyP.1) hs, hker⟩
  rcases D.mem_T hT with h | h
  · left
    have := mul_mem hyP.2 (D.T₁_le_L₁ h)
    rwa [mul_inv_cancel_left] at this
  · right
    have := mul_mem hyP.2 (D.T₁_le_L₁ h)
    rwa [show (y : G) * ((y : G)⁻¹ * s * D.c) = s * D.c by group] at this

theorem relIndex_P₁ : D.P₁.relIndex D.S = 2 := by
  refine relIndex_eq_two_iff.mpr ⟨D.c, D.c_mem, fun b hb => ?_⟩
  by_cases hbL : b ∈ D.L₁
  · refine Or.inr ⟨mem_inf.mpr ⟨hb, hbL⟩, fun h => D.c_not_mem_L₁ ?_⟩
    have := mul_mem (inv_mem hbL) (mem_inf.mp h).2
    rwa [inv_mul_cancel_left] at this
  · exact Or.inl ⟨mem_inf.mpr ⟨mul_mem hb D.c_mem, (D.mem_L₁_or hb).resolve_left hbL⟩,
      fun h => hbL (mem_inf.mp h).2⟩

theorem card_S : Nat.card D.S = 1024 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Q, hQ⟩ := D.sylow_P₁
  set Q' := Q.mapSurjective D.φ₁_surjective with hQ'
  have hS2 : IsPGroup 2 (D.S.subgroupOf D.L) :=
    D.isPGroup_S.of_equiv (subgroupOfEquivOfLe D.S_le_L).symm
  have hle : (Q' : Subgroup (GL (Fin 3) (ZMod 2))) ≤ (D.S.subgroupOf D.L).map D.φ := by
    rw [hQ', Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    have hyP : (y : G) ∈ D.P₁ := by
      have h1 : y ∈ (Q : Subgroup ↥D.L₁) := hy
      rw [hQ] at h1
      exact mem_subgroupOf.mp h1
    exact ⟨inclusion (oddGen_le D.L) y, mem_subgroupOf.mpr hyP.1, rfl⟩
  have heq := Q'.is_maximal' (hS2.map D.φ) hle
  have h1 := card_eq_card_map_mul_card_inf_ker D.φ (D.S.subgroupOf D.L)
  rw [heq, card_sylow_GL] at h1
  have h2 : (D.S.subgroupOf D.L ⊓ D.φ.ker : Subgroup ↥D.L) = D.T.subgroupOf D.L := by
    ext x
    rw [D.φ_ker, mem_inf, mem_subgroupOf, mem_subgroupOf, mem_subgroupOf]
    exact Iff.rfl
  rw [h2, Nat.card_congr (subgroupOfEquivOfLe (D.T_le_S.trans D.S_le_L)).toEquiv, D.card_T,
    Nat.card_congr (subgroupOfEquivOfLe D.S_le_L).toEquiv] at h1
  exact h1

theorem card_P₁ : Nat.card D.P₁ = 512 := by
  have h := relIndex_mul_card D.P₁ D.S
  rw [D.relIndex_P₁, inf_eq_left.mpr D.P₁_le_S, D.card_S] at h
  omega

end Data

end CFSG.ComponentClassification.GrSLit.FinalG
