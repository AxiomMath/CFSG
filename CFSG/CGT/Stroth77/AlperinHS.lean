module

public import CFSG.LocalAnalysis.OddStandard.ONan76Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LHS

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76 CFSG.OddStandard.HigherRank.G2Three.Sec2

variable {G : Type} [Group G]

theorem y2l_psi_injective_of_alperinFrame_two [Finite G] {v₁ v₂ v₃ s t : G}
    (hF : AlperinFrame 2 v₁ v₂ v₃ s t) : Function.Injective (y2l_psi 4 v₁ v₂ v₃) := by
  have h1 : v₁ ^ 4 = 1 := by simpa using hF.pow₁
  have h2 : v₂ ^ 4 = 1 := by simpa using hF.pow₂
  have h3 : v₃ ^ 4 = 1 := by simpa using hF.pow₃
  have hadd := y2l_psi_add h1 h2 h3 hF.comm₁₂ hF.comm₁₃ hF.comm₂₃
  set V := Subgroup.closure ({v₁, v₂, v₃} : Set G)
  have hmem : ∀ x, y2l_psi 4 v₁ v₂ v₃ x ∈ V := fun x =>
    V.mul_mem (V.mul_mem (V.pow_mem (Subgroup.subset_closure (by simp)) _)
      (V.pow_mem (Subgroup.subset_closure (by simp)) _))
      (V.pow_mem (Subgroup.subset_closure (by simp)) _)
  let Rng : Subgroup G :=
    { carrier := Set.range (y2l_psi 4 v₁ v₂ v₃)
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, hadd x y⟩
      one_mem' := ⟨0, y2l_psi_zero 4 v₁ v₂ v₃⟩
      inv_mem' := by
        rintro _ ⟨x, rfl⟩
        refine ⟨-x, ?_⟩
        refine (inv_eq_of_mul_eq_one_right ?_).symm
        rw [← hadd, add_neg_cancel, y2l_psi_zero] }
  have hval : (1 : ZMod 4).val = 1 := rfl
  have hV : V ≤ Rng := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨![1, 0, 0], by simp [y2l_psi, hval]⟩
    · exact ⟨![0, 1, 0], by simp [y2l_psi, hval]⟩
    · exact ⟨![0, 0, 1], by simp [y2l_psi, hval]⟩
  let f : (Fin 3 → ZMod 4) → V := fun x => ⟨y2l_psi 4 v₁ v₂ v₃ x, hmem x⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hV hy
    exact ⟨x, Subtype.ext hx⟩
  have hcard : Nat.card (Fin 3 → ZMod 4) ≤ Nat.card V := by
    rw [hF.card_V, Nat.card_pi]
    simp
  have hinj := (hsurj.bijective_of_nat_card_le hcard).1
  intro x y hxy
  exact hinj (Subtype.ext hxy)

theorem isHSType_of_alperinFrame_two
    [Finite G]
    {v₁ v₂ v₃ s r : G} (hF : AlperinFrame 2 v₁ v₂ v₃ s r) (hs : s ^ 4 = 1) :
    IsHSType ↥(Subgroup.closure ({v₁, v₂, v₃, s, r} : Set G)) := by
  have hrel : ∀ x ∈ rels26 2 false, FreeGroup.lift (![v₁, v₂, v₃, r, s] : Fin 5 → G) x = 1 :=
    y2l_rels_iff.mpr
      { cuv := hF.comm₁₂
        cuw := hF.comm₁₃
        cvw := hF.comm₂₃
        pu := hF.pow₁
        pv := hF.pow₂
        pw := hF.pow₃
        r2 := by rw [sq]; exact hF.t_sq
        crs := hF.t_s
        cru := hF.t_v₁
        crv := hF.t_v₂
        crw := hF.t_v₃
        csu := hF.s_v₁
        csv := hF.s_v₂
        csw := hF.s_v₃
        s4 := by simpa using hs }
  have hψ := y2l_psi_injective_of_alperinFrame_two hF
  have h7 : ∀ x ∈ y2l_ws7 2,
      FreeGroup.lift (![v₁, v₂, v₃, r, s] : Fin 5 → G) (FreeGroup.mk x) ≠ 1 := by
    have key : ∀ d : Fin 3 → ZMod 4, d ≠ 0 → y2l_psi 4 v₁ v₂ v₃ d ≠ 1 := fun d hd h => by
      rw [← y2l_psi_zero 4 v₁ v₂ v₃] at h
      exact hd (hψ h)
    have hval : (2 : ZMod 4).val = 2 := rfl
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    rw [y2l_lift_ws7_word]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [y2l_psi, hval] using key ![2, 0, 0] (by decide)
    · simpa [y2l_psi, hval] using key ![0, 2, 0] (by decide)
    · simpa [y2l_psi, hval] using key ![0, 0, 2] (by decide)
    · simpa [y2l_psi, hval] using key ![2, 2, 0] (by decide)
    · simpa [y2l_psi, hval] using key ![2, 0, 2] (by decide)
    · simpa [y2l_psi, hval] using key ![0, 2, 2] (by decide)
    · simpa [y2l_psi, hval] using key ![2, 2, 2] (by decide)
  obtain ⟨hP, -⟩ := y2l_isPres26_two hrel h7
  have hHS := lemma26HS_holds _ _ _ _ _ _ hP
  have hset : ({v₁, v₂, v₃, r, s} : Set G) = {v₁, v₂, v₃, s, r} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at hHS
  exact hHS

end CFSG.CGT.Stroth77
