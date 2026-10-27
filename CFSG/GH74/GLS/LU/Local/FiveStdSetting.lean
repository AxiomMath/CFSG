module

public import CFSG.GH74.GLS.LU.Local.FiveStdDict2
public import CFSG.GH74.GLS.LU.Local.FiveStdDict3
public import CFSG.GH74.GLS.LU.Local.FiveBundles

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

structure FiveStdSetting (G : Type) [Group G] where
  ι : E → G
  model : Model ι
  K₁ : Subgroup G
  K₂ : Subgroup G
  hK₁ : (K₁ : Set G) = S ι K1l
  hK₂ : (K₂ : Set G) = S ι K2l
  hC : ((Cz (ι zE) : Subgroup G) : Set G) = S ι Cs
  hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  hKK : ∀ x : E, validE x = true → (inKK x = true ↔ ι x ∈ (K₁ : Set G) * (K₂ : Set G))
  hblock : ∀ x ∈ Cs, x.s = false → cjL (ι x) K₁ = K₁ ∧ cjL (ι x) K₂ = K₂

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

abbrev z : G := st.ι zE

theorem V_Cs : V Cs := fun x hx => (mem_Cs_iff x).1 hx

omit [Finite G] in
theorem mem_C_iff {g : G} : g ∈ Cz st.z ↔ ∃ x, validE x = true ∧ st.ι x = g := by
  have h : g ∈ ((Cz st.z : Subgroup G) : Set G) ↔ g ∈ S st.ι Cs := by rw [st.hC]
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := mem_S.1 (h.1 hg)
    exact ⟨x, (mem_Cs_iff x).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact h.2 (mem_S.2 ⟨x, (mem_Cs_iff x).2 hx, rfl⟩)

omit [Finite G] in
theorem ι_mem_C {x : E} (hx : validE x = true) : st.ι x ∈ Cz st.z :=
  st.mem_C_iff.2 ⟨x, hx, rfl⟩

end FiveStdSetting

theorem baseCheck_spec (h : baseCheck = true) :
    Cs.length = 28800 ∧ V K1l ∧ V K2l ∧ V S0 ∧ ((Cs.map codeE).mergeSort (· ≤ ·)).Pairwise (· < ·) ∧
    S0.Nodup ∧ S0.length = 128 ∧ oneE ∈ S0 ∧ zE ∈ S0 ∧ (∀ y ∈ S0, commE zE y = true) ∧
    (∀ x ∈ S0, ∀ y ∈ S0, mulE x y ∈ S0) ∧ (∀ x ∈ S0, invE x ∈ S0) ∧
    (S0.filter fun x => S0.all fun y => commE x y).length = 2 ∧
    (S0.filter inKK).length = 32 ∧ (∀ c ∈ Cs, ∃ s ∈ S0, inKK (mulE c (invE s)) = true) := by
  unfold baseCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, nodupL_iff, List.any_eq_true,
    List.contains_iff_mem, inL] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem fiveStdCheck_spec (h : fiveStdCheck = true) :
    baseCheck = true ∧ sylCover = true ∧ diagCheck = true ∧ coverCheck = true ∧
      ∀ r ∈ reps, checkRep r.1 r.2 = true := by
  unfold fiveStdCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem coverCheck_spec (h : coverCheck = true) :
    Pairs.length = 96 ∧ (∀ r ∈ reps, pairCond r.1 r.2 = true) ∧
      ∀ p ∈ Pairs, ∃ r ∈ reps, ∃ g ∈ Gam, conjPair g r = p := by
  unfold coverCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    List.mem_map] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun p hp => ?_⟩
  obtain ⟨o, ⟨r, hr, rfl⟩, hpo⟩ := h3 p hp
  obtain ⟨g, hg, hgp⟩ := List.mem_map.1 hpo
  exact ⟨r, hr, g, hg, hgp⟩

theorem checkRep_spec {t u : E} (h : checkRep t u = true) :
    ∃ a b : E, (a, b) ∈ tpOf u ∧ checkP t u a b = true ∧ checkW t u a b = true ∧ checkN u a b = true := by
  unfold checkRep at h
  rcases hh : (tpOf u).head? with _ | ⟨a, b⟩
  · rw [hh] at h
    simp at h
  · rw [hh] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨a, b, List.mem_of_mem_head? hh, h.1.1, h.1.2, h.2⟩

end CFSG.GH74.GLS.LU.Local.Five
