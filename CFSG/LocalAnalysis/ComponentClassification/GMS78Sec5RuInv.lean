module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuMask
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSylow

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

theorem mem_plane_cases_check : (allPlanes.all fun P => P.all fun s => P.all fun t =>
    s == t || P.all fun u => u == s || u == t || u == (s ^^^ t)) = true := by
  decide +kernel

theorem mem_plane_cases {P : List Nat} (hP : P ∈ allPlanes) {s t u : Nat} (hs : s ∈ P)
    (ht : t ∈ P) (hst : s ≠ t) (hu : u ∈ P) : u = s ∨ u = t ∨ u = s ^^^ t := by
  have h := mem_plane_cases_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h P hP s hs t ht with h | h
  · exact absurd h hst
  · rcases h u hu with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end RuQCode

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

namespace MaskCoords

variable {μ : G → ℕ} {ν : G → Fin 8} (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem card_gmsA : Nat.card (gmsA L T) = 8 := by
  have hc : Nat.card (gmsA L T) = Nat.card (Fin 8) := Nat.card_congr
    (Equiv.ofBijective (fun b : gmsA L T => ν b) ⟨fun b b' h =>
      Subtype.ext (hM.eq_of_ν_eq b.2 b'.2 h), fun t => by
        obtain ⟨b, hb, hbt⟩ := hM.ν_surj t
        exact ⟨⟨b, hb⟩, hbt⟩⟩)
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_le_of_isElemAbelian {P : Subgroup G} (hPR : P ≤ R) (hP : IsElemAbelian 2 P) :
    Nat.card P ≤ 32 := by
  classical
  have hcomm : ∀ x ∈ P, ∀ x' ∈ P, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hsing : ∀ x ∈ P, μ x ≠ 0 → μ x ∈ singMasks := fun x hx hx0 =>
    (RuQCode.mem_singMasks_iff (hM.lt x (hPR hx))).mpr
      ⟨hx0, (hM.sq_eq_one_iff (hPR hx)).mp (hP.2 x hx)⟩
  have hperp : ∀ x ∈ P, ∀ x' ∈ P, bC (μ x) (μ x') = 0 := fun x hx x' hx' =>
    (hM.commute_iff (hPR hx) (hPR hx')).mp (hcomm x hx x' hx')
  have hinj : ∀ a ∈ P, ∀ b ∈ P, μ a = μ b → a⁻¹ * b ∈ P ⊓ gmsA L T := by
    intro a ha b hb h
    refine mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
    rw [← hM.ker _ (mul_mem (inv_mem (hPR ha)) (hPR hb)),
      hM.mul _ (inv_mem (hPR ha)) _ (hPR hb), hM.μ_inv (hPR ha), h]
    exact Nat.xor_self _
  have hA : Nat.card (P ⊓ gmsA L T : Subgroup G) ≤ 8 := by
    rw [← hM.card_gmsA]
    exact Subgroup.card_le_of_le inf_le_right
  by_cases hex : ∃ a ∈ P, ∃ b ∈ P, μ a ≠ 0 ∧ μ b ≠ 0 ∧ μ a ≠ μ b
  · obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := hex
    obtain ⟨Q, hQ, haQ, hbQ⟩ :=
      RuQCode.exists_plane (hsing a ha ha0) (hsing b hb hb0) hab (hperp a ha b hb)
    have hmem : ∀ x ∈ P, μ x ∈ 0 :: Q := by
      intro x hx
      by_cases hx0 : μ x = 0
      · rw [hx0]
        exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (RuQCode.mem_of_forall_bC_eq_zero hQ (hsing x hx hx0) ?_)
        intro t ht
        rcases RuQCode.mem_plane_cases hQ haQ hbQ hab ht with rfl | rfl | rfl
        · exact hperp a ha x hx
        · exact hperp b hb x hx
        · rw [← hM.mul _ (hPR ha) _ (hPR hb)]
          exact hperp _ (mul_mem ha hb) x hx
    have h1 := card_le_length_mul_card (inf_le_left : P ⊓ gmsA L T ≤ P) μ (0 :: Q) hmem hinj
    have hlen : (0 :: Q).length = 4 := by
      rw [List.length_cons, RuQCode.length_eq_of_mem_allPlanes Q hQ]
    rw [hlen] at h1
    omega
  · push Not at hex
    by_cases h1 : ∃ a ∈ P, μ a ≠ 0
    · obtain ⟨a, ha, ha0⟩ := h1
      have hmem : ∀ x ∈ P, μ x ∈ [0, μ a] := by
        intro x hx
        by_cases hx0 : μ x = 0
        · simp [hx0]
        · simp [hex x hx a ha hx0 ha0]
      have h2 := card_le_length_mul_card (inf_le_left : P ⊓ gmsA L T ≤ P) μ [0, μ a] hmem hinj
      simp only [List.length_cons, List.length_nil] at h2
      omega
    · push Not at h1
      have hmem : ∀ x ∈ P, μ x ∈ [0] := fun x hx => by simp [h1 x hx]
      have h2 := card_le_length_mul_card (inf_le_left : P ⊓ gmsA L T ≤ P) μ [0] hmem hinj
      simp only [List.length_cons, List.length_nil] at h2
      omega

end MaskCoords

theorem card_le_of_isElemAbelian
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    ∀ P : Subgroup G, P ≤ R → IsElemAbelian 2 P → Nat.card P ≤ 32 := by
  obtain ⟨μ, ν, hM⟩ := hS.exists_maskCoords h34 hR₂ h4 hNS
  exact fun P hPR hP => hM.card_le_of_isElemAbelian hPR hP

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
