module

public import CFSG.GH74.GLS.C3.Layer1.Th2V2ss
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.C3.Layer1.St1Bal

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Core

variable {G : Type} [Group G]

@[expose] def IsEStarUnbal (t u : G) (J : Subgroup G) : Prop :=
  IsUnbalancingTriple t u J ∧ ∃ B : Subgroup G, IsE 4 ⊤ B ∧ t ∈ B ∧ u ∈ B

@[expose] def IsEStarUnbalMax (t u : G) (J : Subgroup G) : Prop :=
  IsEStarUnbal t u J ∧ ∀ (t' u' : G) (J' : Subgroup G), IsEStarUnbal t' u' J' →
    twoPartCard (centralizer ({t'} : Set G)) ≤ twoPartCard (centralizer ({t} : Set G))

theorem exists_isEStarUnbal_of_not_balanced [Finite G] {B : Subgroup G} (hB : IsE 4 ⊤ B)
    (hnb : ¬ IsBalancedWrt B) : ∃ (t u : G) (J : Subgroup G), IsEStarUnbal t u J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : ¬ ∀ a ∈ B, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      pPrimeCoreOf 2 (centralizer ({b} : Set G)) ⊓ centralizer ({a} : Set G) ≤
        pPrimeCoreOf 2 (centralizer ({a} : Set G)) := fun h => hnb (isBalancedWrt_of_forall h)
  simp only [not_forall] at h
  obtain ⟨a, ha, ha1, b, hb, hb1, hnle⟩ := h
  obtain ⟨hab, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB.2.1
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hsq a ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hsq b hb) hb1
  obtain ⟨J, hJ⟩ := exists_isUnbalancingTriple_of_not_le ha2 hb2 (hab a ha b hb) hnle
  exact ⟨a, b, J, hJ, B, hB, ha, hb⟩

theorem exists_isEStarUnbalMax [Finite G] (h : ∃ (t u : G) (J : Subgroup G), IsEStarUnbal t u J) :
    ∃ (t u : G) (J : Subgroup G), IsEStarUnbalMax t u J := by
  classical
  obtain ⟨t₀, u₀, J₀, h₀⟩ := h
  let s : Set (G × G × Subgroup G) := {p | IsEStarUnbal p.1 p.2.1 p.2.2}
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image s
    (fun p => twoPartCard (centralizer ({p.1} : Set G))) (Set.toFinite s) ⟨(t₀, u₀, J₀), h₀⟩
  exact ⟨p.1, p.2.1, p.2.2, hp, fun t' u' J' h' => hmax (t', u', J') h'⟩

theorem IsEStarUnbal.pRank_centralizer [Finite G] (hG : pRank 2 G = 4) {t u : G} {J : Subgroup G}
    (h : IsEStarUnbal t u J) : pRank 2 ↥(centralizer ({t, u} : Set G)) = 4 := by
  obtain ⟨-, B, hB, htB, huB⟩ := h
  obtain ⟨hab, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB.2.1
  refine le_antisymm (hG ▸ pRank_le_top' _) ?_
  have hle : B ≤ centralizer ({t, u} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact hab _ htB b hb
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hab _ huB b hb
  exact hB.2.2.trans (C3.Layer1.Back.pRank_mono' hle)

end Core

@[expose] def B_lemma626 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (t u : G) (J : Subgroup G), IsEStarUnbalMax t u J → IsTwoTerminal t J

@[expose] def B_lemma627 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (t u : G) (J : Subgroup G), IsEStarUnbalMax t u J → IsTwoTerminal t J →
        IsV2StarTriple t u J

theorem b_thm2_v2star_ss_of (h626 : B_lemma626) (h627 : B_lemma627) : B_thm2_v2star_ss := by
  intro G _ _ hG ⟨x, y, K, hV⟩
  by_cases hcond : HasL2Model (kBar K) (fun q => q = 5) ∧ pRank 2 ↥(CxK x K) = 2 ∧
      ∃ B : Subgroup G, IsE 4 ⊤ B ∧ ¬ IsBalancedWrt B
  · obtain ⟨h5, hr2, B₀, hB₀, hnb⟩ := hcond
    obtain ⟨t, u, J, hmax⟩ :=
      exists_isEStarUnbalMax (exists_isEStarUnbal_of_not_balanced hB₀ hnb)
    have hterm := h626 G hG x y K hV h5 hr2 t u J hmax
    have hV' := h627 G hG x y K hV h5 hr2 t u J hmax hterm
    exact ⟨t, u, J, hV', fun _ _ _ =>
      ⟨hmax.1.1, hmax.1.pRank_centralizer hG.pRank_eq_four⟩⟩
  · exact ⟨x, y, K, hV, fun h5 hr2 hB => absurd ⟨h5, hr2, hB⟩ hcond⟩

end CFSG.GH74.GLS
