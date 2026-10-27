module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NTr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

structure SgFacts (S F : Subgroup G) (g : G) : Prop where
  rank : RankFacts S
  F_elem : IsElemAbelian 2 F
  F_card : Nat.card F = 8
  g_sq : g ^ 2 = 1
  g_notin : g ∉ S
  g_norm : ∀ x ∈ S, g * x * g⁻¹ ∈ S
  cent_eq : centEl S g = F
  invol : ∀ y ∈ S, (y * g) ^ 2 = 1 → y ∈ centEl S g

private lemma isElemAbelian_top_iff {X : Subgroup G} :
    IsElemAbelian 2 (⊤ : Subgroup X) ↔ IsElemAbelian 2 X := by
  constructor
  · intro h
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact congrArg Subtype.val
        (h.1.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup X)) ⟨b, trivial⟩)
    · intro x hx
      have hx2 := h.2 ⟨x, hx⟩ trivial
      simpa using congrArg (fun z : X => (z : G)) hx2
  · intro h
    haveI := h.1
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact Subtype.ext (mul_comm' a.1 b.1)
    · intro x _
      exact Subtype.ext (h.2 (x : G) x.2)

private lemma isE_toSub {X : Subgroup G} (h : IsE 3 ↥X) :
    IsElemAbelian 2 X ∧ Nat.card X = 8 :=
  ⟨isElemAbelian_top_iff.mp h.1, by rw [h.2]; norm_num⟩

theorem y7n_mem_sup_zpowers {H : Subgroup G} {g : G} (hg2 : g ^ 2 = 1)
    (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H) {x : G} (hx : x ∈ H ⊔ zpowers g) :
    x ∈ H ∨ ∃ y ∈ H, x = y * g := by
  have hgg : g * g = 1 := by simpa [pow_two] using hg2
  have hgN : g ∈ normalizer (H : Set G) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun h => ⟨fun hh => hgH h hh, fun hh => ?_⟩
    have hconj : g * (g * h * g⁻¹) * g⁻¹ = h := by
      have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
      rw [show g * (g * h * g⁻¹) * g⁻¹ = (g * g) * h * (g⁻¹ * g⁻¹) by group,
        hgg, hinv, hgg]
      simp
    rw [← hconj]
    exact hgH _ hh
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ H ∨ ∃ y ∈ H, x = y * g}
      one_mem' := Or.inl (one_mem H)
      mul_mem' := by
        rintro x z (hx | ⟨y, hy, rfl⟩) (hz | ⟨w, hw, rfl⟩)
        · exact Or.inl (mul_mem hx hz)
        · exact Or.inr ⟨x * w, mul_mem hx hw, (mul_assoc x w g).symm⟩
        · refine Or.inr ⟨y * (g * z * g⁻¹), mul_mem hy ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgN z).mp hz
          · rw [show y * (g * z * g⁻¹) * g = (y * g) * z by group]
        · refine Or.inl ?_
          rw [show (y * g) * (w * g) = y * (g * w * g⁻¹) * (g * g) by group, hgg, mul_one]
          exact mul_mem hy ((Subgroup.mem_set_normalizer_iff.mp hgN w).mp hw)
      inv_mem' := by
        rintro x (hx | ⟨y, hy, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨g * y⁻¹ * g⁻¹, ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgN y⁻¹).mp (inv_mem hy)
          · show (y * g)⁻¹ = (g * y⁻¹ * g⁻¹) * g
            rw [mul_inv_rev,
              show g⁻¹ * y⁻¹ = g * y⁻¹ by rw [inv_eq_of_mul_eq_one_right hgg]]
            group }
  have hle : H ⊔ zpowers g ≤ T := by
    refine sup_le (fun x hx => Or.inl hx) ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff]
    exact Or.inr ⟨1, one_mem H, (one_mul g).symm⟩
  exact hle hx

theorem SgFacts.elemCover {S F : Subgroup G} {g : G} (h : SgFacts S F g) :
    ElemCover 8 (S ⊔ zpowers g) := by
  intro x hx hx2
  rcases y7n_mem_sup_zpowers h.g_sq h.g_norm hx with hxS | ⟨y, hy, hxy⟩
  · obtain ⟨E, hES, hEelem, hEcard, hxE⟩ := h.rank.cover x hxS hx2
    exact ⟨E, hES.trans le_sup_left, hEelem, by rw [hEcard], hxE⟩
  · have hx2' : (y * g) ^ 2 = 1 := by rw [← hxy]; exact hx2
    have hycent : y ∈ centEl S g := h.invol y hy hx2'
    have hyF : y ∈ F := h.cent_eq ▸ hycent
    refine ⟨F ⊔ zpowers g, ?_, ?_, ?_, ?_⟩
    · refine sup_le ?_ le_sup_right
      rw [← h.cent_eq]
      exact (show centEl S g ≤ S from inf_le_left).trans le_sup_left
    · refine IsElemAbelian.sup_of_commute h.F_elem (isElemAbelian_zpowers h.g_sq) ?_
      intro a ha b hb
      have haC : a ∈ Subgroup.centralizer ({g} : Set G) := by
        rw [← h.cent_eq] at ha
        exact ha.2
      have hag : a * g = g * a := Subgroup.mem_centralizer_singleton_iff.mp haC
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a g from hag) n).eq
    · rw [← h.F_card]
      exact Subgroup.card_le_of_le le_sup_left
    · rw [hxy]
      exact mul_mem (Subgroup.mem_sup_left hyF) (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

theorem sgFacts_of_frame (fr : Frame G) (hrank : RankFacts fr.S) (hF : IsE 3 ↥fr.F)
    (h13 : fr.Fact13) (hg2 : fr.σ ^ 2 = 1) (hgS : fr.σ ∉ fr.S)
    (hgN : ∀ x ∈ fr.S, fr.σ * x * fr.σ⁻¹ ∈ fr.S) : SgFacts fr.S fr.F fr.σ := by
  have hFsub := isE_toSub hF
  refine ⟨hrank, hFsub.1, hFsub.2, hg2, hgS, hgN, h13.1, ?_⟩
  intro y hy hy2
  have hne : y * fr.σ ≠ 1 := by
    intro h1
    apply hgS
    have hσ : fr.σ = y⁻¹ := (mul_eq_one_iff_inv_eq.mp h1).symm
    rw [hσ]
    exact fr.S.inv_mem hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (y * fr.σ) = 2 := orderOf_eq_prime hy2 hne
  have hmem : y * fr.σ ∈ {w : G | (∃ s ∈ fr.S, w = s * fr.σ) ∧ orderOf w = 2} :=
    ⟨⟨y, hy, rfl⟩, hord⟩
  rw [h13.2.1] at hmem
  obtain ⟨c, hc, hcy⟩ := hmem
  rw [mul_right_cancel hcy]
  exact hc

end CFSG.OddStandard.HigherRank.YamadaG23
