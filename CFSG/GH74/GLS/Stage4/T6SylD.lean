module

public import CFSG.GH74.GLS.Stage4.T6SylC
public import CFSG.GH74.GLS.Stage4.T6SylH
public import CFSG.GH74.GLS.Stage4.T6SylN

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem card_RA (h : T6Ctx N u p) (hR : T6RFacts N p) : Nat.card ↥(RA N p u) = N.q₁ * N.q₂ := by
  have h1 : N.q₂ * Nat.card ↥(RA N p u) ^ 2 = N.q₁ ^ 2 * N.q₂ ^ 3 := by
    rw [← R₂_card_RA h, hR.card]
  have hq₂ : 0 < N.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have h2 : Nat.card ↥(RA N p u) ^ 2 = (N.q₁ * N.q₂) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hq₂
    calc N.q₂ * Nat.card ↥(RA N p u) ^ 2 = N.q₁ ^ 2 * N.q₂ ^ 3 := h1
      _ = N.q₂ * (N.q₁ * N.q₂) ^ 2 := by ring
  exact Nat.pow_left_injective (by norm_num) h2

theorem card_RB (h : T6Ctx N u p) (hR : T6RFacts N p) : Nat.card ↥(RB N p u) = N.q₁ * N.q₂ := by
  rw [RA_card_eq_RB h, card_RA h hR]

theorem norm_cent_R₂ (h : T6Ctx N u p) {v f : G} (hf : f ∈ N.F) (hfv : f * v = v * f)
    {r : G} (hr : r ∈ R₂ N p ⊓ Subgroup.centralizer ({v} : Set G)) :
    f * r * f⁻¹ ∈ R₂ N p ⊓ Subgroup.centralizer ({v} : Set G) := by
  refine ⟨R₂_norm N p (F_le_M₂ h hf) hr.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  calc f * r * f⁻¹ * v = f * (r * (f⁻¹ * v)) := by group
    _ = f * (r * (v * f⁻¹)) := by
        congr 2
        calc f⁻¹ * v = f⁻¹ * (v * f) * f⁻¹ := by group
          _ = f⁻¹ * (f * v) * f⁻¹ := by rw [hfv]
          _ = v * f⁻¹ := by group
    _ = f * ((r * v) * f⁻¹) := by group
    _ = f * ((v * r) * f⁻¹) := by rw [h1]
    _ = v * (f * r * f⁻¹) := by
        have : f * v = v * f := hfv
        calc f * ((v * r) * f⁻¹) = (f * v) * r * f⁻¹ := by group
          _ = (v * f) * r * f⁻¹ := by rw [this]
          _ = v * (f * r * f⁻¹) := by group

theorem card_sup_P₀ (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {v : G}
    (hv : ∀ f ∈ N.F, f * v = v * f) :
    Nat.card ↥((R₂ N p ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ P₀) =
      Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer ({v} : Set G)) * Nat.card ↥P₀ := by
  have hnorm : P₀ ≤ Subgroup.normalizer ((R₂ N p ⊓ Subgroup.centralizer ({v} : Set G) :
      Subgroup G) : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype (fun r hr => norm_cent_R₂ h (hP₀F hf) (hv f (hP₀F hf)) hr)
  have hdisj : Disjoint (R₂ N p ⊓ Subgroup.centralizer ({v} : Set G)) P₀ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h1 : x ∈ (R₂ N p ⊔ N.X₁) ⊓ N.F :=
      ⟨Subgroup.mem_sup_left hx.1.1, hP₀F hx.2⟩
    rw [P_inf_F h] at h1
    exact h1
  exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj

theorem card_Y (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    Nat.card ↥(N.X₁ ⊔ N.X₂ ⊔ P₀) = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  have hnorm : P₀ ≤ Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype (fun x hx => F_norm_X₁X₂ h (hP₀F hf) x hx)
  have hdisj : Disjoint (N.X₁ ⊔ N.X₂) P₀ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h1 : x ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨hP₀F hx.2, X₁_sup_X₂_le_K h hx.1⟩
    rw [h.sec5.F5.F_inter_K] at h1
    exact h1
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    t2H_card_sup_comm_disjoint _ _ (X₁_X₂_comm h) (X₁_inf_X₂ h), h.sec5.loc.card_X₁,
    h.sec5.loc.card_X₂]

theorem exists_sub_Cv (h : T6Ctx N u p) (hR : T6RFacts N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    {v : G} (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    ∃ D : Subgroup G, D ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ ∧ D ≤ Subgroup.centralizer ({v} : Set G) ∧
      Nat.card ↥D = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  have hR₂P : R₂ N p ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ := le_sup_left.trans le_sup_left
  rcases hv with hv | hv | hv
  · subst v
    refine ⟨N.X₁ ⊔ N.X₂ ⊔ P₀, ?_, ?_, card_Y h hP₀F⟩
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact (le_sup_right : N.X₁ ≤ R₂ N p ⊔ N.X₁).trans le_sup_left
      · exact (X₂_le_R₂ h).trans hR₂P
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₁ h hx)
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₂ h hx)
      · intro f hf
        exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_z h (hP₀F hf))
  · subst v
    refine ⟨RA N p u ⊔ P₀, sup_le (inf_le_left.trans hR₂P) le_sup_right, ?_, ?_⟩
    · refine sup_le inf_le_right ?_
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_u h (hP₀F hf))
    · rw [card_sup_P₀ h hP₀F (fun f hf => F_cent_u h hf)]
      exact congrArg (· * Nat.card ↥P₀) (card_RA h hR)
  · subst v
    refine ⟨RB N p u ⊔ P₀, sup_le (inf_le_left.trans hR₂P) le_sup_right, ?_, ?_⟩
    · refine sup_le inf_le_right ?_
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_zu h (hP₀F hf))
    · rw [card_sup_P₀ h hP₀F (fun f hf => F_cent_zu h hf)]
      exact congrArg (· * Nat.card ↥P₀) (card_RB h hR)

theorem card_Cv_Pst (h : T6Ctx N u p) (hR : T6RFacts N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {v : G}
    (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G)) =
      N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  obtain ⟨D, hDP, hDC, hDc⟩ := exists_sub_Cv h hR hP₀F hv
  have h1 : Nat.card ↥D ≤ Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G)) :=
    Subgroup.card_le_of_le (le_inf hDP hDC)
  have h2 := card_pSub_Cv_le h hm hn hP₀c hv (inf_le_right :
    (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) ≤ _)
    ((Pst_pGroup h hR hP₀F hP₀p).to_le inf_le_left)
  omega

end CFSG.GH74.GLS.Stage4.Rest.T6
