module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34TwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Step

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G]

theorem dihedral_of_mulEquiv {X Y : Type} [Group X] [Group Y] {P : Subgroup X} {Q : Subgroup Y}
    (e : P ≃* Q) (h : IsDihedralTwoGroup P ∨ IsSemidihedralTwoGroup P) :
    IsDihedralTwoGroup Q ∨ IsSemidihedralTwoGroup Q := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩

noncomputable def rightConjugateEquiv (P : Subgroup G) (g : G) : P ≃* rightConjugate P g :=
  P.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem inf_le_centralizer_of_mem_union (hc : ⁅A₁, A₂⁆ = ⊥) {a : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) : A₁ ⊓ A₂ ≤ Subgroup.centralizer ({a} : Set G) := by
  rintro x ⟨hx₁, hx₂⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases ha with ha | ha
  · exact (commute_of_comm hc ha hx₂).eq.symm
  · exact (commute_of_comm hc hx₁ ha).eq

omit [Finite G] in
theorem le_centralizer_of_mem_one (hc : ⁅A₁, A₂⁆ = ⊥) {a : G} (ha : a ∈ A₁) :
    A₂ ≤ Subgroup.centralizer ({a} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_comm hc ha hx).eq.symm

omit [Finite G] in
theorem centralizer_ne_top_of_mem_union (hH : overlapClosure A₁ A₂ ≠ ⊤) {a : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  apply hH
  refine eq_top_iff.mpr fun g _ => mem_overlapClosure_of_union ha ha1 ?_
  have hg : g ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [mul_assoc, ← hg, inv_mul_cancel_left]
  exact ha

theorem Hyp.centralizer_le_of_involution (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂)
    (h21 : ¬ A₂ ≤ A₁) (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hex : Nat.card (A₁ ⊓ A₂ : Subgroup G) ≠ 2 ∨
      (¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧
        ¬ (IsDihedralTwoGroup A₂ ∨ IsSemidihedralTwoGroup A₂)))
    {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2) :
    Subgroup.centralizer ({a} : Set G) ≤ overlapClosure A₁ A₂ := by
  have hSH := h.sylow_le_overlapClosure h12 h21
  have hp₁ : IsPGroup 2 A₁ := S.isPGroup'.to_le h.le_one
  have hp₂ : IsPGroup 2 A₂ := S.isPGroup'.to_le h.le_two
  obtain ⟨X, hXU, hXS, hXcard⟩ : ∃ X : Subgroup G, (X : Set G) ⊆ (A₁ : Set G) ∪ A₂ ∧
      X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G) ∧ 4 ≤ Nat.card X := by
    rcases ha with ha | ha
    · exact ⟨A₁ ⊓ Subgroup.centralizer ({a} : Set G), fun x hx => Or.inl hx.1,
        inf_le_inf_right _ h.le_one, four_le_card_inf_centralizer hp₁ h.rank_one ha ha2⟩
    · exact ⟨A₂ ⊓ Subgroup.centralizer ({a} : Set G), fun x hx => Or.inr hx.1,
        inf_le_inf_right _ h.le_two, four_le_card_inf_centralizer hp₂ h.rank_two ha ha2⟩
  have hX := h.fixesOnly_of_card h12 h21 hXU hXcard
  obtain ⟨k, hk, ⟨P, hP⟩, hconj⟩ := h.exists_conj_sylow_inf hSH hXS hX
  have hbU : (k⁻¹ * a * k) ∈ (A₁ : Set G) ∪ A₂ :=
    hconj a ha (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hb2 : orderOf (k⁻¹ * a * k) = 2 := by
    rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]
    exact ha2
  have hb1 : (k⁻¹ * a * k) ≠ 1 := (orderOf_eq_prime_iff.mp hb2).2
  let K := Subgroup.centralizer ({(k⁻¹ * a * k)} : Set G)
  have hbK : (k⁻¹ * a * k) ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hK : K ≠ ⊤ := centralizer_ne_top_of_mem_union hH hbU hb1
  have hrank : 2 ≤ CFSG.Open.pRank 2 (A₁ ⊓ K) ∧ 2 ≤ CFSG.Open.pRank 2 (A₂ ⊓ K) := by
    rcases hbU with h1 | h2
    · refine ⟨two_le_pRank_inf_centralizer hp₁ h.rank_one h1 hb2, ?_⟩
      rw [inf_eq_left.mpr (le_centralizer_of_mem_one h.comm h1)]
      exact h.rank_two
    · have hc' : ⁅A₂, A₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h.comm
      refine ⟨?_, two_le_pRank_inf_centralizer hp₂ h.rank_two h2 hb2⟩
      rw [inf_eq_left.mpr (le_centralizer_of_mem_one hc' h2)]
      exact h.rank_one
  have hc' : ⁅A₂, A₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h.comm
  have hn₁ : ¬ A₁ ⊓ K ≤ A₂ := by
    intro hle
    by_cases h2 : (k⁻¹ * a * k) ∈ A₂
    · exact h12 fun x hx => hle ⟨hx, le_centralizer_of_mem_one hc' h2 hx⟩
    · have h1 : (k⁻¹ * a * k) ∈ A₁ := hbU.resolve_right h2
      exact h2 (hle ⟨h1, hbK⟩)
  have hn₂ : ¬ A₂ ⊓ K ≤ A₁ := by
    intro hle
    by_cases h1 : (k⁻¹ * a * k) ∈ A₁
    · exact h21 fun x hx => hle ⟨hx, le_centralizer_of_mem_one h.comm h1 hx⟩
    · have h2 : (k⁻¹ * a * k) ∈ A₂ := hbU.resolve_left h1
      exact h1 (hle ⟨h2, hbK⟩)
  have h3 : ¬ DihedralCase (P : Subgroup K) (A₁.subgroupOf K) (A₂.subgroupOf K) := by
    rcases hex with hcard | ⟨hd₁, hd₂⟩
    · apply not_dihedralCase_of_card
      rwa [inf_eq_left.mpr (inf_le_centralizer_of_mem_union h.comm hbU)]
    · rintro ⟨⟨b, hb, w, -, hw⟩, hd, -⟩
      by_cases h2 : (k⁻¹ * a * k) ∈ A₂
      · exact hd₁ (dihedral_of_mulEquiv (Subgroup.subgroupOfEquivOfLe
          (le_centralizer_of_mem_one hc' h2)) hd)
      · have h1 : (k⁻¹ * a * k) ∈ A₁ := hbU.resolve_right h2
        have hd' := dihedral_of_mulEquiv ((rightConjugateEquiv _ _).trans
          (MulEquiv.subgroupCongr hw)) hd
        exact hd₂ (dihedral_of_mulEquiv (Subgroup.subgroupOfEquivOfLe
          (le_centralizer_of_mem_one h.comm h1)) hd')
  have hKH : K ≤ overlapClosure A₁ A₂ :=
    h.le_overlapClosure_of_statement h12 h21 IH hK P hP hrank.1 hrank.2 hn₁ hn₂ h3
  intro x hx
  have hx' : k⁻¹ * x * k ∈ K := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc k⁻¹ * x * k * (k⁻¹ * a * k) = k⁻¹ * (x * a) * k := by group
      _ = k⁻¹ * (a * x) * k := by rw [hx]
      _ = k⁻¹ * a * k * (k⁻¹ * x * k) := by group
  have := (overlapClosure A₁ A₂).mul_mem
    ((overlapClosure A₁ A₂).mul_mem hk (hKH hx')) ((overlapClosure A₁ A₂).inv_mem hk)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
