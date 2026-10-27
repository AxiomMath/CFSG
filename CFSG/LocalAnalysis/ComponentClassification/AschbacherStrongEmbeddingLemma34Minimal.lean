module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Closed

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

structure Minimal (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop where
  hyp : Hyp S A₁ A₂
  not_le₁₂ : ¬ A₁ ≤ A₂
  not_le₂₁ : ¬ A₂ ≤ A₁
  ih : Statement (Nat.card G - 1)
  ne_top : overlapClosure A₁ A₂ ≠ ⊤
  not_dihedral : ¬ DihedralCase (S : Subgroup G) A₁ A₂

namespace Minimal

variable (m : Minimal S A₁ A₂)
include m

theorem sylow_le : (S : Subgroup G) ≤ overlapClosure A₁ A₂ :=
  m.hyp.sylow_le_overlapClosure m.not_le₁₂ m.not_le₂₁

theorem mem_sylow {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) : a ∈ (S : Subgroup G) := by
  rcases ha with ha | ha
  · exact m.hyp.le_one ha
  · exact m.hyp.le_two ha

theorem mem_of_conj {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : g ∈ overlapClosure A₁ A₂ :=
  m.hyp.mem_of_conj_mem_sylow m.not_le₁₂ m.not_le₂₁ m.ih m.ne_top m.not_dihedral ha ha1 hS

theorem conj_mem {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂)
    (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : g⁻¹ * a * g ∈ (A₁ : Set G) ∪ A₂ :=
  m.hyp.strongly_closed m.not_le₁₂ m.not_le₂₁ m.ih m.ne_top m.not_dihedral a ha g
    (Subgroup.mem_top g) hS

theorem fixesOnly {b : G} (hb : b ∈ (A₁ : Set G) ∪ A₂) (hb1 : b ≠ 1) :
    FixesOnly (overlapClosure A₁ A₂) (Subgroup.zpowers b) :=
  m.hyp.fixesOnly_of_mem_union m.not_le₁₂ m.not_le₂₁ m.ih m.ne_top m.not_dihedral hb hb1

theorem centralizer_le {b : G} (hb : b ∈ (A₁ : Set G) ∪ A₂) (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≤ overlapClosure A₁ A₂ :=
  m.hyp.centralizer_le_of_mem_union m.not_le₁₂ m.not_le₂₁ m.ih m.ne_top m.not_dihedral hb hb1

theorem mem_of_mem_rightConjugate {b g : G} (hb : b ∈ (A₁ : Set G) ∪ A₂) (hb1 : b ≠ 1)
    (hbg : b ∈ rightConjugate (overlapClosure A₁ A₂) g) : g ∈ overlapClosure A₁ A₂ :=
  (unique_of_fixesOnly (m.hyp.mem_overlapClosure_of_mem_union hb) (m.fixesOnly hb hb1) g).mp hbg

theorem false_of_central {y : G} (hyc : y ∈ Subgroup.center G) (hyy : y * y = 1)
    (hy₁ : y ∉ A₁) (hy₂ : y ∉ A₂) (hn₁ : ¬ A₁ ≤ A₂ ⊔ Subgroup.zpowers y)
    (hn₂ : ¬ A₂ ≤ A₁ ⊔ Subgroup.zpowers y) : False := by
  rcases m.hyp.quotient_central m.not_le₁₂ m.not_le₂₁ m.ih hyc hyy hy₁ hy₂ hn₁ hn₂ with
    htop | ⟨-, a, ha, g, hS, hN⟩
  · exact m.ne_top htop
  · have ha1 : a ≠ 1 := by
      rintro rfl
      apply hN
      rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    exact hN (mem_normalizer_one_of_mem_union m.hyp.comm (m.conj_mem (Or.inl ha) hS))

theorem false_of_central_of_inf_eq_bot (hI : A₁ ⊓ A₂ = ⊥) {y : G}
    (hyc : y ∈ Subgroup.center G) (hyy : y * y = 1) (hy₁ : y ∉ A₁) (hy₂ : y ∉ A₂) : False := by
  have h4₁ := four_le_card_of_two_le_pRank m.hyp.rank_one
  have h4₂ := four_le_card_of_two_le_pRank m.hyp.rank_two
  refine m.false_of_central hyc hyy hy₁ hy₂ (fun hle => ?_) (fun hle => ?_)
  · have := card_le_two_mul_inf_of_le_sup_zpowers hyc hyy hle
    rw [hI, Subgroup.card_bot] at this
    omega
  · have := card_le_two_mul_inf_of_le_sup_zpowers hyc hyy hle
    rw [inf_comm, hI, Subgroup.card_bot] at this
    omega

theorem not_dihedralCase {K : Subgroup G} (P : Subgroup K)
    (hP : P ≤ (S : Subgroup G).subgroupOf K) (hn₁ : ¬ A₁ ⊓ K ≤ A₂) :
    ¬ DihedralCase P (A₁.subgroupOf K) (A₂.subgroupOf K) := by
  rintro ⟨⟨b, hb, w, hwP, hconj⟩, -, -⟩
  have hb' : (b : G) ∈ A₁ := hb
  have heqK : A₁.subgroupOf K = A₂.subgroupOf K → False := fun heq => by
    apply hn₁
    intro x hx
    have hmem : (⟨x, hx.2⟩ : K) ∈ A₁.subgroupOf K := hx.1
    rw [heq] at hmem
    exact hmem
  have hsS : (w : G)⁻¹ * b * w ∈ (S : Subgroup G) := hP hwP
  by_cases hb1 : (b : G) = 1
  · apply heqK
    rw [← hconj]
    have : w⁻¹ * b * w = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb1, mul_one, inv_mul_cancel,
        Subgroup.coe_one]
    rw [this, rightConjugate_one]
  · have hsU := m.conj_mem (Or.inl hb') hsS
    have hsN := mem_normalizer_one_of_mem_union m.hyp.comm hsU
    apply heqK
    rw [← hconj]
    symm
    ext x
    rw [mem_rightConjugate_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h := Subgroup.mem_normalizer_iff.mp hsN (x : G)
    rw [show (w : G)⁻¹ * b * w * x * ((w : G)⁻¹ * b * w)⁻¹ =
      ((w : G)⁻¹ * b * w) * x * ((w : G)⁻¹ * b * w)⁻¹ by rfl]
    exact h.symm

end Minimal

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
