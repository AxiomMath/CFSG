module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Count

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] noncomputable def cnt {G : Type*} [Group G] (b : Set G) (u : G) : ℕ :=
  Set.ncard {w | w ∈ b ∧ w * u = u * w}

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem blk_one (C : Set G) : blk 1 C = C := by
  ext u; simp [blk]

theorem cnt_blk {s₁ s₀ e₀ : G} (hs₁ : s₁ ∈ S) (hs₀ : s₀ ∈ S) {C : Set G} (hC : C ⊆ E)
    (he₀ : e₀ ∈ E) : cnt (blk s₁ C) (s₀ * e₀) =
      Set.ncard {e' | e' ∈ C ∧ ((s₁ * s₀ = s₀ * s₁) ↔ (e' * e₀ = e₀ * e'))} := by
  have hset : {w | w ∈ blk s₁ C ∧ w * (s₀ * e₀) = (s₀ * e₀) * w} =
      (fun e => s₁ * e) '' {e' | e' ∈ C ∧ ((s₁ * s₀ = s₀ * s₁) ↔ (e' * e₀ = e₀ * e'))} := by
    ext w
    constructor
    · rintro ⟨⟨e', he', rfl⟩, hc⟩
      exact ⟨e', ⟨he', (h.comm_iff hs₁ hs₀ (hC he') he₀).1 hc⟩, rfl⟩
    · rintro ⟨e', ⟨he', hiff⟩, rfl⟩
      exact ⟨⟨e', he', rfl⟩, (h.comm_iff hs₁ hs₀ (hC he') he₀).2 hiff⟩
  unfold cnt
  rw [hset, ncard_image_mul_left]

theorem cnt_blk_comm {s₁ s₀ e₀ : G} (hs₁ : s₁ ∈ S) (hs₀ : s₀ ∈ S) {C : Set G} (hC : C ⊆ E)
    (he₀ : e₀ ∈ E) (hσ : s₁ * s₀ = s₀ * s₁) : cnt (blk s₁ C) (s₀ * e₀) =
      Set.ncard {e' | e' ∈ C ∧ e' * e₀ = e₀ * e'} := by
  rw [h.cnt_blk hs₁ hs₀ hC he₀]
  congr 1
  ext e'
  simp [hσ]

theorem cnt_blk_anti {s₁ s₀ e₀ : G} (hs₁ : s₁ ∈ S) (hs₀ : s₀ ∈ S) {C : Set G} (hC : C ⊆ E)
    (he₀ : e₀ ∈ E) (hσ : s₁ * s₀ ≠ s₀ * s₁) : cnt (blk s₁ C) (s₀ * e₀) =
      Set.ncard {e' | e' ∈ C ∧ e' * e₀ ≠ e₀ * e'} := by
  rw [h.cnt_blk hs₁ hs₀ hC he₀]
  congr 1
  ext e'
  simp [hσ]

theorem ncard_E0 : Set.ncard ({1, t} : Set G) = 2 := Set.ncard_pair (Ne.symm h.t_ne)

theorem E0_comm {e₀ : G} (he₀ : e₀ ∈ E) : {e' | e' ∈ ({1, t} : Set G) ∧ e' * e₀ = e₀ * e'} =
    ({1, t} : Set G) := by
  ext e'
  constructor
  · exact fun hh => hh.1
  · intro he'
    refine ⟨he', ?_⟩
    rcases he' with rfl | rfl
    · simp
    · exact (h.t_comm_E e₀ he₀).symm

theorem E0_anti {e₀ : G} (he₀ : e₀ ∈ E) : {e' | e' ∈ ({1, t} : Set G) ∧ e' * e₀ ≠ e₀ * e'} =
    ∅ := by
  ext e'
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro he'
  rcases he' with rfl | rfl
  · simp
  · exact (h.t_comm_E e₀ he₀).symm

theorem E2_central {e₀ : G} (he₀ : e₀ = 1 ∨ e₀ = t) :
    {e' | e' ∈ E2 E t ∧ e' * e₀ = e₀ * e'} = E2 E t := by
  ext e'
  constructor
  · exact fun hh => hh.1
  · intro he'
    refine ⟨he', ?_⟩
    rcases he₀ with rfl | rfl
    · simp
    · exact h.t_comm_E e' he'.1

theorem E2_central_anti {e₀ : G} (he₀ : e₀ = 1 ∨ e₀ = t) :
    {e' | e' ∈ E2 E t ∧ e' * e₀ ≠ e₀ * e'} = ∅ := by
  ext e'
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro he'
  rcases he₀ with rfl | rfl
  · simp
  · exact h.t_comm_E e' he'.1

theorem E2_anti_E2 {e₀ : G} (he₀ : e₀ ∈ E2 E t) :
    Set.ncard {e' | e' ∈ E2 E t ∧ e' * e₀ ≠ e₀ * e'} = 8 := by
  have := h.ef.anti_two e₀ he₀.1 he₀.2.1 he₀.2.2.1 he₀.2.2.2
  convert this using 2
  ext y
  simp only [E2, Set.mem_ofPred_eq, and_assoc]

theorem E2_comm_E2 {e₀ : G} (he₀ : e₀ ∈ E2 E t) :
    Set.ncard {e' | e' ∈ E2 E t ∧ e' * e₀ = e₀ * e'} = 2 := by
  have h1 := ncard_split_by_prop (E2 E t) (fun w => w * e₀ = e₀ * w)
  have h2 := h.E2_anti_E2 he₀
  have h3 : Set.ncard (E2 E t) = 10 := h.ef.card_two
  have h4 : {w | w ∈ E2 E t ∧ ¬ (w * e₀ = e₀ * w)} = {e' | e' ∈ E2 E t ∧ e' * e₀ ≠ e₀ * e'} :=
    rfl
  rw [h4, h2, h3] at h1
  omega

theorem E4_anti_E2 {e₀ : G} (he₀ : e₀ ∈ E2 E t) :
    Set.ncard {e' | e' ∈ E4 E t ∧ e' * e₀ ≠ e₀ * e'} = 8 := by
  have := h.ef.anti_four e₀ he₀.1 he₀.2.1 he₀.2.2.1 he₀.2.2.2
  convert this using 2
  ext y
  simp only [E4, Set.mem_ofPred_eq, and_assoc]

end Hyp69

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem cnt_blk_comm' {u s₁ s₀ e₀ : G} (hu : u = s₀ * e₀) (hs₁ : s₁ ∈ S) (hs₀ : s₀ ∈ S)
    {C : Set G} (hC : C ⊆ E) (he₀ : e₀ ∈ E) (hσ : s₁ * s₀ = s₀ * s₁) :
    cnt (blk s₁ C) u = Set.ncard {e' | e' ∈ C ∧ e' * e₀ = e₀ * e'} := by
  subst hu; exact h.cnt_blk_comm hs₁ hs₀ hC he₀ hσ

theorem cnt_blk_anti' {u s₁ s₀ e₀ : G} (hu : u = s₀ * e₀) (hs₁ : s₁ ∈ S) (hs₀ : s₀ ∈ S)
    {C : Set G} (hC : C ⊆ E) (he₀ : e₀ ∈ E) (hσ : s₁ * s₀ ≠ s₀ * s₁) :
    cnt (blk s₁ C) u = Set.ncard {e' | e' ∈ C ∧ e' * e₀ ≠ e₀ * e'} := by
  subst hu; exact h.cnt_blk_anti hs₁ hs₀ hC he₀ hσ

theorem E4_central_anti {e₀ : G} (he₀ : e₀ = 1 ∨ e₀ = t) :
    {e' | e' ∈ E4 E t ∧ e' * e₀ ≠ e₀ * e'} = ∅ := by
  ext e'
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro he'
  rcases he₀ with rfl | rfl
  · simp
  · exact h.t_comm_E e' he'.1

theorem sigma_a_z {α : G} (hα : AlphaSpec S z t α) : α * z ≠ z * α :=
  h.anti_of_eq_t_mul hα.rel

theorem sigma_z_a {α : G} (hα : AlphaSpec S z t α) : z * α ≠ α * z :=
  h.anti_of_eq_t_mul (h.z_alpha hα)

theorem sigma_r_z {α : G} (hα : AlphaSpec S z t α) : (α * z) * z ≠ z * (α * z) := by
  have : z * (α * z) = t * ((α * z) * z) := by
    calc z * (α * z) = (z * α) * z := by group
      _ = (t * (α * z)) * z := by rw [h.z_alpha hα]
      _ = t * ((α * z) * z) := by group
  exact Ne.symm (h.anti_of_eq_t_mul this)

theorem sigma_r_a {α : G} (hα : AlphaSpec S z t α) : (α * z) * α ≠ α * (α * z) := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  have : α * (α * z) = t * ((α * z) * α) := by
    have h1 : (α * z) * α = t * z := by
      calc (α * z) * α = α * (z * α) * 1 := by group
        _ = α * (t * (α * z)) := by rw [h.z_alpha hα, mul_one]
        _ = (α * t) * (α * z) := by group
        _ = (t * α) * (α * z) := by rw [hαt]
        _ = t * ((α * α) * z) := by group
        _ = t * z := by rw [hα.sq, one_mul]
    calc α * (α * z) = z := by
          calc α * (α * z) = (α * α) * z := by group
            _ = z := by rw [hα.sq, one_mul]
      _ = (t * t) * z := by rw [h.t_sq, one_mul]
      _ = t * (t * z) := by rw [mul_assoc]
      _ = t * ((α * z) * α) := by rw [h1]
  exact Ne.symm (h.anti_of_eq_t_mul this)

section table

variable {α : G} (hα : AlphaSpec S z t α)
include hα

theorem T1 : cnt (blk z {1, t}) z = 2 := by
  rw [h.cnt_blk_comm' (mul_one z).symm h.zS h.zS h.E0_sub (one_mem _) rfl,
    h.E0_comm (one_mem _), h.ncard_E0]

theorem T2 : cnt (blk z (E2 E t)) z = 10 := by
  rw [h.cnt_blk_comm' (mul_one z).symm h.zS h.zS h.E2_sub (one_mem _) rfl,
    h.E2_central (Or.inl rfl)]
  exact h.ef.card_two

theorem T3 : cnt (blk α (E2 E t)) z = 0 := by
  rw [h.cnt_blk_anti' (mul_one z).symm hα.mem h.zS h.E2_sub (one_mem _) (h.sigma_a_z hα),
    h.E2_central_anti (Or.inl rfl)]
  exact Set.ncard_empty _

theorem T4 : cnt (blk (α * z) (E4 E t)) z = 0 := by
  rw [h.cnt_blk_anti' (mul_one z).symm (h.alpha_z_mem hα) h.zS h.E4_sub (one_mem _)
    (h.sigma_r_z hα), h.E4_central_anti (Or.inl rfl)]
  exact Set.ncard_empty _

variable {e : G} (he : e ∈ E2 E t)
include he

theorem T5 : cnt (blk z {1, t}) (z * e) = 2 := by
  rw [h.cnt_blk_comm' rfl h.zS h.zS h.E0_sub he.1 rfl, h.E0_comm he.1, h.ncard_E0]

theorem T6 : cnt (blk z (E2 E t)) (z * e) = 2 := by
  rw [h.cnt_blk_comm' rfl h.zS h.zS h.E2_sub he.1 rfl]
  exact h.E2_comm_E2 he

theorem T7 : cnt (blk α (E2 E t)) (z * e) = 8 := by
  rw [h.cnt_blk_anti' rfl hα.mem h.zS h.E2_sub he.1 (h.sigma_a_z hα)]
  exact h.E2_anti_E2 he

theorem T8 : cnt (blk (α * z) (E4 E t)) (z * e) = 8 := by
  rw [h.cnt_blk_anti' rfl (h.alpha_z_mem hα) h.zS h.E4_sub he.1 (h.sigma_r_z hα)]
  exact h.E4_anti_E2 he

theorem T9 : cnt (blk z {1, t}) (α * e) = 0 := by
  rw [h.cnt_blk_anti' rfl h.zS hα.mem h.E0_sub he.1 (h.sigma_z_a hα), h.E0_anti he.1]
  exact Set.ncard_empty _

theorem T10 : cnt (blk z (E2 E t)) (α * e) = 8 := by
  rw [h.cnt_blk_anti' rfl h.zS hα.mem h.E2_sub he.1 (h.sigma_z_a hα)]
  exact h.E2_anti_E2 he

theorem T11 : cnt (blk α (E2 E t)) (α * e) = 2 := by
  rw [h.cnt_blk_comm' rfl hα.mem hα.mem h.E2_sub he.1 rfl]
  exact h.E2_comm_E2 he

theorem T16 : cnt (blk α {1, t}) e = 2 := by
  have hs₀ : (1 : G) ∈ S := one_mem _
  rw [h.cnt_blk_comm' (one_mul e).symm hα.mem hs₀ h.E0_sub he.1 (by simp),
    h.E0_comm he.1, h.ncard_E0]

theorem T17 : cnt (blk 1 (E2 E t)) e = 2 := by
  have hs₀ : (1 : G) ∈ S := one_mem _
  rw [h.cnt_blk_comm' (one_mul e).symm hs₀ hs₀ h.E2_sub he.1 rfl]
  exact h.E2_comm_E2 he

theorem T18 : cnt (blk α (E2 E t)) e = 2 := by
  have hs₀ : (1 : G) ∈ S := one_mem _
  rw [h.cnt_blk_comm' (one_mul e).symm hα.mem hs₀ h.E2_sub he.1 (by simp)]
  exact h.E2_comm_E2 he

theorem T19 : cnt (blk α {1, t}) (α * e) = 2 := by
  rw [h.cnt_blk_comm' rfl hα.mem hα.mem h.E0_sub he.1 rfl, h.E0_comm he.1, h.ncard_E0]

end table

theorem T13 {α : G} (hα : AlphaSpec S z t α) : cnt (blk α {1, t}) α = 2 := by
  rw [h.cnt_blk_comm' (mul_one α).symm hα.mem hα.mem h.E0_sub (one_mem _) rfl,
    h.E0_comm (one_mem _), h.ncard_E0]

theorem T14 {α : G} (hα : AlphaSpec S z t α) : cnt (blk 1 (E2 E t)) α = 10 := by
  have hs₁ : (1 : G) ∈ S := one_mem _
  rw [h.cnt_blk_comm' (mul_one α).symm hs₁ hα.mem h.E2_sub (one_mem _) (by simp),
    h.E2_central (Or.inl rfl)]
  exact h.ef.card_two

theorem T15 {α : G} (hα : AlphaSpec S z t α) : cnt (blk α (E2 E t)) α = 10 := by
  rw [h.cnt_blk_comm' (mul_one α).symm hα.mem hα.mem h.E2_sub (one_mem _) rfl,
    h.E2_central (Or.inl rfl)]
  exact h.ef.card_two

theorem cnt_union {A B : Set G} (hAB : Disjoint A B) (u : G) :
    cnt (A ∪ B) u = cnt A u + cnt B u :=
  ncard_filter_union hAB (fun w => w * u = u * w)

theorem cnt_empty (u : G) : cnt (∅ : Set G) u = 0 := by
  unfold cnt
  simp

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
