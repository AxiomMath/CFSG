module

public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Finset

variable {n : ℕ} {α : Type*} [DecidableEq α]

@[expose] def rearr (c : Fin n → α) : Finset (Fin n → α) :=
  univ.image fun σ : Equiv.Perm (Fin n) => c ∘ σ

theorem mem_rearr {c μ : Fin n → α} : μ ∈ rearr c ↔ ∃ σ : Equiv.Perm (Fin n), μ = c ∘ σ := by
  simp only [rearr, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨σ, h.symm⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, h.symm⟩

theorem comp_mem_rearr {c μ : Fin n → α} (hμ : μ ∈ rearr c) (σ : Equiv.Perm (Fin n)) :
    μ ∘ σ ∈ rearr c := by
  rw [mem_rearr] at hμ ⊢
  obtain ⟨τ, rfl⟩ := hμ
  exact ⟨τ * σ, by ext a; rfl⟩

theorem card_filter_comp_eq_stabilizer (c : Fin n → α) (τ : Equiv.Perm (Fin n)) :
    ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ : Equiv.Perm (Fin n) =>
        c ∘ (σ : Fin n → Fin n) = c ∘ (τ : Fin n → Fin n)).card =
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun g : Equiv.Perm (Fin n) =>
        c ∘ (g : Fin n → Fin n) = c).card := by
  classical
  refine Finset.card_bij (fun σ _ => σ * τ.symm) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    ext a
    calc c ((σ * τ.symm) a) = (c ∘ σ) (τ.symm a) := rfl
      _ = (c ∘ τ) (τ.symm a) := by rw [hσ]
      _ = c a := by simp
  · intro σ₁ _ σ₂ _ h
    have := congrArg (fun x : Equiv.Perm (Fin n) => x * τ) h
    simpa [mul_assoc] using this
  · intro g hg
    refine ⟨g * τ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      ext a
      calc c ((g * τ) a) = (c ∘ g) (τ a) := rfl
        _ = c (τ a) := by rw [hg]
    · ext x
      simp [mul_assoc]

theorem card_rearr_mul_card_stabilizer (c : Fin n → α) :
    (rearr c).card * Fintype.card {g : Equiv.Perm (Fin n) // c ∘ (g : Fin n → Fin n) = c} =
      n.factorial := by
  classical
  have hmap : ((univ : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))).MapsTo
      (fun σ : Equiv.Perm (Fin n) => c ∘ (σ : Fin n → Fin n)) (rearr c) := by
    intro σ _
    exact mem_rearr.mpr ⟨σ, rfl⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin n))))
    (t := rearr c) (f := fun σ : Equiv.Perm (Fin n) => c ∘ (σ : Fin n → Fin n)) hmap
  rw [show ((univ : Finset (Equiv.Perm (Fin n))).card) = n.factorial from by
    simp [Fintype.card_perm, Fintype.card_fin]] at hsum
  rw [Finset.sum_congr rfl (fun μ hμ => ?_)] at hsum
  · rw [Finset.sum_const, Nat.nsmul_eq_mul] at hsum
    exact hsum.symm
  · obtain ⟨τ, rfl⟩ := mem_rearr.mp hμ
    rw [card_filter_comp_eq_stabilizer]
    exact (Fintype.card_subtype
      (p := fun g : Equiv.Perm (Fin n) => c ∘ (g : Fin n → Fin n) = c)).symm

theorem card_rearr_mul_prod_factorial (c : Fin n → α) :
    (rearr c).card * ∏ i ∈ univ.image c, (univ.filter fun a => c a = i).card.factorial =
      n.factorial := by
  rw [← card_rearr_mul_card_stabilizer c]
  congr 1
  rw [DomMulAct.stabilizer_card']
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_subtype]

theorem card_rearr_mul_prod_factorial_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    (f : Fin n → β) :
    (rearr f).card * ∏ b : β, (univ.filter fun a => f a = b).card.factorial = n.factorial := by
  rw [← card_rearr_mul_prod_factorial f]
  congr 1
  symm
  refine Finset.prod_subset (s₁ := univ.image f) (s₂ := univ) (subset_univ _) ?_
  intro b _ hb
  have hempty : (univ.filter fun a => f a = b) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro a _ h
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, h⟩)
  rw [hempty, Finset.card_empty, Nat.factorial_zero]

theorem card_filter_pair_ne (f : Fin n → α) :
    (univ.filter fun p : Fin n × Fin n => f p.1 ≠ f p.2).card =
      n ^ 2 - ∑ i ∈ univ.image f, (univ.filter fun a => f a = i).card ^ 2 := by
  classical
  let E : Finset (Fin n × Fin n) := univ.filter fun p => f p.1 = f p.2
  let P : Finset (Fin n × Fin n) := univ.filter fun p => f p.1 ≠ f p.2
  change P.card = n ^ 2 - ∑ i ∈ univ.image f, (univ.filter fun a => f a = i).card ^ 2
  have hE : E.card = ∑ i ∈ univ.image f, (univ.filter fun a => f a = i).card ^ 2 := by
    have hmap : (E : Set (Fin n × Fin n)).MapsTo (fun p => f p.1) (univ.image f) := by
      intro p _
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_congr rfl
    intro i _
    have hfib : (E.filter fun p => f p.1 = i) =
        (univ.filter fun a => f a = i) ×ˢ (univ.filter fun b => f b = i) := by
      ext p
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨heq, h1⟩
        exact ⟨h1, by rw [← heq, h1]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1, h2], h1⟩
    rw [hfib, Finset.card_product, pow_two]
  have hsplit : E.card + P.card = n ^ 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n × Fin n)))
      (p := fun p : Fin n × Fin n => f p.1 = f p.2)
    simpa [E, P, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two] using this
  rw [hE] at hsplit
  omega

theorem image_comp_perm (f : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    univ.image (f ∘ σ) = univ.image f := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨σ a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨σ.symm a, by simp⟩

theorem card_filter_comp_perm (f : Fin n → α) (σ : Equiv.Perm (Fin n)) (i : α) :
    (univ.filter fun a => (f ∘ σ) a = i).card =
      (univ.filter fun a => f a = i).card := by
  have h : (univ.filter fun b => f b = i) =
      (univ.filter fun a => (f ∘ σ) a = i).image σ := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hb
      refine ⟨σ.symm b, ?_, by simp⟩
      simpa using hb
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  rw [h, Finset.card_image_of_injective _ σ.injective]

theorem sum_sq_fiber_comp_perm (f : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    ∑ i ∈ univ.image (f ∘ σ), (univ.filter fun a => (f ∘ σ) a = i).card ^ 2 =
      ∑ i ∈ univ.image f, (univ.filter fun a => f a = i).card ^ 2 := by
  rw [image_comp_perm f σ]
  apply Finset.sum_congr rfl
  intro i _
  rw [card_filter_comp_perm f σ i]

theorem exists_perm_apply_zero_one {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin n),
      σ ⟨0, by omega⟩ = a ∧ σ ⟨1, by omega⟩ = b := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let s : Equiv.Perm (Fin n) := Equiv.swap z a
  refine ⟨Equiv.swap (s o) b * s, ?_, ?_⟩
  · have hsz : s z = a := by simp [s]
    have hne1 : a ≠ s o := by
      intro h
      have hzo : o = z := s.injective (by rw [← h, hsz])
      have hval : (1 : ℕ) = 0 := by simpa [o, z] using congrArg Fin.val hzo
      omega
    calc (Equiv.swap (s o) b * s) z = Equiv.swap (s o) b (s z) := rfl
      _ = Equiv.swap (s o) b a := by rw [hsz]
      _ = a := Equiv.swap_apply_of_ne_of_ne hne1 hab
  · calc (Equiv.swap (s o) b * s) o = Equiv.swap (s o) b (s o) := rfl
      _ = b := Equiv.swap_apply_left _ _

theorem card_filter_pair_eq_moved (c : Fin n → α) (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ((rearr c).filter fun μ => μ a ≠ μ b).card =
      ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card := by
  classical
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_apply_zero_one hn hab
  refine Finset.card_bij (fun μ _ => μ ∘ σ) ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_filter] at hμ ⊢
    refine ⟨comp_mem_rearr hμ.1 σ, ?_⟩
    intro h
    exact hμ.2 (by simpa [Function.comp_apply, hσ0, hσ1] using h)
  · intro μ₁ _ μ₂ _ h
    funext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    exact congrFun h y
  · intro ν hν
    refine ⟨ν ∘ (σ.symm : Fin n → Fin n), ?_, ?_⟩
    · simp only [Finset.mem_filter] at hν ⊢
      have h0 : σ.symm a = ⟨0, by omega⟩ := by
        apply σ.injective
        rw [Equiv.apply_symm_apply, hσ0]
      have h1 : σ.symm b = ⟨1, by omega⟩ := by
        apply σ.injective
        rw [Equiv.apply_symm_apply, hσ1]
      refine ⟨comp_mem_rearr hν.1 σ.symm, ?_⟩
      intro h
      exact hν.2 (by simpa [Function.comp_apply, h0, h1] using h)
    · ext x
      simp

theorem sum_card_filter_pair_ne (c : Fin n → α) (hn : 2 ≤ n) :
    (∑ μ ∈ rearr c, (univ.filter fun p : Fin n × Fin n => μ p.1 ≠ μ p.2).card) =
      ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * (n * (n - 1)) := by
  classical
  let P : Finset (Fin n × Fin n) := (univ : Finset (Fin n)).offDiag
  have hPmem : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    exact (Finset.mem_offDiag.mp hp).2.2
  have hPcard : P.card = n * (n - 1) := by
    rw [show P = (univ : Finset (Fin n)).offDiag from rfl, Finset.offDiag_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.mul_sub_left_distrib]
    simp
  have hstep : ∀ μ : Fin n → α,
      (univ.filter fun p : Fin n × Fin n => μ p.1 ≠ μ p.2).card =
        ∑ p ∈ P, if μ p.1 ≠ μ p.2 then (1 : ℕ) else 0 := by
    intro μ
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine (Finset.sum_subset (s₁ := P) (s₂ := (univ : Finset (Fin n × Fin n)))
      (subset_univ P) ?_).symm
    intro p _ hp
    have hpp : p.1 = p.2 := by
      by_contra h
      exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, h⟩)
    simp [hpp]
  have hinner : ∀ p ∈ P,
      (∑ μ ∈ rearr c, if μ p.1 ≠ μ p.2 then (1 : ℕ) else 0) =
        ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card := by
    intro p hp
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
      card_filter_pair_eq_moved c hn (hPmem p hp)]
  calc
    (∑ μ ∈ rearr c, (univ.filter fun p : Fin n × Fin n => μ p.1 ≠ μ p.2).card)
        = ∑ μ ∈ rearr c, ∑ p ∈ P, if μ p.1 ≠ μ p.2 then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro μ _
          exact hstep μ
    _ = ∑ p ∈ P, ∑ μ ∈ rearr c, if μ p.1 ≠ μ p.2 then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ p ∈ P, ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hinner p hp
    _ = P.card * ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * P.card :=
          Nat.mul_comm _ _
    _ = ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * (n * (n - 1)) := by
          simp [hPcard]
  rfl

theorem card_moved_rearr_mul (c : Fin n → α) (hn : 2 ≤ n) :
    ((rearr c).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * (n * (n - 1)) =
      (rearr c).card * (n ^ 2 - ∑ i ∈ univ.image c, (univ.filter fun a => c a = i).card ^ 2) := by
  classical
  rw [← sum_card_filter_pair_ne c hn]
  have hstep : ∀ μ ∈ rearr c,
      (univ.filter fun p : Fin n × Fin n => μ p.1 ≠ μ p.2).card =
        n ^ 2 - ∑ i ∈ univ.image c, (univ.filter fun a => c a = i).card ^ 2 := by
    intro μ hμ
    obtain ⟨σ, rfl⟩ := mem_rearr.mp hμ
    rw [card_filter_pair_ne (c ∘ σ)]
    congr 1
    exact sum_sq_fiber_comp_perm c σ
  calc
    (∑ μ ∈ rearr c, (univ.filter fun p : Fin n × Fin n => μ p.1 ≠ μ p.2).card)
        = ∑ μ ∈ rearr c,
            (n ^ 2 - ∑ i ∈ univ.image c, (univ.filter fun a => c a = i).card ^ 2) := by
          apply Finset.sum_congr rfl
          exact hstep
    _ = (rearr c).card *
          (n ^ 2 - ∑ i ∈ univ.image c, (univ.filter fun a => c a = i).card ^ 2) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]

theorem card_moved_rearr_mul_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    (f : Fin n → β) (hn : 2 ≤ n) :
    ((rearr f).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * (n * (n - 1)) =
      (rearr f).card * (n ^ 2 - ∑ b : β, (univ.filter fun a => f a = b).card ^ 2) := by
  rw [card_moved_rearr_mul f hn]
  congr 1
  congr 1
  refine Finset.sum_subset (s₁ := univ.image f) (s₂ := (univ : Finset β))
    (f := fun b : β => (univ.filter fun a => f a = b).card ^ 2) (subset_univ _) ?_
  intro b _ hb
  have hempty : (univ.filter fun a => f a = b) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro a _ h
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, h⟩)
  rw [hempty, Finset.card_empty]
  simp

@[expose] def topWt (S : Finset (Fin n)) : Fin n → ℤ :=
  fun a => ((S.filter fun j => a < j).card : ℤ)

@[expose] def blocks (S : Finset (Fin n)) : Fin (S.card + 1) → ℕ :=
  fun i => (univ.filter fun a => topWt S a = (i : ℤ)).card

def blockIndex (S : Finset (Fin n)) (a : Fin n) : Fin (S.card + 1) :=
  ⟨(topWt S a).toNat, by
    have hnonneg : 0 ≤ topWt S a := by rw [topWt]; exact Int.natCast_nonneg _
    have hle : topWt S a ≤ (S.card : ℤ) := by
      rw [topWt]
      exact_mod_cast Finset.card_filter_le S (fun j => a < j)
    have hle' : ((topWt S a).toNat : ℤ) ≤ (S.card : ℤ) := by
      rwa [Int.toNat_of_nonneg hnonneg]
    omega⟩

lemma coe_blockIndex (S : Finset (Fin n)) (a : Fin n) :
    (blockIndex S a : ℤ) = topWt S a := by
  rw [blockIndex, Fin.val_mk, Int.toNat_of_nonneg]
  rw [topWt]
  exact Int.natCast_nonneg _

lemma blockIndex_eq_iff (S : Finset (Fin n)) (a : Fin n) (i : Fin (S.card + 1)) :
    blockIndex S a = i ↔ topWt S a = (i : ℤ) := by
  constructor
  · intro h
    rw [← coe_blockIndex, h]
  · intro h
    apply Fin.ext
    have h1 : ((blockIndex S a).val : ℤ) = (i.val : ℤ) := by
      rw [show (blockIndex S a).val = (topWt S a).toNat from rfl,
        Int.toNat_of_nonneg (by rw [topWt]; exact Int.natCast_nonneg _), h]
    omega

lemma blocks_eq_filter_blockIndex (S : Finset (Fin n)) (i : Fin (S.card + 1)) :
    blocks S i = (univ.filter fun a => blockIndex S a = i).card := by
  rw [blocks]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact (blockIndex_eq_iff S a i).symm

theorem sum_blocks (S : Finset (Fin n)) : ∑ i, blocks S i = n := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin (S.card + 1))))
    (g := blockIndex S)
  have hfilter : (univ.filter fun a => blockIndex S a ∈
      (univ : Finset (Fin (S.card + 1)))) = univ := by
    apply Finset.filter_true_of_mem
    intro a _
    simp
  rw [hfilter] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp_rw [blocks_eq_filter_blockIndex]
  exact h

lemma exists_blockIndex_eq (S : Finset (Fin n)) (hn : 0 < n)
    (h0 : (⟨0, hn⟩ : Fin n) ∉ S) (i : Fin (S.card + 1)) :
    ∃ a : Fin n, blockIndex S a = i := by
  classical
  by_cases hi : (i : ℕ) = S.card
  · refine ⟨⟨0, hn⟩, ?_⟩
    apply Fin.ext
    have htop : topWt S ⟨0, hn⟩ = (S.card : ℤ) := by
      rw [topWt]
      congr 1
      have hfilter : S.filter (fun j => (⟨0, hn⟩ : Fin n) < j) = S := by
        apply Finset.filter_true_of_mem
        intro j hj
        have hne : j ≠ (⟨0, hn⟩ : Fin n) := by
          intro h
          exact h0 (h ▸ hj)
        by_contra h
        exact hne (by
          apply Fin.ext
          exact Nat.eq_zero_of_not_pos h)
      rw [hfilter]
    rw [show (blockIndex S ⟨0, hn⟩).val = (topWt S ⟨0, hn⟩).toNat from rfl,
      htop, Int.toNat_natCast, hi]
  · have hlt : (i : ℕ) < S.card := lt_of_le_of_ne (Fin.is_le i) hi
    let t : Fin S.card := ⟨S.card - 1 - (i : ℕ), by omega⟩
    let a : Fin n := S.orderEmbOfFin rfl t
    refine ⟨a, ?_⟩
    apply Fin.ext
    have htop : topWt S a = (i : ℤ) := by
      rw [topWt]
      congr 1
      have hfilter : S.filter (fun j => a < j) =
          (univ.filter fun s : Fin S.card => t < s).image (S.orderEmbOfFin rfl) := by
        ext j
        constructor
        · intro hj
          obtain ⟨hjS, hja⟩ := Finset.mem_filter.mp hj
          have hjrange : j ∈ Set.range (S.orderEmbOfFin rfl) := by
            rwa [Finset.range_orderEmbOfFin]
          obtain ⟨s, rfl⟩ := hjrange
          refine Finset.mem_image.mpr ⟨s, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (S.orderEmbOfFin rfl).lt_iff_lt.mp hja
        · rw [Finset.mem_image]
          rintro ⟨s, hs, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem (k := S.card) rfl s,
            (S.orderEmbOfFin rfl).lt_iff_lt.mpr hs⟩
      have hcard : (S.filter fun j => a < j).card = i.val := by
        rw [hfilter, Finset.card_image_of_injective _ (S.orderEmbOfFin rfl).injective]
        rw [show (univ.filter fun s : Fin S.card => t < s) = Finset.Ioi t by
          ext s; simp [Finset.mem_Ioi]]
        rw [Fin.card_Ioi]
        have ht : t.val = S.card - 1 - i.val := rfl
        omega
      rw [hcard]
    rw [show (blockIndex S a).val = (topWt S a).toNat from rfl, htop,
      Int.toNat_natCast]

theorem blocks_pos {S : Finset (Fin n)} (hn : 0 < n)
    (h0 : (⟨0, hn⟩ : Fin n) ∉ S) (i : Fin (S.card + 1)) :
    0 < blocks S i := by
  obtain ⟨a, ha⟩ := exists_blockIndex_eq S hn h0 i
  rw [blocks_eq_filter_blockIndex]
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

lemma rearr_comp_injective {β : Type*} [DecidableEq β] (f : Fin n → α) (e : α → β) :
    rearr (fun a => e (f a)) = (rearr f).image (fun ν a => e (ν a)) := by
  ext μ
  constructor
  · intro hμ
    rw [mem_rearr] at hμ
    obtain ⟨σ, rfl⟩ := hμ
    exact Finset.mem_image.mpr ⟨f ∘ σ, mem_rearr.mpr ⟨σ, rfl⟩, by ext a; rfl⟩
  · rw [Finset.mem_image]
    rintro ⟨ν, hν, rfl⟩
    rw [mem_rearr] at hν ⊢
    obtain ⟨σ, rfl⟩ := hν
    exact ⟨σ, by ext a; rfl⟩

lemma card_rearr_comp_injective {β : Type*} [DecidableEq β] (f : Fin n → α) (e : α → β)
    (he : Function.Injective e) :
    (rearr (fun a => e (f a))).card = (rearr f).card := by
  rw [rearr_comp_injective f e, Finset.card_image_of_injective _ ?_]
  intro ν₁ ν₂ h
  funext a
  exact he (congrFun h a)

lemma card_moved_rearr_comp_injective {β : Type*} [DecidableEq β] (f : Fin n → α) (e : α → β)
    (he : Function.Injective e) (hn : 2 ≤ n) :
    ((rearr (fun a => e (f a))).filter fun μ =>
        μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card =
      ((rearr f).filter fun ν => ν ⟨0, by omega⟩ ≠ ν ⟨1, by omega⟩).card := by
  classical
  symm
  let Φ : (Fin n → α) → (Fin n → β) := fun ν a => e (ν a)
  refine Finset.card_bij (fun (ν : Fin n → α) _ => Φ ν) ?_ ?_ ?_
  · intro ν hν
    simp only [Finset.mem_filter] at hν ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_rearr] at hν ⊢
      obtain ⟨σ, rfl⟩ := hν.1
      exact ⟨σ, by ext a; rfl⟩
    · intro h
      exact hν.2 (he h)
  · intro ν₁ _ ν₂ _ h
    funext a
    exact he (congrFun h a)
  · intro μ hμ
    simp only [Finset.mem_filter] at hμ ⊢
    rw [mem_rearr] at hμ
    obtain ⟨σ, rfl⟩ := hμ.1
    refine ⟨f ∘ σ, ?_, by ext a; rfl⟩
    refine ⟨?_, ?_⟩
    · exact mem_rearr.mpr ⟨σ, rfl⟩
    · intro h
      exact hμ.2 (by simpa using congrArg e h)

theorem card_rearr_topWt (S : Finset (Fin n)) :
    (rearr (topWt S)).card = Nat.multinomial univ (blocks S) := by
  classical
  let c' : Fin n → Fin (S.card + 1) := blockIndex S
  have htop : topWt S = fun a => (c' a : ℤ) := by
    funext a
    exact (coe_blockIndex S a).symm
  have hcard : (rearr (topWt S)).card = (rearr c').card := by
    rw [htop]
    exact card_rearr_comp_injective c' (fun x : Fin (S.card + 1) => (x : ℤ))
      (fun x y h => Fin.ext (Int.ofNat_injective h))
  have hstab := card_rearr_mul_prod_factorial_of_fintype c'
  have hblocks : (∏ b : Fin (S.card + 1),
      (univ.filter fun a => c' a = b).card.factorial) =
      ∏ i, (blocks S i).factorial := by
    apply Finset.prod_congr rfl
    intro i _
    rw [blocks_eq_filter_blockIndex]
  rw [hblocks] at hstab
  have hmult := Nat.multinomial_spec (s := (univ : Finset (Fin (S.card + 1))))
    (f := blocks S)
  rw [sum_blocks S] at hmult
  have hPpos : 0 < ∏ i : Fin (S.card + 1), (blocks S i).factorial :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have heq : (rearr c').card * (∏ i : Fin (S.card + 1), (blocks S i).factorial) =
      Nat.multinomial univ (blocks S) *
        (∏ i : Fin (S.card + 1), (blocks S i).factorial) := by
    rw [hstab, ← hmult, mul_comm]
  have hcancel := Nat.mul_right_cancel hPpos heq
  rw [hcard, hcancel]

theorem card_moved_rearr_topWt (S : Finset (Fin n)) (hn : 2 ≤ n) :
    ((rearr (topWt S)).filter fun μ =>
        μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card * (n * (n - 1)) =
      Nat.multinomial univ (blocks S) * (n ^ 2 - ∑ i, blocks S i ^ 2) := by
  classical
  let c' : Fin n → Fin (S.card + 1) := blockIndex S
  have htop : topWt S = fun a => (c' a : ℤ) := by
    funext a
    exact (coe_blockIndex S a).symm
  have hmoved : ((rearr (topWt S)).filter fun μ =>
      μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card =
      ((rearr c').filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card := by
    rw [htop]
    exact card_moved_rearr_comp_injective c' (fun x : Fin (S.card + 1) => (x : ℤ))
      (fun x y h => Fin.ext (Int.ofNat_injective h)) hn
  have hcard : (rearr (topWt S)).card = (rearr c').card := by
    rw [htop]
    exact card_rearr_comp_injective c' (fun x : Fin (S.card + 1) => (x : ℤ))
      (fun x y h => Fin.ext (Int.ofNat_injective h))
  have hsum : (∑ i : Fin (S.card + 1), (univ.filter fun a => c' a = i).card ^ 2) =
      ∑ i : Fin (S.card + 1), (blocks S i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [blocks_eq_filter_blockIndex]
  have hmain := card_moved_rearr_mul_of_fintype c' hn
  rw [← hmoved, ← hcard, hsum] at hmain
  rw [card_rearr_topWt S] at hmain
  exact hmain

lemma topWt_pair_eq (a b x : Fin n) (hab : a < b) :
    topWt ({a, b} : Finset (Fin n)) x =
      (if x < a then 2 else if x < b then 1 else 0 : ℤ) := by
  rw [topWt]
  by_cases hxa : x < a
  · have hxb : x < b := lt_trans hxa hab
    rw [if_pos hxa]
    have hf : ({a, b} : Finset (Fin n)).filter (fun j => x < j) = {a, b} := by
      apply Finset.filter_true_of_mem
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hxa
      · exact hxb
    rw [hf, Finset.card_pair hab.ne]
    norm_num
  · rw [if_neg hxa]
    by_cases hxb : x < b
    · rw [if_pos hxb]
      have hf : ({a, b} : Finset (Fin n)).filter (fun j => x < j) = {b} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hj, hlt⟩
          rcases hj with rfl | rfl
          · exact absurd hlt hxa
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, hxb⟩
      rw [hf, Finset.card_singleton]
      norm_num
    · rw [if_neg hxb]
      have hf : ({a, b} : Finset (Fin n)).filter (fun j => x < j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hxa
        · exact hxb
      rw [hf, Finset.card_empty]
      norm_num

lemma topWt_pair_eq_zero (a b x : Fin n) (hab : a < b) :
    topWt ({a, b} : Finset (Fin n)) x = 0 ↔ b ≤ x := by
  rw [topWt_pair_eq a b x hab]
  by_cases hxa : x < a
  · have hxb : x < b := lt_trans hxa hab
    simp [hxa, not_le_of_gt hxb]
  · by_cases hxb : x < b
    · simp [hxa, not_le_of_gt hxb]
    · have hbx : b ≤ x := le_of_not_gt hxb
      simp [hxa, hxb, hbx]

lemma topWt_pair_eq_one (a b x : Fin n) (hab : a < b) :
    topWt ({a, b} : Finset (Fin n)) x = 1 ↔ a ≤ x ∧ x < b := by
  rw [topWt_pair_eq a b x hab]
  by_cases hxa : x < a
  · have hxb : x < b := lt_trans hxa hab
    have hnot : ¬ a ≤ x := not_le_of_gt hxa
    simp [hxa, hxb]
  · by_cases hxb : x < b
    · have hax : a ≤ x := le_of_not_gt hxa
      simp [hxa, hxb, hax]
    · have hnot : ¬ (a ≤ x ∧ x < b) := fun h => hxb h.2
      simp [hxa, hxb]

lemma topWt_pair_eq_two (a b x : Fin n) (hab : a < b) :
    topWt ({a, b} : Finset (Fin n)) x = 2 ↔ x < a := by
  rw [topWt_pair_eq a b x hab]
  by_cases hxa : x < a
  · simp [hxa]
  · by_cases hxb : x < b <;> simp [hxa, hxb]

lemma blocks_pair_zero (a b : Fin n) (hab : a < b) :
    blocks ({a, b} : Finset (Fin n)) ⟨0, by
      rw [Finset.card_pair hab.ne]; omega⟩ = n - b := by
  rw [blocks_eq_filter_blockIndex]
  have hf : (univ.filter fun x : Fin n => blockIndex {a, b} x = ⟨0, by
      rw [Finset.card_pair hab.ne]; omega⟩) = Finset.Ici b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rw [blockIndex_eq_iff]
    simpa using topWt_pair_eq_zero a b x hab
  rw [hf, Fin.card_Ici]

lemma blocks_pair_one (a b : Fin n) (hab : a < b) :
    blocks ({a, b} : Finset (Fin n)) ⟨1, by
      rw [Finset.card_pair hab.ne]; omega⟩ = b - a := by
  rw [blocks_eq_filter_blockIndex]
  have hf : (univ.filter fun x : Fin n => blockIndex {a, b} x = ⟨1, by
      rw [Finset.card_pair hab.ne]; omega⟩) = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    rw [blockIndex_eq_iff]
    simpa using topWt_pair_eq_one a b x hab
  rw [hf, Fin.card_Ico]

lemma blocks_pair_two (a b : Fin n) (hab : a < b) :
    blocks ({a, b} : Finset (Fin n)) ⟨2, by
      rw [Finset.card_pair hab.ne]; omega⟩ = a := by
  rw [blocks_eq_filter_blockIndex]
  have hf : (univ.filter fun x : Fin n => blockIndex {a, b} x = ⟨2, by
      rw [Finset.card_pair hab.ne]; omega⟩) = Finset.Iio a := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [blockIndex_eq_iff]
    simpa using topWt_pair_eq_two a b x hab
  rw [hf, Fin.card_Iio]

lemma pair_eq_pair_of_lt {a b c d : Fin n} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Finset (Fin n)) = {c, d}) : a = c ∧ b = d := by
  have ha : a ∈ ({c, d} : Finset (Fin n)) := by
    rw [← h]
    exact Finset.mem_insert_self a {b}
  have hb : b ∈ ({c, d} : Finset (Fin n)) := by
    rw [← h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · omega
  · exact ⟨rfl, rfl⟩
  · omega
  · omega

lemma exists_fin_three {p : Fin 3 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all
  · rintro (h | h | h) <;> exact ⟨_, h⟩

lemma pair_eq_pair_of_eq {a b c d : Fin n} (ha : a = c) (hb : b = d) :
    ({a, b} : Finset (Fin n)) = {c, d} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ha
    · exact Or.inr hb
  · rintro (rfl | rfl)
    · exact Or.inl ha.symm
    · exact Or.inr hb.symm

lemma exists_blocks_pair_eq_sub_two_iff {a b : Fin n} (hn : 4 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ ({a, b} : Finset (Fin n))) (hab : a < b) :
    (∃ i, blocks ({a, b} : Finset (Fin n)) i = n - 2) ↔
      ({a, b} = ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) ∨
        {a, b} = ({⟨1, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) ∨
        {a, b} = ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n))) := by
  classical
  have hcard : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair hab.ne
  have hcard3 : ({a, b} : Finset (Fin n)).card + 1 = 3 := by omega
  let e : Fin (({a, b} : Finset (Fin n)).card + 1) ≃ Fin 3 := finCongr hcard3
  have hi0 : e.symm (0 : Fin 3) =
      (⟨0, by rw [Finset.card_pair hab.ne]; omega⟩ : Fin (({a, b} : Finset (Fin n)).card + 1)) := by
    apply Fin.ext
    rfl
  have hi1 : e.symm (1 : Fin 3) =
      (⟨1, by rw [Finset.card_pair hab.ne]; omega⟩ : Fin (({a, b} : Finset (Fin n)).card + 1)) := by
    apply Fin.ext
    rfl
  have hi2 : e.symm (2 : Fin 3) =
      (⟨2, by rw [Finset.card_pair hab.ne]; omega⟩ : Fin (({a, b} : Finset (Fin n)).card + 1)) := by
    apply Fin.ext
    rfl
  have hex : (∃ i : Fin (({a, b} : Finset (Fin n)).card + 1),
        blocks ({a, b}) i = n - 2) ↔
      (blocks ({a, b}) (e.symm (0 : Fin 3)) = n - 2 ∨
        blocks ({a, b}) (e.symm (1 : Fin 3)) = n - 2 ∨
        blocks ({a, b}) (e.symm (2 : Fin 3)) = n - 2) := by
    constructor
    · rintro ⟨i, hi⟩
      have h := (exists_fin_three (p := fun k : Fin 3 =>
        blocks ({a, b} : Finset (Fin n)) (e.symm k) = n - 2)).mp ⟨e i, by simpa using hi⟩
      simpa using h
    · rintro (h | h | h)
      · exact ⟨_, by simpa using h⟩
      · exact ⟨_, by simpa using h⟩
      · exact ⟨_, by simpa using h⟩
  rw [hex, hi0, hi1, hi2, blocks_pair_zero a b hab, blocks_pair_one a b hab,
    blocks_pair_two a b hab]
  clear hex hi0 hi1 hi2 e
  have hb_lt : (b : ℕ) < n := b.isLt
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have ha_pos : 0 < (a : ℕ) := by
    have hne : a ≠ (⟨0, by omega⟩ : Fin n) := by
      intro h
      apply h0
      rw [h]
      simp
    by_contra h
    exact hne (by
      apply Fin.ext
      exact Nat.eq_zero_of_not_pos h)
  constructor
  · rintro (h | h | h)
    · have hbval : (b : ℕ) = 2 := by omega
      have haval : (a : ℕ) = 1 := by omega
      have hb : b = (⟨2, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact hbval
      have ha : a = (⟨1, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact haval
      exact Or.inl (pair_eq_pair_of_eq ha hb)
    · have hbval : (b : ℕ) = n - 1 := by omega
      have haval : (a : ℕ) = 1 := by omega
      have hb : b = (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact hbval
      have ha : a = (⟨1, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact haval
      exact Or.inr (Or.inl (pair_eq_pair_of_eq ha hb))
    · have haval : (a : ℕ) = n - 2 := by omega
      have hbval : (b : ℕ) = n - 1 := by omega
      have ha : a = (⟨n - 2, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact haval
      have hb : b = (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        exact hbval
      exact Or.inr (Or.inr (pair_eq_pair_of_eq ha hb))
  · rintro (h | h | h)
    · have hlt : (⟨1, by omega⟩ : Fin n) < (⟨2, by omega⟩ : Fin n) := by
        apply Fin.lt_def.mpr
        simp
      have hp := pair_eq_pair_of_lt hab hlt h
      have ha := hp.1
      have hb := hp.2
      left
      have hbval : (b : ℕ) = 2 := by simpa using congrArg Fin.val hb
      omega
    · have hlt : (⟨1, by omega⟩ : Fin n) < (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.lt_def.mpr
        simp
        omega
      have hp := pair_eq_pair_of_lt hab hlt h
      have ha := hp.1
      have hb := hp.2
      right; left
      have hbval : (b : ℕ) = n - 1 := by simpa using congrArg Fin.val hb
      have haval : (a : ℕ) = 1 := by simpa using congrArg Fin.val ha
      omega
    · have hlt : (⟨n - 2, by omega⟩ : Fin n) < (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.lt_def.mpr
        simp
        omega
      have hp := pair_eq_pair_of_lt hab hlt h
      have ha := hp.1
      right; right
      have haval : (a : ℕ) = n - 2 := by simpa using congrArg Fin.val ha
      omega

theorem exists_blocks_eq_sub_two_iff {S : Finset (Fin n)} (hn : 4 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hS : S.card = 2) :
    (∃ i, blocks S i = n - 2) ↔
      S = {⟨1, by omega⟩, ⟨2, by omega⟩} ∨
        S = {⟨1, by omega⟩, ⟨n - 1, by omega⟩} ∨
        S = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} := by
  classical
  let e := S.orderEmbOfFin hS
  let a : Fin n := e 0
  let b : Fin n := e 1
  have hab : a < b := by
    apply e.strictMono
    exact (by decide : (0 : Fin 2) < 1)
  have hS_eq : S = {a, b} := by
    rw [← Finset.image_orderEmbOfFin_univ S hS]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by omega⟩, rfl⟩
      · exact ⟨⟨1, by omega⟩, rfl⟩
  rw [hS_eq] at h0 ⊢
  exact exists_blocks_pair_eq_sub_two_iff hn h0 hab

lemma topWt_singleton (j a : Fin n) :
    topWt ({j} : Finset (Fin n)) a = (if a < j then 1 else 0 : ℤ) := by
  rw [topWt]
  by_cases h : a < j
  · rw [if_pos h]
    have hf : ({j} : Finset (Fin n)).filter (fun k => a < k) = {j} := by
      apply Finset.filter_true_of_mem
      intro k hk
      simp only [Finset.mem_singleton] at hk
      rwa [hk]
    rw [hf, Finset.card_singleton]
    norm_num
  · rw [if_neg h]
    have hf : ({j} : Finset (Fin n)).filter (fun k => a < k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_singleton] at hk
      rwa [hk]
    rw [hf, Finset.card_empty]
    norm_num

lemma blocks_singleton_zero (j : Fin n) :
    blocks ({j} : Finset (Fin n)) ⟨0, by omega⟩ = n - j := by
  rw [blocks_eq_filter_blockIndex]
  have hf : (univ.filter fun a : Fin n => blockIndex {j} a = ⟨0, by omega⟩) =
      Finset.Ici j := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rw [blockIndex_eq_iff]
    by_cases h : a < j
    · have h' : ¬ j ≤ a := not_le_of_gt h
      simp [topWt_singleton, h, h']
    · have h' : j ≤ a := le_of_not_gt h
      simp [topWt_singleton, h, h']
  rw [hf, Fin.card_Ici]

lemma blocks_singleton_one (j : Fin n) :
    blocks ({j} : Finset (Fin n)) ⟨1, by
      have : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
      omega⟩ = j := by
  rw [blocks_eq_filter_blockIndex]
  have hf : (univ.filter fun a : Fin n => blockIndex {j} a = ⟨1, by
      have : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
      omega⟩) = Finset.Iio j := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [blockIndex_eq_iff]
    by_cases h : a < j <;> simp [topWt_singleton, h]
  rw [hf, Fin.card_Iio]

lemma blocks_singleton_univ (j : Fin n) :
    (univ : Finset (Fin (({j} : Finset (Fin n)).card + 1))) =
      {(⟨0, by omega⟩ : Fin (({j} : Finset (Fin n)).card + 1)),
        (⟨1, by
          have : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
          omega⟩ : Fin (({j} : Finset (Fin n)).card + 1))} := by
  have hcard : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
  ext i
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · left; rfl
  · right
    apply Fin.ext
    have hk : (k : ℕ) = 0 := by
      have := k.isLt
      omega
    simp [hk]

lemma multinomial_blocks_singleton (j : Fin n) :
    Nat.multinomial univ (blocks ({j} : Finset (Fin n))) = n.choose j := by
  let i0 : Fin (({j} : Finset (Fin n)).card + 1) := ⟨0, by omega⟩
  let i1 : Fin (({j} : Finset (Fin n)).card + 1) :=
    ⟨1, by
      have : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
      omega⟩
  have h0 : blocks ({j} : Finset (Fin n)) i0 = n - j := blocks_singleton_zero j
  have h1 : blocks ({j} : Finset (Fin n)) i1 = j := blocks_singleton_one j
  have huniv : (univ : Finset (Fin (({j} : Finset (Fin n)).card + 1))) = {i0, i1} := by
    simpa [i0, i1] using blocks_singleton_univ j
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  rw [Nat.multinomial, huniv, Finset.sum_pair hne, Finset.prod_pair hne, h0, h1]
  rw [Nat.sub_add_cancel j.isLt.le, Nat.choose_eq_factorial_div_factorial j.isLt.le]
  congr 1
  rw [Nat.mul_comm]

lemma sum_sq_blocks_singleton (j : Fin n) :
    (∑ i : Fin (({j} : Finset (Fin n)).card + 1), blocks ({j}) i ^ 2) =
      (n - j) ^ 2 + j ^ 2 := by
  let i0 : Fin (({j} : Finset (Fin n)).card + 1) := ⟨0, by omega⟩
  let i1 : Fin (({j} : Finset (Fin n)).card + 1) :=
    ⟨1, by
      have : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
      omega⟩
  have h0 : blocks ({j} : Finset (Fin n)) i0 = n - j := blocks_singleton_zero j
  have h1 : blocks ({j} : Finset (Fin n)) i1 = j := blocks_singleton_one j
  have huniv : (univ : Finset (Fin (({j} : Finset (Fin n)).card + 1))) = {i0, i1} := by
    simpa [i0, i1] using blocks_singleton_univ j
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  rw [huniv, Finset.sum_pair hne, h0, h1]

theorem card_rearr_topWt_singleton (j : Fin n) :
    (rearr (topWt {j})).card = n.choose j := by
  rw [card_rearr_topWt, multinomial_blocks_singleton]

theorem card_moved_rearr_topWt_singleton (hn : 2 ≤ n) (j : Fin n) (hj : 1 ≤ (j : ℕ)) :
    ((rearr (topWt {j})).filter fun μ =>
        μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card = 2 * (n - 2).choose (j - 1) := by
  classical
  have hmain := card_moved_rearr_topWt ({j} : Finset (Fin n)) hn
  rw [multinomial_blocks_singleton, sum_sq_blocks_singleton] at hmain
  have hsq : n ^ 2 - ((n - j) ^ 2 + j ^ 2) = 2 * (n - j) * j := by
    have h' : n ^ 2 = 2 * (n - j) * j + ((n - j) ^ 2 + j ^ 2) := by
      nlinarith [Nat.sub_add_cancel j.isLt.le]
    exact Nat.sub_eq_of_eq_add h'
  rw [hsq] at hmain
  have hid : Nat.choose n j * (j * (n - j)) =
      Nat.choose (n - 2) (j - 1) * (n * (n - 1)) := by
    have h1 : n * Nat.choose (n - 1) (j - 1) = Nat.choose n j * j := by
      have := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
      have hsub1 : (n - 1) + 1 = n := by omega
      have hsub2 : ((j : ℕ) - 1) + 1 = (j : ℕ) := by omega
      rw [hsub1, hsub2] at this
      exact this
    have h2 : Nat.choose (n - 1) (j - 1) * (n - j) =
        Nat.choose (n - 2) (j - 1) * (n - 1) := by
      have := Nat.choose_mul_succ_eq (n - 2) (j - 1)
      have hsub1 : (n - 2) + 1 = n - 1 := by omega
      have hsub2 : n - 1 - ((j : ℕ) - 1) = n - (j : ℕ) := by omega
      rw [hsub1, hsub2] at this
      exact this.symm
    calc Nat.choose n j * (j * (n - j))
        = (Nat.choose n j * j) * (n - j) := by ring
      _ = (n * Nat.choose (n - 1) (j - 1)) * (n - j) := by rw [← h1]
      _ = n * (Nat.choose (n - 1) (j - 1) * (n - j)) := by ring
      _ = n * (Nat.choose (n - 2) (j - 1) * (n - 1)) := by rw [h2]
      _ = Nat.choose (n - 2) (j - 1) * (n * (n - 1)) := by ring
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.mul_right_cancel hpos
  rw [hmain]
  calc Nat.choose n j * (2 * (n - j) * j)
      = 2 * (Nat.choose n j * (j * (n - j))) := by ring
    _ = 2 * (Nat.choose (n - 2) (j - 1) * (n * (n - 1))) := by rw [hid]
    _ = (2 * Nat.choose (n - 2) (j - 1)) * (n * (n - 1)) := by ring

theorem card_piFinset_moved {τ : Type*} [Fintype τ] [DecidableEq τ]
    (O : τ → Finset (Fin n → α)) (π : Equiv.Perm (Fin n)) :
    ((Fintype.piFinset O).filter fun μ => ∃ r, μ r ∘ π ≠ μ r).card +
        ∏ r, ((O r).filter fun μ => μ ∘ π = μ).card =
      ∏ r, (O r).card := by
  classical
  let P := Fintype.piFinset O
  let M := P.filter fun μ => ∃ r, μ r ∘ π ≠ μ r
  let F := P.filter fun μ => ∀ r, μ r ∘ π = μ r
  have hsplit : M.card + F.card = P.card := by
    have := Finset.card_filter_add_card_filter_not (s := P)
      (p := fun μ => ∃ r, μ r ∘ π ≠ μ r)
    simpa [M, F] using this
  have hF : F = Fintype.piFinset (fun r => (O r).filter fun μ => μ ∘ π = μ) := by
    ext μ
    simp only [F, P, Fintype.mem_piFinset, Finset.mem_filter]
    constructor
    · rintro ⟨hμ, hfix⟩
      exact fun r => ⟨hμ r, hfix r⟩
    · intro h
      exact ⟨fun r => (h r).1, fun r => (h r).2⟩
  rw [hF, Fintype.card_piFinset] at hsplit
  rw [show P.card = ∏ r, (O r).card from by
    simp [P, Fintype.card_piFinset]] at hsplit
  simpa [M, add_comm] using hsplit

end CFSG.LieType.SpecialLinear.ExteriorModel
