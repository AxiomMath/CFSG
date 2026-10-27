module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

@[expose] def zjVh (Mc : Subgroup H) (t τ l : H) : Subgroup H :=
  Mc ⊔ closure ({t, τ, l} : Set H)

theorem Mc_le_zjVh (Mc : Subgroup H) (t τ l : H) : Mc ≤ zjVh Mc t τ l := le_sup_left

theorem t_mem_zjVh (Mc : Subgroup H) (t τ l : H) : t ∈ zjVh Mc t τ l :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem tau_mem_zjVh (Mc : Subgroup H) (t τ l : H) : τ ∈ zjVh Mc t τ l :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem l_mem_zjVh (Mc : Subgroup H) (t τ l : H) : l ∈ zjVh Mc t τ l :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem card_sup_of_le_normalizer {A B : Subgroup H} (hB : B ≤ normalizer (A : Set H))
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : A × B → ↥(A ⊔ B) := fun x => ⟨x.1 * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h : (a : H) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a' : H)⁻¹ * a = b' * (b : H)⁻¹ := by
        have := congrArg (fun z => (a' : H)⁻¹ * z * (b : H)⁻¹) h
        simpa [mul_assoc] using this
      have hA : (a' : H)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
      have hB : b' * (b : H)⁻¹ ∈ B := B.mul_mem b'.2 (B.inv_mem b.2)
      have hmem : (a' : H)⁻¹ * a ∈ A ⊓ B := ⟨hA, h2 ▸ hB⟩
      rw [hAB, Subgroup.mem_bot] at hmem
      have haeq : (a : H) = (a' : H) := by
        have := congrArg (fun z => (a' : H) * z) hmem
        simpa [mul_assoc] using this
      have hbeq : (b : H) = (b' : H) := by
        have h3 : b' * (b : H)⁻¹ = 1 := by rw [← h2, hmem]
        have := congrArg (fun z => z * (b : H)) h3
        simpa [mul_assoc] using this.symm
      exact Prod.ext (Subtype.ext haeq) (Subtype.ext hbeq)
    · rintro ⟨g, hg⟩
      change g ∈ (↑(A ⊔ B) : Set H) at hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at hg
      rw [Set.mem_mul] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem zj_pow_add_fin {G : Type*} [Group G] (x : G) (hx : x * x = 1)
    (a a' : Fin 2) : x ^ (a : ℕ) * x ^ (a' : ℕ) = x ^ ((a + a' : Fin 2) : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (n := 2) ((a : ℕ) + (a' : ℕ))
      (by simpa [pow_two] using hx), ← Fin.val_add]

theorem zj_mul_three_comm {G : Type*} [Group G] {a₁ a₂ a₃ b₁ b₂ b₃ : G}
    (h31 : Commute a₃ b₁) (h21 : Commute a₂ b₁) (h32 : Commute a₃ b₂) :
    a₁ * a₂ * a₃ * (b₁ * b₂ * b₃) = (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃) := by
  calc a₁ * a₂ * a₃ * (b₁ * b₂ * b₃)
      = a₁ * a₂ * (a₃ * b₁) * b₂ * b₃ := by group
    _ = a₁ * a₂ * (b₁ * a₃) * b₂ * b₃ := by rw [h31.eq]
    _ = a₁ * (a₂ * b₁) * a₃ * b₂ * b₃ := by group
    _ = a₁ * (b₁ * a₂) * a₃ * b₂ * b₃ := by rw [h21.eq]
    _ = a₁ * b₁ * a₂ * (a₃ * b₂) * b₃ := by group
    _ = a₁ * b₁ * a₂ * (b₂ * a₃) * b₃ := by rw [h32.eq]
    _ = (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃) := by group

theorem zj_word_mul {G : Type*} [Group G] {t τ l : G}
    (ht : t * t = 1) (htau : τ * τ = 1) (hl : l * l = 1)
    (htt : t * τ = τ * t) (htl : t * l = l * t) (htaul : τ * l = l * τ)
    (a b c a' b' c' : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) *
      (t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ)) =
    t ^ ((a + a' : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
      l ^ ((c + c' : Fin 2) : ℕ) := by
  have ctl : Commute t l := htl
  have ctt : Commute t τ := htt
  have cτl : Commute τ l := htaul
  rw [zj_mul_three_comm (ctl.symm.pow_pow c a') (ctt.symm.pow_pow b a')
    (cτl.symm.pow_pow c b')]
  rw [zj_pow_add_fin t ht a a', zj_pow_add_fin τ htau b b', zj_pow_add_fin l hl c c']

theorem zj_word_sq {G : Type*} [Group G] {t τ l : G}
    (ht : t * t = 1) (htau : τ * τ = 1) (hl : l * l = 1)
    (htt : t * τ = τ * t) (htl : t * l = l * t) (htaul : τ * l = l * τ)
    (a b c : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) *
      (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) = 1 := by
  rw [zj_word_mul ht htau hl htt htl htaul a b c a b c]
  have ha : (a + a : Fin 2) = 0 := by fin_cases a <;> decide
  have hb : (b + b : Fin 2) = 0 := by fin_cases b <;> decide
  have hc : (c + c : Fin 2) = 0 := by fin_cases c <;> decide
  rw [ha, hb, hc]; simp

theorem zj_word_inv {G : Type*} [Group G] {t τ l : G}
    (ht : t * t = 1) (htau : τ * τ = 1) (hl : l * l = 1)
    (htt : t * τ = τ * t) (htl : t * l = l * t) (htaul : τ * l = l * τ)
    (a b c : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ))⁻¹ =
      t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) :=
  inv_eq_of_mul_eq_one_right (zj_word_sq ht htau hl htt htl htaul a b c)

theorem mem_closure_t_tau_l_iff {G : Type*} [Group G] {t τ l x : G}
    (ht : t * t = 1) (htau : τ * τ = 1) (hl : l * l = 1)
    (htt : t * τ = τ * t) (htl : t * l = l * t) (htaul : τ * l = l * τ) :
    x ∈ closure ({t, τ, l} : Set G) ↔
      ∃ a b c : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) := by
  let W : Subgroup G :=
    { carrier := {x | ∃ a b c : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)}
      one_mem' := ⟨0, 0, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
        exact ⟨a + a', b + b', c + c',
          zj_word_mul ht htau hl htt htl htaul a b c a' b' c'⟩
      inv_mem' := by
        rintro x ⟨a, b, c, rfl⟩
        exact ⟨a, b, c, zj_word_inv ht htau hl htt htl htaul a b c⟩ }
  constructor
  · intro hx
    refine (Subgroup.closure_le (k := ({t, τ, l} : Set G)) W).mpr ?_ hx
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  · rintro ⟨a, b, c, rfl⟩
    have ht' : t ∈ closure ({t, τ, l} : Set G) := Subgroup.subset_closure (by simp)
    have hτ' : τ ∈ closure ({t, τ, l} : Set G) := Subgroup.subset_closure (by simp)
    have hl' : l ∈ closure ({t, τ, l} : Set G) := Subgroup.subset_closure (by simp)
    exact (closure ({t, τ, l} : Set G)).mul_mem
      ((closure ({t, τ, l} : Set G)).mul_mem
        (Subgroup.pow_mem (K := closure ({t, τ, l} : Set G)) ht' (a : ℕ))
        (Subgroup.pow_mem (K := closure ({t, τ, l} : Set G)) hτ' (b : ℕ)))
      (Subgroup.pow_mem (K := closure ({t, τ, l} : Set G)) hl' (c : ℕ))

theorem mem_closure_t_tau_l_iff' {G : Type*} [Group G] {t τ l x : G}
    (ht : t * t = 1) (htau : τ * τ = 1) (hl : l * l = 1)
    (htt : t * τ = τ * t) (htl : t * l = l * t) (htaul : τ * l = l * τ) :
    x ∈ closure ({t, τ, l} : Set G) ↔
      x = 1 ∨ x = t ∨ x = τ ∨ x = t * τ ∨ x = l ∨ x = t * l ∨ x = τ * l ∨
        x = t * τ * l := by
  rw [mem_closure_t_tau_l_iff ht htau hl htt htl htaul]
  constructor
  · rintro ⟨a, b, c, rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, 0, by simp⟩
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨1, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
    · exact ⟨1, 0, 1, by simp⟩
    · exact ⟨0, 1, 1, by simp⟩
    · exact ⟨1, 1, 1, by simp⟩

theorem closure_comm {G : Type*} [Group G] {t τ l x y : G}
    (htt : Commute t τ) (htl : Commute t l) (htaul : Commute τ l)
    (hx : x ∈ closure ({t, τ, l} : Set G)) (hy : y ∈ closure ({t, τ, l} : Set G)) :
    Commute x y := by
  refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact Commute.refl _
        | exact htt
        | exact htt.symm
        | exact htl
        | exact htl.symm
        | exact htaul
        | exact htaul.symm
  · intro x _; exact Commute.one_left x
  · intro x _; exact Commute.one_right x
  · intro x y z _ _ _ hxz hyz; exact hxz.mul_left hyz
  · intro y z x _ _ _ hxy hxz; exact hxy.mul_right hxz
  · intro x y _ _ hxy; exact hxy.inv_left
  · intro x y _ _ hxy; exact hxy.inv_right

theorem fin2_add_eq_zero {a a' : Fin 2} (h : a + a' = 0) : a = a' := by
  revert h
  fin_cases a <;> fin_cases a' <;> decide

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
