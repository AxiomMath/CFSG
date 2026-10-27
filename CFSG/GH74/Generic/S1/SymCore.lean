module

public import CFSG.GH74.Generic.S1.FrameNorm

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup

variable {F : Type} [Field F]

structure ModelOps (F : Type) [Field F] (S : Subgroup (GL (Fin 4) F)) where
  norm : GL (Fin 4) F → Prop
  norm_conj : ∀ P, norm P → (∀ k ∈ S, P⁻¹ * k * P ∈ S) ∧ (∀ k ∈ S, P * k * P⁻¹ ∈ S)
  std : GL (Fin 4) F → Prop
  to_std : ∀ ρ : GL (Fin 4) F, ρ * ρ = 1 → ((ρ : Matrix (Fin 4) (Fin 4) F)).det = -1 →
    (∀ k ∈ S, ρ * k * ρ⁻¹ ∈ S) → ∃ ρ' : GL (Fin 4) F, (ρ' = ρ ∨ ρ' = -ρ) ∧ std ρ'
  commutant : ∀ M : GL (Fin 4) F, (∀ k ∈ S, M * k = k * M) →
    ∃ c : F, (M : Matrix (Fin 4) (Fin 4) F) = c • (1 : Matrix (Fin 4) (Fin 4) F)
  diag : ∀ ρ : Fin 4 → GL (Fin 4) F, (∀ j, ρ j * ρ j = 1) →
    (∀ j, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1) → (∀ j, std (ρ j)) →
    (∀ j k, ∃ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        c • (((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) →
    (∀ j k, j ≠ k → ∀ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
      c • ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) →
    ∃ (P : GL (Fin 4) F) (ε : Fin 4 → F), norm P ∧ (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, ((P⁻¹ * ρ j * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ε j • ((reflDiag F j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

theorem det_neg_gl (ρ : GL (Fin 4) F) :
    (((-ρ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).det =
      ((ρ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det := by
  rw [Units.val_neg, Matrix.det_neg, Fintype.card_fin]
  norm_num

theorem conj_eq_of_val_eq_smul {g r : GL (Fin 4) F} {ε : F} (hε : ε = 1 ∨ ε = -1)
    (h : (g : Matrix (Fin 4) (Fin 4) F) = ε • (r : Matrix (Fin 4) (Fin 4) F)) (X : GL (Fin 4) F) :
    g * X * g⁻¹ = r * X * r⁻¹ := by
  rcases hε with rfl | rfl
  · have : g = r := Units.ext (by rw [h, one_smul])
    rw [this]
  · have : g = -r := Units.ext (by rw [h, Units.val_neg, neg_one_smul])
    rw [this, neg_conj_eq]

theorem sym_core {C : Type*} [Group C] {K : Subgroup C} {S : Subgroup (GL (Fin 4) F)}
    (ops : ModelOps F S) (e : ↥K ≃* ↥S) (b : Fin 4 → C)
    (hnormal : ∀ j, ∀ n : ↥K, b j * (n : C) * (b j)⁻¹ ∈ K)
    (hrefl : ∀ j, ∃ ρ : GL (Fin 4) F, ρ * ρ = 1 ∧ ((ρ : Matrix (Fin 4) (Fin 4) F)).det = -1 ∧
      ∀ n n' : ↥K, b j * (n : C) * (b j)⁻¹ = (n' : C) →
        ((e n' : ↥S) : GL (Fin 4) F) = ρ * ((e n : ↥S) : GL (Fin 4) F) * ρ⁻¹)
    (hcomm : ∀ j k, b j * b k = b k * b j)
    (hdist : ∀ j k, j ≠ k → ∃ n : ↥K, b j * (n : C) * (b j)⁻¹ ≠ b k * (n : C) * (b k)⁻¹) :
    ∃ e'' : ↥K ≃* ↥S, ∀ j, ∀ n n' : ↥K, b j * (n : C) * (b j)⁻¹ = (n' : C) →
      ((e'' n' : ↥S) : GL (Fin 4) F) = reflDiag F j * ((e'' n : ↥S) : GL (Fin 4) F) * (reflDiag F j)⁻¹ := by
  classical
  choose ρ hρ2 hρdet hρact using hrefl
  let act : Fin 4 → ↥K → ↥K := fun j n => ⟨b j * (n : C) * (b j)⁻¹, hnormal j n⟩
  have hact : ∀ j n, ((e (act j n) : ↥S) : GL (Fin 4) F) =
      ρ j * ((e n : ↥S) : GL (Fin 4) F) * (ρ j)⁻¹ := fun j n => hρact j n (act j n) rfl
  have hρnorm : ∀ j, ∀ k ∈ S, ρ j * k * (ρ j)⁻¹ ∈ S := by
    intro j k hk
    obtain ⟨n, hn⟩ := e.surjective ⟨k, hk⟩
    have := hact j n
    rw [hn] at this
    rw [← this]
    exact (e (act j n)).2
  have hstd : ∀ j, ∃ ρ' : GL (Fin 4) F, (ρ' = ρ j ∨ ρ' = -ρ j) ∧ ops.std ρ' := fun j =>
    ops.to_std (ρ j) (hρ2 j) (hρdet j) (hρnorm j)
  choose ρ' hρ'eq hρ'std using hstd
  have hρ'2 : ∀ j, ρ' j * ρ' j = 1 := by
    intro j
    rcases hρ'eq j with h | h
    · rw [h]; exact hρ2 j
    · rw [h, neg_mul_neg]; exact hρ2 j
  have hρ'det : ∀ j, ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1 := by
    intro j
    rcases hρ'eq j with h | h
    · rw [h]; exact hρdet j
    · rw [h, det_neg_gl]; exact hρdet j
  have hρ'conj : ∀ j (X : GL (Fin 4) F), ρ' j * X * (ρ' j)⁻¹ = ρ j * X * (ρ j)⁻¹ := by
    intro j X
    rcases hρ'eq j with h | h
    · rw [h]
    · rw [h, neg_conj_eq]
  have hact' : ∀ j n, ((e (act j n) : ↥S) : GL (Fin 4) F) =
      ρ' j * ((e n : ↥S) : GL (Fin 4) F) * (ρ' j)⁻¹ := fun j n => by
    rw [hρ'conj, hact]
  have hcommρ : ∀ j k, ∃ c : F, ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        c • (((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
    intro j k
    have hjk : ∀ n : ↥K, act j (act k n) = act k (act j n) := by
      intro n
      apply Subtype.ext
      change b j * (b k * (n : C) * (b k)⁻¹) * (b j)⁻¹ = b k * (b j * (n : C) * (b j)⁻¹) * (b k)⁻¹
      have h1 := hcomm j k
      calc b j * (b k * (n : C) * (b k)⁻¹) * (b j)⁻¹ = (b j * b k) * (n : C) * (b j * b k)⁻¹ := by
            group
        _ = (b k * b j) * (n : C) * (b k * b j)⁻¹ := by rw [h1]
        _ = b k * (b j * (n : C) * (b j)⁻¹) * (b k)⁻¹ := by group
    have hM : ∀ s ∈ S, ((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k)) * s =
        s * ((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k)) := by
      intro s hs
      obtain ⟨n, hn⟩ := e.surjective ⟨s, hs⟩
      have hns : ((e n : ↥S) : GL (Fin 4) F) = s := by rw [hn]
      have h1 : ((e (act j (act k n)) : ↥S) : GL (Fin 4) F) =
          (ρ' j * ρ' k) * s * (ρ' j * ρ' k)⁻¹ := by
        rw [hact', hact', hns]
        group
      have h2 : ((e (act k (act j n)) : ↥S) : GL (Fin 4) F) =
          (ρ' k * ρ' j) * s * (ρ' k * ρ' j)⁻¹ := by
        rw [hact', hact', hns]
        group
      rw [hjk n] at h1
      have h3 : (ρ' j * ρ' k) * s * (ρ' j * ρ' k)⁻¹ = (ρ' k * ρ' j) * s * (ρ' k * ρ' j)⁻¹ :=
        h1.symm.trans h2
      calc ((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k)) * s
          = (ρ' k * ρ' j)⁻¹ * ((ρ' j * ρ' k) * s * (ρ' j * ρ' k)⁻¹) * (ρ' j * ρ' k) := by group
        _ = (ρ' k * ρ' j)⁻¹ * ((ρ' k * ρ' j) * s * (ρ' k * ρ' j)⁻¹) * (ρ' j * ρ' k) := by rw [h3]
        _ = s * ((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k)) := by group
    obtain ⟨c, hc⟩ := ops.commutant _ hM
    refine ⟨c, ?_⟩
    have h1 : ρ' j * ρ' k = (ρ' k * ρ' j) * ((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k)) := by group
    calc ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        = ((ρ' j * ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := (Units.val_mul _ _).symm
      _ = ((ρ' k * ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (((ρ' k * ρ' j)⁻¹ * (ρ' j * ρ' k) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [← Units.val_mul, ← h1]
      _ = c • (((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [hc, Matrix.mul_smul, Matrix.mul_one, Units.val_mul]
  have hinv : ∀ j, (ρ' j)⁻¹ = ρ' j := fun j => inv_eq_of_mul_eq_one_right (hρ'2 j)
  have hneρ : ∀ j k, j ≠ k → ∀ c : F, ((ρ' j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
      c • ((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro j k hjk c hc
    have hc2 : c * c = 1 := by
      have h1 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) (hρ'2 j)
      simp only [Units.val_mul, Units.val_one] at h1
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h1
      have h2 : ((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ' k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
        rw [← Units.val_mul, hρ'2 k, Units.val_one]
      rw [h2] at h1
      have := congrFun (congrFun h1 0) 0
      simpa using this
    have hconjeq : ∀ X : GL (Fin 4) F, ρ' j * X * (ρ' j)⁻¹ = ρ' k * X * (ρ' k)⁻¹ := by
      intro X
      apply Units.ext
      rw [hinv j, hinv k, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hc,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hc2, one_smul]
    obtain ⟨n, hn⟩ := hdist j k hjk
    apply hn
    have h1 := hact' j n
    rw [hconjeq, ← hact' k n] at h1
    exact congrArg Subtype.val (e.injective (Subtype.ext h1))
  obtain ⟨P, ε, hP, hε, hdiag⟩ := ops.diag ρ' hρ'2 hρ'det hρ'std hcommρ hneρ
  obtain ⟨hP1, hP2⟩ := ops.norm_conj P hP
  refine ⟨e.trans (conjEquiv S P hP1 hP2), fun j n n' hn => ?_⟩
  have hn' : n' = act j n := Subtype.ext hn.symm
  rw [hn']
  change P⁻¹ * ((e (act j n) : ↥S) : GL (Fin 4) F) * P =
    reflDiag F j * (P⁻¹ * ((e n : ↥S) : GL (Fin 4) F) * P) * (reflDiag F j)⁻¹
  rw [hact' j n]
  have hg := conj_eq_of_val_eq_smul (hε j) (hdiag j) (P⁻¹ * ((e n : ↥S) : GL (Fin 4) F) * P)
  rw [← hg]
  group

end CFSG.GH74.Generic.S1
