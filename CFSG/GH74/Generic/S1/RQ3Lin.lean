module

public import CFSG.GH74.Generic.S1.RQ3Odd
public import CFSG.GH74.Generic.S1.SymBlocksLin
public import CFSG.GH74.Generic.Front.DataLin

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem blkLin_oddGenerated [Finite F] (hodd : Odd (Nat.card F)) (a b : Fin 4) (hab : a ≠ b) :
    OddGenerated (blkLin (F := F) a b) := by
  obtain ⟨e⟩ := blkLin_equiv (F := F) a b hab
  let κ : SL(2, F) →* ↥(StatedSL 4 F) := (blkLin (F := F) a b).subtype.comp e.toMonoidHom
  unfold OddGenerated
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1
  · intro g hg
    obtain ⟨s, hs⟩ := e.surjective ⟨g, hg⟩
    have hgs : g = κ s := by
      change g = ((e s : ↥(blkLin (F := F) a b)) : ↥(StatedSL 4 F))
      rw [hs]
    rw [hgs]
    exact map_mem_closure_of_elementary κ {g | g ∈ blkLin (F := F) a b ∧ Odd (orderOf g)}
      (fun e' he' => ⟨(e e').2, odd_orderOf_map_elementary hodd κ he'⟩) s

theorem isDiagAt_pow {c d : Fin 4} {M : Matrix (Fin 4) (Fin 4) F} (hM : IsDiagAt c d M) (n : ℕ) :
    IsDiagAt c d (M ^ n) ∧ ∀ x : Fin 4, (x = c ∨ x = d) → (M ^ n) x x = (M x x) ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, fun x _ => ?_⟩
    · intro i j hij _
      rw [pow_zero, Matrix.one_apply_ne hij]
    · simp
  | succ n ih =>
    rw [pow_succ]
    refine ⟨ih.1.mul hM, fun x hx => ?_⟩
    rw [ih.1.mul_apply_self M hx, ih.2 x hx, pow_succ]

theorem eq_one_of_pow_odd_card_three [Finite F] (hF : Nat.card F = 3) {x : F} {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) : x = 1 := by
  have := Fintype.ofFinite F
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨k, rfl⟩ := hm
    simp at hx
  have hx2 : x ^ 2 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one x hx0
    rw [← Nat.card_eq_fintype_card, hF] at h
    exact h
  obtain ⟨k, rfl⟩ := hm
  calc x = x * (x ^ 2) ^ k := by rw [hx2, one_pow, mul_one]
    _ = x ^ (2 * k + 1) := by rw [← pow_mul, ← pow_succ']
    _ = 1 := hx

theorem odd_le_blkLin [Finite F] (hF : Nat.card F = 3) (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (P : Subgroup ↥(StatedSL 4 F))
    (hP : ∀ g ∈ P, (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) ∧
      (g : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (g : GL (Fin 4) F))
    (hodd : OddGenerated P) : P ≤ blkLin a b := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact ⟨1, rfl⟩)
  have hall := fin4_cases a b c d hab hac had hbc hbd hcd
  have hdiag : ∀ g ∈ P, IsDiagAt c d ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    obtain ⟨h1, h3⟩ := hP g hg
    refine isDiagAt_of_comm h2 ?_ ?_
    · have := congrArg Units.val h1
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    · have := congrArg Units.val h3
      rw [Units.val_mul, Units.val_mul] at this
      exact this
  have hout : ∀ x : Fin 4, ¬ (x = a ∨ x = b) → (x = c ∨ x = d) := by
    intro x hx
    rcases hall x with h' | h' | h' | h'
    · exact absurd (Or.inl h') hx
    · exact absurd (Or.inr h') hx
    · exact Or.inl h'
    · exact Or.inr h'
  have hgen : ∀ g ∈ P, Odd (orderOf g) → g ∈ blkLin a b := by
    intro g hg hgo
    have hgd := hdiag g hg
    set M : Matrix (Fin 4) (Fin 4) F := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hM
    have hMpow : M ^ (orderOf g) = 1 := by
      have h1 : g ^ (orderOf g) = 1 := pow_orderOf_eq_one g
      have h2' : (((g ^ (orderOf g) : ↥(StatedSL 4 F)) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) = 1 := by
        rw [h1]
        rfl
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at h2'
      exact h2'
    have hdiag1 : ∀ x : Fin 4, (x = c ∨ x = d) → M x x = 1 := by
      intro x hx
      have h1 := (isDiagAt_pow hgd (orderOf g)).2 x hx
      rw [hMpow, Matrix.one_apply_eq] at h1
      exact eq_one_of_pow_odd_card_three hF hgo h1.symm
    rw [mem_blkLin]
    intro i j hij
    by_cases hij' : i = j
    · subst hij'
      have hi : ¬ (i = a ∨ i = b) := fun h' => hij ⟨h', h'⟩
      rw [Matrix.one_apply_eq]
      exact hdiag1 i (hout i hi)
    · have hcd' : i = c ∨ i = d ∨ j = c ∨ j = d := by
        by_cases hi : i = a ∨ i = b
        · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
          have := hout j hj
          tauto
        · have := hout i hi
          tauto
      rw [Matrix.one_apply_ne hij']
      exact hgd i j hij' hcd'
  conv_lhs => rw [← hodd]
  refine (Subgroup.closure_le _).2 fun g hg => hgen g hg.1 hg.2

@[expose] noncomputable def linBlockOps3 [Finite F] (hF : Nat.card F = 3) :
    OddBlockOps F (StatedSL 4 F) where
  blk := blkLin
  oddGen := fun a b hab => blkLin_oddGenerated (by rw [hF]; exact ⟨1, rfl⟩) a b hab
  commute := fun a b c d _ _ hac had hbc hbd => blkLin_commute a b c d hac had hbc hbd
  comm_refl := fun a b c _ hca hcb => blkLin_comm_refl a b c hca hcb
  odd_le := fun a b c d hab hac had hbc hbd hcd P hP hodd =>
    odd_le_blkLin hF a b c d hab hac had hbc hbd hcd P hP hodd

theorem linBlockOps3_blk [Finite F] (hF : Nat.card F = 3) (a b : Fin 4) :
    (linBlockOps3 hF).blk a b = blkLin a b := rfl

theorem lin_blk_center3 [Finite F] (hF : Nat.card F = 3) :
    ∃ z ∈ (linBlockOps3 hF).blk 0 1, orderOf z = 2 ∧
      ∀ g ∈ (linBlockOps3 hF).blk 0 1, g * z = z * g := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact ⟨1, rfl⟩)
  let zS : ↥(StatedSL 4 F) :=
    ⟨⟨zDiag F, zDiag F, zDiag_mul_self, zDiag_mul_self⟩, by
      rw [statedSL_eq_detOne, mem_detOne]
      exact det_zDiag⟩
  have hz1 : zS ≠ 1 := by
    intro h
    have h' := congrArg
      (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp only [zS, zDiag, Matrix.diagonal_apply_eq] at h'
    apply h2
    have h'' : (-1 : F) = 1 := by simpa using h'
    linear_combination -h''
  have hzz : zS ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Units.ext zDiag_mul_self)
  refine ⟨zS, isBlockAt_zDiag, ?_, fun g hg => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzz hz1
  · refine Subtype.ext (Units.ext ?_)
    show (((g : GL (Fin 4) F) * (zS : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (((zS : GL (Fin 4) F) * (g : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [Units.val_mul, Units.val_mul]
    exact IsBlockAt.comm_diagonal hg ![-1, -1, 1, 1] rfl

end CFSG.GH74.Generic.S1
