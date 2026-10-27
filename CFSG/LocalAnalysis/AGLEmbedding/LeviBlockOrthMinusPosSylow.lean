module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusHas
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem card_mul_card_dvd_card_pi {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ j, Group (G j)] (S : ∀ j, Subgroup (G j)) {i j : ι} (hij : i ≠ j) :
    Nat.card (S i) * Nat.card (S j) ∣ Nat.card (Subgroup.pi Set.univ S) := by
  let φ : ↥(S i) × ↥(S j) →* ∀ k, G k :=
    MonoidHom.noncommCoprod ((MonoidHom.mulSingle G i).comp (S i).subtype)
      ((MonoidHom.mulSingle G j).comp (S j).subtype)
      (fun a b => Pi.mulSingle_commute hij _ _)
  have hφ : ∀ x : ↥(S i) × ↥(S j),
      φ x = Pi.mulSingle i (x.1 : G i) * Pi.mulSingle j (x.2 : G j) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have hi := congrFun h i
    have hj := congrFun h j
    rw [hφ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one,
      Pi.one_apply] at hi
    rw [hφ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm, one_mul,
      Pi.one_apply] at hj
    exact Prod.ext (Subtype.ext hi) (Subtype.ext hj)
  have hle : φ.range ≤ Subgroup.pi Set.univ S := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    exact Subgroup.mul_mem _ ((Subgroup.mulSingle_mem_pi i _).2 fun _ => x.1.2)
      ((Subgroup.mulSingle_mem_pi j _).2 fun _ => x.2.2)
  rw [← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_dvd_of_le hle

theorem orthCuts_eq_val {r s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts r d)
    (h1 : ∀ l : Fin s, d l.succ - d l.castSucc = 1) (i : Fin (s + 1)) : d i = i := by
  induction i using Fin.induction with
  | zero => exact hd.zero
  | succ l ih =>
    have := hd.mono (Fin.castSucc_lt_succ (i := l))
    have := h1 l
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

theorem hasLeviBlocks_orthParab_blocks (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HasLeviBlocks ↥(orthParab r (minusTailForm K b c) d)
      {N | ∃ j, CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j) ∧
        N = Nat.card (↥(orthLeviBlock K r d b c j) ⧸
          Subgroup.center ↥(orthLeviBlock K r d b c j))} :=
  HasLeviBlocks.of_index (orthLeviBlock K r d b c) (orthLeviHom b c hd)
    (isPGroup_ker_orthLeviHom hd)
    (pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (commutator_range_orthLeviHom_le hd) (isQuasisimple_or_isSolvable_orthLeviBlock hirr)
    (fun j hj => ⟨j, hj, rfl⟩)

theorem eq_inr_of_orthLeviBlock_u42 {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {j : Fin s ⊕ Unit}
    (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j))
    (h : Nat.card (↥(orthLeviBlock K r d b c j) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c j)) = 25920) :
    j = .inr () ∧ r - d (Fin.last s) = 2 ∧ 2 ^ f = 2 := by
  rcases j with l | u
  · change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range at hq
    change Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range ⧸
      Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range) = 25920 at h
    have h2 := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq)
    rw [card_range_toGL_quotient_center (by omega), hK] at h
    exact absurd h (ordA_ne_u42 rfl)
  · obtain rfl : u = () := rfl
    obtain ⟨-, -, h'⟩ := card_orthResDer_quotient_center hK hirr hq
    change Nat.card (↥(orthResDer K b c (r - d (Fin.last s))) ⧸
      Subgroup.center ↥(orthResDer K b c (r - d (Fin.last s)))) = 25920 at h
    rw [h'] at h
    obtain ⟨h3, h4⟩ := (ordTwistedD_eq_u42_iff rfl).1 h
    exact ⟨rfl, by omega, h4⟩

omit [CharP K 2] in
theorem three_dvd_card_orthLeviBlock_inl (hK : Nat.card K = 2) {l : Fin s}
    (hl : 2 ≤ d l.succ - d l.castSucc) : 3 ∣ Nat.card ↥(orthLeviBlock K r d b c (.inl l)) := by
  change 3 ∣ Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range
  rw [← Nat.card_congr (slEquivToGLRange (K := K) _).toEquiv,
    LinearFlag.card_SL_eq (by omega), hK]
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1)
    (Finset.mem_Icc.2 ⟨le_rfl, hl⟩)) _

theorem card_orthLeviBlock_inr_two (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ht : r - d (Fin.last s) = 2) : Nat.card ↥(orthLeviBlock K r d b c (.inr ())) = 25920 := by
  change Nat.card ↥(orthResDer K b c (r - d (Fin.last s))) = 25920
  rw [ht, (orthResDer_two_facts hirr).2.2, hK]
  norm_num

theorem three_pow_five_dvd_card_orthParab (hK : Nat.card K = 2) (hd : OrthCuts r d)
    (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ht : r - d (Fin.last s) = 2)
    {l : Fin s} (hl : 2 ≤ d l.succ - d l.castSucc) :
    3 ^ 5 ∣ Nat.card ↥(orthParab r (minusTailForm K b c) d) := by
  have h1 := card_mul_card_dvd_card_pi (orthLeviBlock K r d b c)
    (Sum.inl_ne_inr : (Sum.inl l : Fin s ⊕ Unit) ≠ .inr ())
  have h2 := Subgroup.card_dvd_of_le (pi_orthLeviBlock_le_range hd hr
    (commutator_orthogonalGroup_quadTail_minus hr hirr))
  rw [card_orthLeviBlock_inr_two hK hirr ht] at h1
  have h4 : 3 ^ 5 ∣ Nat.card ↥(orthLeviBlock K r d b c (.inl l)) * 25920 := by
    rw [show 3 ^ 5 = 3 * 3 ^ 4 by norm_num]
    exact mul_dvd_mul (three_dvd_card_orthLeviBlock_inl hK hl) (by norm_num)
  exact h4.trans (h1.trans (h2.trans (Subgroup.card_range_dvd (orthLeviHom b c hd))))

end CFSG.AGLEmbedding.LeviBlock
