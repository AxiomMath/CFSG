module

public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup

variable {G Q S : Type*} [Group G] [Group Q] [Group S] (πG : G →* S) (πQ : Q →* S)

@[expose] def pullbackSub : Subgroup (G × Q) :=
  (πG.comp (MonoidHom.fst G Q)).eqLocus (πQ.comp (MonoidHom.snd G Q))

theorem mem_pullbackSub {a : G × Q} : a ∈ pullbackSub πG πQ ↔ πG a.1 = πQ a.2 := Iff.rfl

@[expose] def pullbackFst : ↥(pullbackSub πG πQ) →* G :=
  (MonoidHom.fst G Q).comp (pullbackSub πG πQ).subtype

variable {πG πQ}

theorem pullbackFst_surjective (hπQ : Function.Surjective πQ) :
    Function.Surjective (pullbackFst πG πQ) := by
  intro g
  obtain ⟨y, hy⟩ := hπQ (πG g)
  exact ⟨⟨(g, y), (mem_pullbackSub πG πQ).mpr hy.symm⟩, rfl⟩

theorem pullbackFst_ker_le_center (hker : πQ.ker ≤ center Q) :
    (pullbackFst πG πQ).ker ≤ center ↥(pullbackSub πG πQ) := by
  intro g hg
  have h1 : (g : G × Q).1 = 1 := hg
  have h2 := (mem_pullbackSub πG πQ).mp g.2
  rw [h1, map_one] at h2
  have hz : (g : G × Q).2 ∈ center Q := hker (MonoidHom.mem_ker.mpr h2.symm)
  rw [mem_center_iff]
  intro k
  apply Subtype.ext
  apply Prod.ext
  · change (k : G × Q).1 * (g : G × Q).1 = (g : G × Q).1 * (k : G × Q).1
    rw [h1, one_mul, mul_one]
  · exact mem_center_iff.mp hz _

theorem isPGroup_pullbackFst_ker {p : ℕ} (h2 : IsPGroup p πQ.ker) :
    IsPGroup p (pullbackFst πG πQ).ker := by
  intro g
  have h1 : ((g : ↥(pullbackSub πG πQ)) : G × Q).1 = 1 := g.2
  have h2' := (mem_pullbackSub πG πQ).mp (g : ↥(pullbackSub πG πQ)).2
  rw [h1, map_one] at h2'
  obtain ⟨k, hk⟩ := h2 ⟨((g : ↥(pullbackSub πG πQ)) : G × Q).2, MonoidHom.mem_ker.mpr h2'.symm⟩
  refine ⟨k, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
  · change ((g : ↥(pullbackSub πG πQ)) : G × Q).1 ^ p ^ k = 1
    rw [h1, one_pow]
  · change ((g : ↥(pullbackSub πG πQ)) : G × Q).2 ^ p ^ k = 1
    exact congrArg Subtype.val hk

theorem exists_lift_of_section {σ : G →* ↥(pullbackSub πG πQ)}
    (hσ : ∀ g, pullbackFst πG πQ (σ g) = g) : ∃ τ : G →* Q, ∀ g, πQ (τ g) = πG g := by
  refine ⟨(MonoidHom.snd G Q).comp ((pullbackSub πG πQ).subtype.comp σ), fun g => ?_⟩
  have h1 := (mem_pullbackSub πG πQ).mp (σ g).2
  have h2 : ((σ g : ↥(pullbackSub πG πQ)) : G × Q).1 = g := hσ g
  rw [h2] at h1
  exact h1.symm

theorem three_le_pRank_of_four_group [Finite Q] {τ : G →* Q} (hτ : ∀ g, πQ (τ g) = πG g)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : πG a ≠ 1)
    (hb1 : πG b ≠ 1) (hab1 : πG (a * b) ≠ 1) {z : Q} (hz : z ∈ center Q) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzk : πQ z = 1) : 3 ≤ CFSG.pRank 2 Q := by
  have hzc : ∀ y : Q, Commute y z := fun y => (mem_center_iff.mp hz y)
  refine RankThree.PartTwo.Sec4.Census.DoubleCoverLift.le_pRank_two_of_independent
    ![τ a, τ b, z] (fun i => ?_) (fun i j => ?_) (fun v hv hprod => ?_)
  · fin_cases i
    · show τ a ^ 2 = 1
      rw [← map_pow, pow_two, ha, map_one]
    · show τ b ^ 2 = 1
      rw [← map_pow, pow_two, hb, map_one]
    · show z ^ 2 = 1
      rw [pow_two, hz2]
  · have hτab : Commute (τ a) (τ b) := by
      change τ a * τ b = τ b * τ a
      rw [← map_mul, ← map_mul, hab]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two] <;>
      first
        | exact Commute.refl _ | exact hτab | exact hτab.symm | exact hzc _ | exact (hzc _).symm
  · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two] at hprod
    have himg := congrArg πQ hprod
    simp only [map_mul, map_pow, hτ, hzk, one_pow, mul_one, map_one] at himg
    have hval : ∀ w : Fin 2, (w : ℕ) = 0 ∨ (w : ℕ) = 1 := fun w => by
      have := w.isLt; omega
    rcases hval (v 0) with h0 | h0 <;> rcases hval (v 1) with h1 | h1
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i
        · exact Fin.ext h0
        · exact Fin.ext h1
        · exact h2
      have h2' : (v 2 : ℕ) = 1 := (hval _).resolve_left (fun h => h2 (Fin.ext h))
      rw [h0, h1, h2'] at hprod
      simp only [pow_zero, pow_one, one_mul] at hprod
      exact hz1 hprod
    · rw [h0, h1] at himg
      simp only [pow_zero, pow_one, one_mul] at himg
      exact hb1 himg
    · rw [h0, h1] at himg
      simp only [pow_zero, pow_one, mul_one] at himg
      exact ha1 himg
    · rw [h0, h1] at himg
      simp only [pow_one] at himg
      exact hab1 (by rw [map_mul]; exact himg)

theorem pRank_le_one_of_sq_eq_one_mem {P : Type*} [Group P] [Finite P] {H : Subgroup P}
    (hH : Nat.card H ≤ 2) (h : ∀ y : P, y ^ 2 = 1 → y ∈ H) : CFSG.pRank 2 P ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hAH : A ≤ H := fun a ha => h a (elemPow_eq_one_of_isElementaryAbelian a ha)
  have h2 : 2 ^ r ≤ 2 ^ 1 := by
    rw [← hcard, pow_one]
    exact (Subgroup.card_le_of_le hAH).trans hH
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
