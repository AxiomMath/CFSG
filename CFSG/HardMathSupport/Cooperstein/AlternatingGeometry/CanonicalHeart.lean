module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalModule
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm

theorem evenSub_eq (d : ℕ) : evenSub d = evenWeight d := AddSubgroup.ext fun _ => Iff.rfl

theorem constSub_eq (d : ℕ) : constSub d = AddSubgroup.zmultiples (allOnes d) := by
  ext f
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hf
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact ⟨0, funext fun i => i.elim0⟩
    · rcases zmod_two_cases (f ⟨0, hd⟩) with h | h
      · refine ⟨0, funext fun i => ?_⟩
        rw [zero_smul]
        exact ((hf i ⟨0, hd⟩).trans h).symm
      · refine ⟨1, funext fun i => ?_⟩
        rw [one_zsmul]
        exact ((hf i ⟨0, hd⟩).trans h).symm
  · rintro ⟨k, rfl⟩ i j
    simp [allOnes]

@[expose] noncomputable def heartEquivAlt (d : ℕ) : Heart d ≃+ altHeart d :=
  QuotientAddGroup.congr _ _ (AddEquiv.addSubgroupCongr (evenSub_eq d)) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show (y : Fin d → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes d)
      rw [← constSub_eq]; exact hy
    · intro hx
      refine ⟨⟨x.1, by rw [evenSub_eq]; exact x.2⟩, ?_, rfl⟩
      show (x : Fin d → ZMod 2) ∈ constSub d
      rw [constSub_eq]; exact hx)

theorem heartEquivAlt_mk (d : ℕ) (f : ↥(evenSub d)) :
    heartEquivAlt d (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨f.1, by rw [← evenSub_eq]; exact f.2⟩ := rfl

theorem altHeart_irreducible {n : ℕ} (hn : 4 ≤ n) (U : AddSubgroup (altHeart n))
    (hU : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n,
      (QuotientAddGroup.mk x : altHeart n) ∈ U →
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  let e := heartEquivAlt n
  have key : U.comap e.toAddMonoidHom = ⊥ ∨ U.comap e.toAddMonoidHom = ⊤ := by
    apply heart_irreducible hn
    intro σ hσ u hu
    obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact hU σ hσ ⟨f.1, by rw [← evenSub_eq]; exact f.2⟩ hu
  rcases key with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have : e.symm y ∈ U.comap e.toAddMonoidHom := by
      show e (e.symm y) ∈ U
      simpa using hy
    rw [h] at this
    have h0 : e.symm y = 0 := AddSubgroup.mem_bot.1 this
    have : y = 0 := by simpa using congrArg e h0
    exact AddSubgroup.mem_bot.2 this
  · right
    rw [eq_top_iff]
    intro y _
    have : e.symm y ∈ U.comap e.toAddMonoidHom := by rw [h]; trivial
    simpa using this

theorem altHeart_nontrivial {n : ℕ} (hn : 3 ≤ n) : Nontrivial (altHeart n) := by
  have := heart_nontrivial hn
  exact (heartEquivAlt n).injective.nontrivial

theorem exists_ne_three {n : ℕ} (hn : 4 ≤ n) (a b c : Fin n) : ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d _
    by_cases h1 : d = a
    · simp [h1]
    by_cases h2 : d = b
    · simp [h2]
    simp [h d h1 h2]
  have := Finset.card_le_card hsub
  have h3 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := by
    calc ({a, b, c} : Finset (Fin n)).card ≤ ({b, c} : Finset (Fin n)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (({c} : Finset (Fin n)).card + 1) + 1 := by
          have := Finset.card_insert_le b ({c} : Finset (Fin n)); omega
      _ = 3 := by simp
  simp at this
  omega

theorem altHeart_fixed_eq_zero {n : ℕ} (hn : 4 ≤ n) (x : evenWeight n)
    (hx : ∀ σ ∈ alternatingGroup (Fin n),
      (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x) :
    (QuotientAddGroup.mk x : altHeart n) = 0 := by
  have hconst : ∀ a b : Fin n, (x : Fin n → ZMod 2) a = (x : Fin n → ZMod 2) b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨c, hca, hcb, -⟩ := exists_ne_three hn a b a
    obtain ⟨d, hda, hdb, hdc⟩ := exists_ne_three hn a b c
    set ρ : Perm (Fin n) := swap a b * swap b c with hρ
    have hsign : ρ⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, map_inv, hρ, map_mul, sign_swap hab, sign_swap hcb.symm]
      decide
    have h1 := hx _ hsign
    rw [QuotientAddGroup.eq] at h1
    have h2 : ((evenWeightPerm ρ⁻¹ x : evenWeight n) : Fin n → ZMod 2) - (x : Fin n → ZMod 2) ∈
        AddSubgroup.zmultiples (allOnes n) := by
      have h1' : -(evenWeightPerm ρ⁻¹ x) + x ∈ evenWeightOnes n := h1
      have h4 := neg_mem h1'
      have h5 : ((-(-(evenWeightPerm ρ⁻¹ x) + x) : evenWeight n) : Fin n → ZMod 2) ∈
          AddSubgroup.zmultiples (allOnes n) := h4
      have hfun : ((evenWeightPerm ρ⁻¹ x : evenWeight n) : Fin n → ZMod 2) -
          (x : Fin n → ZMod 2) =
          ((-(-(evenWeightPerm ρ⁻¹ x) + x) : evenWeight n) : Fin n → ZMod 2) := by
        funext i
        simp [sub_eq_add_neg, add_comm]
      rw [hfun]
      exact h5
    rw [← constSub_eq] at h2
    have h3 := h2 a d
    have hρd : ρ d = d := by
      rw [hρ, Perm.mul_apply, swap_apply_of_ne_of_ne hdb hdc, swap_apply_of_ne_of_ne hda hdb]
    have hρa : ρ a = b := by
      rw [hρ, Perm.mul_apply, swap_apply_of_ne_of_ne hab hca.symm, swap_apply_left]
    simp only [Pi.sub_apply, evenWeightPerm, inv_inv, hρd, hρa, sub_self] at h3
    exact (sub_eq_zero.1 h3).symm
  have : (x : Fin n → ZMod 2) ∈ constSub n := hconst
  rw [constSub_eq] at this
  rw [QuotientAddGroup.eq_zero_iff]
  exact this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
