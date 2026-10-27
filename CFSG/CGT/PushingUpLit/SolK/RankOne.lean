module

public import CFSG.CGT.PushingUpLit.SolK.SevenFour

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

variable {d : ℕ}

theorem pairVec_mul_pairVec_right (x y p : Fin d) : pairVec x p * pairVec y p = pairVec x y := by
  refine vcoord_ext fun m => ?_
  rw [vcoord_mul, vcoord_pairVec, vcoord_pairVec, vcoord_pairVec]
  have h : ∀ x y z : ZMod 2, x + z + (y + z) = x + y := fun x y z => by
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]
  exact h _ _ _

theorem pairVec_inv (a b : Fin d) : (pairVec a b)⁻¹ = pairVec a b :=
  vcoord_ext fun m => by rw [vcoord_inv]

theorem pairVec_ne_one {a b : Fin d} (hab : a ≠ b) : pairVec a b ≠ 1 := by
  intro h
  have := congrArg (fun v => vcoord v a) h
  simp only [vcoord_pairVec, vcoord_one] at this
  simp [hab] at this

theorem exists_swap_of_small_image (hd : Odd d) {σ : Perm (Fin d)} {j : ℕ} (hσ : σ ^ (2 ^ j) = 1)
    (hσ1 : σ ≠ 1)
    (hz : ∀ v w : ↥(coreMod d), v⁻¹ * coreAct d σ v ≠ 1 → w⁻¹ * coreAct d σ w ≠ 1 →
      v⁻¹ * coreAct d σ v = w⁻¹ * coreAct d σ w) :
    ∃ a b : Fin d, a ≠ b ∧ σ = swap a b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hodd : ¬ 2 ∣ Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    have := Nat.odd_iff.1 hd
    omega
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
  have key : ∀ x, σ x ≠ x → (pairVec x p)⁻¹ * coreAct d σ (pairVec x p) = pairVec x (σ x) := by
    intro x hx
    rw [pairVec_inv, coreAct_pairVec, hp]
    exact pairVec_mul_pairVec_right x (σ x) p
  have hxp : ∀ x, σ x ≠ x → x ≠ p := fun x hx h => hx (by rw [h, hp])
  have hcommon : ∀ x, σ x ≠ x → pairVec x (σ x) = pairVec a (σ a) := by
    intro x hx
    have h1 := key x hx
    have h2 := key a ha
    refine (h1.symm.trans (hz _ _ ?_ ?_)).trans h2
    · rw [h1]
      exact pairVec_ne_one (fun h => hx h.symm)
    · rw [h2]
      exact pairVec_ne_one (fun h => ha h.symm)
  have hmoved : ∀ x, σ x ≠ x → x = a ∨ x = σ a := by
    intro x hx
    have h := congrArg vsupp (hcommon x hx)
    rw [vsupp_pairVec (fun h => hx h.symm), vsupp_pairVec (fun h => ha h.symm)] at h
    have hxm : x ∈ ({x, σ x} : Finset (Fin d)) := by simp
    rw [h] at hxm
    simpa using hxm
  refine ⟨a, σ a, fun h => ha h.symm, ?_⟩
  have hbm : σ (σ a) ≠ σ a := fun h => ha (σ.injective h)
  have hbb : σ (σ a) = a := by
    have h2 := congrArg vsupp (hcommon (σ a) hbm)
    rw [vsupp_pairVec (fun h => hbm h.symm), vsupp_pairVec (fun h => ha h.symm)] at h2
    have hmem : σ (σ a) ∈ ({σ a, σ (σ a)} : Finset (Fin d)) := by simp
    rw [h2] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact h
    · exact absurd h hbm
  ext x
  by_cases hx : σ x = x
  · have hxa : x ≠ a := fun h => ha (h ▸ hx)
    have hxb : x ≠ σ a := fun h => hbm (h ▸ hx)
    rw [hx, swap_apply_of_ne_of_ne hxa hxb]
  · rcases hmoved x hx with h | h
    · rw [h, swap_apply_left]
    · rw [h, swap_apply_right, hbb]

theorem exists_ne_ne (hd : 3 ≤ d) (a b : Fin d) : ∃ p : Fin d, p ≠ a ∧ p ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b} := fun p _ => by
    by_cases hpa : p = a
    · simp [hpa]
    · simp [h p hpa]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem swap_pairVec_value {a b p : Fin d} (hpa : p ≠ a) (hpb : p ≠ b) :
    (pairVec a p)⁻¹ * coreAct d (swap a b) (pairVec a p) = pairVec a b := by
  rw [pairVec_inv, coreAct_pairVec, swap_apply_left, swap_apply_of_ne_of_ne hpa hpb]
  exact pairVec_mul_pairVec_right a b p

theorem swap_eq_of_pairVec_eq {a b a' b' : Fin d} (hab : a ≠ b) (hab' : a' ≠ b')
    (h : pairVec a b = pairVec a' b') : swap a b = swap a' b' := by
  have h1 := congrArg vsupp h
  rw [vsupp_pairVec hab, vsupp_pairVec hab'] at h1
  have ha : a ∈ ({a', b'} : Finset (Fin d)) := by rw [← h1]; simp
  have hb : b ∈ ({a', b'} : Finset (Fin d)) := by rw [← h1]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
  · rcases hb with rfl | rfl
    · exact swap_comm _ _
    · exact absurd rfl hab

end CFSG.CGT.PushingUpLit.SolK
