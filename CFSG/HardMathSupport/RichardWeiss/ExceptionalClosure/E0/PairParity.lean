module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Support

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

theorem zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem heart_supported_pair {N : ℕ} (hN : Even N) {a b r : Fin N} (hab : a ≠ b) (hra : r ≠ a)
    (hrb : r ≠ b) (v : altHeart N)
    (h : ∀ j, j ≠ a → j ≠ b → altHeartCoord r v j = 0) :
    v = 0 ∨ v = (pairEW a b : altHeart N) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hx := x.2
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hx
  have hconst : ∀ j, j ≠ a → j ≠ b → (x : Fin N → ZMod 2) j = (x : Fin N → ZMod 2) r := by
    intro j hja hjb
    have := h j hja hjb
    rw [altHeartCoord_mk] at this
    exact sub_eq_zero.mp this
  have hsum : ∑ j, (x : Fin N → ZMod 2) j =
      (x : Fin N → ZMod 2) a + (x : Fin N → ZMod 2) b +
        ∑ j ∈ (Finset.univ.erase a).erase b, (x : Fin N → ZMod 2) j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase (Finset.univ.erase a) _
        (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)]
    ring
  have hrest : ∑ j ∈ (Finset.univ.erase a).erase b, (x : Fin N → ZMod 2) j = 0 := by
    rw [Finset.sum_congr rfl (g := fun _ => (x : Fin N → ZMod 2) r)]
    · rw [Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩), Finset.card_erase_of_mem
        (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      obtain ⟨m, hm⟩ := hN
      have : ((N - 1 - 1 : ℕ) : ZMod 2) = 0 := by
        rw [(ZMod.natCast_eq_zero_iff _ _)]
        omega
      rw [this, zero_mul]
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
      exact hconst j hj.2 hj.1
  have hab' : (x : Fin N → ZMod 2) a = (x : Fin N → ZMod 2) b := by
    rw [hsum, hrest, add_zero] at hx
    generalize (x : Fin N → ZMod 2) a = p at hx ⊢
    generalize (x : Fin N → ZMod 2) b = q at hx ⊢
    revert p q
    decide
  have hcoord : ∀ j, altHeartCoord r (x : altHeart N) j =
      ((x : Fin N → ZMod 2) a - (x : Fin N → ZMod 2) r) *
        (altHeartCoord r (pairEW a b : altHeart N) j) := by
    intro j
    rw [altHeartCoord_mk, altHeartCoord_mk, pairEW_apply, pairEW_apply]
    by_cases hja : j = a
    · subst hja
      simp [hra, hrb, hab]
      ring
    · by_cases hjb : j = b
      · subst hjb
        simp [hra, hrb, hja, hab']
        ring
      · simp [hja, hjb, hconst j hja hjb, hra, hrb]
  rcases zmod_two_cases' ((x : Fin N → ZMod 2) a - (x : Fin N → ZMod 2) r) with h0 | h1
  · left
    apply altHeartCoord_injective r
    ext j
    rw [hcoord j, h0, zero_mul]
    simp
  · right
    apply altHeartCoord_injective r
    ext j
    rw [hcoord j, h1, one_mul]

variable {W : Type*} [AddCommGroup W] {M : Type*} [Group M] {N : ℕ}
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M}

theorem pair_parity (F : PiFrame θ ρ U π L S) (hN : Even N) (h6 : 6 ≤ N) {t : M} (ht : t ∈ S)
    {a b : Fin N} (hab : a ≠ b) (hθt : θ t = swap a b) (w : W) :
    π ⟨ρ t w - w, F.sTriv t ht w⟩ = 0 ∨
      π ⟨ρ t w - w, F.sTriv t ht w⟩ = (pairEW a b : altHeart N) := by
  classical
  set Δ : Finset (Fin N) := {a, b} with hΔ
  have hcard : 4 ≤ (Finset.univ \ Δ).card := by
    have h1 := Finset.card_univ_sdiff Δ
    have h2 : Δ.card ≤ 2 := Finset.card_le_two
    rw [h1, Fintype.card_fin]
    omega
  obtain ⟨r, hr⟩ : ∃ r, r ∈ Finset.univ \ Δ := Finset.card_pos.1 (by omega)
  have hrΔ : r ∉ Δ := (Finset.mem_sdiff.1 hr).2
  have hra : r ≠ a := fun h => hrΔ (by simp [hΔ, h])
  have hrb : r ≠ b := fun h => hrΔ (by simp [hΔ, h])
  have hsΔ : ∀ i, i ∉ Δ → θ t i = i := by
    intro i hi
    have hia : i ≠ a := fun h => hi (by simp [hΔ, h])
    have hib : i ≠ b := fun h => hi (by simp [hΔ, h])
    rw [hθt, swap_apply_of_ne_of_ne hia hib]
  refine heart_supported_pair hN hab hra hrb _ fun j hja hjb => ?_
  exact support_lemma F ht Δ hcard hsΔ w r j hrΔ
    (fun h => by
      rcases Finset.mem_insert.1 h with h | h
      · exact hja h
      · exact hjb (Finset.mem_singleton.1 h))

variable {W : Type*} [AddCommGroup W] {M : Type*} [Group M] {N : ℕ}
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M}

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
