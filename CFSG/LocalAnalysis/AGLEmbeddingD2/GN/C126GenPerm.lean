module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm

variable {N : ℕ}

@[expose] def c3 (a b c : Fin N) : Perm (Fin N) := swap a b * swap b c

theorem isThreeCycle_c3 {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (c3 a b c).IsThreeCycle := by
  unfold c3
  rw [swap_comm a b]
  exact isThreeCycle_swap_mul_swap_same hab.symm hbc hac

theorem orderOf_c3 {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    orderOf (c3 a b c) = 3 := (isThreeCycle_c3 hab hbc hac).orderOf

theorem c3_pow_three {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    c3 a b c ^ 3 = 1 := by
  rw [← orderOf_c3 hab hbc hac]
  exact pow_orderOf_eq_one _

theorem c3_ne_one {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    c3 a b c ≠ 1 := by
  intro h
  have := orderOf_c3 hab hbc hac
  rw [h, orderOf_one] at this
  omega

theorem swap_c3_swap (a b c : Fin N) :
    swap a b * c3 a b c * swap a b = (c3 a b c)⁻¹ := by
  simp only [c3, mul_inv_rev, swap_inv, ← mul_assoc, swap_mul_self, one_mul]

theorem comm_c3_swap (a b c : Fin N) :
    c3 a b c * swap a b * (c3 a b c)⁻¹ * (swap a b)⁻¹ = c3 a b c * c3 a b c := by
  have h := swap_c3_swap a b c
  rw [swap_inv]
  have h2 : swap a b * (c3 a b c)⁻¹ * swap a b = c3 a b c := by
    have := congrArg (fun x => x⁻¹) h
    simpa [mul_inv_rev, swap_inv, mul_assoc] using this
  calc c3 a b c * swap a b * (c3 a b c)⁻¹ * swap a b
      = c3 a b c * (swap a b * (c3 a b c)⁻¹ * swap a b) := by group
    _ = c3 a b c * c3 a b c := by rw [h2]

theorem c3_mul_self_ne_one {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    c3 a b c * c3 a b c ≠ 1 := by
  intro h
  have h3 := c3_pow_three hab hbc hac
  have h1 : c3 a b c = 1 := by
    have : c3 a b c ^ 3 = (c3 a b c * c3 a b c) * c3 a b c := by rw [pow_succ, pow_two]
    rw [this, h, one_mul] at h3
    exact h3
  exact c3_ne_one hab hbc hac h1

theorem swap_commute_c3 {a b c u v : Fin N} (h : [u, v, a, b].Nodup) (h' : [u, v, b, c].Nodup) :
    swap u v * c3 a b c = c3 a b c * swap u v := by
  have h1 := (disjoint_swap_swap h).commute
  have h2 := (disjoint_swap_swap h').commute
  unfold c3
  rw [← mul_assoc, h1.eq, mul_assoc, h2.eq, mul_assoc]

theorem c3_apply_left {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) : c3 a b c a = b := by
  unfold c3
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]

theorem c3_apply_middle {a b c : Fin N} (hac : a ≠ c) (hbc : b ≠ c) : c3 a b c b = c := by
  unfold c3
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem c3_apply_right {a b c : Fin N} : c3 a b c c = a := by
  unfold c3
  rw [Perm.mul_apply, swap_apply_right, swap_apply_right]

theorem normalClosure_c3 {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Subgroup.normalClosure {c3 a b c} = alternatingGroup (Fin N) := by
  have h3 := isThreeCycle_c3 hab hbc hac
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (by simpa using h3.mem_alternatingGroup)
  · have h3' : Subgroup.closure {σ : Perm (Fin N) | σ.IsThreeCycle} = alternatingGroup (Fin N) :=
      Equiv.Perm.closure_three_cycles_eq_alternating
    rw [← h3', Subgroup.closure_le]
    intro τ hτ
    have hτ' : τ.cycleType = {3} := hτ
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (h3.trans hτ'.symm))
    rw [← hg]
    exact (Subgroup.normalClosure_normal (s := {c3 a b c})).conj_mem (c3 a b c)
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) g

theorem mem_alt_of_pow_three {g : Perm (Fin N)} (h : g ^ 3 = 1) :
    g ∈ alternatingGroup (Fin N) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h1 : Equiv.Perm.sign g ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

theorem exists_not_comm_alt (hN : 4 ≤ N) : ∃ a b : ↥(alternatingGroup (Fin N)), a * b ≠ b * a := by
  let x : Fin N := ⟨0, by omega⟩
  let y : Fin N := ⟨1, by omega⟩
  let z : Fin N := ⟨2, by omega⟩
  let w : Fin N := ⟨3, by omega⟩
  have hxy : x ≠ y := by simp [x, y, Fin.ext_iff]
  have hyz : y ≠ z := by simp [y, z, Fin.ext_iff]
  have hxz : x ≠ z := by simp [x, z, Fin.ext_iff]
  have hxw : x ≠ w := by simp [x, w, Fin.ext_iff]
  have hyw : y ≠ w := by simp [y, w, Fin.ext_iff]
  have hzw : z ≠ w := by simp [z, w, Fin.ext_iff]
  refine ⟨⟨c3 x y z, (isThreeCycle_c3 hxy hyz hxz).mem_alternatingGroup⟩,
    ⟨c3 x y w, (isThreeCycle_c3 hxy hyw hxw).mem_alternatingGroup⟩, fun hab => ?_⟩
  have h := congrArg (fun q : ↥(alternatingGroup (Fin N)) => (q : Perm (Fin N)) x) hab
  simp only [Subgroup.coe_mul, Perm.mul_apply] at h
  rw [c3_apply_left hxy hxw, c3_apply_left hxy hxz, c3_apply_middle hxz hyz,
    c3_apply_middle hxw hyw] at h
  exact hzw h

theorem center_alt_eq_bot (hN : 5 ≤ N) : Subgroup.center (alternatingGroup (Fin N)) = ⊥ := by
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin N)) :=
    alternatingGroup.isSimpleGroup (by simpa using hN)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin N)))
    with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_comm_alt (N := N) (by omega)
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b |>.symm)

theorem isQuasisimple_of_alt (hN : 5 ≤ N) {Γ : Type*} [Group Γ]
    (e : Γ ≃* ↥(alternatingGroup (Fin N))) : CFSG.IsQuasisimple Γ := by
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin N)) :=
    alternatingGroup.isSimpleGroup (by simpa using hN)
  have : IsSimpleGroup Γ := e.isSimpleGroup
  have hcenter : Subgroup.center Γ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ Subgroup.center ↥(alternatingGroup (Fin N)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
    rw [center_alt_eq_bot hN, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  let coord : (Γ ⧸ Subgroup.center Γ) ≃* Γ :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, coord.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Γ) with h | h
    · exfalso
      have h1 : Subgroup.center Γ = ⊤ := (commutator_eq_bot_iff_center_eq_top Γ).1 h
      rw [hcenter] at h1
      have : Nontrivial Γ := e.toEquiv.nontrivial
      exact bot_ne_top h1
    · exact h
  · obtain ⟨a, b, hab⟩ := exists_not_comm_alt (N := N) (by omega)
    refine ⟨coord.symm (e.symm a), coord.symm (e.symm b), fun h => hab ?_⟩
    have := congrArg (fun z => e (coord z)) h
    simpa using this

theorem eq_or_nodup_of_swaps {D : Subgroup (Perm (Fin N))} (hD : IsPGroup 2 D) {a b u v : Fin N}
    (hab : a ≠ b) (huv : u ≠ v) (hs : swap a b ∈ D) (ht : swap u v ∈ D) :
    swap a b = swap u v ∨ [a, b, u, v].Nodup := by
  have hno3 : ∀ x y z : Fin N, x ≠ y → y ≠ z → x ≠ z → swap x y ∈ D → swap y z ∈ D → False := by
    intro x y z hxy hyz hxz h1 h2
    have hm : c3 x y z ∈ D := D.mul_mem h1 h2
    obtain ⟨k, hk⟩ := hD ⟨c3 x y z, hm⟩
    have hk' : c3 x y z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := (orderOf_c3 hxy hyz hxz) ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  by_cases h1 : a = u
  · subst h1
    by_cases h2 : b = v
    · subst h2
      exact Or.inl rfl
    · exact (hno3 b a v hab.symm huv h2 (swap_comm a b ▸ hs) ht).elim
  by_cases h3 : a = v
  · subst h3
    by_cases h4 : b = u
    · subst h4
      exact Or.inl (swap_comm _ _)
    · exact (hno3 u a b huv hab (Ne.symm h4) ht hs).elim
  by_cases h5 : b = u
  · subst h5
    by_cases h6 : a = v
    · exact (h3 h6).elim
    · exact (hno3 a b v hab huv h6 hs ht).elim
  by_cases h7 : b = v
  · subst h7
    exact (hno3 a b u hab h5 h1 hs (swap_comm u b ▸ ht)).elim
  right
  simp [List.nodup_cons, hab, huv, h1, h3, h5, h7]

end CFSG.AGLEmbeddingD2.GN
