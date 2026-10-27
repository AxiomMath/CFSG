module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenPerm
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm CFSG.QuasithinUnique

variable {N : ℕ}

@[expose] def permAct (g : Perm (Fin N)) (x : Fin N → ZMod 2) : Fin N → ZMod 2 :=
  fun i => x (g⁻¹ i)

theorem permAct_zero (g : Perm (Fin N)) : permAct g 0 = 0 := rfl

theorem permAct_add (g : Perm (Fin N)) (x y : Fin N → ZMod 2) :
    permAct g (x + y) = permAct g x + permAct g y := rfl

theorem permAct_single (g : Perm (Fin N)) (i : Fin N) :
    permAct g (Pi.single i (1 : ZMod 2)) = Pi.single (g i) 1 := by
  funext l
  simp only [permAct, Pi.single_apply]
  have : g⁻¹ l = i ↔ l = g i := by
    rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]
  simp only [this]

theorem mem_evenWeight {x : Fin N → ZMod 2} : x ∈ evenWeight N ↔ ∑ i, x i = 0 := by
  simp [evenWeight]

theorem add_self_zmod_two (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

theorem eq_one_of_ne_zero_zmod_two {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem single_add_single_mem_evenWeight (i j : Fin N) :
    (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin N → ZMod 2) ∈ evenWeight N := by
  rw [mem_evenWeight]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

theorem evenWeight_le_closure_pairs (hN : 1 ≤ N) :
    evenWeight N ≤ AddSubgroup.closure {y : Fin N → ZMod 2 |
      ∃ i j : Fin N, i ≠ j ∧ y = Pi.single i 1 + Pi.single j 1} := by
  intro x hx
  rw [mem_evenWeight] at hx
  set P := AddSubgroup.closure {y : Fin N → ZMod 2 |
      ∃ i j : Fin N, i ≠ j ∧ y = Pi.single i 1 + Pi.single j 1} with hP
  let z : Fin N := ⟨0, hN⟩
  have hterm : ∀ i : Fin N, (Pi.single i (x i) + Pi.single z (x i) : Fin N → ZMod 2) ∈ P := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi]
    · have h1 : x i = 1 := eq_one_of_ne_zero_zmod_two hxi
      rw [h1]
      by_cases hiz : i = z
      · rw [hiz]
        have h0 : (Pi.single z (1 : ZMod 2) + Pi.single z 1 : Fin N → ZMod 2) = 0 := by
          funext l
          exact add_self_zmod_two _
        rw [h0]
        exact P.zero_mem
      · exact AddSubgroup.subset_closure ⟨i, z, hiz, rfl⟩
  have hsum : (∑ i, (Pi.single i (x i) + Pi.single z (x i) : Fin N → ZMod 2)) = x := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    have h2 : (∑ i, if l = z then x i else 0) = 0 := by
      by_cases hlz : l = z
      · simp [hlz, hx]
      · simp [hlz]
    rw [h2, add_zero]
  rw [← hsum]
  exact AddSubgroup.sum_mem _ fun i _ => hterm i

theorem exists_notMem_finset (s : Finset (Fin N)) (hs : s.card < N) : ∃ k : Fin N, k ∉ s := by
  by_contra h
  push Not at h
  have : s = Finset.univ := Finset.eq_univ_of_forall h
  rw [this, Finset.card_univ, Fintype.card_fin] at hs
  exact lt_irrefl _ hs

theorem c3_apply_of_ne {a b c l : Fin N} (ha : l ≠ a) (hb : l ≠ b) (hc : l ≠ c) :
    c3 a b c l = l := by
  unfold c3
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hb hc, swap_apply_of_ne_of_ne ha hb]

theorem exists_alt_pair (hN : 4 ≤ N) {u v u' v' : Fin N} (huv : u ≠ v) (huv' : u' ≠ v') :
    ∃ g ∈ alternatingGroup (Fin N), g u = u' ∧ g v = v' := by
  classical
  set s₁ : Perm (Fin N) := swap u u' with hs₁
  have hv₁ : s₁ v ≠ u' := by
    intro h
    rw [hs₁] at h
    have : v = u := by
      have := congrArg (swap u u') h
      simpa using this
    exact huv this.symm
  set s₂ : Perm (Fin N) := swap (s₁ v) v' with hs₂
  have hu₂ : s₂ u' = u' := swap_apply_of_ne_of_ne hv₁.symm huv'
  set g₀ : Perm (Fin N) := s₂ * s₁ with hg₀
  have hg₀u : g₀ u = u' := by
    rw [hg₀, Perm.mul_apply, hs₁, swap_apply_left]
    exact hu₂
  have hg₀v : g₀ v = v' := by
    rw [hg₀, Perm.mul_apply, hs₂, swap_apply_left]
  by_cases hsg : g₀ ∈ alternatingGroup (Fin N)
  · exact ⟨g₀, hsg, hg₀u, hg₀v⟩
  · have hc : 1 < (({u', v'} : Finset (Fin N))ᶜ).card := by
      rw [Finset.card_compl]
      have := Finset.card_le_two (a := u') (b := v')
      simp only [Fintype.card_fin]
      omega
    obtain ⟨w, hw, z, hz, hwz⟩ := Finset.one_lt_card.1 hc
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hw hz
    refine ⟨swap w z * g₀, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap hwz]
      have h1 : sign g₀ = -1 := by
        rcases Int.units_eq_one_or (sign g₀) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hsg
        · exact h
      rw [h1]
      decide
    · rw [Perm.mul_apply, hg₀u, swap_apply_of_ne_of_ne (Ne.symm hw.1) (Ne.symm hz.1)]
    · rw [Perm.mul_apply, hg₀v, swap_apply_of_ne_of_ne (Ne.symm hw.2) (Ne.symm hz.2)]

theorem permAct_c3_add_apply {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : Fin N → ZMod 2) (l : Fin N) :
    (permAct (c3 i j k) x + x) l =
      if l = i then x k + x i else if l = j then x i + x j else if l = k then x j + x k else 0 := by
  simp only [permAct, Pi.add_apply]
  by_cases hli : l = i
  · subst hli
    have : (c3 l j k)⁻¹ l = k := by rw [Equiv.Perm.inv_eq_iff_eq, c3_apply_right]
    simp [this]
  by_cases hlj : l = j
  · subst hlj
    have : (c3 i l k)⁻¹ l = i := by rw [Equiv.Perm.inv_eq_iff_eq, c3_apply_left hij hik]
    simp [this, hli]
  by_cases hlk : l = k
  · subst hlk
    have : (c3 i j l)⁻¹ l = j := by rw [Equiv.Perm.inv_eq_iff_eq, c3_apply_middle hik hjk]
    simp [this, hli, hlj]
  · have : (c3 i j k)⁻¹ l = l := by
      rw [Equiv.Perm.inv_eq_iff_eq, c3_apply_of_ne hli hlj hlk]
    simp [this, hli, hlj, hlk, add_self_zmod_two]

theorem delta_irred (hN : 5 ≤ N) (hodd : Odd N) {U : AddSubgroup (Fin N → ZMod 2)}
    (hU : U ≤ evenWeight N) (hinv : ∀ g ∈ alternatingGroup (Fin N), ∀ x ∈ U, permAct g x ∈ U) :
    U = ⊥ ∨ U = evenWeight N := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hU
  obtain ⟨x, hxU, hx0⟩ : ∃ x ∈ U, x ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot (eq_bot_iff.2 fun x hx => (AddSubgroup.mem_bot).2 (h x hx))
  have hxe := mem_evenWeight.1 (hU hxU)
  obtain ⟨i, hi⟩ : ∃ i, x i = 1 := by
    by_contra h
    push Not at h
    apply hx0
    funext l
    have h0 : x l = 0 := by
      by_contra h0
      exact h l (eq_one_of_ne_zero_zmod_two h0)
    simpa using h0
  obtain ⟨j, hj⟩ : ∃ j, x j = 0 := by
    by_contra h
    push Not at h
    have h1 : ∀ l, x l = 1 := fun l => eq_one_of_ne_zero_zmod_two (h l)
    have : ∑ l, x l = (N : ZMod 2) := by
      simp [h1]
    rw [this] at hxe
    have := hodd.natCast_zmod_two
    rw [hxe] at this
    exact zero_ne_one this
  have hij : i ≠ j := fun h => by
    rw [h, hj] at hi
    exact zero_ne_one hi
  obtain ⟨k, hk⟩ := exists_notMem_finset ({i, j} : Finset (Fin N))
    (lt_of_le_of_lt (Finset.card_le_two) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj⟩ := hk
  have hjk : j ≠ k := Ne.symm hkj
  have hik : i ≠ k := Ne.symm hki
  have hσ : c3 i j k ∈ alternatingGroup (Fin N) :=
    (isThreeCycle_c3 hij hjk hik).mem_alternatingGroup
  have hy : permAct (c3 i j k) x + x ∈ U := U.add_mem (hinv _ hσ x hxU) hxU
  have hpair : ∃ u v : Fin N, u ≠ v ∧
      (Pi.single u (1 : ZMod 2) + Pi.single v 1 : Fin N → ZMod 2) ∈ U := by
    by_cases hxk : x k = 0
    · refine ⟨i, j, hij, ?_⟩
      have : permAct (c3 i j k) x + x = Pi.single i 1 + Pi.single j 1 := by
        funext l
        rw [permAct_c3_add_apply hij hjk hik]
        simp only [Pi.add_apply, Pi.single_apply]
        by_cases hli : l = i
        · subst hli
          simp [hi, hxk, hij]
        by_cases hlj : l = j
        · subst hlj
          simp [hi, hj, hli]
        by_cases hlk : l = k
        · subst hlk
          simp [hxk, hj, hli, hlj]
        · simp [hli, hlj, hlk]
      rw [← this]
      exact hy
    · have hxk1 : x k = 1 := eq_one_of_ne_zero_zmod_two hxk
      refine ⟨j, k, hjk, ?_⟩
      have : permAct (c3 i j k) x + x = Pi.single j 1 + Pi.single k 1 := by
        funext l
        rw [permAct_c3_add_apply hij hjk hik]
        simp only [Pi.add_apply, Pi.single_apply]
        by_cases hli : l = i
        · subst hli
          simp [hi, hxk1, hij, hik, add_self_zmod_two]
        by_cases hlj : l = j
        · subst hlj
          simp [hi, hj, hli, hjk]
        by_cases hlk : l = k
        · subst hlk
          simp [hxk1, hj, hli, hlj]
        · simp [hli, hlj, hlk]
      rw [← this]
      exact hy
  obtain ⟨u, v, huv, hpairU⟩ := hpair
  have hall : ∀ u' v' : Fin N, u' ≠ v' →
      (Pi.single u' (1 : ZMod 2) + Pi.single v' 1 : Fin N → ZMod 2) ∈ U := by
    intro u' v' huv'
    obtain ⟨g, hg, hgu, hgv⟩ := exists_alt_pair (by omega) huv huv'
    have := hinv g hg _ hpairU
    rw [permAct_add, permAct_single, permAct_single, hgu, hgv] at this
    exact this
  intro y hy
  have hmem := evenWeight_le_closure_pairs (by omega) hy
  refine (AddSubgroup.closure_le U |>.2 ?_) hmem
  rintro _ ⟨i, j, hij, rfl⟩
  exact hall i j hij

theorem delta_fix (hN : 3 ≤ N) (hodd : Odd N) {x : Fin N → ZMod 2} (hx : x ∈ evenWeight N)
    (hfix : ∀ g ∈ alternatingGroup (Fin N), permAct g x = x) : x = 0 := by
  have hconst : ∀ i j, x i = x j := by
    intro i j
    by_contra hne
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    obtain ⟨k, hk⟩ := exists_notMem_finset ({i, j} : Finset (Fin N))
      (lt_of_le_of_lt (Finset.card_le_two) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hki, hkj⟩ := hk
    have hjk : j ≠ k := Ne.symm hkj
    have hik : i ≠ k := Ne.symm hki
    have h1 := hfix (c3 i j k) (isThreeCycle_c3 hij hjk hik).mem_alternatingGroup
    have h2 := congrFun h1 j
    simp only [permAct] at h2
    have : (c3 i j k)⁻¹ j = i := by rw [Equiv.Perm.inv_eq_iff_eq, c3_apply_left hij hik]
    rw [this] at h2
    exact hne h2
  have hsum : ∑ l, x l = (N : ZMod 2) * x ⟨0, by omega⟩ := by
    rw [Finset.sum_congr rfl (fun l _ => hconst l ⟨0, by omega⟩)]
    simp
  rw [mem_evenWeight, hsum, hodd.natCast_zmod_two, one_mul] at hx
  funext l
  rw [hconst l ⟨0, by omega⟩, hx]
  rfl

theorem delta_four (hN : 5 ≤ N) {a b p : Fin N} (hab : a ≠ b) (hbp : b ≠ p) (hap : a ≠ p) :
    4 ≤ {y : Fin N → ZMod 2 | ∃ v ∈ evenWeight N, permAct (c3 a b p) v + v = y}.ncard := by
  obtain ⟨u, hu⟩ := exists_notMem_finset ({a, b, p} : Finset (Fin N))
    (lt_of_le_of_lt (Finset.card_le_three) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨hua, hub, hup⟩ := hu
  have hcu : c3 a b p u = u := c3_apply_of_ne hua hub hup
  set σ := c3 a b p with hσ
  have key : ∀ (q r : Fin N), q ≠ u → σ q = r →
      permAct σ (Pi.single q 1 + Pi.single u 1) + (Pi.single q 1 + Pi.single u 1) =
        Pi.single r 1 + Pi.single q 1 := by
    intro q r hq hr
    rw [permAct_add, permAct_single, permAct_single, hr, hcu]
    funext l
    simp only [Pi.add_apply]
    have h2 : ∀ a b c : ZMod 2, (a + c) + (b + c) = a + b := by decide
    exact h2 _ _ _
  let f : Fin 4 → (Fin N → ZMod 2) := ![0, Pi.single b 1 + Pi.single a 1,
    Pi.single p 1 + Pi.single b 1, Pi.single a 1 + Pi.single p 1]
  have hσa : σ a = b := c3_apply_left hab hap
  have hσb : σ b = p := c3_apply_middle hap hbp
  have hσp : σ p = a := c3_apply_right
  have hrange : Set.range f ⊆ {y : Fin N → ZMod 2 |
      ∃ v ∈ evenWeight N, permAct σ v + v = y} := by
    rintro _ ⟨m, rfl⟩
    fin_cases m
    · exact ⟨0, (evenWeight N).zero_mem, by simp [permAct_zero, f]⟩
    · exact ⟨Pi.single a 1 + Pi.single u 1, single_add_single_mem_evenWeight a u,
        by simpa [f] using key a b (Ne.symm hua) hσa⟩
    · exact ⟨Pi.single b 1 + Pi.single u 1, single_add_single_mem_evenWeight b u,
        by simpa [f] using key b p (Ne.symm hub) hσb⟩
    · exact ⟨Pi.single p 1 + Pi.single u 1, single_add_single_mem_evenWeight p u,
        by simpa [f] using key p a (Ne.symm hup) hσp⟩
  have hval : ∀ m : Fin 4, (f m a, f m b, f m p) =
      (![(0, 0, 0), (1, 1, 0), (0, 1, 1), (1, 0, 1)] : Fin 4 → ZMod 2 × ZMod 2 × ZMod 2) m := by
    intro m
    fin_cases m <;> simp [f, hab, hap, hbp, hab.symm, hap.symm, hbp.symm]
  have hinj : Function.Injective f := by
    have hv : ∀ m m' : Fin 4, (![(0, 0, 0), (1, 1, 0), (0, 1, 1), (1, 0, 1)] :
        Fin 4 → ZMod 2 × ZMod 2 × ZMod 2) m = ![(0, 0, 0), (1, 1, 0), (0, 1, 1), (1, 0, 1)] m' →
        m = m' := by decide
    intro m m' h
    refine hv m m' ?_
    rw [← hval m, ← hval m', h]
  have hcard : (Set.range f).ncard = 4 := by
    rw [Set.ncard_range_of_injective hinj]
    simp
  calc 4 = (Set.range f).ncard := hcard.symm
    _ ≤ _ := Set.ncard_le_ncard hrange (Set.toFinite _)

end CFSG.AGLEmbeddingD2.GN
