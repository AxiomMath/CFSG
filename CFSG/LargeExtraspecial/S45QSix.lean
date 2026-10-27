module

public import CFSG.LargeExtraspecial.S45QSylow
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Equiv Equiv.Perm Subgroup

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem isSimpleGroup_alternatingGroup_six : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)

theorem factorial_lt_of_le_five {j : ℕ} (hj : j ≤ 5) : j.factorial < 360 := by
  interval_cases j <;> decide

theorem card_le_sixty_of_lt {K : Subgroup (Perm (Fin 6))} (hKA : K ≤ alternatingGroup (Fin 6))
    (hne : K ≠ alternatingGroup (Fin 6)) : Nat.card K ≤ 60 := by
  have := isSimpleGroup_alternatingGroup_six
  set K' := K.subgroupOf (alternatingGroup (Fin 6))
  have hK' : K' ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hKA fun σ hσ => ?_
    have : (⟨σ, hσ⟩ : alternatingGroup (Fin 6)) ∈ K' := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hdvd := card_dvd_factorial_index hK'
  rw [card_alternatingGroup_six] at hdvd
  have h6 : 6 ≤ K'.index := by
    by_contra h
    have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    have := factorial_lt_of_le_five (j := K'.index) (by omega)
    omega
  have hmul := K'.card_mul_index
  rw [card_alternatingGroup_six, Nat.card_congr (subgroupOfEquivOfLe hKA).toEquiv] at hmul
  nlinarith

theorem alternatingGroup_le_of_index_le_five {P : Subgroup (Perm (Fin 6))} (hP : P.index ≤ 5) :
    alternatingGroup (Fin 6) ≤ P := by
  have := isSimpleGroup_alternatingGroup_six
  set P' := P.subgroupOf (alternatingGroup (Fin 6))
  by_cases hP' : P' = ⊤
  · intro σ hσ
    have : (⟨σ, hσ⟩ : alternatingGroup (Fin 6)) ∈ P' := hP' ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hdvd := card_dvd_factorial_index hP'
  rw [card_alternatingGroup_six] at hdvd
  have hle : P'.index ≤ P.index := by
    have := relIndex_le_of_le_right (H := P) (le_top : alternatingGroup (Fin 6) ≤ ⊤)
      (by rw [relIndex_top_right]; exact (index_ne_zero_of_finite))
    rwa [relIndex_top_right] at this
  have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  have := factorial_lt_of_le_five (j := P'.index) (by omega)
  omega

theorem isCycle_and_unique_fixed_of_orderOf_eq_five {u : Perm (Fin 6)} (hu : orderOf u = 5) :
    u.IsCycle ∧ ∃ x, u x = x ∧ ∀ y, y ≠ x → u y ≠ y := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (hu ▸ Nat.prime_five)
  have hle := sum_cycleType_le u
  rw [hn, hu, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have hn0 : n = 0 := by omega
  subst hn0
  have hcyc : u.IsCycle := by
    rw [← card_cycleType_eq_one, hn, Multiset.card_replicate]
  refine ⟨hcyc, ?_⟩
  have hsupp : u.support.card = 5 := by
    rw [← sum_cycleType, hn, hu, Multiset.sum_replicate, smul_eq_mul]
  have hc : u.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hsupp, Fintype.card_fin]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  refine ⟨x, ?_, fun y hy => ?_⟩
  · have hxc : x ∈ u.supportᶜ := by
      rw [hx]
      exact Finset.mem_singleton_self x
    rwa [Finset.mem_compl, mem_support, not_not] at hxc
  · rw [← mem_support]
    by_contra h
    have hyc : y ∈ u.supportᶜ := Finset.mem_compl.mpr h
    rw [hx, Finset.mem_singleton] at hyc
    exact hy hyc

theorem exists_apply_eq_self_of_involution {σ : Perm (Fin 6)}
    (hσA : σ ∈ alternatingGroup (Fin 6)) (hσ : orderOf σ = 2) : ∃ z, σ z = z := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (hσ ▸ Nat.prime_two)
  have hle := sum_cycleType_le σ
  rw [hn, hσ, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have hsign := sign_of_cycleType σ
  rw [mem_alternatingGroup.mp hσA, hn, hσ, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hn1 : n = 1 := by
    have : n ≤ 2 := by omega
    interval_cases n
    · exact absurd hsign (by decide)
    · rfl
    · exact absurd hsign (by decide)
  subst hn1
  by_contra h
  push Not at h
  have huniv : σ.support = Finset.univ := by
    ext z
    simp only [mem_support, Finset.mem_univ, iff_true]
    exact h z
  have h4 := sum_cycleType σ
  rw [huniv, hn, hσ, Multiset.sum_replicate, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at h4
  omega

theorem simple_of_fixed {K : Subgroup (Perm (Fin 6))} (hKA : K ≤ alternatingGroup (Fin 6))
    {x : Fin 6} (hfix : ∀ k ∈ K, k x = x) (h15 : 15 ∣ Nat.card K) :
    IsSimpleGroup K ∧ Nat.card K = 60 := by
  classical
  let φ : Perm {y : Fin 6 // y ≠ x} →* Perm (Fin 6) := ofSubtype
  have hφ : Function.Injective φ := ofSubtype_injective
  have hKr : K ≤ φ.range := by
    intro k hk
    have h₁ : ∀ y, k y ≠ x ↔ y ≠ x := fun y => by
      rw [Ne, Ne, ← (hfix k hk), k.injective.eq_iff, hfix k hk]
    refine ⟨k.subtypePerm h₁, ofSubtype_subtypePerm h₁ fun y hy hyx => hy ?_⟩
    rw [hyx]
    exact hfix k hk
  set K' := K.comap φ
  have hmap : K'.map φ = K := map_comap_eq_self hKr
  let e : K' ≃* K := (K'.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hmap)
  have hK'A : K' ≤ alternatingGroup {y : Fin 6 // y ≠ x} := by
    intro σ hσ
    have h := hKA (mem_comap.mp hσ)
    rw [mem_alternatingGroup, sign_ofSubtype] at h
    exact mem_alternatingGroup.mpr h
  have hcard5 : Nat.card {y : Fin 6 // y ≠ x} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  have hA5 : IsSimpleGroup (alternatingGroup {y : Fin 6 // y ≠ x}) :=
    alternatingGroup.isSimpleGroup (by omega)
  have : Nontrivial {y : Fin 6 // y ≠ x} := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard5]
    norm_num
  have hA5card : Nat.card (alternatingGroup {y : Fin 6 // y ≠ x}) = 60 := by
    rw [nat_card_alternatingGroup, hcard5]
    decide
  have hK'card : Nat.card K' = Nat.card K := Nat.card_congr e.toEquiv
  set K'' := K'.subgroupOf (alternatingGroup {y : Fin 6 // y ≠ x})
  have hK''card : Nat.card K'' = Nat.card K := by
    rw [← hK'card]
    exact Nat.card_congr (subgroupOfEquivOfLe hK'A).toEquiv
  have hK''top : K'' = ⊤ := by
    by_contra hne
    have hdvd := card_dvd_factorial_index hne
    have hmul := K''.card_mul_index
    rw [hA5card] at hdvd hmul
    rw [hK''card] at hmul
    obtain ⟨c, hc⟩ := h15
    have hi : K''.index = 1 ∨ K''.index = 2 ∨ K''.index = 4 := by
      rw [hc, mul_assoc] at hmul
      have h1 : c * K''.index = 4 := by omega
      have : K''.index ∣ 4 := ⟨c, by rw [← h1, mul_comm]⟩
      have h4 : K''.index ≤ 4 := Nat.le_of_dvd (by norm_num) this
      interval_cases h : K''.index
      · exact absurd this (by norm_num)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd this (by norm_num)
      · exact Or.inr (Or.inr rfl)
    rcases hi with h | h | h
    · exact hne (index_eq_one.mp h)
    · rw [h] at hdvd
      norm_num at hdvd
    · rw [h] at hdvd
      norm_num at hdvd
  have hK'eq : K' = alternatingGroup {y : Fin 6 // y ≠ x} := by
    refine le_antisymm hK'A fun σ hσ => ?_
    have : (⟨σ, hσ⟩ : alternatingGroup {y : Fin 6 // y ≠ x}) ∈ K'' := hK''top ▸ mem_top _
    exact mem_subgroupOf.mp this
  have e' : K ≃* alternatingGroup {y : Fin 6 // y ≠ x} :=
    e.symm.trans (MulEquiv.subgroupCongr hK'eq)
  refine ⟨e'.isSimpleGroup, ?_⟩
  rw [Nat.card_congr e'.toEquiv, hA5card]

theorem simple_of_transitive {K : Subgroup (Perm (Fin 6))} (hKA : K ≤ alternatingGroup (Fin 6))
    {x : Fin 6} (htr : ∀ a : Fin 6, ∃ k ∈ K, k x = a) (h15 : 15 ∣ Nat.card K)
    (hle : Nat.card K ≤ 60) : IsSimpleGroup K ∧ Nat.card K = 60 := by
  have hpre : MulAction.IsPretransitive K (Fin 6) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨k, hk, hka⟩ := htr a
    obtain ⟨l, hl, hlb⟩ := htr b
    refine ⟨⟨l * k⁻¹, mul_mem hl (inv_mem hk)⟩, ?_⟩
    change (l * k⁻¹) a = b
    rw [← hka]
    simp [hlb]
  have horb : ∀ z : Fin 6, Nat.card (MulAction.stabilizer K z) * 6 = Nat.card K := by
    intro z
    have h := (MulAction.stabilizer K z).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive] at h
    simpa using h
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h30 : Nat.card K = 30 ∨ Nat.card K = 60 := by
    have := horb x
    omega
  rcases h30 with h30 | h60
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [h30]; norm_num)
    obtain ⟨z, hz⟩ := exists_apply_eq_self_of_involution (hKA t.2)
      (by rwa [Subgroup.orderOf_coe])
    have hts : t ∈ MulAction.stabilizer K z := hz
    have hst : Nat.card (MulAction.stabilizer K z) = 5 := by
      have := horb z
      omega
    have h1 := orderOf_dvd_natCard (⟨t, hts⟩ : MulAction.stabilizer K z)
    rw [hst, Subgroup.orderOf_mk, ht] at h1
    norm_num at h1
  · obtain ⟨e⟩ := CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
      (G := K) (Ω := Fin 6) hpre (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]) h60
    exact ⟨e.isSimpleGroup, h60⟩

theorem simple_of_le_alternatingGroup {K : Subgroup (Perm (Fin 6))}
    (hKA : K ≤ alternatingGroup (Fin 6)) (h15 : 15 ∣ Nat.card K) :
    IsSimpleGroup K ∧ (Nat.card K = 60 ∨ Nat.card K = 360) := by
  by_cases hK : K = alternatingGroup (Fin 6)
  · subst hK
    exact ⟨isSimpleGroup_alternatingGroup_six, Or.inr card_alternatingGroup_six⟩
  have hle := card_le_sixty_of_lt hKA hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (dvd_trans (by norm_num) h15)
  rw [← Subgroup.orderOf_coe] at hu
  obtain ⟨hcyc, x, hux, hmove⟩ := isCycle_and_unique_fixed_of_orderOf_eq_five hu
  by_cases hfix : ∀ k ∈ K, k x = x
  · obtain ⟨h1, h2⟩ := simple_of_fixed hKA hfix h15
    exact ⟨h1, Or.inl h2⟩
  push Not at hfix
  obtain ⟨k₀, hk₀, hk₀x⟩ := hfix
  have htr : ∀ a : Fin 6, ∃ k ∈ K, k x = a := by
    intro a
    by_cases hax : a = x
    · exact ⟨1, one_mem K, by rw [hax, Perm.one_apply]⟩
    obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (hmove _ hk₀x) (hmove a hax)
    refine ⟨(u : Perm (Fin 6)) ^ i * k₀, mul_mem (pow_mem u.2 i) hk₀, ?_⟩
    rw [Perm.mul_apply, hi]
  obtain ⟨h1, h2⟩ := simple_of_transitive hKA htr h15 hle
  exact ⟨h1, Or.inl h2⟩

theorem simple_of_two_mul_card_eq {K P : Subgroup (Perm (Fin 6))} (hKP : K ≤ P)
    (hcard : 2 * Nat.card K = Nat.card P) (h60 : 60 ≤ Nat.card K) : IsSimpleGroup K := by
  have hPi := P.card_mul_index
  rw [card_perm_six] at hPi
  by_cases h144 : 144 ≤ Nat.card P
  · have hidx : P.index ≤ 5 := by
      by_contra h
      have : 6 ≤ P.index := by omega
      nlinarith
    have hA := alternatingGroup_le_of_index_le_five hidx
    have hdvd : P.index ∣ 2 := by
      have := index_dvd_of_le hA
      rwa [alternatingGroup.index_eq_two] at this
    have hP12 : P.index = 1 ∨ P.index = 2 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : P.index
      · simp at hdvd
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hP12 with h1 | h2
    · have hPtop : P = ⊤ := index_eq_one.mp h1
      have hKi : K.index = 2 := by
        have hK := K.card_mul_index
        rw [card_perm_six] at hK
        rw [h1] at hPi
        have hK360 : Nat.card K = 360 := by omega
        rw [hK360] at hK
        omega
      rw [eq_alternatingGroup_of_index_eq_two hKi]
      exact isSimpleGroup_alternatingGroup_six
    · exfalso
      rw [h2] at hPi
      have hPA : alternatingGroup (Fin 6) = P :=
        eq_of_le_of_card_ge hA (by rw [card_alternatingGroup_six]; omega)
      have hKA : K ≤ alternatingGroup (Fin 6) := hPA ▸ hKP
      have hne : K ≠ alternatingGroup (Fin 6) := by
        intro h
        rw [h, card_alternatingGroup_six] at hcard
        omega
      have := card_le_sixty_of_lt hKA hne
      omega
  · have hidx6 : P.index = 6 := by
      have h1 : P.index ≤ 6 := by
        by_contra h
        have : 7 ≤ P.index := by omega
        nlinarith
      have h2 : 6 ≤ P.index := by
        by_contra h
        have : P.index ≤ 5 := by omega
        nlinarith
      omega
    rw [hidx6] at hPi
    have hK60 : Nat.card K = 60 := by omega
    by_cases hKA : K ≤ alternatingGroup (Fin 6)
    · exact (simple_of_le_alternatingGroup hKA (by rw [hK60]; norm_num)).1
    · exfalso
      have hrel : (alternatingGroup (Fin 6)).relIndex K = 2 := by
        have h1 := relIndex_le_of_le_right (H := alternatingGroup (Fin 6)) (le_top : K ≤ ⊤)
          (by rw [relIndex_top_right, alternatingGroup.index_eq_two]; norm_num)
        rw [relIndex_top_right, alternatingGroup.index_eq_two] at h1
        have h2 : (alternatingGroup (Fin 6)).relIndex K ≠ 1 := fun h => hKA (relIndex_eq_one.mp h)
        have hm := ((alternatingGroup (Fin 6)).subgroupOf K).card_mul_index
        change _ * (alternatingGroup (Fin 6)).relIndex K = _ at hm
        have h3 : (alternatingGroup (Fin 6)).relIndex K ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hm
          omega
        omega
      have hLcard : Nat.card ↥(alternatingGroup (Fin 6) ⊓ K) = 30 := by
        have hm := ((alternatingGroup (Fin 6)).subgroupOf K).card_mul_index
        change _ * (alternatingGroup (Fin 6)).relIndex K = _ at hm
        rw [hrel, hK60, ← inf_subgroupOf_right,
          Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at hm
        omega
      have := (simple_of_le_alternatingGroup (inf_le_left : alternatingGroup (Fin 6) ⊓ K ≤ _)
        (by rw [hLcard]; norm_num)).2
      omega

theorem dihedral_pair_mem :
    swap (0 : Fin 6) 1 * swap 2 3 ∈ alternatingGroup (Fin 6) ∧
      swap (0 : Fin 6) 2 * swap 4 5 ∈ alternatingGroup (Fin 6) ∧
      (swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 1 * swap 2 3) = 1 ∧
      (swap (0 : Fin 6) 2 * swap 4 5) * (swap 0 2 * swap 4 5) = 1 ∧
      ((swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 2 * swap 4 5)) ^ 2 ^ 2 = 1 ∧
      (swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 2 * swap 4 5) ≠
        (swap (0 : Fin 6) 2 * swap 4 5) * (swap 0 1 * swap 2 3) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    rfl

end CFSG.LargeExtraspecial.S45Q
