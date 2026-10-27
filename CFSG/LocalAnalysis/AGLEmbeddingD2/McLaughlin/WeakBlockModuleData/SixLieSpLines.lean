module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.AGLEmbeddingD2.McLaughlin.Lie TauCeti.GLSymplecticFin

section Sp

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem torus_sp_eq_bot (hF : Nat.card F = 2) (k : Fin n) : Symplectic.torus n F k = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h := torus_pow_eq_one_sp k hg
  rw [hF] at h
  simpa using h

omit [Finite F] [CharP F 2] in
theorem rootGroup_sp_isPGroup [Finite F] [CharP F 2] {γ : Fin n → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum n F).roots) :
    IsPGroup 2 ((Symplectic.rootDatum n F).rootGroup γ) :=
  isPGroup_of_isParametrization Sp.isParametrization hγ

theorem posUnipotent_sp_isPGroup :
    IsPGroup 2 (posUnipotent (Symplectic.rootDatum n F)) :=
  posUnipotent_isPGroup_of (Symplectic.steinbergExtras n F) fun _ hγ => rootGroup_sp_isPGroup hγ

theorem rankOne_sp_facts (hF : Nat.card F = 2) (i : Fin n) :
    Nat.card (rankOne (Symplectic.rootDatum n F).rootGroup i) = 6 ∧
    (∃ a ∈ rankOne (Symplectic.rootDatum n F).rootGroup i,
      ∃ b ∈ rankOne (Symplectic.rootDatum n F).rootGroup i, a * b ≠ b * a) ∧
    (∃ c ∈ rankOne (Symplectic.rootDatum n F).rootGroup i, c ≠ 1 ∧ c ^ 3 = 1) := by
  have : Finite (StatedSp n F) := inferInstance
  set L := rankOne (Symplectic.rootDatum n F).rootGroup i with hL
  obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
  have hpar := Sp.isParametrization (n := n) (F := F)
  have hα : (Pi.single i 1 : Fin n → ℤ) ∈ (Symplectic.rootDatum n F).roots :=
    (RootSystem.ofCartan (Symplectic.rootDatum n F).isFiniteType
      (Symplectic.rootDatum n F).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin n → ℤ) ∈ (Symplectic.rootDatum n F).roots :=
    (RootSystem.ofCartan (Symplectic.rootDatum n F).isFiniteType
      (Symplectic.rootDatum n F).divisible).neg_mem _ hα
  set u := φ (sl2Upper 1) with hu
  set l := φ (sl2Lower 1) with hl
  have huL : u ∈ L := by
    apply (le_sup_left : (Symplectic.rootDatum n F).rootGroup (Pi.single i 1) ≤ L)
    rw [hu, hx 1]
    exact ((hpar _ hα).1 _).2 ⟨1, rfl⟩
  have hlL : l ∈ L := by
    apply (le_sup_right : (Symplectic.rootDatum n F).rootGroup (-Pi.single i 1) ≤ L)
    rw [hl, hy 1]
    exact ((hpar _ hα').1 _).2 ⟨1, rfl⟩
  have hnc : u * l ≠ l * u := by
    intro h
    apply sl2_upper_lower_not_commute (F := F)
    apply hφ
    simp only [map_mul]
    rw [← hu, ← hl, mul_assoc, ← h]
  have hu2 : u ^ 2 = 1 := by
    have h11 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
    have hx0 : Sp.x n F (Pi.single i 1) 0 = 1 := by
      have h0 := (hpar _ hα).2.1 0 0
      rw [add_zero] at h0
      exact left_eq_mul.mp h0
    rw [hu, hx 1, sq, ← (hpar _ hα).2.1 1 1, h11, hx0]
  have hu1 : u ≠ 1 := fun h => hnc (by rw [h, one_mul, mul_one])
  have hc1 : u * l ≠ 1 := by
    intro h
    apply hnc
    have hl' : l = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hl', mul_inv_cancel, inv_mul_cancel]
  have hc3 : (u * l) ^ 3 = 1 := by
    rw [hu, hl, ← map_mul, ← map_pow, sl2_upper_lower_cube, map_one]
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd6 : Nat.card L ∣ 6 := card_rankOne_dvd_six_of_sl2 hF hpar hx hy
  have hd2 : 2 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L huL
    rwa [orderOf_eq_prime hu2 hu1] at this
  have hd3 : 3 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L (L.mul_mem huL hlL)
    rwa [orderOf_eq_prime hc3 hc1] at this
  refine ⟨?_, ⟨u, huL, l, hlL, hnc⟩, ⟨u * l, L.mul_mem huL hlL, hc1, hc3⟩⟩
  have h6 : 6 ∣ Nat.card L := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd2 hd3
  exact Nat.dvd_antisymm hdvd6 h6

theorem not_nine_dvd_card_borel_sup_rankOne_sp (hF : Nat.card F = 2) (i : Fin n) :
    ¬ 9 ∣ Nat.card (borel (Symplectic.rootDatum n F) (Symplectic.torus n F) ⊔
        rankOne (Symplectic.rootDatum n F).rootGroup i : Subgroup _) :=
  not_nine_dvd_card_borel_sup_rankOne_of (Symplectic.isCTGroupDatum n F)
    (Symplectic.steinbergExtras n F) (torus_sp_eq_bot hF) posUnipotent_sp_isPGroup i
    (rankOne_sp_facts hF i).1

omit [Finite F] [CharP F 2] in
theorem stdVec_support_two (r : RootSubgroupIndex n) :
    ∃ a b : Fin n, ∀ p, stdVec r p ≠ 0 → p = a ∨ p = b := by
  rcases r with i | i | ⟨i, j, h⟩ | ⟨i, j, h⟩ | ⟨i, j, h⟩
  · refine ⟨i, i, fun p hp => Or.inl ?_⟩
    by_contra hne
    apply hp
    simp [stdVec, Pi.single_eq_of_ne hne]
  · refine ⟨i, i, fun p hp => Or.inl ?_⟩
    by_contra hne
    apply hp
    simp [stdVec, Pi.single_eq_of_ne hne]
  · refine ⟨i, j, fun p hp => ?_⟩
    by_contra hne
    push Not at hne
    apply hp
    simp [stdVec, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2]
  · refine ⟨i, j, fun p hp => ?_⟩
    by_contra hne
    push Not at hne
    apply hp
    simp [stdVec, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2]
  · refine ⟨i, j, fun p hp => ?_⟩
    by_contra hne
    push Not at hne
    apply hp
    simp [stdVec, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2]

omit [Finite F] [CharP F 2] in
theorem stdVec_support_le_two (r : RootSubgroupIndex n) {p q s : Fin n} (hpq : p ≠ q)
    (hqs : q ≠ s) (hps : p ≠ s) : stdVec r p = 0 ∨ stdVec r q = 0 ∨ stdVec r s = 0 := by
  obtain ⟨a, b, hab⟩ := stdVec_support_two r
  by_contra h
  push Not at h
  have hp := hab p h.1
  have hq := hab q h.2.1
  have hs := hab s h.2.2
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hs with h' | h' <;>
    simp_all

omit [Finite F] [CharP F 2] in
theorem sp_root_support {x y : Fin n} (hxy : x.val + 2 ≤ y.val) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (hs : ∀ k, k ≠ x → k ≠ y → γ k = 0) :
    γ x = 0 ∨ γ y = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy⟩ := hcon
  rw [roots_eq] at hγ
  obtain ⟨r, hr⟩ := hγ
  have hyn : y.val < n := y.isLt
  set q : Fin n := ⟨x.val + 1, by omega⟩ with hq
  have hne1 : x ≠ q := Fin.ne_of_val_ne (by simp [hq])
  have hne2 : q ≠ y := Fin.ne_of_val_ne (by simp [hq]; omega)
  have hne3 : x ≠ y := Fin.ne_of_val_ne (by omega)
  have key := stdVec_support_le_two r hne1 hne2 hne3
  rw [hr] at key
  have e1 : toStd n γ x ≠ 0 := by
    simp only [toStd]
    have : (if h : 0 < x.val then γ ⟨x.val - 1, by omega⟩ else 0) = 0 := by
      split_ifs with h
      · exact hs _ (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
      · rfl
    rw [this, sub_zero]
    split_ifs <;> omega
  have e2 : toStd n γ q ≠ 0 := by
    simp only [toStd]
    have h0 : γ q = 0 := hs _ (Fin.ne_of_val_ne (by simp [hq])) (Fin.ne_of_val_ne
      (by simp [hq]; omega))
    have hqpos : 0 < q.val := by simp [hq]
    have : (if h : 0 < q.val then γ ⟨q.val - 1, by omega⟩ else 0) = γ x := by
      rw [dif_pos hqpos]
      congr 1
    rw [this, h0]
    omega
  have e3 : toStd n γ y ≠ 0 := by
    simp only [toStd]
    have : (if h : 0 < y.val then γ ⟨y.val - 1, by omega⟩ else 0) = 0 := by
      rw [dif_pos (by omega)]
      exact hs _ (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
    rw [this, sub_zero]
    split_ifs <;> omega
  tauto

omit [Finite F] [CharP F 2] in
theorem not_adjacent_of_cartanC_eq_zero {i j : Fin n} (hij : i ≠ j) (h : cartanC n i j = 0) :
    ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  intro hadj
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  simp only [cartanC, Matrix.of_apply, if_neg hij, if_pos hadj] at h
  split_ifs at h <;> omega

omit [Finite F] [CharP F 2] in
theorem sp_orthogonal_cases (hn0 : 0 < n) (hn : n ≤ 4) (I : Set (Fin n))
    (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → cartanC n i j = 0) :
    (∃ i : Fin n, I ⊆ {i}) ∨ ∃ x y : Fin n, x.val + 2 ≤ y.val ∧ I ⊆ {x, y} := by
  have hna : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun i hi j hj hij => not_adjacent_of_cartanC_eq_zero hij (h i hi j hj hij)
  by_cases hex : ∃ x ∈ I, ∃ y ∈ I, x.val + 2 ≤ y.val
  · obtain ⟨x, hx, y, hy, hxy⟩ := hex
    right
    refine ⟨x, y, hxy, fun z hz => ?_⟩
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    have h1 := hna z hz x hx hne.1
    have h2 := hna z hz y hy hne.2
    have h3 := hna x hx y hy (Fin.ne_of_val_ne (by omega))
    have hzn : z.val < n := z.isLt
    have hyn : y.val < n := y.isLt
    have hzx : z.val ≠ x.val := fun e => hne.1 (Fin.ext e)
    have hzy : z.val ≠ y.val := fun e => hne.2 (Fin.ext e)
    omega
  · left
    by_cases hI : I.Nonempty
    · obtain ⟨i, hi⟩ := hI
      refine ⟨i, fun z hz => ?_⟩
      by_contra hne
      have hne' : z ≠ i := fun e => hne (by simpa using e)
      have h1 := hna z hz i hi hne'
      have hzi : z.val ≠ i.val := fun e => hne' (Fin.ext e)
      rcases lt_or_gt_of_ne hzi with hlt | hlt
      · exact hex ⟨z, hz, i, hi, by omega⟩
      · exact hex ⟨i, hi, z, hz, by omega⟩
    · exact ⟨⟨0, hn0⟩, by rw [Set.not_nonempty_iff_eq_empty.mp hI]; exact Set.empty_subset _⟩

theorem sp_tail_three {i j : Fin n} (hF : Nat.card F = 2) (h : spTail n i j) :
    ∃ V : Subgroup (StatedSp n F),
      V ≤ rankOne (Symplectic.rootDatum n F).rootGroup i ⊔
        rankOne (Symplectic.rootDatum n F).rootGroup j ∧ ⁅V, V⁆ = V ∧
      ∃ v ∈ V, v ^ 3 = 1 ∧ v ≠ 1 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hj : (⟨i.val + 1, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    obtain ⟨V, hV, hp, v, hv, h3, hc⟩ := sp_tail_exc_three hF h1
    rw [hj] at hV
    exact ⟨V, hV, hp, v, hv, h3, fun e => hc (e ▸ one_mem _)⟩
  · have hi : (⟨j.val + 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    obtain ⟨V, hV, hp, v, hv, h3, hc⟩ := sp_tail_exc_three hF h1
    rw [hi] at hV
    exact ⟨V, by rwa [sup_comm], hp, v, hv, h3, fun e => hc (e ▸ one_mem _)⟩

theorem sp_lines_core (hn0 : 0 < n) (hn : n ≤ 4) (hF : Nat.card F = 2)
    {A : Subgroup (StatedSp n F)}
    (hBA : borel (Symplectic.rootDatum n F) (Symplectic.torus n F) ≤ A)
    (hperf : ∀ V : Subgroup (StatedSp n F), V ≤ A → ⁅V, V⁆ = V → ¬ 3 ∣ Nat.card V)
    {E : Subgroup (StatedSp n F)} (hEA : E ≤ A) (hE : Nat.card E = 9) :
    ∃ E₁ : Subgroup (StatedSp n F), E₁ ≤ E ∧ Nat.card E₁ = 3 ∧
      A ⊓ Subgroup.normalizer (E : Set _) ≤ Subgroup.normalizer (E₁ : Set _) := by
  have hct := Symplectic.isCTGroupDatum n F
  have hext := Symplectic.steinbergExtras n F
  have hH := torus_sp_eq_bot (n := n) hF
  have hU2 := posUnipotent_sp_isPGroup (n := n) (F := F)
  have hfacts := rankOne_sp_facts (n := n) hF
  have hL := twoLevi_sp (n := n) hF
  have hAeq := eq_borel_sup_rankOne hct hext hBA
  set D := Symplectic.rootDatum n F with hD
  have hLA : ∀ i ∈ negIndices D A, rankOne D.rootGroup i ≤ A := fun i hi =>
    rankOne_le_of_mem_negIndices hBA hi
  have hAS : ∀ S : Set (Fin D.rank), negIndices D A ⊆ S →
      A ≤ borel D (Symplectic.torus n F) ⊔ ⨆ k ∈ S, rankOne D.rootGroup k :=
    fun S hS => hAeq.le.trans (sup_le_sup_left (biSup_mono fun k hk => hS hk) _)
  have hnp : ∀ i ∈ negIndices D A,
      ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i :=
    fun i hi hp => hperf _ (hLA i hi) hp (by rw [(hfacts i).1]; norm_num)
  have hcart : ∀ i ∈ negIndices D A, ∀ j ∈ negIndices D A, i ≠ j → cartanC n i j = 0 := by
    intro i hi j hj hij
    by_contra hA
    rcases hL.pair i j hij hA (hnp i hi) (hnp j hj) with hp | he
    · exact hperf _ (sup_le (hLA i hi) (hLA j hj)) hp
        ((show 3 ∣ Nat.card (rankOne D.rootGroup i) by rw [(hfacts i).1]; norm_num).trans
          (Subgroup.card_dvd_of_le le_sup_left))
    · obtain ⟨V, hV, hVp, v, hv, hv3, hv1⟩ := sp_tail_three hF he
      have hVA : V ≤ A := hV.trans (sup_le (hLA i hi) (hLA j hj))
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      apply hperf V hVA hVp
      have := Subgroup.orderOf_dvd_natCard V hv
      rwa [orderOf_eq_prime hv3 hv1] at this
  rcases sp_orthogonal_cases hn0 hn (negIndices D A) hcart with ⟨i, hi⟩ | ⟨x, y, hxy, hsub⟩
  ·
    exfalso
    have hAi : A ≤ borel D (Symplectic.torus n F) ⊔ rankOne D.rootGroup i :=
      (hAS {i} hi).trans (sup_le_sup_left iSup_singleton.le _)
    apply not_nine_dvd_card_borel_sup_rankOne_sp hF i
    rw [← hE]
    exact Subgroup.card_dvd_of_le (hEA.trans hAi)
  ·
    have hxy' : x ≠ y := Fin.ne_of_val_ne (by omega)
    have hAxy : A ≤ borel D (Symplectic.torus n F) ⊔
        (rankOne D.rootGroup x ⊔ rankOne D.rootGroup y) :=
      (hAS {x, y} hsub).trans (sup_le_sup_left iSup_pair.le _)
    have hcz : cartanC n x y = 0 := by
      have : (D.cartan x y) = cartanC n x y := rfl
      simp only [cartanC, Matrix.of_apply, if_neg hxy']
      rw [if_neg]
      intro hadj
      omega
    refine exists_line_of_two_nodes hext hH hU2
      (commutes_rankOne_of_cartan_eq_zero hext hxy' hcz)
      (hfacts x).1 (hfacts y).1 (hfacts x).2.1 ?_ hAxy hEA hE
    intro γ hγ _ hvan
    have hs : ∀ k, k ≠ x → k ≠ y → γ k = 0 := fun k hkx hky =>
      hvan k (by
        intro hk
        rcases hk with hk | hk
        · exact hkx hk
        · exact hky (Set.mem_singleton_iff.mp hk))
    have hsup := sp_root_support hxy hγ hs
    rcases hsup with h0 | h0
    · exact (hct.le_rankOne y γ hγ fun k hk => by
        by_cases hkx : k = x
        · rw [hkx]; exact h0
        · exact hs k hkx hk).trans le_sup_right
    · exact (hct.le_rankOne x γ hγ fun k hk => by
        by_cases hky : k = y
        · rw [hky]; exact h0
        · exact hs k hk hky).trans le_sup_left

end Sp

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
