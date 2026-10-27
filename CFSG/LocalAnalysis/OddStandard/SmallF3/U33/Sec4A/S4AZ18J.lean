module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18I
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma32to34

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

private lemma z18_closure_pair_ne_top {T : Type} [Group T] {a b : T} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a)
    (hbig : ∃ x : T, x ≠ 1 ∧ x ≠ a ∧ x ≠ b ∧ x ≠ a * b) :
    Subgroup.closure ({a, b} : Set T) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx1, hxa, hxb, hxab⟩ := hbig
  have hx : x ∈ Subgroup.closure ({a, b} : Set T) := htop ▸ Subgroup.mem_top x
  rcases mem_closure_pair_cases hab ha hb hx with h | h | h | h
  · exact hx1 h
  · exact hxa h
  · exact hxb h
  · exact hxab h

theorem z18_T_lemma {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (hexp : ∀ g : T, g ^ 4 = 1) {a b : T} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hC : ∀ x : T, x * a = a * x → x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hbig : ∃ x : T, x ≠ 1 ∧ x ≠ a ∧ x ≠ b ∧ x ≠ a * b)
    (hconj : ∀ g : T, g * a * g⁻¹ ≠ b) :
    ∃ M : Subgroup T, M.index = 2 ∧ a ∉ M ∧ ∀ u ∈ M, u * u = 1 → u = 1 ∨ u = b := by
  classical
  set A : Subgroup T := Subgroup.closure ({a, b} : Set T) with hA
  have hmem : ∀ k : T, k ∈ A ↔ k = 1 ∨ k = a ∨ k = b ∨ k = a * b := by
    intro k
    rw [hA]
    refine ⟨fun hk => mem_closure_pair_cases hab ha hb hk, ?_⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have h4ne1 : a * b ≠ 1 := by
    intro h
    exact hne (by rw [← mul_one a, ← hb, ← mul_assoc, h, one_mul])
  have hab4a : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (by rw [h, mul_one]))
  have hab4b : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (by rw [h, one_mul]))
  have hcardA : Nat.card A = 4 := by
    have hset : (A : Set T) = ((({1, a, b, a * b} : Finset T)) : Set T) := by
      ext k
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      exact hmem k
    have h : Nat.card A = Nat.card ((({1, a, b, a * b} : Finset T)) : Set T) :=
      Nat.card_congr (Set.equivOfEq hset)
    rw [h, Nat.card_eq_card_toFinset, Finset.toFinset_coe]
    have hne1 : (1 : T) ∉ ({a, b, a * b} : Finset T) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, h4ne1.symm⟩
    have hnet : a ∉ ({b, a * b} : Finset T) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, hab4a.symm⟩
    have hnes : b ∉ ({a * b} : Finset T) := by
      simp only [Finset.mem_singleton]
      exact hab4b.symm
    rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hnet,
      Finset.card_insert_of_notMem hnes, Finset.card_singleton]
  have hcentral : Subgroup.centralizer (A : Set T) = A := by
    apply le_antisymm
    · intro x hx
      rw [hmem x]
      exact hC x ((Subgroup.mem_centralizer_iff.mp hx) a
        (Subgroup.subset_closure (by simp))).symm
    · have hcomm : Set.Pairwise ({a, b} : Set T) Commute := by
        intro x hx y hy hxy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hab
        · exact hab.symm
        · exact absurd rfl hxy
      haveI : IsMulCommutative A := by
        rw [hA]
        exact Subgroup.isMulCommutative_closure hcomm
      exact Subgroup.le_centralizer A
  rcases lemma33 hT A hcardA hcentral with htop | ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact (z18_closure_pair_ne_top ha hb hab hbig (hA ▸ htop)).elim
  · have hDexp : ∀ g : DihedralGroup (2 ^ m), g ^ 4 = 1 := by
      intro g
      have h := congrArg e (hexp (e.symm g))
      simpa [map_pow, e.apply_symm_apply] using h
    have hm12 : m = 1 ∨ m = 2 := by
      have := z18_dih_exp hDexp
      omega
    rcases hm12 with hm1 | hm2
    · subst hm1
      have hcardT : Nat.card T = 4 := by
        calc
          Nat.card T = Nat.card (DihedralGroup (2 ^ 1)) := Nat.card_congr e.toEquiv
          _ = 2 * 2 ^ 1 := DihedralGroup.nat_card
          _ = 4 := by norm_num
      exact (z18_closure_pair_ne_top ha hb hab hbig
        (hA ▸ Subgroup.eq_top_of_card_eq A (by rw [hcardA, hcardT]))).elim
    · subst hm2
      have e4 : T ≃* DihedralGroup 4 :=
        e.trans (MulEquiv.cast (show (2 : ℕ) ^ 2 = 4 by norm_num))
      have hsa : e4 a * e4 a = 1 := by rw [← map_mul, ha, map_one]
      have hsb : e4 b * e4 b = 1 := by rw [← map_mul, hb, map_one]
      have hsab : e4 a * e4 b = e4 b * e4 a := by rw [← map_mul, ← map_mul, hab]
      have hsa1 : e4 a ≠ 1 := fun h => ha1 (e4.injective (by rw [h, map_one]))
      have hsb1 : e4 b ≠ 1 := fun h => hb1 (e4.injective (by rw [h, map_one]))
      have hsne : e4 a ≠ e4 b := fun h => hne (e4.injective h)
      have hsC : ∀ x : DihedralGroup 4, x * e4 a = e4 a * x →
          x = 1 ∨ x = e4 a ∨ x = e4 b ∨ x = e4 a * e4 b := by
        intro x hx
        have hx' : e4.symm x * a = a * e4.symm x := by
          have h := congrArg e4.symm hx
          simpa [map_mul] using h
        rcases hC (e4.symm x) hx' with h | h | h | h
        · left; rw [← e4.apply_symm_apply x, h, map_one]
        · right; left; rw [← e4.apply_symm_apply x, h]
        · right; right; left; rw [← e4.apply_symm_apply x, h]
        · right; right; right; rw [← e4.apply_symm_apply x, h, map_mul]
      have hsconj : ∀ g : DihedralGroup 4, g * e4 a * g⁻¹ ≠ e4 b := by
        intro g hg
        exact hconj (e4.symm g) (by
          have h := congrArg e4.symm hg
          simpa [map_mul, map_inv] using h)
      have hcheck := z18_d8_check hsa hsb hsab hsa1 hsb1 hsne hsC hsconj
      refine ⟨(Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4)).comap e4.toMonoidHom,
        ?_, ?_, ?_⟩
      · rw [Subgroup.index_comap_of_surjective
          (H := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4))
          (f := e4.toMonoidHom) e4.surjective]
        have hR : Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4)) = 4 := by
          calc
            Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4))
                = orderOf (DihedralGroup.r 1 : DihedralGroup 4) :=
                  Nat.card_zpowers (DihedralGroup.r 1 : DihedralGroup 4)
            _ = 4 := DihedralGroup.orderOf_r_one
        have hcardD : Nat.card (DihedralGroup 4) = 8 := by
          calc
            Nat.card (DihedralGroup 4) = 2 * 4 := DihedralGroup.nat_card
            _ = 8 := by norm_num
        have hidx := Subgroup.card_mul_index
          (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4))
        rw [hR, hcardD] at hidx
        omega
      · intro haM
        have hRa : e4 a ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4) :=
          (Subgroup.mem_comap).mp haM
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hRa
        rw [DihedralGroup.r_one_zpow] at hk
        exact hcheck.1 (k : ZMod 4) hk
      · intro u huM huu
        have huR : e4 u ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 4) :=
          (Subgroup.mem_comap).mp huM
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huR
        rw [DihedralGroup.r_one_zpow] at hk
        have hsq : DihedralGroup.r (k : ZMod 4) * DihedralGroup.r (k : ZMod 4) = 1 := by
          rw [hk, ← map_mul, huu, map_one]
        rcases hcheck.2 (k : ZMod 4) hsq with h | h
        · left; apply e4.injective; rw [map_one, hk.symm, h]
        · right; apply e4.injective; rw [hk.symm, h]
  · obtain ⟨g, hg⟩ := z18_sd_not_exp4 hn
    exact (hg (by
      have h := congrArg e (hexp (e.symm g))
      simpa [map_pow, e.apply_symm_apply] using h)).elim
  · haveI : NeZero (2 ^ m) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
    have hqa : e a * e a = 1 := by rw [← map_mul, ha, map_one]
    have hqb : e b * e b = 1 := by rw [← map_mul, hb, map_one]
    have hqa1 : e a ≠ 1 := fun h => ha1 (e.injective (by rw [h, map_one]))
    have hqb1 : e b ≠ 1 := fun h => hb1 (e.injective (by rw [h, map_one]))
    exact (hne (e.injective (z18_quat_unique_invol hqa hqb hqa1 hqb1))).elim

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
