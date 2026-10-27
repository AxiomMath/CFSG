module

public import CFSG.Fischer.Classification.PartIII.Symp.Transvection

public section

namespace CFSG.Fischer.Classification.LocalSymp

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer Symplectic Matrix

variable {n : ℕ}

section SymplecticType

@[expose] def permAct (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun k => x (σ⁻¹ k)

theorem permAct_mul (σ τ : Equiv.Perm (Fin n)) : permAct (σ * τ) = permAct σ ∘ permAct τ := by
  funext x k
  simp [permAct, _root_.mul_inv_rev, Equiv.Perm.mul_apply]

theorem permAct_injective : Function.Injective (permAct (n := n)) := by
  intro σ τ h
  apply inv_injective
  ext k
  have := congrFun (congrFun h (Pi.single (σ⁻¹ k) 1)) k
  simp only [permAct, Pi.single_eq_same] at this
  by_contra hne
  rw [Pi.single_eq_of_ne (fun h => hne (congrArg Fin.val h.symm))] at this
  exact one_ne_zero this

theorem permAct_swap {i j : Fin n} (hij : i ≠ j) :
    permAct (Equiv.swap i j) =
      tv (dotProductBilin (ZMod 2) (ZMod 2)) (Pi.single i 1 + Pi.single j 1) := by
  funext x k
  simp only [permAct, Equiv.swap_inv, tv_apply, dotProductBilin_apply_apply, dotProduct_add,
    dotProduct_single, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero, mul_one,
      ← add_assoc, zmod2_add_self, zero_add]
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), zero_add,
      mul_one, add_comm (x i), ← add_assoc, zmod2_add_self, zero_add]
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
      add_zero, mul_zero, add_zero]

theorem isSymplecticType_isSwap :
    IsSymplecticType {σ : Equiv.Perm (Fin n) | σ.IsSwap} := by
  refine isSymplecticType_of_tv (dotProductBilin (ZMod 2) (ZMod 2)) permAct (fun x y => ?_)
    permAct_mul permAct_injective ?_
  · rw [dotProductBilin_apply_apply, dotProductBilin_apply_apply, dotProduct_comm]
  · rintro σ ⟨i, j, hij, rfl⟩
    refine ⟨Pi.single i 1 + Pi.single j 1, ?_, permAct_swap hij⟩
    rw [dotProductBilin_apply_apply, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_single, dotProduct_single, dotProduct_single, dotProduct_single,
      Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij)]
    rfl

end SymplecticType

section Count

theorem eq_of_isSwap_of_support_eq {σ τ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (h : σ.support = τ.support) : σ = τ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hcd] at h
  have h' := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
  simp only [Finset.coe_pair] at h'
  rcases Set.pair_eq_pair_iff.1 h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Equiv.swap_comm _ _

theorem ncard_isSwap_le : {σ : Equiv.Perm (Fin n) | σ.IsSwap}.ncard ≤ n.choose 2 := by
  have h := Set.ncard_le_ncard_of_injOn (t := ((Finset.univ : Finset (Fin n)).powersetCard 2 :
      Set (Finset (Fin n)))) (fun σ => σ.support)
    (fun σ hσ => by
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Equiv.Perm.card_support_eq_two.2 hσ⟩)
    fun σ hσ τ hτ h => eq_of_isSwap_of_support_eq hσ hτ h
  rwa [Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h

theorem swap_mul_swap_comm {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  refine (Equiv.Perm.Disjoint.commute fun x => ?_).eq
  by_cases hx : x = a ∨ x = b
  · right
    rcases hx with rfl | rfl
    · exact Equiv.swap_apply_of_ne_of_ne hac had
    · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · push Not at hx
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hx.1 hx.2)

theorem swap_ne_swap {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    Equiv.swap a b ≠ Equiv.swap c d := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) h
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac had] at this
  exact hab this.symm

variable (h3 : 3 ≤ n)

abbrev i0 : Fin n := ⟨0, by omega⟩

abbrev i1 : Fin n := ⟨1, by omega⟩

abbrev i2 : Fin n := ⟨2, by omega⟩

theorem i0_ne_i1 : i0 h3 ≠ i1 h3 := Fin.ne_of_val_ne (by simp)

theorem i0_ne_i2 : i0 h3 ≠ i2 h3 := Fin.ne_of_val_ne (by simp)

theorem i1_ne_i2 : i1 h3 ≠ i2 h3 := Fin.ne_of_val_ne (by simp)

theorem swap_mul_swap_ne :
    Equiv.swap (i0 h3) (i1 h3) * Equiv.swap (i1 h3) (i2 h3) ≠
      Equiv.swap (i1 h3) (i2 h3) * Equiv.swap (i0 h3) (i1 h3) := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (i0 h3)) h
  simp only [Equiv.Perm.mul_apply] at this
  rw [Equiv.swap_apply_of_ne_of_ne (i0_ne_i1 h3) (i0_ne_i2 h3), Equiv.swap_apply_left,
    Equiv.swap_apply_left] at this
  exact i1_ne_i2 h3 this

theorem choose_le_ncard_muSet_isSwap :
    (n - 3).choose 2 ≤ (muSet {σ : Equiv.Perm (Fin n) | σ.IsSwap} (Equiv.swap (i0 h3) (i1 h3))
      (Equiv.swap (i1 h3) (i2 h3))).ncard := by
  set S := ({i0 h3, i1 h3, i2 h3} : Finset (Fin n))
  have hS : S.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [i0_ne_i1 h3, i0_ne_i2 h3]),
      Finset.card_pair (i1_ne_i2 h3)]
  set T := (Finset.univ \ S).powersetCard 2
  have hT : T.card = (n - 3).choose 2 := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, hS]
  have hsub : (T : Set (Finset (Fin n))) ⊆ (fun σ => σ.support) ''
      muSet {σ : Equiv.Perm (Fin n) | σ.IsSwap} (Equiv.swap (i0 h3) (i1 h3))
        (Equiv.swap (i1 h3) (i2 h3)) := by
    intro A hA
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hA
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hA.2
    have ha : a ∉ S := (Finset.mem_sdiff.1 (hA.1 (Finset.mem_insert_self a {b}))).2
    have hb : b ∉ S := (Finset.mem_sdiff.1 (hA.1 (by simp))).2
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
    refine ⟨Equiv.swap a b, ⟨⟨⟨a, b, hab, rfl⟩, swap_ne_swap hab ha.1 ha.2.1,
      swap_mul_swap_comm ha.1 ha.2.1 hb.1 hb.2.1⟩, ⟨⟨a, b, hab, rfl⟩,
      swap_ne_swap hab ha.2.1 ha.2.2, swap_mul_swap_comm ha.2.1 ha.2.2 hb.2.1 hb.2.2⟩⟩,
      Equiv.Perm.support_swap hab⟩
  calc (n - 3).choose 2 = (T : Set (Finset (Fin n))).ncard := by rw [Set.ncard_coe_finset, hT]
    _ ≤ _ := Set.ncard_le_ncard hsub
    _ ≤ _ := Set.ncard_image_le

theorem choose_two_lt {n : ℕ} (hn : n = 3 ∨ 6 ≤ n) : n.choose 2 < 4 * (1 + (n - 3).choose 2) := by
  rcases hn with rfl | hn
  · decide
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : (6 + (k + 1)).choose 2 = (6 + k).choose 2 + (6 + k) := by
      rw [show 6 + (k + 1) = (6 + k) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right,
        add_comm]
    have h2 : (6 + (k + 1) - 3).choose 2 = (6 + k - 3).choose 2 + (6 + k - 3) := by
      rw [show 6 + (k + 1) - 3 = (6 + k - 3) + 1 by omega, Nat.choose_succ_succ,
        Nat.choose_one_right, add_comm]
    rw [h1, h2]
    have := ih (by omega)
    omega

end Count

end CFSG.Fischer.Classification.LocalSymp
