module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltHeartFaithful
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CanonicalHeart

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {n : ℕ}

theorem evenWeightPerm_apply (σ : Perm (Fin n)) (x : evenWeight n) (i : Fin n) :
    (evenWeightPerm σ x : Fin n → ZMod 2) i = (x : Fin n → ZMod 2) (σ⁻¹ i) := rfl

@[expose] def evenWeightPermHom (σ : Perm (Fin n)) : evenWeight n →+ evenWeight n where
  toFun := evenWeightPerm σ
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem mem_evenWeightOnes_of_forall_eq {x : evenWeight n} {c : ZMod 2}
    (h : ∀ i, (x : Fin n → ZMod 2) i = c) : x ∈ evenWeightOnes n := by
  show (x : Fin n → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes n)
  rw [AddSubgroup.mem_zmultiples_iff]
  rcases zmod_two_cases c with rfl | rfl
  · exact ⟨0, funext fun i => by simp [h i]⟩
  · exact ⟨1, funext fun i => by simp [h i, allOnes]⟩

theorem exists_forall_eq_of_mem_evenWeightOnes {x : evenWeight n} (hx : x ∈ evenWeightOnes n) :
    ∃ c : ZMod 2, ∀ i, (x : Fin n → ZMod 2) i = c := by
  have hx' : (x : Fin n → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes n) := hx
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx'
  exact ⟨(k : ZMod 2), fun i => by rw [← hk]; simp [allOnes]⟩

@[expose] noncomputable def altAct (σ : Perm (Fin n)) : altHeart n →+ altHeart n :=
  QuotientAddGroup.map _ _ (evenWeightPermHom σ) fun x hx => by
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    exact mem_evenWeightOnes_of_forall_eq (c := c) fun i => hc _

theorem altAct_mk (σ : Perm (Fin n)) (x : evenWeight n) :
    altAct σ (x : altHeart n) = (evenWeightPerm σ x : altHeart n) := rfl

theorem altAct_mul (σ τ : Perm (Fin n)) (v : altHeart n) :
    altAct (σ * τ) v = altAct σ (altAct τ v) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

theorem altAct_one (v : altHeart n) : altAct 1 v = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

theorem altAct_inv_apply (σ : Perm (Fin n)) (v : altHeart n) : altAct σ⁻¹ (altAct σ v) = v := by
  rw [← altAct_mul, inv_mul_cancel, altAct_one]

theorem altAct_apply_inv (σ : Perm (Fin n)) (v : altHeart n) : altAct σ (altAct σ⁻¹ v) = v := by
  rw [← altAct_mul, mul_inv_cancel, altAct_one]

private theorem pairEW_apply_single (a b i : Fin n) :
    ((pairEW a b : evenWeight n) : Fin n → ZMod 2) i =
      (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) i +
        (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) i := by
  rw [pairEW_apply, Pi.single_apply, Pi.single_apply]

theorem evenWeightPerm_pairEW (σ : Perm (Fin n)) (a b : Fin n) :
    evenWeightPerm σ (pairEW a b) = pairEW (σ a) (σ b) :=
  Subtype.ext (funext fun p => by rw [evenWeightPerm_pairEW_apply, pairEW_apply])

theorem pairEW_comm (a b : Fin n) : pairEW a b = pairEW b a :=
  Subtype.ext (funext fun p => by rw [pairEW_apply, pairEW_apply, add_comm])

theorem mk_pairEW_ne_zero {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (pairEW a b : altHeart n) ≠ 0 := by
  intro h
  obtain ⟨d, hd⟩ := exists_forall_eq_of_mem_evenWeightOnes ((QuotientAddGroup.eq_zero_iff _).1 h)
  have ha := hd a
  have hc := hd c
  rw [pairEW_apply_single, Pi.single_eq_same, Pi.single_eq_of_ne hab] at ha
  rw [pairEW_apply_single, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb] at hc
  rw [← hc] at ha
  exact absurd ha (by decide)

theorem apply_inv_eq_of_mk_eq {σ : Perm (Fin n)} {a : Fin n} (ha : σ a = a) {x : evenWeight n}
    (h : (evenWeightPerm σ x : altHeart n) = (x : altHeart n)) (i : Fin n) :
    (x : Fin n → ZMod 2) (σ⁻¹ i) = (x : Fin n → ZMod 2) i := by
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes (QuotientAddGroup.eq.1 h)
  have hσa : σ⁻¹ a = a := by rw [Perm.inv_eq_iff_eq]; exact ha.symm
  have hca := hc a
  have hci := hc i
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply,
    evenWeightPerm_apply] at hca hci
  rw [hσa, neg_add_cancel] at hca
  rw [← hca] at hci
  exact neg_add_eq_zero.1 hci

theorem zmod_two_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert a b; decide

theorem altHeart_endo_eq_zero_or_id (hn : 5 ≤ n) (g : altHeart n →+ altHeart n)
    (hg : ∀ σ ∈ alternatingGroup (Fin n), ∀ v, g (altAct σ v) = altAct σ (g v)) :
    g = 0 ∨ g = AddMonoidHom.id (altHeart n) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  set i3 : Fin n := ⟨3, by omega⟩ with hi3
  set i4 : Fin n := ⟨4, by omega⟩ with hi4
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have h03 : i0 ≠ i3 := by simp [hi0, hi3, Fin.ext_iff]
  have h04 : i0 ≠ i4 := by simp [hi0, hi4, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  have h13 : i1 ≠ i3 := by simp [hi1, hi3, Fin.ext_iff]
  have h14 : i1 ≠ i4 := by simp [hi1, hi4, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [hi2, hi3, Fin.ext_iff]
  have h24 : i2 ≠ i4 := by simp [hi2, hi4, Fin.ext_iff]
  have h34 : i3 ≠ i4 := by simp [hi3, hi4, Fin.ext_iff]
  set p : altHeart n := (pairEW i0 i1 : altHeart n) with hp
  have hp0 : p ≠ 0 := mk_pairEW_ne_zero h01 h02.symm h12.symm
  have key : ∀ U : AddSubgroup (altHeart n),
      (∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ U, altAct σ v ∈ U) → p ∈ U → U = ⊤ := by
    intro U hU hpU
    rcases altHeart_irreducible (by omega) U (fun σ hσ x hx => by
      rw [← altAct_mk]; exact hU σ hσ _ hx) with h | h
    · exact absurd ((AddSubgroup.mem_bot).1 (h ▸ hpU)) hp0
    · exact h
  have hfix : ∀ σ ∈ alternatingGroup (Fin n), altAct σ p = p → altAct σ (g p) = g p := by
    intro σ hσ hσp
    rw [← hg σ hσ, hσp]
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (g p)
  have hconst : ∀ i : Fin n, i ≠ i0 → i ≠ i1 →
      (y : Fin n → ZMod 2) i = (y : Fin n → ZMod 2) i2 := by
    intro i hi0' hi1'
    by_cases hi2' : i = i2
    · rw [hi2']
    obtain ⟨k, hk0, hk1, hk2, hki⟩ := exists_ne_four hn i0 i1 i2 i
    set σ : Perm (Fin n) := swap i i2 * swap i2 k with hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, hσ, map_mul, sign_swap hi2', sign_swap (Ne.symm hk2)]
      decide
    have hσ0 : σ i0 = i0 := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne h02 (Ne.symm hk0),
        swap_apply_of_ne_of_ne (Ne.symm hi0') h02]
    have hσ1 : σ i1 = i1 := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne h12 (Ne.symm hk1),
        swap_apply_of_ne_of_ne (Ne.symm hi1') h12]
    have hσi : σ i = i2 := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne hi2' (Ne.symm hki), swap_apply_left]
    have hσp : altAct σ p = p := by
      rw [hp, altAct_mk, evenWeightPerm_pairEW, hσ0, hσ1]
    have hyσ : (evenWeightPerm σ y : altHeart n) = (y : altHeart n) := by
      rw [← altAct_mk, hy, hfix σ hσA hσp]
    have := apply_inv_eq_of_mk_eq hσ0 hyσ i2
    rwa [show σ⁻¹ i2 = i by rw [Perm.inv_eq_iff_eq, hσi]] at this
  have hy01 : (y : Fin n → ZMod 2) i0 = (y : Fin n → ZMod 2) i1 := by
    set τ : Perm (Fin n) := swap i0 i1 * swap i2 i3 with hτ
    have hτA : τ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, hτ, map_mul, sign_swap h01, sign_swap h23]
      decide
    have hτ4 : τ i4 = i4 := by
      rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm h24) (Ne.symm h34),
        swap_apply_of_ne_of_ne (Ne.symm h04) (Ne.symm h14)]
    have hτ0 : τ i0 = i1 := by
      rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne h02 h03, swap_apply_left]
    have hτ1 : τ i1 = i0 := by
      rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne h12 h13, swap_apply_right]
    have hτp : altAct τ p = p := by
      rw [hp, altAct_mk, evenWeightPerm_pairEW, hτ0, hτ1, pairEW_comm]
    have hyτ : (evenWeightPerm τ y : altHeart n) = (y : altHeart n) := by
      rw [← altAct_mk, hy, hfix τ hτA hτp]
    have := apply_inv_eq_of_mk_eq hτ4 hyτ i0
    rw [show τ⁻¹ i0 = i1 by rw [Perm.inv_eq_iff_eq, hτ1]] at this
    exact this.symm
  have hgp : g p = 0 ∨ g p = p := by
    by_cases hc : (y : Fin n → ZMod 2) i0 = (y : Fin n → ZMod 2) i2
    · left
      rw [← hy]
      refine (QuotientAddGroup.eq_zero_iff _).2
        (mem_evenWeightOnes_of_forall_eq (c := (y : Fin n → ZMod 2) i2) ?_)
      intro i
      by_cases hi0' : i = i0
      · rw [hi0', hc]
      by_cases hi1' : i = i1
      · rw [hi1', ← hy01, hc]
      exact hconst i hi0' hi1'
    · right
      rw [← hy, hp]
      refine QuotientAddGroup.eq.2
        (mem_evenWeightOnes_of_forall_eq (c := -((y : Fin n → ZMod 2) i2)) ?_)
      intro i
      have hy0 := zmod_two_eq_add_one_of_ne hc
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply,
        pairEW_apply_single]
      by_cases hi0' : i = i0
      · rw [hi0', Pi.single_eq_same, Pi.single_eq_of_ne h01, hy0]
        rcases zmod_two_cases ((y : Fin n → ZMod 2) i2) with h | h <;> rw [h] <;> rfl
      by_cases hi1' : i = i1
      · rw [hi1', Pi.single_eq_of_ne (Ne.symm h01), Pi.single_eq_same, ← hy01, hy0]
        rcases zmod_two_cases ((y : Fin n → ZMod 2) i2) with h | h <;> rw [h] <;> rfl
      rw [Pi.single_eq_of_ne hi0', Pi.single_eq_of_ne hi1', hconst i hi0' hi1']
      rcases zmod_two_cases ((y : Fin n → ZMod 2) i2) with h | h <;> rw [h] <;> rfl
  rcases hgp with h0 | h1
  · left
    have hU := key g.ker (fun σ hσ v hv => by
      rw [AddMonoidHom.mem_ker] at hv ⊢
      rw [hg σ hσ, hv, map_zero]) (AddMonoidHom.mem_ker.2 h0)
    refine AddMonoidHom.ext fun v => ?_
    exact AddMonoidHom.mem_ker.1 (hU ▸ AddSubgroup.mem_top v)
  · right
    let U : AddSubgroup (altHeart n) :=
      { carrier := {v | g v = v}
        add_mem' := fun {a b} (ha : g a = a) (hb : g b = b) => by
          show g (a + b) = a + b
          rw [map_add, ha, hb]
        zero_mem' := map_zero g
        neg_mem' := fun {a} (ha : g a = a) => by
          show g (-a) = -a
          rw [map_neg, ha] }
    have hU := key U (fun σ hσ v (hv : g v = v) => by
      show g (altAct σ v) = altAct σ v
      rw [hg σ hσ, hv]) h1
    refine AddMonoidHom.ext fun v => ?_
    exact (show v ∈ U from hU ▸ AddSubgroup.mem_top v)

end CFSG.HardMathSupport.Cooperstein.Coordinator
