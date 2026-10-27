module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Cover

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

section Geometry

theorem card_lines_through : ∀ φ ∈ Rset, (Rset.filter (fun x => dot φ x = 0)).card = 4 := by
  decide

theorem ker_erase_eq : ∀ φ ∈ Rset, (Finset.univ.filter (fun z : Z3 => dot φ z = 0)).erase 0 =
    Rset.filter (fun x => dot φ x = 0) ∪
      (Rset.filter (fun x => dot φ x = 0)).image (fun x => x + x) := by
  decide

theorem disjoint_lines : ∀ φ ∈ Rset, Disjoint (Rset.filter (fun x => dot φ x = 0))
    ((Rset.filter (fun x => dot φ x = 0)).image (fun x => x + x)) := by
  decide

theorem add_self_injective : ∀ x y : Z3, x + x = y + y → x = y := by
  decide

theorem ne_zero_of_mem_Rset : ∀ x ∈ Rset, x ≠ 0 := by
  decide

end Geometry

section Cover

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def eCyc (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) : Module.End K V :=
  act ρ 0 + act ρ x + act ρ (x + x)

theorem three_smul_z3 (x : Z3) : x + x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = t
  revert t
  decide

theorem eCyc_mem_fixOf (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) (v : V) :
    eCyc ρ x v ∈ fixOf ρ {x} := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simp only [eCyc, LinearMap.add_apply, map_add]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← act_add, ← act_add,
    ← act_add, add_zero, ← add_assoc, three_smul_z3]
  abel

theorem eCyc_of_mem [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {x : Z3} {v : V}
    (hv : v ∈ fixOf ρ {x}) : eCyc ρ x v = v := by
  have hx : act ρ x v = v := hv x rfl
  have hxx : act ρ (x + x) v = v := by rw [act_add, Module.End.mul_apply, hx, hx]
  simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, hx, hxx]
  have h2 : v + v = 0 := by rw [← two_nsmul]; exact two_nsmul_eq_zero' (K := K) v
  rw [h2, zero_add]

theorem eCyc_comm_eN (ρ : Multiplicative Z3 →* Module.End K V) (x φ : Z3) (v : V) :
    eN ρ φ (eCyc ρ x v) = eCyc ρ x (eN ρ φ v) := by
  simp only [eCyc, LinearMap.add_apply, map_add, act_eN_comm]

theorem sum_eCyc [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {φ : Z3} (hφ : φ ∈ Rset)
    (v : V) : ∑ x ∈ Rset.filter (fun x => dot φ x = 0), eCyc ρ x v = v + eN ρ φ v := by
  classical
  set L := Rset.filter (fun x => dot φ x = 0) with hL
  have h0 : (0 : Z3) ∈ Finset.univ.filter (fun z : Z3 => dot φ z = 0) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [dot]⟩
  have hN : eN ρ φ v = act ρ 0 v + ∑ z ∈ (Finset.univ.filter (fun z : Z3 => dot φ z = 0)).erase 0,
      act ρ z v := by
    unfold eN
    rw [LinearMap.sum_apply, ← Finset.add_sum_erase _ _ h0]
  have hsplit : ∑ z ∈ (Finset.univ.filter (fun z : Z3 => dot φ z = 0)).erase 0, act ρ z v =
      ∑ x ∈ L, act ρ x v + ∑ x ∈ L, act ρ (x + x) v := by
    rw [ker_erase_eq φ hφ, Finset.sum_union (disjoint_lines φ hφ),
      Finset.sum_image (fun x _ y _ hxy => add_self_injective x y hxy)]
  have hLsum : ∑ x ∈ L, eCyc ρ x v =
      L.card • v + (∑ x ∈ L, act ρ x v + ∑ x ∈ L, act ρ (x + x) v) := by
    simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, Finset.sum_add_distrib,
      Finset.sum_const]
    abel
  rw [hLsum, card_lines_through φ hφ, ← hsplit, hN, act_zero, Module.End.one_apply]
  have h4 : (4 : ℕ) • v = 0 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, mul_smul, two_nsmul_eq_zero' (K := K)]
  have h2 : v + v = 0 := by rw [← two_nsmul]; exact two_nsmul_eq_zero' (K := K) v
  rw [h4, zero_add, ← add_assoc, h2, zero_add]

theorem finrank_finset_sup_le [FiniteDimensional K V] {ι : Type*} (L : Finset ι)
    (Y : ι → Submodule K V) : finrank K (L.sup Y : Submodule K V) ≤ ∑ x ∈ L, finrank K (Y x) := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert a L ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

theorem range_eN [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {φ : Z3} (hφ : φ ∈ Rset) :
    LinearMap.range (eN ρ φ) = fixOf ρ {x | dot φ x = 0} := by
  refine le_antisymm ?_ fun v hv => ⟨v, eN_of_mem ρ hφ hv⟩
  rintro _ ⟨v, rfl⟩
  exact eN_mem_fixOf ρ φ v

theorem exists_six_of_twelve [CharP K 2] [FiniteDimensional K V]
    (ρ : Multiplicative Z3 →* Module.End K V)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp1 : ∀ x : Z3, x ≠ 0 → Even (finrank K (fixOf ρ {x})))
    (h12 : 12 ≤ finrank K V) {φ : Z3} (hφ : φ ∈ Rset) (hW : fixOf ρ {x | dot φ x = 0} ≠ ⊥) :
    ∃ x ∈ Rset, dot φ x = 0 ∧ 6 ≤ finrank K (fixOf ρ {x}) := by
  classical
  set W := fixOf ρ {x | dot φ x = 0} with hWdef
  set L := Rset.filter (fun x => dot φ x = 0) with hL
  set X : Submodule K V := LinearMap.ker (eN ρ φ) with hX
  set Xx : Z3 → Submodule K V := fun x => X ⊓ fixOf ρ {x} with hXx
  by_contra hcon
  push Not at hcon
  have hWX : ∀ x, W ⊓ Xx x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvX, -⟩
    rw [Submodule.mem_bot, ← eN_of_mem ρ hφ hvW]
    exact LinearMap.mem_ker.1 hvX
  have hWle : ∀ x ∈ L, W ≤ fixOf ρ {x} := by
    intro x hx v hv y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hv y (by
      have := (Finset.mem_filter.1 hx).2
      simpa [dot, mul_comm] using this)
  have hdimx : ∀ x ∈ L, finrank K W + finrank K (Xx x) ≤ finrank K (fixOf ρ {x}) := by
    intro x hx
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Xx x)
    rw [hWX x, finrank_bot, add_zero] at h1
    rw [← h1]
    exact Submodule.finrank_mono (sup_le (hWle x hx) inf_le_right)
  have hXle : X ≤ L.sup Xx := by
    intro v hv
    have hv0 : eN ρ φ v = 0 := LinearMap.mem_ker.1 hv
    have hsum := sum_eCyc ρ hφ v
    rw [hv0, add_zero] at hsum
    rw [← hsum]
    refine Submodule.sum_mem _ fun x hx => ?_
    refine (Finset.le_sup (f := Xx) hx) ⟨?_, eCyc_mem_fixOf ρ x v⟩
    change eN ρ φ (eCyc ρ x v) = 0
    rw [eCyc_comm_eN, hv0, map_zero]
  have hXdim : finrank K X ≤ ∑ x ∈ L, finrank K (Xx x) :=
    (Submodule.finrank_mono hXle).trans (finrank_finset_sup_le L Xx)
  have hrn : finrank K W + finrank K X = finrank K V := by
    have := LinearMap.finrank_range_add_finrank_ker (eN ρ φ)
    rw [range_eN ρ hφ] at this
    exact this
  have h4 : ∀ x ∈ L, finrank K (fixOf ρ {x}) ≤ 4 := by
    intro x hx
    have hxR := (Finset.mem_filter.1 hx).1
    have h6 := hcon x hxR (Finset.mem_filter.1 hx).2
    obtain ⟨k, hk⟩ := hp1 x (ne_zero_of_mem_Rset x hxR)
    omega
  have hsum4 : ∑ x ∈ L, finrank K (fixOf ρ {x}) ≤ 16 := by
    calc ∑ x ∈ L, finrank K (fixOf ρ {x}) ≤ ∑ _x ∈ L, 4 := Finset.sum_le_sum h4
      _ = 16 := by rw [Finset.sum_const, card_lines_through φ hφ, smul_eq_mul]
  have hsumlow : 4 * finrank K W + ∑ x ∈ L, finrank K (Xx x) ≤
      ∑ x ∈ L, finrank K (fixOf ρ {x}) := by
    calc 4 * finrank K W + ∑ x ∈ L, finrank K (Xx x)
        = ∑ x ∈ L, (finrank K W + finrank K (Xx x)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, card_lines_through φ hφ, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hdimx
  have hW2 : 2 ≤ finrank K W := by
    have hpos : 0 < finrank K W := Nat.pos_of_ne_zero fun h => hW (Submodule.finrank_eq_zero.1 h)
    obtain ⟨k, hk⟩ := hpN φ hφ
    have hk' : finrank K W = k + k := hk
    omega
  omega

@[expose] def GoodSix (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) : Prop :=
  x ≠ 0 ∧ 6 ≤ finrank K (fixOf ρ {x}) ∧ ∃ y : Z3, ∃ u ∈ fixOf ρ {x}, act ρ y u ≠ u

theorem fixOf_univ_le (ρ : Multiplicative Z3 →* Module.End K V) (S : Set Z3) :
    fixOf ρ Set.univ ≤ fixOf ρ S := fun _ hv x _ => hv x (Set.mem_univ x)

theorem cover_six [CharP K 2] [FiniteDimensional K V] (ρ : Multiplicative Z3 →* Module.End K V)
    (hfaith : ∀ x, act ρ x = 1 → x = 0)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp1 : ∀ x : Z3, x ≠ 0 → Even (finrank K (fixOf ρ {x})))
    (h12 : 12 ≤ finrank K V) :
    (⊤ : Submodule K V) ≤ ⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x} := by
  classical
  have hgood_of : ∀ x : Z3, 6 ≤ finrank K (fixOf ρ {x}) → fixOf ρ {x} ≤ fixOf ρ Set.univ →
      ∃ x', GoodSix ρ x' ∧ fixOf ρ Set.univ ≤ fixOf ρ {x'} := by
    intro x hx6 hxu
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Z3, act ρ y₀ ≠ 1 := ⟨![1, 0, 0], fun h => by
      have := hfaith _ h
      have h0 := congrFun this 0
      simp at h0⟩
    obtain ⟨u, hu⟩ : ∃ u, act ρ y₀ u ≠ u := by
      by_contra hall
      push Not at hall
      exact hy₀ (LinearMap.ext fun v => by simpa using hall v)
    obtain ⟨φ', hφ', hmv⟩ : ∃ φ' ∈ Rset, act ρ y₀ (eN ρ φ' u) ≠ eN ρ φ' u := by
      by_contra hall
      push Not at hall
      apply hu
      rw [← sum_eN (K := K) ρ u, map_sum]
      exact Finset.sum_congr rfl fun φ' hφ' => hall φ' hφ'
    obtain ⟨x', hx'⟩ : ∃ x', x' ∈ Rset.filter (fun x => dot φ' x = 0) := by
      have := card_lines_through φ' hφ'
      exact Finset.card_pos.1 (by omega)
    have hx'R := (Finset.mem_filter.1 hx').1
    have hx'φ := (Finset.mem_filter.1 hx').2
    have hmem : eN ρ φ' u ∈ fixOf ρ {x'} := fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact eN_mem_fixOf ρ φ' u y (by simpa [dot, mul_comm] using hx'φ)
    refine ⟨x', ⟨ne_zero_of_mem_Rset x' hx'R, ?_, y₀, _, hmem, hmv⟩, fixOf_univ_le ρ _⟩
    exact hx6.trans (Submodule.finrank_mono (hxu.trans (fixOf_univ_le ρ _)))
  have hN : ∀ φ ∈ Rset, fixOf ρ {x | dot φ x = 0} ≤ ⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x} := by
    intro φ hφ
    by_cases hW : fixOf ρ {x | dot φ x = 0} = ⊥
    · rw [hW]
      exact bot_le
    obtain ⟨x, hxR, hxφ, hx6⟩ := exists_six_of_twelve ρ hpN hp1 h12 hφ hW
    have hWx : fixOf ρ {x | dot φ x = 0} ≤ fixOf ρ {x} := fun v hv y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hv y (by simpa [dot, mul_comm] using hxφ)
    by_cases hmv : ∃ y : Z3, ∃ u ∈ fixOf ρ {x}, act ρ y u ≠ u
    · exact hWx.trans (le_iSup₂_of_le x ⟨ne_zero_of_mem_Rset x hxR, hx6, hmv⟩ le_rfl)
    · push Not at hmv
      have hxu : fixOf ρ {x} ≤ fixOf ρ Set.univ := fun u hu y _ => hmv y u hu
      obtain ⟨x', hx', hux'⟩ := hgood_of x hx6 hxu
      exact (hWx.trans (hxu.trans hux')).trans (le_iSup₂_of_le x' hx' le_rfl)
  intro v _
  rw [← sum_eN (K := K) ρ v]
  exact Submodule.sum_mem _ fun φ hφ => hN φ hφ (eN_mem_fixOf ρ φ v)

end Cover

end CFSG.HardMathSupport.Timmesfeld.CrossChar
