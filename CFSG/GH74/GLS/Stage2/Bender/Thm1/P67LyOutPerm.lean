module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut

open Equiv Equiv.Perm Subgroup

section ThreeCycle

theorem x1p_cycleType {x1p : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1) :
    x1p.cycleType = {3} := by
  subst hx
  exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

private theorem swap_three_four_commute {x1p : Perm (Fin 11)}
    (hx : x1p = swap 0 2 * swap 0 1) : swap (3 : Fin 11) 4 * x1p = x1p * swap 3 4 := by
  subst hx
  decide

theorem exists_even_conj_x1p {x1p y : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1)
    (hy : y.cycleType = {3}) :
    ∃ τ ∈ alternatingGroup (Fin 11), τ * y * τ⁻¹ = x1p := by
  have hconj : IsConj y x1p :=
    isConj_iff_cycleType_eq.2 (hy.trans (x1p_cycleType hx).symm)
  obtain ⟨π, hπ⟩ := isConj_iff.1 hconj
  by_cases hs : sign π = 1
  · exact ⟨π, mem_alternatingGroup.2 hs, hπ⟩
  · refine ⟨swap 3 4 * π, ?_, ?_⟩
    · have hπ' : sign π = -1 := (Int.units_eq_one_or (sign π)).resolve_left hs
      rw [mem_alternatingGroup, map_mul, sign_swap (by decide), hπ']
      rfl
    · calc swap 3 4 * π * y * (swap 3 4 * π)⁻¹ = swap 3 4 * (π * y * π⁻¹) * (swap 3 4)⁻¹ := by
            simp [mul_assoc]
        _ = x1p := by
            rw [hπ, swap_inv, swap_three_four_commute hx, mul_assoc, swap_mul_self, mul_one]

end ThreeCycle

section DoubleCentralizer

private theorem apply_mem_of_commute {x1p σ : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1)
    (h : ∀ c ∈ alternatingGroup (Fin 11), c * x1p = x1p * c → σ * c = c * σ)
    {i j k : Fin 11} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : 3 ≤ i.val) (hj : 3 ≤ j.val) (hk : 3 ≤ k.val) :
    σ i = i ∨ σ i = j ∨ σ i = k := by
  set c : Perm (Fin 11) := swap i j * swap j k with hc
  have hc_alt : c ∈ alternatingGroup (Fin 11) := by
    rw [mem_alternatingGroup, hc, map_mul, sign_swap hij, sign_swap hjk]
    rfl
  have hc_fix : ∀ y : Fin 11, y ≠ i → y ≠ j → y ≠ k → c y = y := by
    intro y hyi hyj hyk
    rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hyj hyk, swap_apply_of_ne_of_ne hyi hyj]
  have hdisj : c.Disjoint x1p := by
    intro y
    by_cases hy : 3 ≤ y.val
    · right
      have h1 : y ≠ 0 := fun e => by rw [e] at hy; exact absurd hy (by decide)
      have h2 : y ≠ 1 := fun e => by rw [e] at hy; exact absurd hy (by decide)
      have h3 : y ≠ 2 := fun e => by rw [e] at hy; exact absurd hy (by decide)
      rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
    · left
      refine hc_fix y ?_ ?_ ?_
      · intro e; rw [e] at hy; exact hy hi
      · intro e; rw [e] at hy; exact hy hj
      · intro e; rw [e] at hy; exact hy hk
  have hσc := h c hc_alt hdisj.commute
  have hci : c i ≠ i := by
    rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, swap_apply_left]
    exact fun e => hij e.symm
  have hmoved : c (σ i) ≠ σ i := by
    have h1 : c (σ i) = σ (c i) := by
      have := congrArg (fun f : Perm (Fin 11) => f i) hσc
      simp only [Perm.mul_apply] at this
      exact this.symm
    rw [h1]
    exact fun e => hci (σ.injective e)
  by_contra hcon
  exact hmoved (hc_fix _ (fun e => hcon (Or.inl e)) (fun e => hcon (Or.inr (Or.inl e)))
    (fun e => hcon (Or.inr (Or.inr e))))

private theorem apply_eq_of_commute {x1p σ : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1)
    (h : ∀ c ∈ alternatingGroup (Fin 11), c * x1p = x1p * c → σ * c = c * σ)
    {i j k l m : Fin 11}
    (hd : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
      3 ≤ i.val ∧ 3 ≤ j.val ∧ 3 ≤ k.val ∧ 3 ≤ l.val ∧ 3 ≤ m.val) :
    σ i = i := by
  obtain ⟨hij, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm, hi, hj, hk, hl, hm⟩ := hd
  have h1 := apply_mem_of_commute hx h hij hik hjk hi hj hk
  have h2 := apply_mem_of_commute hx h hil him hlm hi hl hm
  rcases h1 with h1 | h1 | h1
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hjl
    · exact absurd (h1.symm.trans h2) hjm
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hkl
    · exact absurd (h1.symm.trans h2) hkm

private theorem apply_eq_of_three_le {x1p σ : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1)
    (h : ∀ c ∈ alternatingGroup (Fin 11), c * x1p = x1p * c → σ * c = c * σ)
    (p : Fin 11) (hp : 3 ≤ p.val) : σ p = p := by
  have hcases : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by
    revert p; decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact apply_eq_of_commute hx h (j := 4) (k := 5) (l := 6) (m := 7) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 5) (l := 6) (m := 7) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 6) (m := 7) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 5) (m := 7) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 5) (m := 6) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 5) (m := 6) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 5) (m := 6) (by decide)
  · exact apply_eq_of_commute hx h (j := 3) (k := 4) (l := 5) (m := 6) (by decide)

theorem eq_zpowers_of_commute_of_alt {x1p σ : Perm (Fin 11)} (hx : x1p = swap 0 2 * swap 0 1)
    (h : ∀ c ∈ alternatingGroup (Fin 11), c * x1p = x1p * c → σ * c = c * σ) :
    σ ∈ zpowers x1p := by
  have hfix := apply_eq_of_three_le hx h
  have hx_alt : x1p ∈ alternatingGroup (Fin 11) := by
    rw [mem_alternatingGroup, hx, map_mul, sign_swap (by decide), sign_swap (by decide)]
    rfl
  have hσx : σ * x1p = x1p * σ := h x1p hx_alt rfl
  have hcomm : ∀ y : Fin 11, σ (x1p y) = x1p (σ y) := fun y => by
    have := congrArg (fun f : Perm (Fin 11) => f y) hσx
    simpa only [Perm.mul_apply] using this
  have hxfix : ∀ y : Fin 11, 3 ≤ y.val → x1p y = y := by
    intro y hy
    have h1 : y ≠ 0 := fun e => by rw [e] at hy; exact absurd hy (by decide)
    have h2 : y ≠ 1 := fun e => by rw [e] at hy; exact absurd hy (by decide)
    have h3 : y ≠ 2 := fun e => by rw [e] at hy; exact absurd hy (by decide)
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
  have hx0 : x1p 0 = 1 := by rw [hx]; decide
  have hx1 : x1p 1 = 2 := by rw [hx]; decide
  have hx2 : x1p 2 = 0 := by rw [hx]; decide
  have hlow : ∀ q : Fin 11, q = 0 ∨ q = 1 ∨ q = 2 ∨ 3 ≤ q.val := by decide
  have hσ0 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 2 := by
    rcases hlow (σ 0) with h0 | h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr h0)
    · exfalso
      have h1 : σ (σ 0) = σ 0 := hfix _ h0
      have h2 : σ 0 = 0 := σ.injective h1
      rw [h2] at h0
      exact absurd h0 (by decide)
  have hs1 : σ 1 = x1p (σ 0) := by
    have := hcomm 0
    rwa [hx0] at this
  have hs2 : σ 2 = x1p (σ 1) := by
    have := hcomm 1
    rwa [hx1] at this
  have hlow3 : ∀ y : Fin 11, ¬ 3 ≤ y.val → y = 0 ∨ y = 1 ∨ y = 2 := by decide
  rcases hσ0 with h0 | h0 | h0
  · have e1 : σ 1 = 1 := by rw [hs1, h0, hx0]
    have e2 : σ 2 = 2 := by rw [hs2, e1, hx1]
    have : σ = 1 := by
      refine Equiv.ext fun y => ?_
      by_cases hy : 3 ≤ y.val
      · exact hfix y hy
      · rcases hlow3 y hy with rfl | rfl | rfl
        · exact h0
        · exact e1
        · exact e2
    rw [this]
    exact one_mem _
  · have e1 : σ 1 = 2 := by rw [hs1, h0, hx1]
    have e2 : σ 2 = 0 := by rw [hs2, e1, hx2]
    have : σ = x1p := by
      refine Equiv.ext fun y => ?_
      by_cases hy : 3 ≤ y.val
      · rw [hfix y hy, hxfix y hy]
      · rcases hlow3 y hy with rfl | rfl | rfl
        · rw [h0, hx0]
        · rw [e1, hx1]
        · rw [e2, hx2]
    rw [this]
    exact mem_zpowers _
  · have e1 : σ 1 = 0 := by rw [hs1, h0, hx2]
    have e2 : σ 2 = 1 := by rw [hs2, e1, hx0]
    have : σ = x1p * x1p := by
      refine Equiv.ext fun y => ?_
      by_cases hy : 3 ≤ y.val
      · rw [hfix y hy, Perm.mul_apply, hxfix y hy, hxfix y hy]
      · rcases hlow3 y hy with rfl | rfl | rfl
        · rw [h0, Perm.mul_apply, hx0, hx1]
        · rw [e1, Perm.mul_apply, hx1, hx2]
        · rw [e2, Perm.mul_apply, hx2, hx0]
    rw [this]
    exact Subgroup.mul_mem _ (mem_zpowers _) (mem_zpowers _)

end DoubleCentralizer

section Automorphism

theorem exists_perm_conj_of_aut {C : Type} [Group C] (ρ : C →* Perm (Fin 11))
    (hρ : ∀ σ : Perm (Fin 11), σ ∈ ρ.range ↔ σ ∈ alternatingGroup (Fin 11)) (α : MulAut C)
    (hker : ∀ c : C, ρ (α c) = 1 ↔ ρ c = 1) :
    ∃ σ : Perm (Fin 11), ∀ c : C, ρ (α c) = σ * ρ c * σ⁻¹ := by
  classical
  let q : C →* alternatingGroup (Fin 11) :=
    ρ.codRestrict (alternatingGroup (Fin 11)) (fun c => (hρ _).1 ⟨c, rfl⟩)
  have hq_surj : Function.Surjective q := by
    intro a
    obtain ⟨c, hc⟩ := (hρ a).2 a.2
    exact ⟨c, Subtype.ext hc⟩
  have hq_ker : ∀ c : C, q c = 1 ↔ ρ c = 1 := fun c => by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hmem : ∀ c : C, c ∈ q.ker ↔ ρ c = 1 := fun c => (MonoidHom.mem_ker).trans (hq_ker c)
  have hmap : q.ker.map α.toMonoidHom = q.ker := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem _).2 ((hker x).2 ((hmem x).1 hx))
    · intro hy
      refine ⟨α.symm y, ?_, by simp⟩
      rw [hmem, ← hker]
      simpa using (hmem y).1 hy
  let θ : C ⧸ q.ker ≃* alternatingGroup (Fin 11) :=
    QuotientGroup.quotientKerEquivOfSurjective q hq_surj
  have hθ : ∀ c : C, θ (QuotientGroup.mk c) = q c := fun c => rfl
  let ψ : C ⧸ q.ker ≃* C ⧸ q.ker := QuotientGroup.congr q.ker q.ker α hmap
  let σ' : MulAut (alternatingGroup (Fin 11)) := (θ.symm.trans ψ).trans θ
  have hσ' : ∀ c : C, σ' (q c) = q (α c) := by
    intro c
    show θ (ψ (θ.symm (q c))) = _
    rw [← hθ c, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)).2 σ'
  refine ⟨π, fun c => ?_⟩
  have h1 : (MulAut.conjNormal π : MulAut (alternatingGroup (Fin 11))) (q c) = q (α c) := by
    rw [hπ]
    exact hσ' c
  have h2 := congrArg Subtype.val h1
  rw [MulAut.conjNormal_apply] at h2
  exact h2.symm

end Automorphism

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut
