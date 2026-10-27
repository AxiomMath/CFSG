module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp Equiv

variable {V : Type} [CommGroup V]

private def cbsC3 {K : ℕ} (u x y : Fin K) : Perm (Fin K) := swap u x * swap x y

private theorem cbsC3_mem {K : ℕ} {u x y : Fin K} (hux : u ≠ x) (hxy : x ≠ y) :
    cbsC3 u x y ∈ alternatingGroup (Fin K) := by
  rw [Equiv.Perm.mem_alternatingGroup, cbsC3, map_mul, Equiv.Perm.sign_swap hux,
    Equiv.Perm.sign_swap hxy]
  decide

private theorem cbsC3_apply_of_ne {K : ℕ} {u x y i : Fin K} (hu : i ≠ u) (hx : i ≠ x)
    (hy : i ≠ y) : cbsC3 u x y i = i := by
  simp only [cbsC3, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne hx hy, swap_apply_of_ne_of_ne hu hx]

private theorem cbsC3_apply_left {K : ℕ} {u x y : Fin K} (hux : u ≠ x) (huy : u ≠ y) :
    cbsC3 u x y u = x := by
  simp only [cbsC3, Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne hux huy, swap_apply_left]

private theorem cbsC3_mem_stab {K : ℕ} {a b u x y : Fin K} (hux : u ≠ x) (hxy : x ≠ y)
    (hua : u ≠ a) (hub : u ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    (⟨cbsC3 u x y, cbsC3_mem hux hxy⟩ : alternatingGroup (Fin K)) ∈ altStabilizer K {a, b} := by
  rw [mem_altStabilizer_iff]
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact cbsC3_apply_of_ne (Ne.symm hua) (Ne.symm hxa) (Ne.symm hya)
  · exact cbsC3_apply_of_ne (Ne.symm hub) (Ne.symm hxb) (Ne.symm hyb)

private theorem cbs_two_pts {K : ℕ} (S : Finset (Fin K)) (hS : S.card + 2 ≤ K) :
    ∃ x y : Fin K, x ∉ S ∧ y ∉ S ∧ x ≠ y := by
  classical
  have hcard : 1 < (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx hy
  exact ⟨x, y, hx, hy, hxy⟩

private theorem cbs_fix {K : ℕ} (hK : 9 ≤ K) {a b : Fin K} (π : Perm (Fin K))
    (hcomm : ∀ σ : alternatingGroup (Fin K), σ ∈ altStabilizer K {a, b} →
      ∀ i, π ((σ : Perm (Fin K)) i) = (σ : Perm (Fin K)) (π i)) {p : Fin K} (hpa : p ≠ a)
    (hpb : p ≠ b) : π p = p := by
  classical
  by_contra hne
  by_cases hu : π p = a ∨ π p = b
  ·
    have hc3 := Finset.card_le_three (a := a) (b := b) (c := p)
    obtain ⟨x, y, hx, hy, hxy⟩ := cbs_two_pts ({a, b, p} : Finset (Fin K)) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
    have hmem := cbsC3_mem_stab (a := a) (b := b) (u := p) (x := x) (y := y) (Ne.symm hx.2.2) hxy
      hpa hpb hx.1 hx.2.1 hy.1 hy.2.1
    have h1 := hcomm _ hmem p
    have h2 : (cbsC3 p x y) (π p) = π p := by
      rcases hu with h | h <;> rw [h] <;>
        exact cbsC3_apply_of_ne (by first | exact Ne.symm hpa | exact Ne.symm hpb)
          (by first | exact Ne.symm hx.1 | exact Ne.symm hx.2.1)
          (by first | exact Ne.symm hy.1 | exact Ne.symm hy.2.1)
    have h3 : π (cbsC3 p x y p) = π p := h1.trans h2
    have h4 := π.injective h3
    rw [cbsC3_apply_left (Ne.symm hx.2.2) (Ne.symm hy.2.2)] at h4
    exact hx.2.2 h4
  · push Not at hu
    have hc4 := Finset.card_le_four (a := a) (b := b) (c := p) (d := π p)
    obtain ⟨x, y, hx, hy, hxy⟩ := cbs_two_pts ({a, b, p, π p} : Finset (Fin K)) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
    have hmem := cbsC3_mem_stab (a := a) (b := b) (u := π p) (x := x) (y := y)
      (Ne.symm hx.2.2.2) hxy hu.1 hu.2 hx.1 hx.2.1 hy.1 hy.2.1
    have h1 := hcomm _ hmem p
    have h2 : (cbsC3 (π p) x y) p = p :=
      cbsC3_apply_of_ne (Ne.symm hne) (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1)
    rw [h2] at h1
    rw [cbsC3_apply_left (Ne.symm hx.2.2.2) (Ne.symm hy.2.2.2)] at h1
    exact hx.2.2.2 h1.symm

theorem cb_swap_or_one {X Y : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ} (hm : 7 ≤ m)
    (θ : ↥X ≃* alternatingGroup (Fin (m + 2))) {a b : Fin (m + 2)} (hab : a ≠ b)
    (hY : (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (m + 2) {a, b})
    (hn : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (htY : ∀ y ∈ Y, t * y = y * t) :
    (∀ (x : MulAut V) (hx : x ∈ X),
        (θ ⟨t * x * t⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
          (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2)))) ∨
      (∀ (x : MulAut V) (hx : x ∈ X),
        (θ ⟨t * x * t⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
          Equiv.swap a b * (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap a b)⁻¹) := by
  classical
  have hfin : Finite ↥X := Finite.of_equiv _ θ.symm.toEquiv
  let f : ↥X →* ↥X :=
    { toFun := fun x => ⟨t * (x : MulAut V) * t⁻¹, hn x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (by simpa [f] using h1)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  let φ : MulAut (alternatingGroup (Fin (m + 2))) :=
    θ.symm.trans ((MulEquiv.ofBijective f hbij).trans θ)
  obtain ⟨π, hπ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (m + 2)
    (by omega) (by omega)).2 φ
  have hπx : ∀ (x : MulAut V) (hx : x ∈ X),
      (θ ⟨t * x * t⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
        π * (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * π⁻¹ := by
    intro x hx
    have h1 := congrArg (fun e : MulAut (alternatingGroup (Fin (m + 2))) =>
      (e (θ ⟨x, hx⟩) : Equiv.Perm (Fin (m + 2)))) hπ
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [φ, f]
  have hcomm : ∀ σ : alternatingGroup (Fin (m + 2)), σ ∈ altStabilizer (m + 2) {a, b} →
      ∀ i, π ((σ : Equiv.Perm (Fin (m + 2))) i) = (σ : Equiv.Perm (Fin (m + 2))) (π i) := by
    intro σ hσ i
    rw [← hY] at hσ
    obtain ⟨z, hz, rfl⟩ := hσ
    have hzY : (z : MulAut V) ∈ Y := hz
    have hz' : t * (z : MulAut V) * t⁻¹ = z := by
      rw [htY _ hzY]
      group
    have e1 : (⟨t * (z : MulAut V) * t⁻¹, hn z z.2⟩ : ↥X) = z := Subtype.ext hz'
    have h1 := hπx z z.2
    have h2 : (θ ⟨t * (z : MulAut V) * t⁻¹, hn z z.2⟩ : Equiv.Perm (Fin (m + 2))) =
        (θ z : Equiv.Perm (Fin (m + 2))) := by rw [e1]
    have h3 : (θ z : Equiv.Perm (Fin (m + 2))) *  π = π * (θ z : Equiv.Perm (Fin (m + 2))) := by
      have h6 : (θ z : Equiv.Perm (Fin (m + 2))) =
          π * (θ z : Equiv.Perm (Fin (m + 2))) * π⁻¹ :=
        calc (θ z : Equiv.Perm (Fin (m + 2))) = θ ⟨t * (z : MulAut V) * t⁻¹, hn z z.2⟩ := h2.symm
          _ = π * (θ ⟨(z : MulAut V), z.2⟩ : Equiv.Perm (Fin (m + 2))) * π⁻¹ := h1
          _ = π * (θ z : Equiv.Perm (Fin (m + 2))) * π⁻¹ := rfl
      rw [eq_mul_inv_iff_mul_eq] at h6
      exact h6
    have h4 := h3
    have h5 := congrArg (fun g : Equiv.Perm (Fin (m + 2)) => g i) h4
    simp only [Perm.mul_apply] at h5
    exact h5.symm
  have hfix : ∀ p : Fin (m + 2), p ≠ a → p ≠ b → π p = p := fun p hpa hpb =>
    cbs_fix (by omega) π hcomm hpa hpb
  have hπa : π a = a ∨ π a = b := by
    by_contra hcon
    push Not at hcon
    have h1 := hfix (π a) hcon.1 hcon.2
    exact hcon.1 (π.injective h1)
  have hπb : π b = a ∨ π b = b := by
    by_contra hcon
    push Not at hcon
    have h1 := hfix (π b) hcon.1 hcon.2
    exact hcon.2 (π.injective h1)
  rcases hπa with ha | ha
  ·
    have hb : π b = b := by
      rcases hπb with hb | hb
      · exact absurd (π.injective (hb.trans ha.symm)) (Ne.symm hab)
      · exact hb
    have hπ1 : π = 1 := by
      refine Equiv.ext fun p => ?_
      rw [Perm.one_apply]
      by_cases hpa : p = a
      · rw [hpa]; exact ha
      by_cases hpb : p = b
      · rw [hpb]; exact hb
      exact hfix p hpa hpb
    left
    intro x hx
    rw [hπx x hx, hπ1]
    simp
  ·
    have hb : π b = a := by
      rcases hπb with hb | hb
      · exact hb
      · exact absurd (π.injective (hb.trans ha.symm)) (Ne.symm hab)
    have hπs : π = swap a b := by
      refine Equiv.ext fun p => ?_
      by_cases hpa : p = a
      · rw [hpa, ha, swap_apply_left]
      by_cases hpb : p = b
      · rw [hpb, hb, swap_apply_right]
      rw [swap_apply_of_ne_of_ne hpa hpb]
      exact hfix p hpa hpb
    right
    intro x hx
    rw [hπx x hx, hπs]

end CFSG.CGT.PushingUpLit.CGT6
