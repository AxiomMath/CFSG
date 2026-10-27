module

public import CFSG.Fischer.Uniq.LocalHyperoval
public import CFSG.Fischer.Polar.Defs
public import CFSG.Fischer.Uniq.Xi

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

@[expose] def LinesByPerp : Prop :=
  ∀ x y : Fin 693, x ≠ y → perp x y → lineThru x y = {z | ∀ w, perp w x → perp w y → perp w z}

variable {Z : Type} [Group Z] {D : Set Z} {s : Z}

namespace LocalPoints

variable (L : LocalPoints polarModel D s)

@[expose] def pts (U : Set Z) : Set (Fin 693) := {p | (L.χ.symm p : Z) ∈ U}

theorem mem_pts {U : Set Z} {p : Fin 693} : p ∈ L.pts U ↔ (L.χ.symm p : Z) ∈ U := Iff.rfl

theorem χ_mem_pts {U : Set Z} (x : LocalClass D s) : L.χ x ∈ L.pts U ↔ (x : Z) ∈ U := by
  rw [mem_pts, Equiv.symm_apply_apply]

theorem pts_inter (U V : Set Z) : L.pts (U ∩ V) = L.pts U ∩ L.pts V := rfl

theorem ncard_pts {U : Set Z} (hU : U ⊆ LocalClass D s) : (L.pts U).ncard = U.ncard := by
  refine Set.ncard_congr (fun p _ => (L.χ.symm p : Z)) (fun p hp => hp)
    (fun p q _ _ e => L.χ.symm.injective (Subtype.ext e)) (fun x hx => ?_)
  exact ⟨L.χ ⟨x, hU hx⟩, by rw [χ_mem_pts]; exact hx, by simp⟩

theorem pts_lineIn (x y : LocalClass D s) :
    L.pts (lineIn (LocalClass D s) x y) =
      {q | ∀ w, perp w (L.χ x) → perp w (L.χ y) → perp w q} := by
  ext q
  rw [mem_pts]
  constructor
  · rintro ⟨-, h⟩ w hwx hwy
    have h1 := (L.comm (L.χ.symm w) x).2 (by rw [Equiv.apply_symm_apply]; exact hwx)
    have h2 := (L.comm (L.χ.symm w) y).2 (by rw [Equiv.apply_symm_apply]; exact hwy)
    have := (L.comm (L.χ.symm w) (L.χ.symm q)).1 (h _ (L.χ.symm w).2 h1 h2)
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · intro h
    refine ⟨(L.χ.symm q).2, fun w hw hwx hwy => ?_⟩
    have := h (L.χ ⟨w, hw⟩) ((L.comm ⟨w, hw⟩ x).1 hwx) ((L.comm ⟨w, hw⟩ y).1 hwy)
    have h' := (L.comm ⟨w, hw⟩ (L.χ.symm q)).2 (by rw [Equiv.apply_symm_apply]; exact this)
    exact h'

omit L in
theorem mul_mul_mem_localClass (hP : Pair Z D) (x y : LocalClass D s) :
    (x : Z) * y * x ∈ LocalClass D s := by
  have hx : (x : Z) * x = 1 := Pair.mul_self hP x.2.1
  have h1 : Commute (x : Z) s := x.2.2.2
  have h2 : Commute (y : Z) s := y.2.2.2
  refine ⟨Pair.mul_mul_mem hP x.2.1 y.2.1, fun h => y.2.2.1 ?_,
    ((h1.mul_left h2).mul_left h1 : Commute ((x : Z) * y * x) s)⟩
  calc (y : Z) = x * (x * y * x) * x := by
        rw [show (x : Z) * (x * y * x) * x = (x * x) * y * (x * x) by group, hx, one_mul, mul_one]
    _ = x * s * x := by rw [h]
    _ = s := by rw [h1.eq, mul_assoc, hx, mul_one]

theorem pts_conj (hP : Pair Z D) {U : Set Z} (hU : U ⊆ LocalClass D s) (x : LocalClass D s) :
    L.pts ((fun y => (x : Z) * y * x) '' U) = tvP (L.χ x) '' L.pts U := by
  ext q
  constructor
  · rintro ⟨y, hy, hyq⟩
    refine ⟨L.χ ⟨y, hU hy⟩, (L.χ_mem_pts _).2 hy, ?_⟩
    rw [← polarModel_tv, ← L.tau x ⟨y, hU hy⟩ (mul_mul_mem_localClass hP x ⟨y, hU hy⟩)]
    rw [← Equiv.apply_symm_apply L.χ q]
    congr 1
    exact Subtype.ext hyq
  · rintro ⟨p, hp, rfl⟩
    have hyA : (L.χ.symm p : Z) ∈ LocalClass D s := (L.χ.symm p).2
    rw [← Equiv.apply_symm_apply L.χ p, ← polarModel_tv,
      ← L.tau x (L.χ.symm p) (mul_mul_mem_localClass hP x _), χ_mem_pts]
    exact ⟨_, hp, rfl⟩

theorem eq_of_pts_eq {U V : Set Z} (hU : U ⊆ LocalClass D s) (hV : V ⊆ LocalClass D s)
    (h : L.pts U = L.pts V) : U = V := by
  ext z
  constructor
  · intro hz
    have := (L.χ_mem_pts ⟨z, hU hz⟩).2 hz
    rw [h] at this
    exact (L.χ_mem_pts ⟨z, hU hz⟩).1 this
  · intro hz
    have := (L.χ_mem_pts ⟨z, hV hz⟩).2 hz
    rw [← h] at this
    exact (L.χ_mem_pts ⟨z, hV hz⟩).1 this

theorem isLine_pts_iff (hF1 : LinesByPerp) {Λ : Set (Fin 693)} :
    IsLine Λ ↔ ∃ L', IsLineIn (LocalClass D s) L' ∧ L.pts L' = Λ := by
  constructor
  · rintro ⟨p, q, hpq, hperp, rfl⟩
    refine ⟨lineIn (LocalClass D s) (L.χ.symm p) (L.χ.symm q),
      ⟨_, (L.χ.symm p).2, _, (L.χ.symm q).2, fun h => hpq ?_, ?_, rfl⟩, ?_⟩
    · exact L.χ.symm.injective (Subtype.ext h)
    · exact (L.comm _ _).2 (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hperp)
    · rw [pts_lineIn, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hF1 p q hpq hperp]
  · rintro ⟨_, ⟨x, hx, y, hy, hxy, hc, rfl⟩, rfl⟩
    have hne : L.χ ⟨x, hx⟩ ≠ L.χ ⟨y, hy⟩ := fun h =>
      hxy (congrArg Subtype.val (L.χ.injective h))
    have hp : perp (L.χ ⟨x, hx⟩) (L.χ ⟨y, hy⟩) := (L.comm ⟨x, hx⟩ ⟨y, hy⟩).1 hc
    refine ⟨_, _, hne, hp, ?_⟩
    exact (L.pts_lineIn ⟨x, hx⟩ ⟨y, hy⟩).trans (hF1 _ _ hne hp).symm

theorem isHyperovalIn_iff (hF1 : LinesByPerp) (hP : Pair Z D) {U : Set Z}
    (hU : U ⊆ LocalClass D s) : IsHyperovalIn (LocalClass D s) U ↔ IsClosedHyperoval (L.pts U) := by
  have hlineA : ∀ {L'}, IsLineIn (LocalClass D s) L' → L' ⊆ LocalClass D s := by
    rintro _ ⟨x, -, y, -, -, -, rfl⟩ z hz
    exact hz.1
  constructor
  · intro h
    refine ⟨fun Λ hΛ => ?_, fun p hp => ?_⟩
    · obtain ⟨L', hL', rfl⟩ := (L.isLine_pts_iff hF1).1 hΛ
      rw [← pts_inter, L.ncard_pts (Set.inter_subset_left.trans (hlineA hL'))]
      exact h.inter L' hL'
    · rw [← Equiv.apply_symm_apply L.χ p, ← L.pts_conj hP hU, h.closed _ hp]
  · intro h
    refine ⟨hU, fun L' hL' => ?_, fun x hx => ?_⟩
    · rw [← L.ncard_pts (Set.inter_subset_left.trans (hlineA hL')), pts_inter]
      exact h.inter _ ((L.isLine_pts_iff hF1).2 ⟨L', hL', rfl⟩)
    · have hcl := h.closed (L.χ ⟨x, hU hx⟩) ((L.χ_mem_pts _).2 hx)
      rw [← L.pts_conj hP hU] at hcl
      refine L.eq_of_pts_eq ?_ hU hcl
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mul_mem_localClass hP ⟨x, hU hx⟩ ⟨y, hU hy⟩

end LocalPoints

end CFSG.Fischer
