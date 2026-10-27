module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.RadCent

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open

@[expose] def Frame (p : ℕ) {Y : Type*} [Group Y] (y : Y) : Prop :=
  ∃ Gen T : Set Y,
    (∀ q ∈ Gen ∪ T, y * q = q * y) ∧
    (∀ s q, s * y = y * s → q ∈ T → s * q = q * s) ∧
    (∀ s q, s * y = y * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen) ∧
    (∀ s : Y, (orderOf s).Coprime p →
      (∀ q ∈ Gen ∪ T, (MulAut.conj s : MulAut Y) q = q) → (MulAut.conj s : MulAut Y) = 1) ∧
    IsPGroup p (Subgroup.closure (Gen ∪ T))

theorem kdCharPAt_of_frame {S Y : Type} [Group S] [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (e : S ≃* Y) (hZ : Subgroup.center Y = ⊥) (hF : ∀ y : Y, orderOf y = p → Frame p y) :
    KDCharPAt p S := by
  haveI : Finite S := Finite.of_equiv Y e.symm.toEquiv
  intro u hu
  obtain ⟨Gen, T, h1, hT, hGen, huniq, hMp⟩ := hF (e u) (by rw [MulEquiv.orderOf_eq]; exact hu)
  have hZS : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have : e a ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_center_iff.1 ha (e.symm y)
      have h2 := congrArg e this
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [hZ, Subgroup.mem_bot] at this
    exact e.injective (by rw [this, map_one])
  refine gLAPLayer_centralizer_eq_bot_of_framework hZS u {q | e q ∈ Gen} {q | e q ∈ T}
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    apply e.injective
    rw [map_mul, map_mul]
    exact h1 (e q) (by rcases hq with hq | hq; exacts [Or.inl hq, Or.inr hq])
  · intro s q hs hq
    apply e.injective
    rw [map_mul, map_mul]
    refine hT (e s) (e q) ?_ hq
    rw [← map_mul, ← map_mul, hs]
  · intro s q hs hq
    have hs' : e s * e u = e u * e s := by rw [← map_mul, ← map_mul, hs]
    have := hGen (e s) (e q) hs' hq
    show e (s * q * s⁻¹) ∈ Gen
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro s hs hfix
    have key : MulAut.congr e (MulAut.conj s : MulAut S) = MulAut.conj (e s) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have hcop : (orderOf (e s)).Coprime p := by
      rw [MulEquiv.orderOf_eq e s]; exact hs
    have h1 : (MulAut.conj (e s) : MulAut Y) = 1 := by
      refine huniq (e s) hcop fun q0 hq0 => ?_
      have hmem : e.symm q0 ∈ {q' | e q' ∈ Gen} ∪ {q' | e q' ∈ T} := by
        rcases hq0 with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      have := hfix _ hmem
      have h2 := congrArg e this
      simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2 ⊢
      exact h2
    exact (MulAut.congr e).injective (by rw [key, h1, map_one])
  · refine (hMp.comap_of_injective e.toMonoidHom e.injective).to_le ?_
    refine (Subgroup.closure_le _).2 fun q hq => ?_
    show e q ∈ Subgroup.closure (Gen ∪ T)
    apply Subgroup.subset_closure
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr hq

theorem kdCharPAt_of_frame_simple {S Y : Type} [Group S] [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (e : S ≃* Y) (hs : IsSimpleGroup Y) (hF : ∀ y : Y, orderOf y = p → Frame p y) :
    KDCharPAt p S := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact kdCharPAt_of_frame e h hF
  · haveI : Finite S := Finite.of_equiv Y e.symm.toEquiv
    intro u _
    refine le_bot_iff.1 (sSup_le fun L hL => ?_)
    exfalso
    refine false_of_glaPComponent_of_comm hL fun a b => ?_
    have hb : e b ∈ Subgroup.center Y := by rw [h]; trivial
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hb (e a)

end CFSG.HardMathSupport.Dickson.KD
