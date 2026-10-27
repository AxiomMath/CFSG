module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def SPLCellFor (S : Type) [Group S] (p r : ℕ) : Prop :=
  ∀ (Ē : Subgroup S) (ζ γ : MulAut S), CFSG.Open.IsElemAbelian p Ē → Nat.card Ē = p ^ 4 →
    ζ ^ p = 1 → (∀ x ∈ Ē, ζ x = x) → Group.IsSolvable ↥(autFix ζ) →
    (∃ k : ℕ, γ ^ r ^ k = 1) → (∀ x ∈ Ē, γ x ∈ Ē) → γ * ζ = ζ * γ → (∃ x ∈ Ē, γ x ≠ x) → False

theorem SPLCellFor.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {p r : ℕ}
    (h : SPLCellFor T p r) : SPLCellFor S p r := by
  intro Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt
  obtain ⟨k, hk⟩ := hγ
  have hcongr : ∀ (α : MulAut S) (t : T), MulAut.congr e α t = e (α (e.symm t)) := fun α t => rfl
  refine h (Ē.map e.toMonoidHom) (MulAut.congr e ζ) (MulAut.congr e γ) ⟨?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    have h1 : x * y = y * x := congrArg Subtype.val
      (hE.1.is_comm.comm (⟨x, hx⟩ : ↥Ē) ⟨y, hy⟩)
    change (a : T) * b = b * a
    rw [← hxa, ← hyb]
    change e x * e y = e y * e x
    rw [← map_mul, ← map_mul, h1]
  · rintro _ ⟨y, hy, rfl⟩
    change (e y) ^ p = 1
    rw [← map_pow, hE.2 y hy, map_one]
  · rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hcard
    exact hcard
  · rw [← map_pow, hζp, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    rw [hcongr]
    simp [hζE y hy]
  · let ψ : ↥(autFix (MulAut.congr e ζ)) →* ↥(autFix ζ) :=
      { toFun := fun a => ⟨e.symm a.1, by
          have ha : (MulAut.congr e ζ) a.1 = a.1 := a.2
          rw [hcongr] at ha
          change ζ (e.symm a.1) = e.symm a.1
          have := congrArg e.symm ha
          simpa using this⟩
        map_one' := by
          apply Subtype.ext
          exact map_one _
        map_mul' := fun a b => by
          apply Subtype.ext
          exact map_mul _ _ _ }
    have hinj : Function.Injective ψ := by
      intro a b hab
      apply Subtype.ext
      exact e.symm.injective (congrArg Subtype.val hab)
    exact Group.isSolvable_of_isSolvable_injective (f := ψ) hinj
  · exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨γ y, hγE y hy, ?_⟩
    rw [hcongr]
    simp
  · rw [← map_mul, hcomm, map_mul]
  · obtain ⟨y, hy, hne⟩ := hnt
    refine ⟨e y, ⟨y, hy, rfl⟩, fun h' => hne ?_⟩
    rw [hcongr] at h'
    simpa using h'

end CFSG.HardMathSupport.Curtis.Coordinator
