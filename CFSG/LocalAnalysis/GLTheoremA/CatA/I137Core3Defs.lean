module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Yardstones.Md0ec50421ce4 TauCeti

@[expose] def Core3Group (S : Type) [Group S] : Prop :=
  ∀ (T A : Subgroup S), IsPGroup 2 T → T ≠ ⊥ → A ≤ Subgroup.normalizer (T : Set S) →
    ∀ (Q₀ : Type) [Group Q₀], (∃ f : A →* Q₀, Function.Surjective f) →
      catalogIs Q₀ (S9.isList93 3) → catalogIs Q₀ S9.isL3four

@[expose] def Core3At (P : LieTypeIndex → Prop) : Prop :=
  ∀ d : ValidLieTypeIndex, P d.1 → ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* (CFSGIndex.lie d).Group) → Core3Group S

theorem Core3At.mono {P Q : LieTypeIndex → Prop} (hPQ : ∀ d, P d → Q d) (h : Core3At Q) :
    Core3At P :=
  fun d hd S _ _ e => h d (hPQ _ hd) S e

theorem Core3At.or {P Q : LieTypeIndex → Prop} (hP : Core3At P) (hQ : Core3At Q) :
    Core3At fun d => P d ∨ Q d := by
  intro d hd S _ _ e
  rcases hd with h | h
  · exact hP d h S e
  · exact hQ d h S e

theorem Core3Group.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : Core3Group S') : Core3Group S := by
  intro T A hT2 hT hA Q₀ _ ⟨f, hf⟩ hQ
  refine h (T.map e.toMonoidHom) (A.map e.toMonoidHom) (hT2.map _) ?_ ?_ Q₀
    ⟨f.comp (A.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom,
      hf.comp (MulEquiv.surjective _)⟩ hQ
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · exact (Subgroup.map_mono hA).trans (Subgroup.le_normalizer_map _)

theorem card_dvd_of_surjective {A Q₀ : Type*} [Group A] [Group Q₀] [Finite A] (f : A →* Q₀)
    (hf : Function.Surjective f) : Nat.card Q₀ ∣ Nat.card A := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem list93three_cases {Q₀ : Type} [Group Q₀] (h : catalogIs Q₀ (S9.isList93 3)) :
    ∃ d : ValidLieTypeIndex, Nonempty (Q₀ ≃* (CFSGIndex.lie d).Group) ∧
      ((∃ q : PrimePower, d.1 = .D 4 q ∧ q.card = 2) ∨
        (∃ q : PrimePower, d.1 = .B 2 q ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .G2 q ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .twistedA 3 q ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .twistedA 5 q ∧ q.card = 2) ∨
        (∃ q : PrimePower, d.1 = .trialityD4 q ∧ q.card = 2) ∨
        d.1 = .reeF4 1 ∨
        (∃ q : PrimePower, d.1 = .A 2 q ∧ q.p = 2 ∧ q.card % 3 = 1) ∨
        (∃ q : PrimePower, d.1 = .twistedA 2 q ∧ q.p = 2 ∧ q.card % 3 = 2)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with ⟨h5, -⟩ | ⟨-, hi⟩
  · norm_num at h5
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · rcases hi with h | h | h | h | h | h | h | h | h <;> exact h.elim
  · rcases hi with h | h | h | h | h | h | h | h | h <;> exact h.elim
  · refine ⟨⟨d, hv⟩, ⟨e⟩, ?_⟩
    rcases hi with h | h | h | h | h | h | h | h | h
    · cases d <;> simp only [S9.isD4two, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 4 := by
        rcases n with _ | _ | _ | _ | _ | n <;> simp_all
      exact Or.inl ⟨q, rfl, by simpa using h⟩
    · cases d <;> simp only [S9.isSp4eight, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 2 := by
        rcases n with _ | _ | _ | n <;> simp_all
      exact Or.inr (Or.inl ⟨q, rfl, by simpa using h⟩)
    · cases d <;> simp only [S9.isG2eight, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i q
      exact Or.inr (Or.inr (Or.inl ⟨q, rfl, h⟩))
    · cases d <;> simp only [S9.isU4eight, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 3 := by
        rcases n with _ | _ | _ | _ | n <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by simpa using h⟩)))
    · cases d <;> simp only [S9.isU6two, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 5 := by
        rcases n with _ | _ | _ | _ | _ | _ | n <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by simpa using h⟩))))
    · cases d <;> simp only [S9.isTD4two, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i q
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, h⟩)))))
    · cases d <;> simp only [S9.isReeF48, onLie] at h
      all_goals first | exact h.elim | skip
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by subst h; rfl)))))))
    · cases d <;> simp only [S9.isL3char2, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 2 := by
        rcases n with _ | _ | _ | n <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, rfl, by simpa using h⟩)))))))
    · cases d <;> simp only [S9.isU3char2, onLie] at h
      all_goals first | exact h.elim | skip
      rename_i n q
      obtain rfl : n = 2 := by
        rcases n with _ | _ | _ | n <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨q, rfl, by simpa using h⟩)))))))
  · rcases hi with h | h | h | h | h | h | h | h | h <;> exact h.elim

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
