module

public import CFSG.Perm.OrbitTree

public section

namespace CFSG.KC.D43

variable {G V : Type*} [Group G] [MulAction G V] [InvolutiveNeg V]

theorem pm_trans {a b c : V} (h1 : a = b ∨ a = -b) (h2 : a = c ∨ a = -c) : b = c ∨ b = -c := by
  rcases h1 with rfl | rfl <;> rcases h2 with h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr (by rw [← h, neg_neg])
  · exact Or.inl (neg_injective h)

theorem pm_neg {a b : V} (h : a = b ∨ a = -b) : -a = b ∨ -a = -b := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg b)

theorem exists_hom_signed {ι : Type*} (s : ι → G) {N : ℕ} (P : ℕ → V) (T : ι → ℕ → ℕ)
    (hneg : ∀ (g : G) (v : V), g • -v = -(g • v))
    (hT : ∀ i, ∀ p < N, T i p < N ∧ (s i • P p = P (T i p) ∨ s i • P p = -P (T i p)))
    (hinj : ∀ p < N, ∀ q < N, (P p = P q ∨ P p = -P q) → p = q) :
    ∃ ρ : ↥(Subgroup.closure (Set.range s)) →* Equiv.Perm (Fin N),
      ∀ i (p : Fin N), ((ρ ⟨s i, Subgroup.subset_closure ⟨i, rfl⟩⟩ p : Fin N) : ℕ) = T i p := by
  classical
  set H := Subgroup.closure (Set.range s) with hH
  set F : Set V := {v | ∃ p < N, v = P p ∨ v = -P p} with hFdef
  have hF : F.Finite := by
    have hsub : F ⊆ (fun p => P p) '' Set.Iio N ∪ (fun p => -P p) '' Set.Iio N := by
      rintro v ⟨p, hp, rfl | rfl⟩
      · exact Or.inl ⟨p, hp, rfl⟩
      · exact Or.inr ⟨p, hp, rfl⟩
    exact (((Set.finite_Iio N).image _).union ((Set.finite_Iio N).image _)).subset hsub
  have hSF : ∀ x ∈ Set.range s, ∀ v ∈ F, x • v ∈ F := by
    rintro _ ⟨i, rfl⟩ v ⟨p, hp, hv⟩
    obtain ⟨hlt, he⟩ := hT i p hp
    refine ⟨T i p, hlt, ?_⟩
    rcases hv with rfl | rfl
    · exact he
    · rw [hneg]
      exact pm_neg he
  have hex : ∀ g ∈ H, ∀ p < N, ∃ q < N, g • P p = P q ∨ g • P p = -P q := fun g hg p hp =>
    CFSG.Perm.smul_mem_of_finite_of_mem_closure hF hSF hg (x := P p) ⟨p, hp, Or.inl rfl⟩
  let f : G → ℕ → ℕ := fun g p =>
    if h : ∃ q < N, g • P p = P q ∨ g • P p = -P q then Classical.choose h else p
  have hf : ∀ g ∈ H, ∀ p < N, f g p < N ∧ (g • P p = P (f g p) ∨ g • P p = -P (f g p)) := by
    intro g hg p hp
    have h := hex g hg p hp
    have e : f g p = Classical.choose h := dif_pos h
    rw [e]
    exact Classical.choose_spec h
  have huniq : ∀ g ∈ H, ∀ p < N, ∀ q < N, (g • P p = P q ∨ g • P p = -P q) → f g p = q := by
    intro g hg p hp q hq e
    obtain ⟨h1, h2⟩ := hf g hg p hp
    exact hinj _ h1 _ hq (pm_trans h2 e)
  have hmul : ∀ g ∈ H, ∀ h ∈ H, ∀ p < N, f (g * h) p = f g (f h p) := by
    intro g hg h hh p hp
    obtain ⟨h1, h2⟩ := hf h hh p hp
    obtain ⟨h3, h4⟩ := hf g hg _ h1
    refine huniq _ (H.mul_mem hg hh) p hp _ h3 ?_
    rw [mul_smul]
    rcases h2 with e | e
    · rw [e]
      exact h4
    · rw [e, hneg]
      exact pm_neg h4
  have hone : ∀ p < N, f 1 p = p := fun p hp =>
    huniq 1 H.one_mem p hp p hp (Or.inl (one_smul _ _))
  let perm : H → Equiv.Perm (Fin N) := fun g =>
    { toFun := fun p => ⟨f g p, (hf g g.2 p p.2).1⟩
      invFun := fun p => ⟨f (g⁻¹ : H) p, (hf _ (g⁻¹ : H).2 p p.2).1⟩
      left_inv := fun p => Fin.ext (by
        change f ((g⁻¹ : H) : G) (f (g : G) p) = p
        rw [← hmul _ (g⁻¹ : H).2 _ g.2 p p.2, Subgroup.coe_inv, inv_mul_cancel, hone p p.2])
      right_inv := fun p => Fin.ext (by
        change f (g : G) (f ((g⁻¹ : H) : G) p) = p
        rw [← hmul _ g.2 _ (g⁻¹ : H).2 p p.2, Subgroup.coe_inv, mul_inv_cancel, hone p p.2]) }
  refine ⟨{ toFun := perm, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact Equiv.ext fun p => Fin.ext (hone p p.2)
  · intro g h
    exact Equiv.ext fun p => Fin.ext (hmul g g.2 h h.2 p p.2)
  · intro i p
    exact huniq _ (Subgroup.subset_closure ⟨i, rfl⟩) p p.2 _ (hT i p p.2).1 (hT i p p.2).2

end CFSG.KC.D43

end
