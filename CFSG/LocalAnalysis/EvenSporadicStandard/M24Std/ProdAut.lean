module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.M24Std

variable {S : Type*} [Group S]

namespace ProdAut

theorem fst_of_ne_one (hsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (M : Subgroup (S × S)) [M.Normal] {s : S} (hs : s ≠ 1) (hsM : (s, 1) ∈ M) :
    ∀ t : S, (t, 1) ∈ M := by
  have hP : (M.comap (MonoidHom.inl S S)).Normal := Subgroup.Normal.comap inferInstance _
  rcases hsimple _ hP with h | h
  · exfalso
    have : s ∈ M.comap (MonoidHom.inl S S) := hsM
    rw [h] at this
    exact hs ((Subgroup.mem_bot).1 this)
  · intro t
    have : t ∈ M.comap (MonoidHom.inl S S) := by rw [h]; trivial
    exact this

theorem snd_of_ne_one (hsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (M : Subgroup (S × S)) [M.Normal] {s : S} (hs : s ≠ 1) (hsM : (1, s) ∈ M) :
    ∀ t : S, (1, t) ∈ M := by
  have hP : (M.comap (MonoidHom.inr S S)).Normal := Subgroup.Normal.comap inferInstance _
  rcases hsimple _ hP with h | h
  · exfalso
    have : s ∈ M.comap (MonoidHom.inr S S) := hsM
    rw [h] at this
    exact hs ((Subgroup.mem_bot).1 this)
  · intro t
    have : t ∈ M.comap (MonoidHom.inr S S) := by rw [h]; trivial
    exact this

theorem exists_factor (hcentral : ∀ a : S, (∀ c, a * c = c * a) → a = 1)
    (M : Subgroup (S × S)) [hM : M.Normal] {m : S × S} (hm : m ∈ M) (hm1 : m ≠ 1) :
    (∃ s : S, s ≠ 1 ∧ (s, 1) ∈ M) ∨ (∃ s : S, s ≠ 1 ∧ (1, s) ∈ M) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  obtain ⟨a, b⟩ := m
  have ha : a = 1 := by
    apply hcentral
    intro c
    have h1 : (a, b) * ((c, 1) * (a, b)⁻¹ * (c, 1)⁻¹) ∈ M :=
      M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) _)
    have e : (a, b) * ((c, 1) * (a, b)⁻¹ * (c, 1)⁻¹) = (a * c * a⁻¹ * c⁻¹, (1 : S)) := by
      ext <;> simp [mul_assoc]
    rw [e] at h1
    by_contra hne
    apply hc1 _ _ h1
    intro h
    apply hne
    calc a * c = a * c * a⁻¹ * c⁻¹ * c * a := by group
      _ = 1 * c * a := by rw [h]
      _ = c * a := by rw [one_mul]
  have hb : b = 1 := by
    apply hcentral
    intro c
    have h1 : (a, b) * ((1, c) * (a, b)⁻¹ * (1, c)⁻¹) ∈ M :=
      M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) _)
    have e : (a, b) * ((1, c) * (a, b)⁻¹ * (1, c)⁻¹) = ((1 : S), b * c * b⁻¹ * c⁻¹) := by
      ext <;> simp [mul_assoc]
    rw [e] at h1
    by_contra hne
    apply hc2 _ _ h1
    intro h
    apply hne
    calc b * c = b * c * b⁻¹ * c⁻¹ * c * b := by group
      _ = 1 * c * b := by rw [h]
      _ = c * b := by rw [one_mul]
  exact hm1 (by rw [ha, hb]; rfl)

theorem mulAut_prod_cases (hsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentral : ∀ a : S, (∀ c, a * c = c * a) → a = 1) (hnt : ∃ s : S, s ≠ 1)
    (α : MulAut (S × S)) :
    ((∀ x : S, (α (x, 1)).2 = 1) ∧ ∀ x : S, (α (1, x)).1 = 1) ∨
      ((∀ x : S, (α (x, 1)).1 = 1) ∧ ∀ x : S, (α (1, x)).2 = 1) := by
  obtain ⟨s0, hs0⟩ := hnt
  set β : MulAut (S × S) := α⁻¹ with hβ
  have hβα : ∀ m, β (α m) = m := fun m => by simp [hβ]
  have hαβ : ∀ m, α (β m) = m := fun m => by simp [hβ]
  let M1 : Subgroup (S × S) := (MonoidHom.snd S S).ker.comap β.toMonoidHom
  let M2 : Subgroup (S × S) := (MonoidHom.fst S S).ker.comap β.toMonoidHom
  have h1n : M1.Normal := Subgroup.Normal.comap (MonoidHom.normal_ker _) _
  have h2n : M2.Normal := Subgroup.Normal.comap (MonoidHom.normal_ker _) _
  have hm1 : α (s0, 1) ∈ M1 := by
    show (β (α (s0, 1))).2 = 1
    rw [hβα]
  have hm2 : α (1, s0) ∈ M2 := by
    show (β (α (1, s0))).1 = 1
    rw [hβα]
  have hne1 : α (s0, 1) ≠ 1 := fun h => hs0 (by
    have := congrArg β h
    rw [hβα, map_one] at this
    exact (Prod.ext_iff.1 this).1)
  have hne2 : α (1, s0) ≠ 1 := fun h => hs0 (by
    have := congrArg β h
    rw [hβα, map_one] at this
    exact (Prod.ext_iff.1 this).2)
  have H1 : (∀ s, (β (s, 1)).2 = 1) ∨ (∀ s, (β (1, s)).2 = 1) := by
    rcases exists_factor hcentral M1 hm1 hne1 with ⟨s, hs, hsM⟩ | ⟨s, hs, hsM⟩
    · exact Or.inl (fst_of_ne_one hsimple M1 hs hsM)
    · exact Or.inr (snd_of_ne_one hsimple M1 hs hsM)
  have H2 : (∀ s, (β (s, 1)).1 = 1) ∨ (∀ s, (β (1, s)).1 = 1) := by
    rcases exists_factor hcentral M2 hm2 hne2 with ⟨s, hs, hsM⟩ | ⟨s, hs, hsM⟩
    · exact Or.inl (fst_of_ne_one hsimple M2 hs hsM)
    · exact Or.inr (snd_of_ne_one hsimple M2 hs hsM)
  have hβinj : ∀ m, β m = 1 → m = 1 := fun m h => by
    have := congrArg α h
    rwa [hαβ, map_one] at this
  have hsplit : ∀ u v : S, β (u, v) = β (u, 1) * β (1, v) := fun u v => by
    rw [← map_mul]; simp
  have key : ∀ m : S × S, ∀ x y : S, α m = (x, y) → β (x, y) = m := fun m x y h => by
    rw [← h, hβα]
  rcases H1 with H1 | H1 <;> rcases H2 with H2 | H2
  · exfalso
    have : β (s0, 1) = 1 := Prod.ext (H2 s0) (H1 s0)
    exact hs0 (Prod.ext_iff.1 (hβinj _ this)).1
  · left
    constructor
    · intro x
      obtain ⟨u, v, huv⟩ : ∃ u v, α (x, 1) = (u, v) := ⟨_, _, rfl⟩
      rw [huv]
      have e := key _ _ _ huv
      rw [hsplit] at e
      have e2 := congrArg Prod.snd e
      simp only [Prod.snd_mul, H1 u, one_mul] at e2
      have : β (1, v) = 1 := Prod.ext (H2 v) e2
      exact (Prod.ext_iff.1 (hβinj _ this)).2
    · intro x
      obtain ⟨u, v, huv⟩ : ∃ u v, α (1, x) = (u, v) := ⟨_, _, rfl⟩
      rw [huv]
      have e := key _ _ _ huv
      rw [hsplit] at e
      have e1 := congrArg Prod.fst e
      simp only [Prod.fst_mul, H2 v, mul_one] at e1
      have : β (u, 1) = 1 := Prod.ext e1 (H1 u)
      exact (Prod.ext_iff.1 (hβinj _ this)).1
  · right
    constructor
    · intro x
      obtain ⟨u, v, huv⟩ : ∃ u v, α (x, 1) = (u, v) := ⟨_, _, rfl⟩
      rw [huv]
      have e := key _ _ _ huv
      rw [hsplit] at e
      have e2 := congrArg Prod.snd e
      simp only [Prod.snd_mul, H1 v, mul_one] at e2
      have : β (u, 1) = 1 := Prod.ext (H2 u) e2
      exact (Prod.ext_iff.1 (hβinj _ this)).1
    · intro x
      obtain ⟨u, v, huv⟩ : ∃ u v, α (1, x) = (u, v) := ⟨_, _, rfl⟩
      rw [huv]
      have e := key _ _ _ huv
      rw [hsplit] at e
      have e1 := congrArg Prod.fst e
      simp only [Prod.fst_mul, H2 u, one_mul] at e1
      have : β (1, v) = 1 := Prod.ext e1 (H1 v)
      exact (Prod.ext_iff.1 (hβinj _ this)).2
  · exfalso
    have : β (1, s0) = 1 := Prod.ext (H2 s0) (H1 s0)
    exact hs0 (Prod.ext_iff.1 (hβinj _ this)).2

theorem apply_eq_mul (α : MulAut (S × S)) (a b : S) : α (a, b) = α (a, 1) * α (1, b) := by
  rw [← map_mul]; simp

theorem bijective_of_preserve (α : MulAut (S × S)) (hp1 : ∀ x : S, (α (x, 1)).2 = 1)
    (hp2 : ∀ x : S, (α (1, x)).1 = 1) :
    Function.Bijective (fun a : S => (α (a, 1)).1) ∧
      Function.Bijective (fun b : S => (α (1, b)).2) := by
  refine ⟨⟨fun a a' h => ?_, fun y => ?_⟩, ⟨fun b b' h => ?_, fun y => ?_⟩⟩
  · have : α (a, 1) = α (a', 1) := Prod.ext h (by rw [hp1, hp1])
    exact (Prod.ext_iff.1 (α.injective this)).1
  · refine ⟨(α.symm (y, 1)).1, ?_⟩
    have h := congrArg Prod.fst (α.apply_symm_apply (y, 1))
    rw [apply_eq_mul] at h
    simpa [hp2] using h
  · have : α (1, b) = α (1, b') := Prod.ext (by rw [hp2, hp2]) h
    exact (Prod.ext_iff.1 (α.injective this)).2
  · refine ⟨(α.symm (1, y)).2, ?_⟩
    have h := congrArg Prod.snd (α.apply_symm_apply (1, y))
    rw [apply_eq_mul] at h
    simpa [hp1] using h

theorem bijective_of_swap (α : MulAut (S × S)) (hs1 : ∀ x : S, (α (x, 1)).1 = 1)
    (hs2 : ∀ x : S, (α (1, x)).2 = 1) :
    Function.Bijective (fun a : S => (α (a, 1)).2) ∧
      Function.Bijective (fun b : S => (α (1, b)).1) := by
  refine ⟨⟨fun a a' h => ?_, fun y => ?_⟩, ⟨fun b b' h => ?_, fun y => ?_⟩⟩
  · have : α (a, 1) = α (a', 1) := Prod.ext (by rw [hs1, hs1]) h
    exact (Prod.ext_iff.1 (α.injective this)).1
  · refine ⟨(α.symm (1, y)).1, ?_⟩
    have h := congrArg Prod.snd (α.apply_symm_apply (1, y))
    rw [apply_eq_mul] at h
    simpa [hs2] using h
  · have : α (1, b) = α (1, b') := Prod.ext h (by rw [hs2, hs2])
    exact (Prod.ext_iff.1 (α.injective this)).2
  · refine ⟨(α.symm (y, 1)).2, ?_⟩
    have h := congrArg Prod.fst (α.apply_symm_apply (y, 1))
    rw [apply_eq_mul] at h
    simpa [hs1] using h

theorem exists_prod_preserve (α : MulAut (S × S)) (hp1 : ∀ x : S, (α (x, 1)).2 = 1)
    (hp2 : ∀ x : S, (α (1, x)).1 = 1) :
    ∃ f₁ f₂ : MulAut S, ∀ a b : S, α (a, b) = (f₁ a, f₂ b) := by
  obtain ⟨h1, h2⟩ := bijective_of_preserve α hp1 hp2
  let φ₁ : S →* S := (MonoidHom.fst S S).comp (α.toMonoidHom.comp (MonoidHom.inl S S))
  let φ₂ : S →* S := (MonoidHom.snd S S).comp (α.toMonoidHom.comp (MonoidHom.inr S S))
  refine ⟨MulEquiv.ofBijective φ₁ h1, MulEquiv.ofBijective φ₂ h2, fun a b => ?_⟩
  rw [apply_eq_mul]
  ext
  · simp [φ₁, hp2]
  · simp [φ₂, hp1]

theorem exists_prod_swap (α : MulAut (S × S)) (hs1 : ∀ x : S, (α (x, 1)).1 = 1)
    (hs2 : ∀ x : S, (α (1, x)).2 = 1) :
    ∃ f₁ f₂ : MulAut S, ∀ a b : S, α (a, b) = (f₁ b, f₂ a) := by
  obtain ⟨h1, h2⟩ := bijective_of_swap α hs1 hs2
  let φ₁ : S →* S := (MonoidHom.fst S S).comp (α.toMonoidHom.comp (MonoidHom.inr S S))
  let φ₂ : S →* S := (MonoidHom.snd S S).comp (α.toMonoidHom.comp (MonoidHom.inl S S))
  refine ⟨MulEquiv.ofBijective φ₁ h2, MulEquiv.ofBijective φ₂ h1, fun a b => ?_⟩
  rw [apply_eq_mul]
  ext
  · simp [φ₁, hs1]
  · simp [φ₂, hs2]

end ProdAut

end CFSG.EvenSporadicStandard.M24Std
