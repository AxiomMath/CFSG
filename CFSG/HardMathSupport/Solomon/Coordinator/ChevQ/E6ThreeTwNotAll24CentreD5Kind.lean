module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option maxRecDepth 100000

section Invariant

@[expose] def D5Inv (Ψ : Set (Fin Tag.E6.rank → ℤ)) (Ω x : Fin Tag.E6.rank → ℤ) : Prop :=
  (∀ γ ∈ Ψ, (4 : ℤ) ∣ iform x γ) ∧ (16 : ℤ) ∣ iform x Ω

theorem D5Inv.add {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω x y : Fin Tag.E6.rank → ℤ}
    (hx : D5Inv Ψ Ω x) (hy : D5Inv Ψ Ω y) : D5Inv Ψ Ω (x + y) :=
  ⟨fun γ hγ => by rw [iform_add_left]; exact dvd_add (hx.1 γ hγ) (hy.1 γ hγ),
    by rw [iform_add_left]; exact dvd_add hx.2 hy.2⟩

theorem D5Inv.neg {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω x : Fin Tag.E6.rank → ℤ}
    (hx : D5Inv Ψ Ω x) : D5Inv Ψ Ω (-x) := by
  have e : ∀ y : Fin Tag.E6.rank → ℤ, iform (-x) y = -iform x y := fun y => by
    have := iform_smul_left (τ := Tag.E6) (-1) x y
    rw [neg_one_smul] at this
    rw [this]
    ring
  exact ⟨fun γ hγ => by rw [e]; exact (dvd_neg).2 (hx.1 γ hγ), by rw [e]; exact (dvd_neg).2 hx.2⟩

theorem iform_self_E6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  rw [← dotProduct_mulVec_eq_iform]
  exact rootForm_self (Or.inr (Or.inl rfl)) hγ

theorem corootPair_E6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (x : Fin Tag.E6.rank → ℤ) : corootPair γ x = iform γ x := by
  unfold corootPair
  rw [iform_self_E6 hγ]
  omega

theorem D5Inv.reflect {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ}
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) (h4 : ∀ γ ∈ Ψ, (4 : ℤ) ∣ iform Ω γ)
    {γ₀ : Fin Tag.E6.rank → ℤ} (hγ₀ : γ₀ ∈ Ψ) {x : Fin Tag.E6.rank → ℤ} (hx : D5Inv Ψ Ω x) :
    D5Inv Ψ Ω (rootReflection γ₀ • x) := by
  rw [rootReflection_smul (hΨ γ₀ hγ₀), corootPair_E6 (hΨ γ₀ hγ₀)]
  have hc : (4 : ℤ) ∣ iform γ₀ x := by rw [iform_comm]; exact hx.1 γ₀ hγ₀
  obtain ⟨c', hc'⟩ := hc
  refine ⟨fun γ hγ => ?_, ?_⟩
  · rw [iform_sub_left, iform_smul_left, hc']
    exact dvd_sub (hx.1 γ hγ) ⟨c' * iform γ₀ γ, by ring⟩
  · rw [iform_sub_left, iform_smul_left, hc']
    have h4' : (4 : ℤ) ∣ iform γ₀ Ω := by rw [iform_comm]; exact h4 γ₀ hγ₀
    obtain ⟨d, hd⟩ := h4'
    exact dvd_sub hx.2 ⟨c' * d, by rw [hd]; ring⟩

@[expose] def D5Good (Ψ : Set (Fin Tag.E6.rank → ℤ)) (Ω : Fin Tag.E6.rank → ℤ)
    (w : WeylGroup Tag.E6) : Prop :=
  (∀ x, D5Inv Ψ Ω x → D5Inv Ψ Ω (w • x) ∧ D5Inv Ψ Ω (w⁻¹ • x)) ∧ D5Inv Ψ Ω (w • Ω - Ω)

theorem D5Good.mul {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ}
    {w₁ w₂ : WeylGroup Tag.E6} (h₁ : D5Good Ψ Ω w₁) (h₂ : D5Good Ψ Ω w₂) :
    D5Good Ψ Ω (w₁ * w₂) := by
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · rw [mul_smul]
    exact (h₁.1 _ (h₂.1 x hx).1).1
  · rw [mul_inv_rev, mul_smul]
    exact (h₂.1 _ (h₁.1 x hx).2).2
  · have := (h₁.1 _ h₂.2).1.add h₁.2
    rwa [smul_sub, sub_add_sub_cancel, ← mul_smul] at this

theorem D5Good.inv {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ}
    {w : WeylGroup Tag.E6} (h : D5Good Ψ Ω w) : D5Good Ψ Ω w⁻¹ := by
  refine ⟨fun x hx => ⟨(h.1 x hx).2, ?_⟩, ?_⟩
  · rw [inv_inv]
    exact (h.1 x hx).1
  · have := (h.1 _ h.2).2.neg
    rwa [smul_sub, inv_smul_smul, neg_sub] at this

theorem D5Good.one {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ} :
    D5Good Ψ Ω 1 := by
  refine ⟨fun x hx => ⟨by simpa using hx, by simpa using hx⟩, ?_⟩
  rw [one_smul, sub_self]
  exact ⟨fun γ _ => by
      rw [show iform (0 : Fin Tag.E6.rank → ℤ) γ = 0 from by simp [iform]]
      exact dvd_zero _,
    by rw [show iform (0 : Fin Tag.E6.rank → ℤ) Ω = 0 from by simp [iform]]; exact dvd_zero _⟩

theorem D5Good.reflect {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ}
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) (h4 : ∀ γ ∈ Ψ, (4 : ℤ) ∣ iform Ω γ)
    {γ₀ : Fin Tag.E6.rank → ℤ} (hγ₀ : γ₀ ∈ Ψ) : D5Good Ψ Ω (rootReflection γ₀) := by
  have hr := hΨ γ₀ hγ₀
  refine ⟨fun x hx => ⟨D5Inv.reflect hΨ h4 hγ₀ hx, ?_⟩, ?_⟩
  · rw [rootReflection_inv hr]
    exact D5Inv.reflect hΨ h4 hγ₀ hx
  · rw [rootReflection_smul hr, corootPair_E6 hr]
    have hc : (4 : ℤ) ∣ iform γ₀ Ω := by rw [iform_comm]; exact h4 γ₀ hγ₀
    obtain ⟨c', hc'⟩ := hc
    have e : Ω - iform γ₀ Ω • γ₀ - Ω = -(iform γ₀ Ω • γ₀) := by abel
    rw [e]
    refine ⟨fun γ hγ => ?_, ?_⟩
    · have e1 : iform (-(iform γ₀ Ω • γ₀)) γ = -(iform γ₀ Ω * iform γ₀ γ) := by
        have := iform_smul_left (τ := Tag.E6) (-(iform γ₀ Ω)) γ₀ γ
        rw [neg_smul] at this
        rw [this]
        ring
      rw [e1, hc']
      exact ⟨-(c' * iform γ₀ γ), by ring⟩
    · have e1 : iform (-(iform γ₀ Ω • γ₀)) Ω = -(iform γ₀ Ω * iform γ₀ Ω) := by
        have := iform_smul_left (τ := Tag.E6) (-(iform γ₀ Ω)) γ₀ Ω
        rw [neg_smul] at this
        rw [this]
        ring
      rw [e1, hc']
      exact ⟨-(c' * c'), by ring⟩

theorem D5Good.of_mem_closure {Ψ : Set (Fin Tag.E6.rank → ℤ)} {Ω : Fin Tag.E6.rank → ℤ}
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) (h4 : ∀ γ ∈ Ψ, (4 : ℤ) ∣ iform Ω γ)
    {w : WeylGroup Tag.E6}
    (hw : w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    D5Good Ψ Ω w := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    exact D5Good.reflect hΨ h4 hγ
  | one => exact D5Good.one
  | mul _ _ _ _ h₁ h₂ => exact h₁.mul h₂
  | inv _ _ h => exact h.inv

theorem not_exists_neg_of_invariant {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) {Ω : Fin Tag.E6.rank → ℤ}
    (hspan : Ω ∈ AddSubgroup.closure Ψ) (h4 : ∀ γ ∈ Ψ, (4 : ℤ) ∣ iform Ω γ)
    (h16 : ¬ (16 : ℤ) ∣ 2 * iform Ω Ω) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ},
      ∀ γ ∈ Ψ, w • γ = -γ := by
  rintro ⟨w, hw, hneg⟩
  have hall : ∀ x ∈ AddSubgroup.closure Ψ, w • x = -x := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact hneg x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy, neg_add]
    | neg x _ hx => rw [smul_neg, hx]
  have hwΩ : w • Ω = -Ω := hall Ω hspan
  have h := (D5Good.of_mem_closure hΨ h4 hw).2
  rw [hwΩ] at h
  have h2 := h.2
  have e : iform (-Ω - Ω) Ω = -(2 * iform Ω Ω) := by
    have := iform_sub_left (τ := Tag.E6) (-Ω) Ω Ω
    rw [this]
    have h' : iform (-Ω) Ω = -iform Ω Ω := by
      have := iform_smul_left (τ := Tag.E6) (-1) Ω Ω
      rw [neg_one_smul] at this
      rw [this]
      ring
    rw [h']
    ring
  rw [e] at h2
  exact h16 ((dvd_neg).1 h2)

end Invariant

section Nodes

@[expose] def sD5a : Finset (Option (Fin Tag.E6.rank)) :=
  ({some 1, some 2, some 3, some 4, some 5} : Finset (Option (Fin 6)))

@[expose] def sD5b : Finset (Option (Fin Tag.E6.rank)) :=
  ({some 0, some 1, some 2, some 3, some 4} : Finset (Option (Fin 6)))

@[expose] def sD5c : Finset (Option (Fin Tag.E6.rank)) :=
  ({none, some 1, some 2, some 3, some 4} : Finset (Option (Fin 6)))

@[expose] def lD5a : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![some 5, some 4, some 3, some 2, some 1] : Fin 5 → Option (Fin 6))

@[expose] def lD5b : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![some 0, some 2, some 3, some 4, some 1] : Fin 5 → Option (Fin 6))

@[expose] def lD5c : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![none, some 1, some 3, some 2, some 4] : Fin 5 → Option (Fin 6))

@[expose] def d5Vec (l : Fin 5 → Option (Fin Tag.E6.rank)) : Fin Tag.E6.rank → ℤ :=
  (2 : ℤ) • e6ExtVec (l 0) + (4 : ℤ) • e6ExtVec (l 1) + (6 : ℤ) • e6ExtVec (l 2) +
    (3 : ℤ) • e6ExtVec (l 3) + (5 : ℤ) • e6ExtVec (l 4)

theorem lD5a_range : (Finset.univ.image lD5a) = sD5a := by decide +kernel

theorem lD5b_range : (Finset.univ.image lD5b) = sD5b := by decide +kernel

theorem lD5c_range : (Finset.univ.image lD5c) = sD5c := by decide +kernel

theorem d5Vec_a_dvd : ∀ j : Fin 5, (4 : ℤ) ∣ iform (d5Vec lD5a) (e6ExtVec (lD5a j)) := by
  decide +kernel

theorem d5Vec_b_dvd : ∀ j : Fin 5, (4 : ℤ) ∣ iform (d5Vec lD5b) (e6ExtVec (lD5b j)) := by
  decide +kernel

theorem d5Vec_c_dvd : ∀ j : Fin 5, (4 : ℤ) ∣ iform (d5Vec lD5c) (e6ExtVec (lD5c j)) := by
  decide +kernel

theorem d5Vec_a_self : iform (d5Vec lD5a) (d5Vec lD5a) = 20 := by decide +kernel

theorem d5Vec_b_self : iform (d5Vec lD5b) (d5Vec lD5b) = 20 := by decide +kernel

theorem d5Vec_c_self : iform (d5Vec lD5c) (d5Vec lD5c) = 20 := by decide +kernel

end Nodes

section Transport

theorem iform_neg_right_E6 (x y : Fin Tag.E6.rank → ℤ) : iform x (-y) = -iform x y := by
  have := iform_smul_right (τ := Tag.E6) (-1) x y
  rw [neg_one_smul] at this
  rw [this]
  ring

theorem dvd_iform_of_mem_rootsOf {C : Finset (Option (Fin Tag.E6.rank))}
    {Ω : Fin Tag.E6.rank → ℤ} (h4 : ∀ x ∈ C, (4 : ℤ) ∣ iform Ω (e6ExtVec x))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank)))) :
    (4 : ℤ) ∣ iform Ω γ := by
  obtain ⟨-, n, hn, hγn⟩ := hγ
  have hsum : ∀ m : Option (Fin Tag.E6.rank) → ℕ, (∀ x, m x ≠ 0 → x ∈ C) →
      (4 : ℤ) ∣ iform Ω (kacE6.combo m) := by
    intro m hm
    rw [iform_comm, kacE6.iform_combo_left]
    refine Finset.dvd_sum fun x _ => ?_
    by_cases hx : m x = 0
    · rw [hx]
      simp
    · rw [iform_comm, kacE6_extRoot]
      exact Dvd.dvd.mul_left (h4 x (hm x hx)) _
  have hn' : ∀ x, n x ≠ 0 → x ∈ C := fun x hx => by simpa using hn x hx
  rcases hγn with rfl | rfl
  · exact hsum n hn'
  · rw [iform_neg_right_E6]
    exact (dvd_neg).2 (hsum n hn')

theorem not_exists_neg_of_labelled {C : Finset (Option (Fin Tag.E6.rank))}
    {l : Fin 5 → Option (Fin Tag.E6.rank)} (hl : Finset.univ.image l = C)
    (h4 : ∀ j, (4 : ℤ) ∣ iform (d5Vec l) (e6ExtVec (l j)))
    (hself : iform (d5Vec l) (d5Vec l) = 20) (v : WeylGroup Tag.E6) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun α => v • α) ''
        kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))),
        w • γ = -γ := by
  have hmemC : ∀ j, l j ∈ C := fun j => by rw [← hl]; simp
  have h4C : ∀ x ∈ C, (4 : ℤ) ∣ iform (d5Vec l) (e6ExtVec x) := by
    intro x hx
    rw [← hl] at hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact h4 j
  apply not_exists_neg_of_invariant (Ω := v • d5Vec l)
  · rintro _ ⟨γ, hγ, rfl⟩
    exact IsRoot.smul hγ.1 v
  · have hcl : ∀ j, v • e6ExtVec (l j) ∈ AddSubgroup.closure
        ((fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank)))) := fun j =>
      AddSubgroup.subset_closure ⟨e6ExtVec (l j), by
        rw [← kacE6_extRoot]
        exact extRoot_mem_rootsOf kacE6 (Finset.mem_coe.2 (hmemC j)), rfl⟩
    unfold d5Vec
    rw [smul_add, smul_add, smul_add, smul_add, smul_comm v (2 : ℤ), smul_comm v (4 : ℤ),
      smul_comm v (6 : ℤ), smul_comm v (3 : ℤ), smul_comm v (5 : ℤ)]
    exact add_mem (add_mem (add_mem (add_mem (AddSubgroup.zsmul_mem _ (hcl 0) _)
      (AddSubgroup.zsmul_mem _ (hcl 1) _)) (AddSubgroup.zsmul_mem _ (hcl 2) _))
      (AddSubgroup.zsmul_mem _ (hcl 3) _)) (AddSubgroup.zsmul_mem _ (hcl 4) _)
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [iform_smul]
    exact dvd_iform_of_mem_rootsOf h4C hγ
  · rw [iform_smul, hself]
    decide

theorem not_exists_neg_D5 {C : Finset (Option (Fin Tag.E6.rank))}
    (hC : C = sD5a ∨ C = sD5b ∨ C = sD5c) (v : WeylGroup Tag.E6) :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun α => v • α) ''
        kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))), s = rootReflection γ},
      ∀ γ ∈ (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))),
        w • γ = -γ := by
  rcases hC with rfl | rfl | rfl
  · exact not_exists_neg_of_labelled lD5a_range d5Vec_a_dvd d5Vec_a_self v
  · exact not_exists_neg_of_labelled lD5b_range d5Vec_b_dvd d5Vec_b_self v
  · exact not_exists_neg_of_labelled lD5c_range d5Vec_c_dvd d5Vec_c_self v

end Transport

section Class

@[expose] def kcD5B (zl : List ℕ) : Bool :=
  zl.all fun x => szF zl x == 40 &&
    ((cmpF zl x == sD5a) || (cmpF zl x == sD5b) || (cmpF zl x == sD5c))

set_option synthInstance.maxSize 1024 in
theorem kc_d5 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    cntB m0.val m1.val m2.val m3.val m4.val m5.val = 40 →
    kcD5B (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

theorem card_sD5 : sD5a.card = 5 ∧ sD5b.card = 5 ∧ sD5c.card = 5 := by decide

theorem d5_class_data {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 40) (i : KernelComponent (rootCharHom a)) :
    ∃ (v : WeylGroup Tag.E6) (C : Finset (Option (Fin Tag.E6.rank))),
      (C = sD5a ∨ C = sD5b ∨ C = sD5c) ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' kacE6.rootsOf (↑C : Set (Option (Fin Tag.E6.rank))) ∧
      (componentRoots (rootCharHom a) i).ncard = 40 ∧
        compRank (componentRoots (rootCharHom a) i) = 5 := by
  classical
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  have hcnt := ncard_kernelRoots_eq_cntB hζ w hchar
  have hk0 : cntB m0.val m1.val m2.val m3.val m4.val m5.val = 40 := by rwa [hcnt] at hk
  have hB := kc_d5 m0 m1 m2 m3 m4 m5 hsum hk0
  obtain ⟨x, hx, hroots, hncard, hrank, -⟩ := hcl i
  have hx' := List.all_eq_true.1 hB x hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hx'
  obtain ⟨hsz, hc⟩ := hx'
  obtain ⟨c5a, c5b, c5c⟩ := card_sD5
  have hC : cmpF (zlC m0 m1 m2 m3 m4 m5) x = sD5a ∨ cmpF (zlC m0 m1 m2 m3 m4 m5) x = sD5b ∨
      cmpF (zlC m0 m1 m2 m3 m4 m5) x = sD5c := by
    rcases hc with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨w⁻¹, cmpF (zlC m0 m1 m2 m3 m4 m5) x, hC, hroots, by rw [hncard, hsz], ?_⟩
  rw [hrank]
  rcases hC with h | h | h <;> rw [h] <;> assumption

theorem kernelReflectionGroup_le_closure {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : kernelRoots (rootCharHom a) ⊆ Ψ) :
    kernelReflectionGroup a ≤
      Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, i, hγ, rfl⟩
  rw [conj_simple_eq_rootReflection]
  exact Subgroup.subset_closure ⟨_, hΨ hγ, rfl⟩

theorem not_twistInner_of_neg {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    {ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} {u : WeylGroup Tag.E6}
    (hu : u ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hρ : ∀ γ ∈ Ψ, ρ γ = -(u • γ))
    (hno : ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ},
      ∀ γ ∈ Ψ, w • γ = -γ) : ¬ twistInner Ψ ρ := by
  rintro ⟨w, hw, hwρ⟩
  refine hno ⟨u⁻¹ * w, mul_mem (inv_mem hu) hw, fun γ hγ => ?_⟩
  rw [mul_smul, ← hwρ γ hγ, hρ γ hγ, smul_neg, inv_smul_smul]

end Class

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
