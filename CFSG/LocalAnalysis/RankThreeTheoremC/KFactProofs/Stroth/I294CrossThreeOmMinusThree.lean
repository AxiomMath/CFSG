module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusStep

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure RotOrth (Q : QuadraticForm K V) (u v u' v' : V) : Prop where
  uu : polar Q u u' = 0
  uv : polar Q u v' = 0
  vu : polar Q v u' = 0
  vv : polar Q v v' = 0

theorem RotOrth.symm {u v u' v' : V} (h : RotOrth Q u v u' v') : RotOrth Q u' v' u v :=
  ⟨by rw [polar_comm]; exact h.uu, by rw [polar_comm]; exact h.vu,
    by rw [polar_comm]; exact h.uv, by rw [polar_comm]; exact h.vv⟩

theorem RotOrth.of_mem_perp2 {u v u' v' : V} (hu : u' ∈ perp2 Q u v) (hv : v' ∈ perp2 Q u v) :
    RotOrth Q u v u' v' :=
  ⟨(mem_perp2.1 hu).1, (mem_perp2.1 hv).1, (mem_perp2.1 hu).2, (mem_perp2.1 hv).2⟩

theorem exists_three_rotPairs [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ y, g (g (g y)) = y) :
    ∃ (c₁ c₂ c₃ : K) (u₁ v₁ u₂ v₂ u₃ v₃ : V),
      IsRotPair Q c₁ u₁ v₁ ∧ IsRotPair Q c₂ u₂ v₂ ∧ IsRotPair Q c₃ u₃ v₃ ∧
      RotMode g u₁ v₁ ∧ RotMode g u₂ v₂ ∧ RotMode g u₃ v₃ ∧
      RotOrth Q u₁ v₁ u₂ v₂ ∧ RotOrth Q u₁ v₁ u₃ v₃ ∧ RotOrth Q u₂ v₂ u₃ v₃ := by
  have hS₀ : PolarNondegOn Q (⊤ : Submodule K V) := polarNondegOn_top hQ
  have hg₀ : ∀ x ∈ (⊤ : Submodule K V), g x ∈ (⊤ : Submodule K V) := fun x _ => Submodule.mem_top
  have hdim₀ : 3 ≤ Module.finrank K (⊤ : Submodule K V) := by rw [finrank_top]; omega
  obtain ⟨c₁, u₁, v₁, h₁, hu₁, hv₁, m₁⟩ := exists_rotPair_in h3 hg hg3 hS₀ hg₀ hdim₀
  have hS₁ : PolarNondegOn Q ((⊤ : Submodule K V) ⊓ perp2 Q u₁ v₁) :=
    h₁.polarNondegOn_inf_perp2 h3 hS₀ hu₁ hv₁
  have hg₁ := m₁.stable_inf_perp2 hg hg₀
  have hdim₁ : 3 ≤ Module.finrank K ((⊤ : Submodule K V) ⊓ perp2 Q u₁ v₁ : Submodule K V) := by
    have := h₁.finrank_inf_perp2 h3 hu₁ hv₁
    rw [finrank_top] at this
    omega
  obtain ⟨c₂, u₂, v₂, h₂, hu₂, hv₂, m₂⟩ := exists_rotPair_in h3 hg hg3 hS₁ hg₁ hdim₁
  have hS₂ : PolarNondegOn Q (((⊤ : Submodule K V) ⊓ perp2 Q u₁ v₁) ⊓ perp2 Q u₂ v₂) :=
    h₂.polarNondegOn_inf_perp2 h3 hS₁ hu₂ hv₂
  have hg₂ := m₂.stable_inf_perp2 hg hg₁
  have hdim₂ : 3 ≤ Module.finrank K
      (((⊤ : Submodule K V) ⊓ perp2 Q u₁ v₁) ⊓ perp2 Q u₂ v₂ : Submodule K V) := by
    have h' := h₂.finrank_inf_perp2 h3 hu₂ hv₂
    have h'' := h₁.finrank_inf_perp2 h3 hu₁ hv₁
    rw [finrank_top] at h''
    omega
  obtain ⟨c₃, u₃, v₃, h₃, hu₃, hv₃, m₃⟩ := exists_rotPair_in h3 hg hg3 hS₂ hg₂ hdim₂
  have o₁₂ : RotOrth Q u₁ v₁ u₂ v₂ :=
    RotOrth.of_mem_perp2 (Submodule.mem_inf.1 hu₂).2 (Submodule.mem_inf.1 hv₂).2
  have o₂₃ : RotOrth Q u₂ v₂ u₃ v₃ :=
    RotOrth.of_mem_perp2 (Submodule.mem_inf.1 hu₃).2 (Submodule.mem_inf.1 hv₃).2
  have o₁₃ : RotOrth Q u₁ v₁ u₃ v₃ :=
    RotOrth.of_mem_perp2 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hu₃).1).2
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv₃).1).2
  exact ⟨c₁, c₂, c₃, u₁, v₁, u₂, v₂, u₃, v₃, h₁, h₂, h₃, m₁, m₂, m₃, o₁₂, o₁₃, o₂₃⟩

section Cube

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def powHom (t : G) (ht : t ^ 3 = 1) : Multiplicative (ZMod 3) →* G where
  toFun a := t ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_add, ← pow_eq_pow_mod _ ht]

@[expose] def cubeHom (t₁ t₂ t₃ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1) (h₃ : t₃ ^ 3 = 1)
    (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃) (c₂₃ : Commute t₂ t₃) :
    Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →* G :=
  (powHom t₁ h₁).noncommCoprod
    ((powHom t₂ h₂).noncommCoprod (powHom t₃ h₃) fun a b => c₂₃.pow_pow _ _)
    fun a p => (c₁₂.pow_pow _ _).mul_right (c₁₃.pow_pow _ _)

theorem cubeHom_apply (t₁ t₂ t₃ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1) (h₃ : t₃ ^ 3 = 1)
    (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃) (c₂₃ : Commute t₂ t₃)
    (a b c : Multiplicative (ZMod 3)) :
    cubeHom t₁ t₂ t₃ h₁ h₂ h₃ c₁₂ c₁₃ c₂₃ (a, b, c) =
      t₁ ^ a.toAdd.val * (t₂ ^ b.toAdd.val * t₃ ^ c.toAdd.val) := rfl

theorem pow_smul_eq_self' {t : G} {x : X} (h : t • x = x) (n : ℕ) : t ^ n • x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

theorem eq_zero_of_pow_smul {t : G} {x : X} (ht : t ^ 3 = 1) (hx : t • x ≠ x) {n : ℕ}
    (hn : n < 3) (h : t ^ n • x = x) : n = 0 := by
  interval_cases n
  · rfl
  · exact absurd (by simpa using h) hx
  · exfalso
    apply hx
    calc t • x = t • (t ^ 2 • x) := by rw [h]
      _ = (t * t ^ 2) • x := (mul_smul _ _ _).symm
      _ = x := by rw [← pow_succ', ht, one_smul]

theorem cubeHom_injective (t₁ t₂ t₃ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1) (h₃ : t₃ ^ 3 = 1)
    (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃) (c₂₃ : Commute t₂ t₃) (x₁ x₂ x₃ : X)
    (n₁ : t₁ • x₁ ≠ x₁) (n₂ : t₂ • x₂ ≠ x₂) (n₃ : t₃ • x₃ ≠ x₃)
    (f₁₂ : t₂ • x₁ = x₁) (f₁₃ : t₃ • x₁ = x₁) (f₂₁ : t₁ • x₂ = x₂) (f₂₃ : t₃ • x₂ = x₂)
    (f₃₁ : t₁ • x₃ = x₃) (f₃₂ : t₂ • x₃ = x₃) :
    Function.Injective (cubeHom t₁ t₂ t₃ h₁ h₂ h₃ c₁₂ c₁₃ c₂₃) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c⟩ habc
  rw [cubeHom_apply] at habc
  have hval : ∀ (z : Multiplicative (ZMod 3)), z.toAdd.val < 3 := fun z => ZMod.val_lt _
  have hzero : ∀ (z : Multiplicative (ZMod 3)), z.toAdd.val = 0 → z = 1 := fun z hz =>
    toAdd_eq_zero.1 ((ZMod.val_eq_zero z.toAdd).1 hz)
  have ha : a = 1 := by
    apply hzero
    refine eq_zero_of_pow_smul h₁ n₁ (hval a) ?_
    have := congrArg (fun k : G => k • x₁) habc
    simp only [mul_smul, one_smul] at this
    rwa [pow_smul_eq_self' f₁₃, pow_smul_eq_self' f₁₂] at this
  have hb : b = 1 := by
    apply hzero
    refine eq_zero_of_pow_smul h₂ n₂ (hval b) ?_
    have habc' : t₂ ^ b.toAdd.val * (t₁ ^ a.toAdd.val * t₃ ^ c.toAdd.val) = 1 := by
      rw [← (c₁₂.pow_pow a.toAdd.val b.toAdd.val).left_comm]
      exact habc
    have := congrArg (fun k : G => k • x₂) habc'
    simp only [mul_smul, one_smul] at this
    rwa [pow_smul_eq_self' f₂₃, pow_smul_eq_self' f₂₁] at this
  have hc : c = 1 := by
    apply hzero
    refine eq_zero_of_pow_smul h₃ n₃ (hval c) ?_
    have habc' : t₃ ^ c.toAdd.val * (t₁ ^ a.toAdd.val * t₂ ^ b.toAdd.val) = 1 := by
      rw [← (c₁₃.pow_pow a.toAdd.val c.toAdd.val).left_comm,
        ← (c₂₃.pow_pow b.toAdd.val c.toAdd.val).eq]
      exact habc
    have := congrArg (fun k : G => k • x₃) habc'
    simp only [mul_smul, one_smul] at this
    rwa [pow_smul_eq_self' f₃₂, pow_smul_eq_self' f₃₁] at this
  rw [ha, hb, hc]
  rfl

end Cube

theorem exists_injective_hom_three [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) :
    ∃ φ : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →*
        (V ≃ₗ[K] V), Function.Injective φ ∧
      (∀ a, φ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧ ∀ a, φ a * g = g * φ a := by
  have hg3' : ∀ y, g (g (g y)) = y := fun y => by
    have h := congrArg (fun f : V ≃ₗ[K] V => f y) hg3
    simpa [pow_succ] using h
  obtain ⟨c₁, c₂, c₃, u₁, v₁, u₂, v₂, u₃, v₃, h₁, h₂, h₃, m₁, m₂, m₃, o₁₂, o₁₃, o₂₃⟩ :=
    exists_three_rotPairs h3 hQ hdim hg hg3'
  have p₁ := h₁.rotAut_pow_three
  have p₂ := h₂.rotAut_pow_three
  have p₃ := h₃.rotAut_pow_three
  have k₁₂ : Commute h₁.rotAut h₂.rotAut :=
    h₁.rotAut_comm_rotAut h₂ o₁₂.uu o₁₂.uv o₁₂.vu o₁₂.vv
  have k₁₃ : Commute h₁.rotAut h₃.rotAut :=
    h₁.rotAut_comm_rotAut h₃ o₁₃.uu o₁₃.uv o₁₃.vu o₁₃.vv
  have k₂₃ : Commute h₂.rotAut h₃.rotAut :=
    h₂.rotAut_comm_rotAut h₃ o₂₃.uu o₂₃.uv o₂₃.vu o₂₃.vv
  refine ⟨cubeHom h₁.rotAut h₂.rotAut h₃.rotAut p₁ p₂ p₃ k₁₂ k₁₃ k₂₃, ?_, ?_, ?_⟩
  · refine cubeHom_injective (X := V) h₁.rotAut h₂.rotAut h₃.rotAut p₁ p₂ p₃ k₁₂ k₁₃ k₂₃ u₁ u₂ u₃
      (h₁.rotAut_ne h3) (h₂.rotAut_ne h3) (h₃.rotAut_ne h3) ?_ ?_ ?_ ?_ ?_ ?_
    · exact h₂.rotAut_of_perp o₁₂.symm.uu o₁₂.symm.vu
    · exact h₃.rotAut_of_perp o₁₃.symm.uu o₁₃.symm.vu
    · exact h₁.rotAut_of_perp o₁₂.uu o₁₂.vu
    · exact h₃.rotAut_of_perp o₂₃.symm.uu o₂₃.symm.vu
    · exact h₁.rotAut_of_perp o₁₃.uu o₁₃.vu
    · exact h₂.rotAut_of_perp o₂₃.uu o₂₃.vu
  · rintro ⟨a, b, c⟩
    rw [cubeHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ h₁.rotAut_mem_orthogonalGroup _)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ h₂.rotAut_mem_orthogonalGroup _)
        (Subgroup.pow_mem _ h₃.rotAut_mem_orthogonalGroup _))
  · rintro ⟨a, b, c⟩
    rw [cubeHom_apply]
    have e₁ : Commute h₁.rotAut g := h₁.rotAut_comm_of_mode hg m₁
    have e₂ : Commute h₂.rotAut g := h₂.rotAut_comm_of_mode hg m₂
    have e₃ : Commute h₃.rotAut g := h₃.rotAut_comm_of_mode hg m₃
    exact ((e₁.pow_left _).mul_left ((e₂.pow_left _).mul_left (e₃.pow_left _))).eq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus
