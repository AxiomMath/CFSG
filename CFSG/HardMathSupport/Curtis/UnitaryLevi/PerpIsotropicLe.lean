module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.IsotropicNotOrthogonal
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearHermGram

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction

variable {p f : ℕ} {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

theorem le_of_isotropic_orthogonal (hE : UnitaryFieldData p f E) [FiniteDimensional E V]
    {B : V →ₛₗ[hE.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBs : B.SeparatingLeft)
    {X T : Submodule E V} (hX : ∀ x ∈ X, ∀ y ∈ X, B x y = 0)
    (hT : ∀ v ∈ T, B v v = 0)
    (hperp : ∀ b : V, B b b = 0 → (∀ x ∈ X, B x b = 0) → ∀ v ∈ T, B b v = 0) : T ≤ X := by
  intro v hvT
  by_contra hvX
  set P := X.orthogonalBilin B with hP
  have hXP : X ≤ P := fun x hx y hy => hX y hy x hx
  have hvP : v ∈ P := fun x hx =>
    hperp x (hX x hx x hx) (fun y hy => hX y hy x hx) v hvT
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl X
  set C : Submodule E V := D ⊓ P with hC
  have hXC : X ⊔ C = P := by
    rw [hC, ← sup_inf_assoc_of_le D hXP, hD.sup_eq_top, top_inf_eq]
  have hCD : C ≤ D := inf_le_left
  have hCP : C ≤ P := inf_le_right
  have hsymm : ∀ a b, B a b = 0 → B b a = 0 := fun a b hab => by rw [← hB.eq a b, hab, map_zero]
  obtain ⟨x, hx, c, hc, hxc⟩ := Submodule.mem_sup.mp (hXC ▸ hvP)
  have hcX : c ∉ X := fun hcX => hvX (by rw [← hxc]; exact X.add_mem hx hcX)
  have hc0 : c ≠ 0 := fun h0 => hcX (h0 ▸ X.zero_mem)
  have hcP : ∀ y ∈ X, B y c = 0 := fun y hy => hCP hc y hy
  have hcc : B c c = 0 := by
    have h1 := hT v hvT
    rw [← hxc] at h1
    have h2 : B x c = 0 := hcP x hx
    have h3 : B c x = 0 := hsymm _ _ h2
    simpa [map_add, LinearMap.add_apply, hX x hx x hx, h2, h3] using h1
  have hC0 : ∀ c' ∈ C, (∀ d ∈ C, B c' d = 0) → c' = 0 := by
    intro c' hc' hd
    have hc'P : c' ∈ P := hCP hc'
    have hmem : c' ∈ P.orthogonalBilin B := by
      intro y hy
      obtain ⟨x', hx', d, hd', rfl⟩ := Submodule.mem_sup.mp (hXC ▸ hy)
      rw [map_add, LinearMap.add_apply, hc'P x' hx', hsymm _ _ (hd d hd'), zero_add]
    rw [SesqShear.orthogonalBilin_orthogonalBilin_eq (σ := hE.bar) hE.bar_bar hB hBs X] at hmem
    have : c' ∈ X ⊓ D := ⟨hmem, hCD hc'⟩
    rwa [hD.inf_eq_bot, Submodule.mem_bot] at this
  let H : C →ₛₗ[hE.bar] C →ₗ[E] E := B.domRestrict₁₂ C C
  have hHsymm : H.IsSymm := ⟨fun a b => hB.eq a b⟩
  have hHsep : H.SeparatingLeft := by
    intro a ha
    exact Subtype.ext (hC0 a a.2 fun d hd => ha ⟨d, hd⟩)
  by_cases hdim : 2 ≤ Module.finrank E C
  · obtain ⟨u, hu0, hu⟩ := exists_isotropic_not_orthogonal hE hHsymm hHsep hdim
      (w := ⟨c, hc⟩) (fun h => hc0 (congrArg Subtype.val h))
    have h1 := hperp (u : V) hu0 (fun y hy => hCP u.2 y hy) v hvT
    apply hu
    show B (u : V) c = 0
    rw [← hxc, map_add] at h1
    have h2 : B (u : V) x = 0 := hsymm _ _ (hCP u.2 x hx)
    rwa [h2, zero_add] at h1
  · have hle : Module.finrank E C ≤ 1 := by omega
    obtain ⟨v0, hv0⟩ := finrank_le_one_iff.mp hle
    obtain ⟨a0, ha0⟩ := hv0 ⟨c, hc⟩
    have ha0' : a0 ≠ 0 := fun h => hc0 (by
      have := congrArg Subtype.val ha0
      simpa [h] using this.symm)
    refine hc0 (hC0 c hc fun d hd => ?_)
    obtain ⟨a1, ha1⟩ := hv0 ⟨d, hd⟩
    have hd' : d = (a1 / a0) • c := by
      have h1 := congrArg Subtype.val ha1
      have h2 := congrArg Subtype.val ha0
      simp only [SetLike.val_smul] at h1 h2
      rw [← h2, smul_smul, ← h1, div_mul_cancel₀ _ ha0']
    rw [hd', map_smul, hcc, smul_zero]

end CFSG.HardMathSupport.Curtis.UnitaryLevi
