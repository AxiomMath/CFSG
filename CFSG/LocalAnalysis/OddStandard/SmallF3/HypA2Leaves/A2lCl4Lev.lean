module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Stab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Dual

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def Cl24Lev (P : HypPair Q) (g : elementaryGroup Q) : Prop :=
  (∀ w ∈ P.perp, (g : V ≃ₗ[K] V) w ∈ P.perp ∧
      ((g⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) w ∈ P.perp) ∧
    ∀ z, (∀ w ∈ P.perp, polar Q z w = 0) → (g : V ≃ₗ[K] V) z = z

variable {P : HypPair Q} {g : elementaryGroup Q}

theorem Cl24Lev.apply_e (hg : Cl24Lev P g) : (g : V ≃ₗ[K] V) P.e = P.e :=
  hg.2 _ fun _ hw => cl24_polar_e_of_mem_perp P hw

@[expose] noncomputable def cl24_levEquiv (hg : Cl24Lev P g) : P.perp ≃ P.perp where
  toFun w := ⟨(g : V ≃ₗ[K] V) w, (hg.1 w w.2).1⟩
  invFun w := ⟨((g⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) w, (hg.1 w w.2).2⟩
  left_inv w := Subtype.ext (by
    show ((g⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) w) = w
    rw [← LinearEquiv.mul_apply]
    simp)
  right_inv w := Subtype.ext (by
    show (g : V ≃ₗ[K] V) (((g⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) w) = w
    rw [← LinearEquiv.mul_apply]
    simp)

theorem cl24_polar_levEquiv (hg : Cl24Lev P g) (v w : P.perp) :
    polar Q (cl24_levEquiv hg v : V) (cl24_levEquiv hg w : V) = polar Q (v : V) (w : V) :=
  polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) v w

theorem cl24_conj_eps (hg : Cl24Lev P g) (w : P.perp) :
    g * cl24_eps P w * g⁻¹ = cl24_eps P (cl24_levEquiv hg w) := by
  apply Subtype.ext
  change (g : V ≃ₗ[K] V) * eichler Q P.e w * (g : V ≃ₗ[K] V)⁻¹
      = eichler Q P.e ((g : V ≃ₗ[K] V) w)
  rw [eichler_conj (elementaryGroup_le_orthogonalGroup Q g.2) P.e w, hg.apply_e]

theorem cl24_lev_exists [Finite K] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    {x y : V} (hxW : x ∈ P₁.perp) (hyW : y ∈ P₁.perp) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Q x = Q y) :
    ∃ g : elementaryGroup Q, Cl24Lev P₁ g ∧ (g : V ≃ₗ[K] V) x = y := by
  haveI : Finite V := Module.finite_of_finite K
  have he₂ : P₂.e ∈ P₁.perp := by
    rw [HypPair.mem_perp]; exact ⟨h₁₂.ee, h₁₂.fe⟩
  have hf₂ : P₂.f ∈ P₁.perp := by
    rw [HypPair.mem_perp]; exact ⟨h₁₂.ef, h₁₂.ff⟩
  have he₃ : P₃.e ∈ P₁.perp := by
    rw [HypPair.mem_perp]; exact ⟨h₁₃.ee, h₁₃.fe⟩
  have hf₃ : P₃.f ∈ P₁.perp := by
    rw [HypPair.mem_perp]; exact ⟨h₁₃.ef, h₁₃.ff⟩
  obtain ⟨g, hg, hgx, hgW, hgz⟩ :=
    exists_mem_elementaryGroup_apply_eq_of_mem (P₁.polarNondegOn_perp hQ) h₂₃ he₂ hf₂ he₃ hf₃
      hxW hyW hx hy hxy
  refine ⟨⟨g, hg⟩, ⟨fun w hw => ⟨hgW w hw, ?_⟩, fun z hz => hgz z hz⟩, hgx⟩
  change (g⁻¹ : V ≃ₗ[K] V) w ∈ P₁.perp
  have hinj : Function.Injective fun u : P₁.perp => (⟨g u, hgW u u.2⟩ : P₁.perp) := by
    intro u v huv
    exact Subtype.ext (g.injective (congrArg Subtype.val huv))
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective).1 hinj ⟨w, hw⟩
  have hgu : g (u : V) = w := congrArg Subtype.val hu
  have hfinv : g⁻¹ w = (u : V) := by
    rw [← hgu, LinearEquiv.inv_apply_apply']
  rw [hfinv]
  exact u.2

section Action

variable {X : Type*} [MulAction (elementaryGroup Q) X]
  (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1)

theorem cl24_mem_D_smul (hg : Cl24Lev P g) (y : X) (w : P.perp) :
    w ∈ cl24_D hK P (g • y) ↔ (cl24_levEquiv hg).symm w ∈ cl24_D hK P y := by
  rw [cl24_mem_D, cl24_mem_D]
  have hconj : cl24_eps P w = g * cl24_eps P ((cl24_levEquiv hg).symm w) * g⁻¹ := by
    simpa using (cl24_conj_eps hg ((cl24_levEquiv hg).symm w)).symm
  rw [hconj, mul_smul, mul_smul, inv_smul_smul]
  exact smul_left_cancel_iff g

theorem cl24_card_D_smul (hg : Cl24Lev P g) (y : X) :
    Nat.card (cl24_D hK P (g • y)) = Nat.card (cl24_D hK P y) :=
  Nat.card_congr (Equiv.subtypeEquiv (cl24_levEquiv hg).symm fun w => cl24_mem_D_smul hK hg y w)

theorem cl24_mem_perpIn_smul (hg : Cl24Lev P g) (y : X) (v : P.perp) :
    v ∈ cl24_perpIn P (cl24_D hK P (g • y)) ↔
      (cl24_levEquiv hg).symm v ∈ cl24_perpIn P (cl24_D hK P y) := by
  rw [cl24_mem_perpIn, cl24_mem_perpIn]
  constructor
  · intro h d hd
    have hmem : cl24_levEquiv hg d ∈ cl24_D hK P (g • y) := by
      rw [cl24_mem_D_smul hK hg y (cl24_levEquiv hg d)]
      simpa using hd
    have hzero := h _ hmem
    rw [← Equiv.apply_symm_apply (cl24_levEquiv hg) v,
      cl24_polar_levEquiv hg ((cl24_levEquiv hg).symm v) d] at hzero
    exact hzero
  · intro h d hd
    have hd' : (cl24_levEquiv hg).symm d ∈ cl24_D hK P y :=
      (cl24_mem_D_smul hK hg y d).1 hd
    have hzero := h _ hd'
    rw [← cl24_polar_levEquiv hg ((cl24_levEquiv hg).symm v) ((cl24_levEquiv hg).symm d)] at hzero
    simpa using hzero

theorem cl24_card_perpIn_smul (hg : Cl24Lev P g) (y : X) :
    Nat.card (cl24_perpIn P (cl24_D hK P (g • y))) =
      Nat.card (cl24_perpIn P (cl24_D hK P y)) :=
  Nat.card_congr (Equiv.subtypeEquiv (cl24_levEquiv hg).symm fun v =>
    cl24_mem_perpIn_smul hK hg y v)

end Action

end CFSG.OddStandard.SmallF3.HypA2Leaves
