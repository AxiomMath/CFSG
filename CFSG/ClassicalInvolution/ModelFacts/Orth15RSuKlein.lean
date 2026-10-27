module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuFix
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Std
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuSlayer

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer LayerData alphaOf_klein_of_three_layers
  outerAction outerEquiv outerAction_apply outerEquiv_apply eq_one_of_outerAction_eq_one)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem rigid_psu (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {H : Type}
    [Group H] (ψ : Su K p f 4 →* H) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (g : Su K p f 4) {m : Su K p f 4} (hmix : MixProp (suMat m))
    (c : ↥(inducedAutOn ψ.range)) (hodd : Odd (orderOf c))
    (hQ : ∀ q ∈ R0 K p f ⊔ R0' K p f,
      c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c)
    (hQm : c * innerHom ψ (g * m * g⁻¹) = innerHom ψ (g * m * g⁻¹) * c) : c = 1 := by
  have hperf : Group.IsPerfect (Su K p f 4) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hK)
      (by norm_num) (fun h => absurd h (by norm_num))
  set π : Su K p f 4 →* Su K p f 4 ⧸ Subgroup.center (Su K p f 4) :=
    QuotientGroup.mk' (Subgroup.center (Su K p f 4)) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = Subgroup.center (Su K p f 4) := QuotientGroup.ker_mk' _
  set φ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) :=
    outerAction ψ hker π hπ hπk c with hφ
  have hfix : ∀ r : Su K p f 4, c * innerHom ψ r = innerHom ψ r * c → φ (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hker π hπ hπk).injective
    apply Subtype.ext
    rw [hφ, outerAction_apply, outerEquiv_apply, hr]
    group
  set γ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := MulAut.conj (π g) with hγ
  have hγp : ∀ s : Su K p f 4, γ (π s) = π (g * s * g⁻¹) := fun s => by
    rw [hγ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := γ⁻¹ * φ * γ with hα
  have hαp : ∀ s : Su K p f 4, α (π s) = (γ⁻¹) (φ (γ (π s))) := fun s => rfl
  have hαfix : ∀ q : Su K p f 4,
      c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c → α (π q) = π q := by
    intro q hq
    rw [hαp, hγp, hfix _ hq, ← hγp]
    simp
  have hφn : φ ^ orderOf c = 1 := by
    rw [hφ, ← map_pow, pow_orderOf_eq_one, map_one]
  have hαn : α ^ orderOf c = 1 := by
    have := conj_pow (a := γ⁻¹) (b := φ) (i := orderOf c)
    rw [inv_inv] at this
    rw [hα, this, hφn]
    group
  have hα2 : α * α = 1 :=
    aut_sq_eq_one hK hp hq π hπ hπk.le α
      (fun A => hαfix _ (hQ _ (Subgroup.mem_sup_left ⟨A, rfl⟩)))
      (fun A => hαfix _ (hQ _ (Subgroup.mem_sup_right ⟨A, rfl⟩))) hmix (hαfix m hQm)
  have hα1 : α = 1 := by
    obtain ⟨m', hm'⟩ := hodd
    have : α ^ (2 * m' + 1) = α := by
      rw [pow_succ, pow_mul, pow_two, hα2, one_pow, one_mul]
    rw [← this, ← hm', hαn]
  have hφ1 : φ = 1 := by
    have : φ = γ * α * γ⁻¹ := by rw [hα]; group
    rw [this, hα1]
    group
  exact eq_one_of_outerAction_eq_one ψ hker π hπ hπk hφ1

theorem alphaOf_klein_psu (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {H : Type} [Group H] [Finite H] (ψ : Su K p f 4 →* H)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) (hz : ψ (zneg K p f) = 1)
    {Q : Subgroup (Su K p f 4)} (hQu : SLayer (u0 K p f) Q) (ht0Q : t0 K p f ∈ Q)
    {m : Su K p f 4} (hmQ : m ∈ Q) (hmix : MixProp (suMat m)) (g : Su K p f 4) :
    alphaOf (Subgroup.closure ({innerHom ψ (g * u0 K p f * g⁻¹),
      innerHom ψ (g * x0 K p f * g⁻¹)} : Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hperf : Group.IsPerfect (Su K p f 4) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hK)
      (by norm_num) (fun h => absurd h (by norm_num))
  obtain ⟨hcen, hnorm, -⟩ := innerHom_spec ψ hker
  have : (innerHom ψ).range.Normal := hnorm
  obtain ⟨g', hg'u, hg'x⟩ := exists_conj_t0 hK h2
  have hekernel : (innerHom ψ).ker ≤ Subgroup.center (Su K p f 4) := fun s hs => hcen s hs
  let τ : MulAut (Su K p f 4) := MulAut.conj g
  have hτ : ∀ s, τ s = g * s * g⁻¹ := fun s => rfl
  have hτz : τ (zneg K p f) = zneg K p f := by
    rw [hτ, Subgroup.mem_center_iff.mp zneg_mem_center g]
    group
  have hez : innerHom ψ (zneg K p f) = 1 := by
    have : (⟨ψ (zneg K p f), mem_normalizer_range ψ (zneg K p f)⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 := Subtype.ext hz
    rw [innerHom_apply, this, map_one]
  have ht0u : t0 K p f = x0 K p f * u0 K p f := rfl
  have hux : u0 K p f * x0 K p f = t0 K p f := x0_mul_u0.symm
  have hxt : x0 K p f * t0 K p f = u0 K p f := by rw [ht0u, ← mul_assoc, x0_mul_self, one_mul]
  have hg't : g' * t0 K p f * g'⁻¹ = u0 K p f := by
    calc g' * t0 K p f * g'⁻¹ = (g' * x0 K p f * g'⁻¹) * (g' * u0 K p f * g'⁻¹) := by
          rw [ht0u]
          group
      _ = u0 K p f := by rw [hg'x, hg'u, hxt]
  show alphaOf (Subgroup.closure ({innerHom ψ (τ (u0 K p f)), innerHom ψ (τ (x0 K p f))} :
      Set ↥(inducedAutOn ψ.range))) = ⊥
  have hb12 : innerHom ψ (τ (u0 K p f)) * innerHom ψ (τ (x0 K p f)) =
      innerHom ψ (τ (t0 K p f)) := by
    rw [← map_mul, ← map_mul, hux]
  have hb₁sq : innerHom ψ (τ (u0 K p f)) * innerHom ψ (τ (u0 K p f)) = 1 := by
    rw [← map_mul, ← map_mul, u0_mul_self, hτz, hez]
  have hb₂sq : innerHom ψ (τ (x0 K p f)) * innerHom ψ (τ (x0 K p f)) = 1 := by
    rw [← map_mul, ← map_mul, x0_mul_self, map_one, map_one]
  have hcomm : innerHom ψ (τ (u0 K p f)) * innerHom ψ (τ (x0 K p f)) =
      innerHom ψ (τ (x0 K p f)) * innerHom ψ (τ (u0 K p f)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, x0_mul_u0]
  have hne₁ : innerHom ψ (τ (u0 K p f)) ≠ 1 := fun h => by
    have := hcen _ h
    rw [hτ] at this
    exact u0_not_central hK (InnerL4.mem_center_of_conj_mem_center this)
  have hne₂ : innerHom ψ (τ (x0 K p f)) ≠ 1 := fun h => by
    have := hcen _ h
    rw [hτ] at this
    exact x0_not_central hK h2 (InnerL4.mem_center_of_conj_mem_center this)
  have hne₃ : innerHom ψ (τ (u0 K p f)) * innerHom ψ (τ (x0 K p f)) ≠ 1 := fun h => by
    rw [hb12] at h
    have := hcen _ h
    rw [hτ] at this
    exact t0_not_central hK (InnerL4.mem_center_of_conj_mem_center this)
  have hL₁ := (slayer_x0 hK h2 hq).map τ
  have hL₂ := hQu.map τ
  have hL₃ := (hQu.map (MulAut.conj g')).map τ
  rw [show (MulAut.conj g') (u0 K p f) = t0 K p f from hg'u] at hL₃
  set B : Subgroup ↥(inducedAutOn ψ.range) := Subgroup.closure
    ({innerHom ψ (τ (u0 K p f)), innerHom ψ (τ (x0 K p f))} : Set ↥(inducedAutOn ψ.range))
    with hB
  have hu0Q' : u0 K p f ∈ Q.map (MulAut.conj g').toMonoidHom := ⟨t0 K p f, ht0Q, hg't⟩
  have hx0eq : innerHom ψ (τ (x0 K p f)) =
      innerHom ψ (τ (t0 K p f)) * (innerHom ψ (τ (u0 K p f)))⁻¹ := by
    rw [ht0u, map_mul, map_mul, mul_inv_cancel_right]
  have hcov₁ : B ≤ Subgroup.zpowers (innerHom ψ (τ (x0 K p f))) ⊔
      ((R0 K p f ⊔ R0' K p f).map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_right ⟨τ (u0 K p f), ⟨u0 K p f, u0_mem, rfl⟩, rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hcov₂ : B ≤ Subgroup.zpowers (innerHom ψ (τ (u0 K p f))) ⊔
      (Q.map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    have hP : innerHom ψ (τ (t0 K p f)) ∈ (Q.map τ.toMonoidHom).map (innerHom ψ) :=
      ⟨τ (t0 K p f), ⟨t0 K p f, ht0Q, rfl⟩, rfl⟩
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [hx0eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hP)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hcov₃ : B ≤ Subgroup.zpowers (innerHom ψ (τ (t0 K p f))) ⊔
      ((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    have hP : innerHom ψ (τ (u0 K p f)) ∈
        ((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ) :=
      ⟨τ (u0 K p f), ⟨u0 K p f, hu0Q', rfl⟩, rfl⟩
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_right hP
    · rw [hx0eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hP))
  have d₁ := hL₁.layerData (innerHom ψ) hekernel B hcov₁
  have d₂ := hL₂.layerData (innerHom ψ) hekernel B hcov₂
  have d₃ := hL₃.layerData (innerHom ψ) hekernel B hcov₃
  have d₃' : LayerData (innerHom ψ).range B
      (innerHom ψ (τ (u0 K p f)) * innerHom ψ (τ (x0 K p f)))
      (((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ)) := by
    rw [hb12]
    exact d₃
  refine alphaOf_klein_of_three_layers (innerHom ψ).range ⟨_, rfl⟩ ⟨_, rfl⟩ hb₁sq hb₂sq hcomm
    hne₁ hne₂ hne₃ d₂ d₁ d₃' ?_
  intro c hodd hc₁ hc₂ _
  refine rigid_psu hK hp hq ψ hker g hmix c hodd ?_ ?_
  · intro q hq'
    exact hc₂ _ ⟨τ q, ⟨q, hq', rfl⟩, rfl⟩
  · exact hc₁ _ ⟨τ m, ⟨m, hmQ, rfl⟩, rfl⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
