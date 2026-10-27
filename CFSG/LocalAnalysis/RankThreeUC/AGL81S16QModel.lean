module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QAux

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem model_Q (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) {H : Type} [Group H] [Finite H]
    (hH2 : ∀ h : H, h * h = 1) (ρ : H →* Equiv.Perm (Fin 4 → F))
    (hadd : ∀ (h : H) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y)
    (hN : ∀ h : H, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ x)
    (hQ : ∀ K : Subgroup H, K.index < Nat.card F → ∀ x : Fin 4 → F, (∀ k ∈ K, ρ k x = x) →
      ∀ h : H, ρ h x = x) :
    ∀ h : H, ∃ g ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h x = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x := by
  have hinv : ∀ (h : H) (y : Fin 4 → F), ρ h (ρ h⁻¹ y) = y := fun h y => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  let α : H → ((Fin 4 → F) ≃+ (Fin 4 → F)) := fun h => { toEquiv := ρ h, map_add' := hadd h }
  have hα : ∀ h x, α h x = ρ h x := fun h x => rfl
  have hsymm : ∀ (h : H) (y : Fin 4 → F), (α h).symm y = ρ h⁻¹ y := fun h y => by
    rw [AddEquiv.symm_apply_eq, hα]
    exact (hinv h y).symm
  have hθ : ∀ h : H, ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), ρ h (c • x) = θ c • ρ h x :=
    fun h => exists_semilinear_statedSU hF (α h) (fun g hg => by
      obtain ⟨g', hg', hg'x⟩ := hN h g hg
      exact ⟨g', hg', fun x => by rw [hsymm, hsymm]; exact hg'x x⟩)
  choose θ hθ using hθ
  let H₀ : Subgroup H :=
    { carrier := {h | ∀ (c : F) (x : Fin 4 → F), ρ h (c • x) = c • ρ h x}
      mul_mem' := fun {a b} ha hb c x => by
        show ρ (a * b) (c • x) = c • ρ (a * b) x
        rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hb, ha]
      one_mem' := fun c x => by
        show ρ 1 (c • x) = c • ρ 1 x
        rw [map_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
      inv_mem' := fun {a} ha c x => by
        show ρ a⁻¹ (c • x) = c • ρ a⁻¹ x
        apply (ρ a).injective
        rw [hinv a, ha c (ρ a⁻¹ x), hinv a] }
  have hindex : H₀.index < Nat.card F := by
    classical
    haveI : Finite (F ≃+* F) := Finite.of_injective (fun θ : F ≃+* F => (θ : F → F))
      DFunLike.coe_injective
    let e : H → (F ≃+* F) := fun h => RingEquiv.ofBijective (θ h)
      ⟨(θ h).injective, Finite.injective_iff_surjective.mp (θ h).injective⟩
    have he : ∀ h k : H, e h = e k → h⁻¹ * k ∈ H₀ := by
      intro h k hk c x
      have hθeq : θ h = θ k := by
        ext c
        exact congrArg (fun r : F ≃+* F => r c) hk
      show ρ (h⁻¹ * k) (c • x) = c • ρ (h⁻¹ * k) x
      rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      apply (ρ h).injective
      rw [hinv h (ρ k (c • x)), hθ h c (ρ h⁻¹ (ρ k x)), hinv h (ρ k x), hθ k c x, hθeq]
    have hinj : Function.Injective (fun q : H ⧸ H₀ => e q.out) := by
      intro q₁ q₂ hq
      have h1 := he _ _ hq
      have h2 : ((q₁.out : H) : H ⧸ H₀) = ((q₂.out : H) : H ⧸ H₀) := QuotientGroup.eq.mpr h1
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
    calc H₀.index = Nat.card (H ⧸ H₀) := rfl
      _ ≤ Nat.card (F ≃+* F) := Nat.card_le_card_of_injective _ hinj
      _ < Nat.card F := card_ringEquiv_lt F
  have hH₀2 : IsPGroup 2 ↥H₀ := fun a => ⟨1, by simpa [pow_two] using Subtype.ext (hH2 (a : H))⟩
  have hWeven : Even (Nat.card (Fin 4 → F)) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩,
      by norm_num⟩
  obtain ⟨w, hw0, hwfix⟩ := exists_ne_zero_fixed hH₀2 hWeven (ρ.comp H₀.subtype)
    (fun a => (α (a : H)).map_zero)
  have hfixall : ∀ (h : H) (c : F), ρ h (c • w) = c • w := by
    intro h c
    refine hQ H₀ hindex (c • w) (fun k hk => ?_) h
    have hkw : ρ k w = w := hwfix ⟨k, hk⟩
    rw [hk c w, hkw]
  have hlin : ∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = c • ρ h x := by
    intro h c x
    have hw1 : ρ h w = w := by simpa using hfixall h 1
    have h1 : θ h c = c := by
      have h2 := hfixall h c
      rw [hθ h c w, hw1] at h2
      exact smul_left_injective F hw0 h2
    rw [hθ h c x, h1]
  intro h
  let f : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := ρ h
      map_add' := hadd h
      map_smul' := fun c x => hlin h c x }
  have hAx : ∀ x, (LinearMap.toMatrix' f) *ᵥ x = ρ h x := by
    intro x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hρ2 : ∀ x, ρ h (ρ h x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, hH2 h, map_one, Equiv.Perm.one_apply]
  have hAA : LinearMap.toMatrix' f * LinearMap.toMatrix' f = 1 := by
    ext i j
    have := congrFun (show (LinearMap.toMatrix' f * LinearMap.toMatrix' f) *ᵥ
        (Pi.single j 1 : Fin 4 → F) = Pi.single j 1 by
      rw [← mulVec_mulVec, hAx, hAx, hρ2]) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  have hsy : ρ h⁻¹ = ρ h := by rw [inv_eq_of_mul_eq_one_right (hH2 h)]
  obtain ⟨g, hgS, hg⟩ := exists_mem_statedSU_of_normalizes hF (LinearMap.toMatrix' f) hAA
    (fun g hg => by
      obtain ⟨g', hg', hg'x⟩ := hN h g hg
      refine ⟨g', hg', fun x => ?_⟩
      rw [hAx, hAx, ← hsy]
      exact hg'x x)
  exact ⟨g, hgS, fun x => by rw [hg, hAx]⟩

end CFSG.LocalAnalysis.RankThreeUC
