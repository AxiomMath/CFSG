module

public import CFSG.CGT.Timmesfeld75.L2AutInvol
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open scoped MatrixGroups

theorem exists_frobenius_normal_form {K : Type*} [Group K] {F : Type} [Field F] [Finite F]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (ψ₀ : K ≃* SL(2, F)) (α : MulAut K)
    (hαα : α * α = 1) (hαout : α ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ e : ℕ, f = 2 * e ∧ ∃ ψ : K ≃* SL(2, F), ∀ x : K,
      ((ψ (α x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (ψ x : Matrix (Fin 2) (Fin 2) F).map (fun c => c ^ 2 ^ e) := by
  have : CharP F 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hαα' : ∀ x, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, hαα, MulAut.one_apply]
  obtain ⟨τ, hτ⟩ : ∃ τ : SL(2, F) ≃* SL(2, F), ∀ y, τ y = ψ₀ (α (ψ₀.symm y)) :=
    ⟨ψ₀.symm.trans (α.trans ψ₀), fun _ => rfl⟩
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    rw [hτ, hτ, ψ₀.symm_apply_apply, hαα', ψ₀.apply_symm_apply]
  rcases CFSG.CGT.Timmesfeld75.autInvol_inner_or_field τ hττ with ⟨g, -, hg⟩ | ⟨k, σ, hσ, hk⟩
  ·
    refine absurd ⟨ψ₀.symm g, MulEquiv.ext fun x => ψ₀.injective ?_⟩ hαout
    have h1 := hg (ψ₀ x)
    rw [hτ, ψ₀.symm_apply_apply] at h1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ψ₀.apply_symm_apply, h1]
  · obtain ⟨ψ, hψ⟩ : ∃ ψ : K ≃* SL(2, F), ∀ x, ψ x = k * ψ₀ x * k⁻¹ :=
      ⟨ψ₀.trans (MulAut.conj k), fun _ => rfl⟩
    have hψα : ∀ x, ψ (α x) = Matrix.SpecialLinearGroup.map (σ : F →+* F) (ψ x) := fun x => by
      have h1 := hk (ψ₀ x)
      rw [hτ, ψ₀.symm_apply_apply] at h1
      rw [hψ, hψ, h1]
    have hσσ : ∀ s, σ (σ s) = s := fun s => by
      obtain ⟨x, hx⟩ := ψ.surjective (CFSG.CGT.Timmesfeld75.utriElt s)
      have h1 := hψα (α x)
      rw [hαα', hψα x, hx] at h1
      have h2 := congrArg (fun y : SL(2, F) => y 0 1) h1
      simpa [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.CGT.Timmesfeld75.utriElt_apply_01]
        using h2.symm
    obtain ⟨⟨r, hr⟩, hpow⟩ := ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf hF
      (σ := σ) hσ (RingEquiv.ext hσσ)
    refine ⟨f / 2, by omega, ψ, fun x => ?_⟩
    rw [hψα x]
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, hpow]

theorem exists_sl2_map_subtype_eq {F : Type} [Field F] (F₀ : Subfield F) (g : SL(2, F))
    (hg : ∀ i j, g i j ∈ F₀) :
    ∃ g₀ : SL(2, F₀), Matrix.SpecialLinearGroup.map F₀.subtype g₀ = g := by
  set M₀ : Matrix (Fin 2) (Fin 2) F₀ := Matrix.of fun i j => ⟨g i j, hg i j⟩
  have hM : F₀.subtype.mapMatrix M₀ = g := by
    ext i j
    rfl
  have hdet : M₀.det = 1 := Subtype.ext (by
    have h := RingHom.map_det F₀.subtype M₀
    rw [hM, g.2] at h
    exact h)
  exact ⟨⟨M₀, hdet⟩, Subtype.ext hM⟩

theorem natCard_subfield_le_of_pow_two_pow_eq {F : Type} [Field F] [Finite F] {e : ℕ}
    (he : 1 ≤ e) (F₀ : Subfield F) (hF₀ : ∀ c ∈ F₀, c ^ 2 ^ e = c) : Nat.card F₀ ≤ 2 ^ e := by
  classical
  have := Fintype.ofFinite F
  set S := Finset.univ.filter fun c : F => c ^ 2 ^ e = c with hSdef
  have hS : S.val ⊆ (Polynomial.X ^ 2 ^ e - Polynomial.X : Polynomial F).roots := by
    intro c hc
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_pow_sub_X_ne_zero F (by omega) one_lt_two)]
    have hc' : c ^ 2 ^ e = c := by simpa [hSdef] using hc
    simp [hc']
  have h := Polynomial.card_le_degree_of_subset_roots hS
  rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq F (by omega) one_lt_two] at h
  refine le_trans ?_ h
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective (fun c => ⟨c, by simpa [hSdef] using hF₀ c c.2⟩)
    fun a b hab => Subtype.ext (congrArg (fun x : S => (x : F)) hab)

theorem card_le_of_frobenius_fixed {F : Type} [Field F] [Finite F] {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ (2 * e)) {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ e)
    (X : Subgroup SL(2, F))
    (hX : ∀ g ∈ X, ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ e =
      (g : Matrix (Fin 2) (Fin 2) F) i j) :
    Nat.card X ≤ Nat.card SL(2, k) := by
  have : CharP F 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  set F₀ : Subfield F := (iterateFrobenius F 2 e).eqLocusField (RingHom.id F)
  have hmem : ∀ c : F, c ∈ F₀ ↔ c ^ 2 ^ e = c := fun _ => Iff.rfl
  have hcard₀ : Nat.card F₀ ≤ 2 ^ e :=
    natCard_subfield_le_of_pow_two_pow_eq he F₀ fun c hc => (hmem c).1 hc
  have hlift : ∀ g : X, ∃ g₀ : SL(2, F₀), Matrix.SpecialLinearGroup.map F₀.subtype g₀ = g :=
    fun g => exists_sl2_map_subtype_eq F₀ g fun i j => (hmem _).2 (hX g g.2 i j)
  choose φ hφ using hlift
  have hinj : Function.Injective φ := fun g h hgh => Subtype.ext (by rw [← hφ g, ← hφ h, hgh])
  calc Nat.card X ≤ Nat.card SL(2, F₀) := Nat.card_le_card_of_injective φ hinj
    _ = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := CFSG.CGT.Timmesfeld75.card_sl2
    _ ≤ 2 ^ e * ((2 ^ e) ^ 2 - 1) :=
      Nat.mul_le_mul hcard₀ (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcard₀ 2) 1)
    _ = Nat.card SL(2, k) := by rw [CFSG.CGT.Timmesfeld75.card_sl2, hk]

theorem isEmpty_mulEquiv_sl2_prod {k k₂ : Type} [Field k] [Finite k] [Field k₂] [Finite k₂]
    {m : ℕ} (hm : 2 ≤ m) (hk₂ : Nat.card k₂ = 2 ^ m) :
    IsEmpty (SL(2, k₂) ≃* SL(2, k) × SL(2, k)) := by
  refine ⟨fun φ => ?_⟩
  have : CharP k₂ 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hk₂
  have h4 : ∃ s : Finset k₂, s.card = 4 := by
    have := Fintype.ofFinite k₂
    have hle : 4 ≤ (Finset.univ : Finset k₂).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk₂]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  have : IsSimpleGroup SL(2, k₂) := CFSG.ComponentClassification.GMS78.u3_isSimpleGroup_SL2 k₂ h4
  have : IsSimpleGroup (SL(2, k) × SL(2, k)) := φ.symm.isSimpleGroup
  set u : SL(2, k) := CFSG.CGT.Timmesfeld75.utriElt 1 with hudef
  have hu : u ≠ 1 := fun h => by
    have h01 := congrArg (fun y : SL(2, k) => y 0 1) h
    simp only [hudef, CFSG.CGT.Timmesfeld75.utriElt_apply_01,
      CFSG.CGT.Timmesfeld75.one_apply_01] at h01
    exact one_ne_zero h01
  have hN := IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((⊤ : Subgroup SL(2, k)).prod (⊥ : Subgroup SL(2, k)))
  rcases hN with h | h
  · have hmem : ((u, 1) : SL(2, k) × SL(2, k)) ∈ (⊤ : Subgroup SL(2, k)).prod ⊥ :=
      Subgroup.mem_prod.2 ⟨Subgroup.mem_top u, Subgroup.one_mem _⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hu (congrArg Prod.fst hmem)
  · have hmem : ((1, u) : SL(2, k) × SL(2, k)) ∈ (⊤ : Subgroup SL(2, k)).prod ⊥ :=
      h ▸ Subgroup.mem_top _
    exact hu (Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hmem).2)

end CFSG.LocalAnalysis.EvenBN.GMS
