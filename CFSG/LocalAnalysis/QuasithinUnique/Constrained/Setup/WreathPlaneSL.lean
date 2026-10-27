module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatural
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellGamma

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Campbell

abbrev V4' : Type := Multiplicative (Fin 2 → ZMod 2)

instance isKleinFour_V4' : IsKleinFour V4' := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    decide +kernel
  · rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    revert g
    decide +kernel

@[expose] def natActHom : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* MulAut V4' where
  toFun := natAct
  map_one' := by
    ext x
    simp [natAct]
  map_mul' g g' := by
    ext x
    simp [natAct, mul_smul]

theorem natActHom_injective : Function.Injective natActHom := by
  intro g g' h
  apply slPerm_injective (k := ZMod 2)
  refine Equiv.ext fun w => ?_
  have := congrArg (fun a : MulAut V4' => Multiplicative.toAdd (a (Multiplicative.ofAdd w))) h
  simpa [natActHom, natAct, slPerm_apply] using this

theorem natActHom_bijective : Function.Bijective natActHom := by
  refine ⟨natActHom_injective, ?_⟩
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h2 : Nat.card (MulAut V4') = 6 := card_mulAut
  exact (Function.Injective.bijective_of_nat_card_le natActHom_injective (by rw [h1, h2])).2

@[expose] noncomputable def slEquivAut : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* MulAut V4' :=
  MulEquiv.ofBijective natActHom natActHom_bijective

theorem slEquivAut_apply (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (w : Fin 2 → ZMod 2) :
    Multiplicative.toAdd (slEquivAut g (Multiplicative.ofAdd w)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec w := by
  show Multiplicative.toAdd (natAct g (Multiplicative.ofAdd w)) = _
  simp only [natAct, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd]
  rw [Matrix.SpecialLinearGroup.smul_def]
  exact Matrix.smul_eq_mulVec _ _

section Rep

variable {G : Type*} [Group G]

theorem exists_natural_rep {P U : Subgroup G} [IsKleinFour ↥U]
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    ∃ (ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ψ : ↥U ≃* V4'),
      (∀ (p : ↥P) (u u' : ↥U), (u' : G) = (p : G) * (u : G) * (p : G)⁻¹ →
        Multiplicative.toAdd (ψ u') =
          (ρ p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ u))) ∧
      (∀ p : ↥P, ρ p = 1 ↔ ∀ u : ↥U, (p : G) * u = u * p) ∧
      (Function.Surjective ρ ↔
        ∀ σ : MulAut ↥U, ∃ p : ↥P, ∀ u : ↥U, ((σ u : ↥U) : G) = p * u * p⁻¹) := by
  classical
  let act : ↥P →* MulAut ↥U := (U.normalizerMonoidHom).comp (Subgroup.inclusion hPU)
  have hact : ∀ (p : ↥P) (u : ↥U), ((act p u : ↥U) : G) = (p : G) * u * (p : G)⁻¹ := fun p u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hPU p) u
  obtain ⟨e⟩ : Nonempty (↥U ≃* V4') := IsKleinFour.nonempty_mulEquiv
  let ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    slEquivAut.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp act)
  have hρ : ∀ p, slEquivAut (ρ p) = MulAut.congr e (act p) := fun p =>
    slEquivAut.apply_symm_apply _
  refine ⟨ρ, e, ?_, ?_, ?_⟩
  · intro p u u' hu'
    have h1 : u' = act p u := Subtype.ext (by rw [hact, hu'])
    have h2 : slEquivAut (ρ p) (e u) = e u' := by
      rw [hρ, h1]
      simp [MulAut.congr_apply]
    have h3 := slEquivAut_apply (ρ p) (Multiplicative.toAdd (e u))
    rw [ofAdd_toAdd, h2] at h3
    exact h3
  · intro p
    constructor
    · intro hp u
      have h1 : act p = 1 := by
        have := hρ p
        rw [hp, map_one] at this
        exact (MulAut.congr e).injective (this.symm.trans (map_one _).symm)
      have h2 := congrArg (fun a : MulAut ↥U => ((a u : ↥U) : G)) h1
      simp only [hact, MulAut.one_apply] at h2
      calc (p : G) * u = ((p : G) * u * (p : G)⁻¹) * p := by group
        _ = u * p := by rw [h2]
    · intro hp
      have h1 : act p = 1 := by
        refine MulEquiv.ext fun u => Subtype.ext ?_
        rw [hact]
        show (p : G) * u * (p : G)⁻¹ = u
        calc (p : G) * u * (p : G)⁻¹ = (u * p) * (p : G)⁻¹ := by rw [hp u]
          _ = u := by group
      have h2 : slEquivAut (ρ p) = 1 := by
        rw [hρ, h1, map_one]
      exact slEquivAut.injective (h2.trans (map_one _).symm)
  · constructor
    · intro hs σ
      obtain ⟨g, hg⟩ := hs (slEquivAut.symm (MulAut.congr e σ))
      refine ⟨g, fun u => ?_⟩
      have h1 : act g = σ := by
        have := hρ g
        rw [hg, MulEquiv.apply_symm_apply] at this
        exact (MulAut.congr e).injective this.symm
      rw [← h1, hact]
      rfl
    · intro hs A
      obtain ⟨p, hp⟩ := hs ((MulAut.congr e).symm (slEquivAut A))
      refine ⟨p, ?_⟩
      have h1 : act p = (MulAut.congr e).symm (slEquivAut A) :=
        MulEquiv.ext fun u => Subtype.ext (by rw [hact, hp]; rfl)
      have h2 : slEquivAut (ρ p) = slEquivAut A := by
        rw [hρ, h1, MulEquiv.apply_symm_apply]
      exact slEquivAut.injective h2

end Rep

theorem eq_bot_of_normal_isPGroup {U : Type*} [Group U] [IsKleinFour U]
    (N : Subgroup (MulAut U)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  by_contra hne
  have hcard := card_le_two_of_isPGroup hN
  have hone : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
  have h2 : Nat.card ↥N = 2 := by omega
  obtain ⟨t0, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have huniq := (Nat.card_eq_two_iff' (1 : ↥N)).mp h2
  have ht2 : t0 ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥N) (x := t0)
    rwa [h2] at this
  obtain ⟨T, hTN⟩ := t0
  have hT2 : T * T = 1 := by
    have := congrArg Subtype.val ht2
    simpa [pow_two] using this
  have hT1 : T ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcard' : 1 < Nat.card (cubeSubgroup U) := by rw [card_cubeSubgroup]; norm_num
  have hfin : Finite ↥(cubeSubgroup U) := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥(cubeSubgroup U) := Finite.one_lt_card_iff_nontrivial.mp hcard'
  obtain ⟨c0, hc0⟩ := exists_ne (1 : ↥(cubeSubgroup U))
  obtain ⟨c, hccube⟩ := c0
  have hc3 : c ^ 3 = 1 := mem_cubeSubgroup.mp hccube
  have hc1 : c ≠ 1 := fun h => hc0 (Subtype.ext h)
  have hconj : c * T * c⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ hTN _
  have hne1 : (⟨c * T * c⁻¹, hconj⟩ : ↥N) ≠ 1 := by
    intro h
    apply hT1
    have h' : c * T * c⁻¹ = 1 := congrArg Subtype.val h
    calc T = c⁻¹ * (c * T * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group
  obtain ⟨x0, -, hx0⟩ := huniq
  have e1 : (⟨c * T * c⁻¹, hconj⟩ : ↥N) = ⟨T, hTN⟩ := (hx0 _ hne1).trans (hx0 _ ht1).symm
  have hct : c * T * c⁻¹ = T := congrArg Subtype.val e1
  have hTc : T * c = c * T := by
    calc T * c = (c * T * c⁻¹) * c := by rw [hct]
      _ = c * T := by group
  have hcomm : c⁻¹ * T = T * c⁻¹ := by
    calc c⁻¹ * T = c⁻¹ * (T * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * T) * c⁻¹ := by rw [hTc]
      _ = T * c⁻¹ := by group
  have hinv := invol_inv_mul hc3 hT1 hT2
  have hcc : c = c⁻¹ := by
    calc c = T * c⁻¹ * T := hinv.symm
      _ = c⁻¹ * T * T := by rw [hcomm]
      _ = c⁻¹ := by rw [mul_assoc, hT2, mul_one]
  apply hc1
  have hc2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hcc]
      _ = 1 := mul_inv_cancel c
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hc2]; group

end CFSG.QuasithinUnique.Setup.Wreath
