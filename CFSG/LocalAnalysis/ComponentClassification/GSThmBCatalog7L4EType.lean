module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Main
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ESplit

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4M

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector

theorem eq_card_of_psl2 {X : Type} [Group X] {N : Subgroup X} [N.Normal] (hN : N = ⊥)
    {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXm : Blueprint.LieModel (X ⧸ N) .PSL 2 p g)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀))
    (eX : X ≃* GorensteinWalter.PSL2 F₀) : p ^ g = Nat.card F₀ := by
  obtain ⟨-, F', _, _, hF', ⟨eF'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hXm
  have hQodd : Odd (p ^ g) := (hp.odd_of_ne_two hp2).pow
  have h1 : Nat.card (X ⧸ N) = p ^ g * ((p ^ g) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (eF'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F').symm).toEquiv,
      Catalog7Std.card_psl2_of_odd hQodd hF']
  have h2 : Nat.card (X ⧸ N) = Nat.card X := by
    subst hN
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have h3 : Nat.card X = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eX.toEquiv, Catalog7Std.card_psl2_of_odd hF₀ rfl]
  have h4 : p ^ g * ((p ^ g) ^ 2 - 1) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    have ha := Catalog7Std.two_dvd_mul_sq_sub (p ^ g)
    have hb := Catalog7Std.two_dvd_mul_sq_sub (Nat.card F₀)
    omega
  exact Catalog7Std.eq_of_mul_sq_sub_eq (Nat.one_le_pow _ _ hp.pos) Nat.card_pos h4

variable {H : Type} [Group H] [Finite H]

theorem psl4_component_type (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) (φ : ↥(generalizedFitting H) ≃* projectiveSL 4 k)
    {ρ : H →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hρW : ∀ w : ↥(generalizedFitting H), ρ w = MulAut.conj (φ w))
    {x : H} (hx : orderOf x = 2) {X : Subgroup H} (hXF : X ≤ generalizedFitting H)
    (hXx : X ≤ centralizer ({x} : Set H))
    (hX : IsPComponent 2 (X.subgroupOf (centralizer ({x} : Set H))))
    {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ g)
    (hXm : Blueprint.LieModel (X ⧸ pPrimeCore 2 X) .PSL 2 p g) :
    pPrimeCore 2 X = ⊥ ∧
      ((p ^ g = Nat.card k ^ 2 ∧
          (SelectorRowS 4 k ρ (generalizedFitting H) x X ∨
            ∃ B : GL (Fin 4) k, ρ x = conjAut 4 k B * dualAut 4 k ∧
              (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B ∧
              ¬ ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
                ∀ v ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ v = 0)) ∨
        (p ^ g = Nat.card k ∧ 5 ≤ Nat.card k ∧ ∃ A : GL (Fin 4) k,
          ρ x = conjAut 4 k A * dualAut 4 k ∧ (A : Matrix (Fin 4) (Fin 4) k)ᵀ = A ∧
          ∃ ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k,
            (∀ v, v ⬝ᵥ (((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (ψ v).det) ∧
            (X.map ρ = (splitLeftHom ψ).range.map (conjAut 4 k) ∨
              X.map ρ = (splitRightHom ψ).range.map (conjAut 4 k)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hq3 : 3 ≤ Nat.card k := by
    rw [hk]
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    exact h3.trans (Nat.le_self_pow (by omega) ℓ)
  have : Finite (projectiveSL 4 k) := Finite.of_equiv _ φ.toEquiv
  set C := centralizer ({x} : Set H) with hCdef
  obtain ⟨-, F', _, _, hF', ⟨eF'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hXm
  have hQodd : Odd (p ^ g) := (hp.odd_of_ne_two hp2).pow
  let eB : X ⧸ pPrimeCore 2 X ≃* GorensteinWalter.PSL2 F' :=
    eF'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F').symm
  have hQ3 : 3 < Nat.card F' := by rw [hF']; omega
  have hcardB : Nat.card (X ⧸ pPrimeCore 2 X) = p ^ g * ((p ^ g) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eB.toEquiv, Catalog7Std.card_psl2_of_odd hQodd hF']
  have hXq : CFSG.IsQuasisimple X :=
    Catalog7Std.isQuasisimple_of_model hC hx hXx hXF hX φ fun α hα2 hα1 L' hL' =>
      CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components 4 k hk2
        (by norm_num) α hα1 hα2 2 Nat.prime_two L' hL'
  have hcore : pPrimeCore 2 X = center X := by
    apply le_antisymm
    · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hXq (pPrimeCore 2 X)
        with h | h
      · exact h
      · exfalso
        have h1 : Nat.card (X ⧸ pPrimeCore 2 X) = 1 := by
          have := Subgroup.index_top (G := X)
          rw [← h] at this
          exact this
        rw [hcardB] at h1
        have h25 : 25 ≤ (p ^ g) ^ 2 := by nlinarith
        have : 5 * 24 ≤ p ^ g * ((p ^ g) ^ 2 - 1) :=
          Nat.mul_le_mul h5 (by omega)
        omega
    · intro z hz
      have hz' : (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hz) y']
      exact (QuotientGroup.eq_one_iff z).mp
        (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 hQ3 eB hz')
  have hZodd : Odd (Nat.card (center X)) := by
    rw [← hcore]
    have h := (pPrimeCore_coprime_card (p := 2) (G := X))
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  let eZ : X ⧸ center X ≃* X ⧸ pPrimeCore 2 X := QuotientGroup.quotientMulEquivOfEq hcore.symm
  have hXmZ : Blueprint.LieModel (X ⧸ center X) .PSL 2 p g :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hXm
  have hsrc : StatedClassicalModel (X ⧸ center X) .PSL 2 p g ∨
      Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (X ⧸ center X) .PSL 3 2 2 :=
    Or.inl (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hXmZ)
  have hXC : CFSG.Assembly.IsComponentOf X C := by
    have hsub : (X.subgroupOf C).IsSubnormal := hX.choose_spec.2.1
    have hq : CFSG.IsQuasisimple (X.subgroupOf C) :=
      (isQuasisimple_congr (subgroupOfEquivOfLe hXx)).mpr hXq
    exact (isComponentOf_iff_isComponent_subgroupOf hXx).mpr ⟨hq, hsub⟩
  have hcore1 : ∀ {F₀ : Type} [Field F₀] [Finite F₀], 3 < Nat.card F₀ →
      Nonempty (X ≃* GorensteinWalter.PSL2 F₀) → pPrimeCore 2 X = ⊥ := by
    intro F₀ _ _ h3 ⟨eX⟩
    rw [hcore, eq_bot_iff]
    intro z hz
    exact (mem_bot).mpr (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 h3 eX hz)
  have hcard : ∀ {F₀ : Type} [Field F₀] [Finite F₀], Odd (Nat.card F₀) → 3 < Nat.card F₀ →
      Nonempty (X ≃* GorensteinWalter.PSL2 F₀) → p ^ g = Nat.card F₀ := by
    intro F₀ _ _ hF₀ h3 ⟨eX⟩
    exact eq_card_of_psl2 (hcore1 h3 ⟨eX⟩) hp hp2 hXm hF₀ eX
  have hbig : ∀ {E : Type} [Field E] [Finite E], Nat.card E = Nat.card k ^ 2 →
      Nonempty (X ≃* projectiveSL 2 E) → pPrimeCore 2 X = ⊥ ∧ p ^ g = Nat.card k ^ 2 := by
    intro E _ _ hE ⟨eX⟩
    have hE3 : 3 < Nat.card E := by rw [hE]; nlinarith
    have hEodd : Odd (Nat.card E) := by rw [hE]; exact hodd.pow
    have hiso : Nonempty (X ≃* GorensteinWalter.PSL2 E) :=
      ⟨eX.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm⟩
    exact ⟨hcore1 hE3 hiso, (hcard hEodd hE3 hiso).trans hE⟩
  obtain ⟨-, hCA, hCW', hL₁⟩ := OddSelector.socle_images φ hinj hρW hXF hXC
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (by norm_num : 3 ≤ 4)
  obtain ⟨B, τ, ε, hε, hρx⟩ := hform (ρ x)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρx
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρx
      obtain ⟨μ, hμ, hsq, -⟩ := OddSelector.inner_case_reduction hx le_rfl hℓ hℓ2 he hk hinj
        hL₁ hρx hp2 hsrc (fun _ => Or.inr hZodd)
      obtain ⟨hrow, E, _, _, hE, hiso⟩ :=
        OddSelector.selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρx hμ hsq
      obtain ⟨h1, h2⟩ := hbig hE hiso
      exact ⟨h1, Or.inl ⟨h2, Or.inl hrow⟩⟩
    · exact (OddSelector.field_case_false hx (by norm_num) hℓ hℓ2 he hk hinj hL₁ hτ hρx hp2
        hsrc).elim
  · rw [pow_one] at hρx
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρx
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by
        rw [← hρx, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph (by norm_num) B hα2 with hB | hB
      · by_cases hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
            ∀ v ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ v = 0
        · obtain ⟨h5k, ψ, hψ, hfac⟩ :=
            OddSelector.Catalog7L4E.split_component_factor hℓ hℓ2 he hk hL₁ hρx hB hsplit
          obtain ⟨-, hiso⟩ :=
            OddSelector.Catalog7L4E.split_component_iso hℓ hℓ2 he hk hinj hL₁ hρx hB hsplit
          exact ⟨hcore1 (by omega) hiso,
            Or.inr ⟨hcard hodd (by omega) hiso, h5k, B, hρx, hB, ψ, hψ, hfac⟩⟩
        · obtain ⟨-, E, _, _, hE, hiso⟩ :=
            OddSelector.selectorRowO_of_nonsplit hodd hinj hCA hCW' hL₁ hρx hB hsplit
          obtain ⟨h1, h2⟩ := hbig hE hiso
          exact ⟨h1, Or.inl ⟨h2, Or.inr ⟨B, hρx, hB, hsplit⟩⟩⟩
      · exact (OddSelector.symplectic_case_false le_rfl hℓ hℓ2 he hk hinj hL₁ hρx hB hp2
          hsrc).elim
    · exact (OddSelector.graph_field_case_false hx le_rfl hℓ hℓ2 he hk hinj hL₁ hτ hρx hp2
        hsrc).elim

end Catalog7L4M

end CFSG.ComponentClassification.GSThmB
