module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterFPF
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterFlag
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14NonembedScalar
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOne

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {K : Type} [Field K] {n : ℕ}

section NatRep

variable {Y : Type} [Group Y]

@[expose] noncomputable def opNatEquiv (ψ : Y →* StatedSp n K) :
    Y →* ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)).toMonoidHom.comp
    ((natRep (StatedSp n K)).comp ψ).toHomUnits

theorem opNatEquiv_injective {ψ : Y →* StatedSp n K} (hψ : Function.Injective ψ) :
    Function.Injective (opNatEquiv ψ) := by
  intro a b h
  apply hψ
  apply natRep_injective (StatedSp n K)
  exact LinearMap.ext fun v =>
    congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) => e v) h

theorem spForm_β_eq_pairedSympForm (u v : Fin n ⊕ Fin n → K) :
    (spForm n K).β u v =
      CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n u v := by
  rw [spForm_β, dotProduct_spJ_mulVec,
    CFSG.LocalAnalysis.ComponentInitial.pairedSympForm_apply]

end NatRep

section Restrict

variable {Y : Type} [Group Y] {V : Type} [AddCommGroup V] [Module K V]

@[expose] noncomputable def opRestrict (ρ : Y →* (V ≃ₗ[K] V)) (X : Subgroup Y)
    (U : Submodule K V) (hU : ∀ w ∈ X, ∀ u ∈ U, ρ w u ∈ U) : X →* (U ≃ₗ[K] U) where
  toFun w :=
    { toFun := fun u => ⟨ρ w u, hU w w.2 u u.2⟩
      invFun := fun u => ⟨ρ (w : Y)⁻¹ u, hU _ (X.inv_mem w.2) u u.2⟩
      map_add' := fun u v => Subtype.ext (by simp)
      map_smul' := fun c u => Subtype.ext (by simp)
      left_inv := fun u => Subtype.ext (by
        change ρ (w : Y)⁻¹ (ρ w u) = u
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun u => Subtype.ext (by
        change ρ w (ρ (w : Y)⁻¹ u) = u
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl) }
  map_one' := LinearEquiv.ext fun u => Subtype.ext (by
    change ρ ((1 : X) : Y) u = u
    rw [OneMemClass.coe_one, map_one]
    rfl)
  map_mul' w w' := LinearEquiv.ext fun u => Subtype.ext (by
    change ρ ((w * w' : X) : Y) u = ρ w (ρ w' u)
    rw [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply])

theorem opRestrict_apply (ρ : Y →* (V ≃ₗ[K] V)) (X : Subgroup Y) (U : Submodule K V)
    (hU : ∀ w ∈ X, ∀ u ∈ U, ρ w u ∈ U) (w : X) (u : U) :
    ((opRestrict ρ X U hU w u : U) : V) = ρ w u := rfl

end Restrict

section Core

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (pairedSympForm_isAlt
  pairedSympForm_nondegenerate finrank_standard)

theorem false_of_nonembedding_data [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (ψ : Y →* StatedSp n K) (hψ : Function.Injective ψ) (Q₁ X' : Subgroup Y)
    (hQ : IsPGroup 2 Q₁) (hQne : Q₁ ≠ ⊥) (hXN : X' ≤ normalizer (Q₁ : Set Y))
    [IsSimpleGroup X'] (hZ : center X' = ⊥) {x y : Y} (hx : x ∈ X') (hy : y ∈ X')
    (hxy : x * y = y * x) (hy1 : y ≠ 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hxℓ : x ^ ℓ = 1) (hx1 : x ≠ 1)
    (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j < n → ¬ ℓ ∣ Nat.card K ^ (2 * j) - 1)
    (hord' : ∀ i, 1 ≤ i → i < n → ¬ ℓ ∣ Nat.card K ^ i - 1)
    {m : ℕ} (hym : y ^ m = 1) (hmq : m ∣ Nat.card K - 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : Y →* Module.End K (Fin n ⊕ Fin n → K) := (natRep (StatedSp n K)).comp ψ with hρdef
  have hρ : IsIsometric (spForm n K) ρ := fun h u v => isIsometric_natRep_statedSp n K (ψ h) u v
  have hinj : Function.Injective ρ := (natRep_injective _).comp hψ
  set U := isoSeq (spForm n K) ρ Q₁ 1 with hUdef
  have hU : U ≠ ⊥ := isoSeq_one_ne_bot (spForm n K) ρ 2 hρ hinj Q₁ hQ hQne
  have hUX : ∀ w ∈ X', ∀ u ∈ U, opNatEquiv ψ w u ∈ U := fun w hw u hu =>
    apply_mem_isoSeq (spForm n K) ρ hρ Q₁ 1 (hXN hw) hu
  have hUiso := isoSeq_isTotallyIsotropic (spForm n K) ρ Q₁ 1
  have hdimV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_standard
  have hdimU : 2 * finrank K U ≤ 2 * n := by
    have := two_mul_finrank_le_of_isTotallyIsotropic (spForm n K) hUiso
    rwa [hdimV] at this
  have heB : ∀ w a b, CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n
      (opNatEquiv ψ w a) (opNatEquiv ψ w b) =
        CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n a b := fun w a b => by
    rw [← spForm_β_eq_pairedSympForm, ← spForm_β_eq_pairedSympForm]
    exact hρ w a b
  have hex : opNatEquiv ψ x ^ ℓ = 1 := by rw [← map_pow, hxℓ, map_one]
  have hex1 : opNatEquiv ψ x ≠ 1 := fun h =>
    hx1 (opNatEquiv_injective hψ (by rw [h, map_one]))
  have hbig : ∀ W : Submodule K (Fin n ⊕ Fin n → K), W ≠ ⊥ →
      (∀ w ∈ W, opNatEquiv ψ x w ∈ W) → n ≤ finrank K W := fun W hW hWx =>
    le_finrank_of_isometry pairedSympForm_isAlt pairedSympForm_nondegenerate hdimV (heB x) hℓ
      hex hex1 hℓK hℓq hord hord' hW hWx
  have hUdim : finrank K U = n :=
    le_antisymm (by omega) (hbig U hU (fun u hu => hUX x hx u hu))
  set res := opRestrict (opNatEquiv ψ) X' U hUX with hresdef
  have hres_inj : Function.Injective res := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal res.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff res).1 hk
    · exfalso
      obtain ⟨u, hu, hxu⟩ := exists_apply_ne_of_isometry pairedSympForm_isAlt
        pairedSympForm_nondegenerate hdimV (heB x) hℓ hex hex1 hℓK hℓq hord hU
      have hmem : (⟨x, hx⟩ : X') ∈ res.ker := hk ▸ Subgroup.mem_top _
      have := congrArg (fun f : U ≃ₗ[K] U => ((f ⟨u, hu⟩ : U) : Fin n ⊕ Fin n → K))
        (MonoidHom.mem_ker.1 hmem)
      exact hxu this
  have hnt : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  have hirr : ∀ W : Submodule K U, (∀ w ∈ W, res ⟨x, hx⟩ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      have hmap : W.map U.subtype ≠ ⊥ := by
        obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
        intro h
        have hwm : (w : Fin n ⊕ Fin n → K) ∈ W.map U.subtype := ⟨w, hw, rfl⟩
        rw [h, Submodule.mem_bot] at hwm
        exact hw0 (Subtype.ext hwm)
      have hinv : ∀ v ∈ W.map U.subtype, opNatEquiv ψ x v ∈ W.map U.subtype := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨res ⟨x, hx⟩ w, hW w hw, rfl⟩
      have h1 := hbig _ hmap hinv
      have h2 : finrank K (W.map U.subtype) = finrank K W :=
        (Submodule.equivMapOfInjective _ U.injective_subtype W).finrank_eq.symm
      have h3 : finrank K W ≤ finrank K U := Submodule.finrank_le W
      exact Submodule.eq_top_of_finrank_eq (by omega)
  have hres_xy : res ⟨x, hx⟩ * res ⟨y, hy⟩ = res ⟨y, hy⟩ * res ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg res (Subtype.ext hxy)
  have hres_ym : res ⟨y, hy⟩ ^ m = 1 := by
    rw [← map_pow, show (⟨y, hy⟩ : X') ^ m = 1 from Subtype.ext (by simp [hym]), map_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_of_commute_of_irreducible hres_xy hirr hres_ym hmq
  have hc := mem_center_of_eq_smul res hres_inj ha
  rw [hZ, Subgroup.mem_bot] at hc
  exact hy1 (congrArg Subtype.val hc)

end Core

@[expose] def OmegaMinusNonembeddingDataInput : Prop :=
  ∀ (Y : Type) [Group Y] (N g : ℕ), 6 ≤ N → Even N → 1 ≤ g →
    CFSG.Blueprint.LieModel Y .POmegaMinus N 2 g →
    ∃ (Q₁ X' : Subgroup Y) (x y : Y) (ℓ : ℕ), IsPGroup 2 Q₁ ∧ Q₁ ≠ ⊥ ∧
      X' ≤ normalizer (Q₁ : Set Y) ∧ IsSimpleGroup X' ∧ center X' = ⊥ ∧ x ∈ X' ∧ y ∈ X' ∧
      x * y = y * x ∧ y ≠ 1 ∧ y ^ (2 ^ g + 1) = 1 ∧ ℓ.Prime ∧ ℓ ≠ 2 ∧ x ^ ℓ = 1 ∧ x ≠ 1 ∧
      (∀ j, 1 ≤ j → j < N - 1 → ¬ ℓ ∣ (2 ^ (2 * g)) ^ (2 * j) - 1) ∧
      (∀ i, 1 ≤ i → i < N - 1 → ¬ ℓ ∣ (2 ^ (2 * g)) ^ i - 1)

theorem omegaMinusSpNonembeddingInput_of_data (h : OmegaMinusNonembeddingDataInput) :
    OmegaMinusSpNonembeddingInput := by
  intro Y _ N g hN hNe hg hY K _ _ hK φ hφ
  obtain ⟨Q₁, X', x, y, ℓ, hQ, hQne, hXN, hsimple, hZ, hx, hy, hxy, hy1, hyr, hℓ, hℓ2, hxℓ, hx1,
    hord, hord'⟩ := h Y N g hN hNe hg hY
  obtain ⟨hc, -⟩ := charP_two_and_four_le_of_card hK (by omega : 2 ≤ 2 * g)
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h0).symm
  have hℓq : ¬ ℓ ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd))
  refine false_of_nonembedding_data φ hφ Q₁ X' hQ hQne hXN hZ hx hy hxy hy1 hℓ hxℓ hx1 hℓK hℓq
    (fun j hj hjn => by rw [hK]; exact hord j hj hjn)
    (fun i hi hin => by rw [hK]; exact hord' i hi hin) hyr ?_
  rw [hK]
  have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 * g) := Nat.one_le_two_pow
  refine ⟨2 ^ g - 1, ?_⟩
  zify [h1, h2]
  ring

end CFSG.SeitzReduction.SymplecticPilot
