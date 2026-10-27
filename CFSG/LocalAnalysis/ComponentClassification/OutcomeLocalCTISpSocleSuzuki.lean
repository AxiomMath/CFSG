module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceSuzuki

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Blueprint CFSG.LieType.Ree

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A} {K : Type} [Field K]

theorem exists_inner_conj_eta [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1))
    {s : StatedSp 2 K}
    (hα2 : spInner 2 K s * exceptionalAut K ^ (2 * m + 1) *
      (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) = 1) :
    ∃ χ ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)),
      spInner 2 K s * exceptionalAut K ^ (2 * m + 1) =
        χ * exceptionalAut K ^ (2 * m + 1) * χ⁻¹ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  set ηG : zpowers (minorAut K ^ (2 * m + 1)) :=
    ⟨minorAut K ^ (2 * m + 1), mem_zpowers _⟩ with hηG
  set u := (antiSpEquiv K).symm s with hu
  set x : etaProduct K m := SemidirectProduct.inl u * SemidirectProduct.inr ηG with hx
  have hΘx : etaProductHom K m x = spInner 2 K s * exceptionalAut K ^ (2 * m + 1) := by
    rw [hx, map_mul, etaProductHom_inl, hηG, etaProductHom_inr_eta, hu,
      MulEquiv.apply_symm_apply]
  have hxr : x.right = ηG := by
    rw [hx, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul]
  have hγ2f : exceptionalAut K ^ (2 * (2 * m + 1)) = 1 := by rw [← hγord, pow_orderOf_eq_one]
  have hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1 := by
    have hγ2 : exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← two_mul, hγ2f]
    have key : spInner 2 K s * exceptionalAut K ^ (2 * m + 1) *
        (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) =
          spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) :=
      calc _ = spInner 2 K s * (exceptionalAut K ^ (2 * m + 1) * spInner 2 K s) *
            exceptionalAut K ^ (2 * m + 1) := by simp only [mul_assoc]
        _ = spInner 2 K s * spInner 2 K ((exceptionalSpAut K ^ (2 * m + 1)) s) *
            (exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1)) := by
          rw [exceptionalAut_pow_mul_spInner]
          simp only [mul_assoc]
        _ = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) := by
          rw [hγ2, mul_one, map_mul]
    have h1 : s * (exceptionalSpAut K ^ (2 * m + 1)) s = 1 :=
      spInner_injective (by rw [← key, hα2, map_one])
    have hs : s = antiSpEquiv K u := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hs, exceptionalSpAut_pow_apply, ← map_mul] at h1
    exact (antiSpEquiv K).injective (h1.trans (map_one _).symm)
  have hxl : x.left = u := by
    simp only [hx, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, mul_one]
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [sq, SemidirectProduct.mul_left, hxr, hxl, SemidirectProduct.one_left]
      exact hu1
    · rw [sq, SemidirectProduct.mul_right, hxr, SemidirectProduct.one_right]
      have h := pow_orderOf_eq_one (minorAut K ^ (2 * m + 1))
      rw [orderOf_eta m hK] at h
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h]; rfl)
  obtain ⟨h, hh⟩ := eta_involution_conj m hK x hxr hx2
  have hconj := congrArg (etaProductHom K m) hh
  rw [map_mul, map_mul, map_inv, hΘx, etaProductHom_inl, etaProductHom_inr_eta] at hconj
  refine ⟨(spInner 2 K (antiSpEquiv K h))⁻¹, inv_mem (spInner_mem_inner _), ?_⟩
  rw [inv_inv]
  calc spInner 2 K s * exceptionalAut K ^ (2 * m + 1)
      = (spInner 2 K (antiSpEquiv K h))⁻¹ * (spInner 2 K (antiSpEquiv K h) *
          (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) *
          (spInner 2 K (antiSpEquiv K h))⁻¹) * spInner 2 K (antiSpEquiv K h) := by group
    _ = _ := by rw [hconj]

theorem sp_socle_suzuki_false [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {m : ℕ} (hm : 1 ≤ m)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (φ : W ≃* StatedProj (StatedSp 2 K)) {ρ : A →* MulAut (StatedProj (StatedSp 2 K))}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) {s : StatedSp 2 K}
    (hρa : ρ a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have ha2 : a ^ 2 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hαα : ρ a * ρ a = 1 := by rw [← map_mul, ← sq, ha2, map_one]
  rw [hρa] at hαα
  obtain ⟨χ, -, hχ⟩ := exists_inner_conj_eta hK hαα
  rw [← hρa] at hχ
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  have hW : W.map ρ = OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) :=
    map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hCW' : (W ⊓ centralizer {a}).map ρ = ψ.range.map (MulAut.conj χ).toMonoidHom := by
    rw [hCWimg, hχ, ← map_conj_inner_inf_centralizer, ← hrange]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (ψ.range.map (MulAut.conj χ).toMonoidHom) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCW'] at this
  have hid : (MulAut.conj χ⁻¹).toMonoidHom.comp (MulAut.conj χ).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : Subgroup (MulAut (StatedProj (StatedSp 2 K))),
      L₀ = (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ ψ.range := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [Subgroup.map_map _ (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj χ).toMonoidHom, hid,
      Subgroup.map_id, ← hL₀def] at this
  obtain ⟨-, -, hSz⟩ := suzuki_simple hm hK
  have : IsSimpleGroup ψ.range := (MonoidHom.ofInjective hψinj).symm.isSimpleGroup
  have hL₀eq : L₀ = ψ.range := eq_of_isComponentOf_simple this hL₀
  have eLS : L ≃* suzukiGroup m K := ((L.equivMapOfInjective ρ hinj).trans
    (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective).trans
      (MulEquiv.subgroupCongr (hL₀def.symm.trans hL₀eq)))).trans
        (MonoidHom.ofInjective hψinj).symm
  have : IsSimpleGroup L := eLS.isSimpleGroup
  have hLnab := exists_ne_commute_of_isQuasisimple hLCW.2.2
  obtain ⟨eZ⟩ := nonempty_quotient_center_mulEquiv hLnab eLS
  obtain ⟨h1, h2, h3⟩ :=
    UnbalancingLocal.small_standard_source_Suzuki_model_exclusion_stated hm hK ⟨eZ⟩
  rcases hsrc with h | e7 | h
  · exact h1 p f hp2 h
  · exact (not_nonempty_iff.mpr h2 e7).elim
  · exact h3 h

theorem sp_socle_classify [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {r e : ℕ} (hr : 2 ≤ r)
    (he : 1 ≤ e) (hre : ¬ (r = 2 ∧ e = 1)) (hK : Nat.card K = 2 ^ e)
    (φ : W ≃* StatedProj (StatedSp r K)) {ρ : A →* MulAut (StatedProj (StatedSp r K))}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hZ : center (StatedProj (StatedSp r K)) = ⊥) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) :
    ∃ (g : StatedSp r K) (σ : K ≃+* K), σ ≠ 1 ∧ ρ a = spInner r K g * fieldAut r K σ := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hnI : ρ a ∉ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := fun h =>
    sp_socle_inner_false ha hLCW (by omega) he hK φ hinj hρW hZ h
  have hE : ρ a ∈ spSemilinearAutGroup r K →
      ∃ (g : StatedSp r K) (σ : K ≃+* K), σ ≠ 1 ∧ ρ a = spInner r K g * fieldAut r K σ := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    refine ⟨g, σ, ?_, hgσ⟩
    rintro rfl
    rw [map_one, mul_one] at hgσ
    exact hnI (hgσ ▸ spInner_mem_inner g)
  by_cases hr3 : 3 ≤ r
  · apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hr3).1]
    exact mem_top _
  · obtain rfl : r = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism he hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    have hρa2 : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
    rcases Nat.even_or_odd e with he' | ho
    · exact hE (heven he' _ hρa2)
    · exfalso
      obtain ⟨s, hs⟩ := hodd ho _ hρa2 hnI
      obtain ⟨m, rfl⟩ := ho
      have hm : 1 ≤ m := by omega
      rw [eq_exceptionalAut hγ] at hs
      exact sp_socle_suzuki_false ha hLCW hm hK φ hinj hρW hs hp2 hsrc

end CFSG.ComponentClassification.OutcomeLocal
