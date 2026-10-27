module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnBad
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnV
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnWeyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSubB
public import CFSG.GH74.GLS.Stage2.OddAut.FixedCore
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_false_of_outer_three_q2_frame (hA2m : D4OuterThreeA2Minus) {p f : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  obtain ⟨T', m', hT', hm'T, hm'3, hm'n, hm'δ, hTδ, hidx, hNmono, -, -⟩ :=
    d4Minus_exists_N' hf hq hK hσ hg₀
  have hNδ : ∀ x ∈ T' ⊔ Subgroup.zpowers m',
      fieldActor (t := TwistTag.D4) σ σ x ∈ T' ⊔ Subgroup.zpowers m' := by
    have hle : T' ⊔ Subgroup.zpowers m' ≤ (T' ⊔ Subgroup.zpowers m').comap
        ((fieldActor (t := TwistTag.D4) σ σ : MulAut _).toMonoidHom) := by
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_sup_left (hTδ t ht)
      · show fieldActor (t := TwistTag.D4) σ σ m' ∈ T' ⊔ Subgroup.zpowers m'
        rw [hm'δ]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers m')
    exact fun x hx => hle hx
  have hVe : IsElementaryAbelian 3 V := h2.2.2.1
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨β, hβ⟩ := d4_exists_conj_le_Bδ hp hp2 hf K hK σ hσ _ hidx hNδ V hV3
  let e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (β⁻¹ :
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  have hconjapply : ∀ x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      MulAut.congr e x = β⁻¹ * x * β := fun x =>
    MulEquiv.ext fun y => rfl
  have h2' := h2.map_mulEquiv (MulAut.congr e)
  have h3' := N3Full.map_mulEquiv e h3
  have hmemV' : ∀ x' ∈ V.map (MulAut.congr e).toMonoidHom, ∃ x ∈ V, x' = β⁻¹ * x * β := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, hconjapply x⟩
  have hVe' : IsElementaryAbelian 3 (V.map (MulAut.congr e).toMonoidHom) := h2'.2.2.1
  have hVc' : Nat.card (V.map (MulAut.congr e).toMonoidHom) = 9 := by
    have := h2'.2.2.2.1
    simpa using this
  have hV0' : ∀ x ∈ V.map (MulAut.congr e).toMonoidHom,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      g ∈ T' ⊔ Subgroup.zpowers m' ∧ (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV' x' hx'
    obtain ⟨g, δ, hg, hδ, hgδ⟩ := hβ x hx
    exact ⟨g, δ, hg, hδ, hgδ⟩
  obtain ⟨φ, hφV, hφout⟩ := hout
  have hout' : ∃ φ' ∈ V.map (MulAut.congr e).toMonoidHom, φ' ∉ (MulAut.conj :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut (graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)).range := by
    refine ⟨MulAut.congr e φ, Subgroup.mem_map_of_mem _ hφV, ?_⟩
    rintro ⟨g, hg⟩
    apply hφout
    refine ⟨e.symm g, ?_⟩
    apply (MulAut.congr e).injective
    have h1 : MulAut.congr e (MulAut.conj (e.symm g)) = MulAut.conj g :=
      MulEquiv.ext fun y => by
        show e (e.symm g * e.symm y * (e.symm g)⁻¹) = g * y * g⁻¹
        rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
    rw [h1]
    exact hg
  rcases d4Minus_weyl_cases hp hp2 hf K hK σ hσ T' m' hm'T hm'3 hm'n hm'δ hTδ _ hVe' hVc' hV0'
    hout' with ⟨φ', hφ'V, hφ'out, t, ht, hφ'⟩ | ⟨v, n, δ, hv, hv1, hv3, hvV, hn, hnT, hδ, heV, hev⟩
  ·
    have hφ'3 : φ' ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian φ' hφ'V
    have hψ3' : (MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rcases hφ' with h1 | h1
      · rw [← h1]
        exact hφ'3
      · rw [← h1, inv_pow, hφ'3, inv_one]
    have hN := normSeq_eq_one_of_pow_eq_one hcen hψ3 hψ3'
    rw [normSeq_three] at hN
    have hD0 := d4Minus_out_of_toral hA2m hp hp2 hp3 hf hq K hK σ hσ L hg₀ t
      ((hT' t).1 ht) hN
    have hD : D4Out φ' := by
      rcases hφ' with h1 | h1
      · rw [h1]
        exact hD0
      · have h4 := hD0.inv
        rw [← h1, inv_inv] at h4
        exact h4
    have hφ'1 : φ' ≠ 1 := fun h1 => hφ'out (h1 ▸ ⟨1, map_one _⟩)
    exact false_of_fixed_core hcen h2' h3' hφ'V hφ'1 hD.1 hD.2
  ·
    refine d4Minus_bad_case hp hp2 hp3 hf hq K hK σ hσ L hg₀ h2' h3' v n δ ((hT' v).1 hv) hv1 hv3
      hvV (hNmono n hn).1 (fun htor => hnT ((hT' n).2 ((hNmono n hn).2 htor))) hδ heV hev

theorem d4_false_of_outer_three_q2 (hA2m : D4OuterThreeA2Minus) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := by
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = p ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ := d4Minus_exists_frame (L := AlgebraicClosure K) p hp2 hf
  exact d4_false_of_outer_three_q2_frame hA2m hp hp2 hp3 hf hq K hK σ hσ (AlgebraicClosure K)
    ⟨hg₀C, hg₀P, hg₀F⟩ h2 h3 hout

end CFSG.GH74.GLS.Stage2.Bender.Thm1
