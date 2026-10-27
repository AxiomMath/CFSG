module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5Dich
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5Gl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3NSBig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Can
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3CoverBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.A5.Kc3L5 CFSG.QuasithinUnique.A5.Kc3NSC

theorem kc3ForS_l5 : Kc3ForS Kc3L5 := by
  classical
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hD hperf hSL hS hT hST hTK hTS
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ⟩ := exists_equiv_Gl hmod
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  set V' : Subgroup ↥K := V.subgroupOf K with hV'
  have hV2 : IsPGroup 2 ↥V := hQ2.to_le hVQ
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact AppC.card_evenWeight
  have hV'card : Nat.card V' = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hVcard]
  set Vg : Subgroup Gl := V'.map ρ.toMonoidHom with hVg
  have hVg2 : IsPGroup 2 Vg := hV'2.map ρ.toMonoidHom
  have hVg16 : Nat.card Vg = 16 := by
    rw [Subgroup.card_map_of_injective ρ.injective, hV'card]
  have hmemVg : ∀ z : Gl, z ∈ Vg ↔ ρ.symm z ∈ V' := fun z => Subgroup.mem_map_equiv
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := Delta5.a5_card
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hcardA5]; norm_num)
  obtain ⟨ℓ, hℓ⟩ := hα y
  have h5dvd : 5 ∣ orderOf ℓ := by
    rw [← hy, ← hℓ]
    exact orderOf_map_dvd α ℓ
  set k : ↥L := ℓ ^ (orderOf ℓ / 5) with hk
  have hk5 : orderOf k = 5 := orderOf_pow_orderOf_div (orderOf_pos ℓ).ne' h5dvd
  let k₀ : ↥K := ⟨(k : G), hLK k.2⟩
  have hk₀5 : orderOf k₀ = 5 := by
    have : orderOf (k₀ : ↥K) = orderOf k := by
      rw [← Subgroup.orderOf_coe k, ← Subgroup.orderOf_coe k₀]
    rw [this, hk5]
  have hx5 : orderOf (ρ k₀) = 5 := by rw [MulEquiv.orderOf_eq, hk₀5]
  have hxN : ρ k₀ ∈ Subgroup.normalizer (Vg : Set Gl) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hmemVg, hmemVg]
    have e : ρ.symm (ρ k₀ * z * (ρ k₀)⁻¹) = k₀ * ρ.symm z * k₀⁻¹ := by simp [map_mul, map_inv]
    rw [e]
    have := Subgroup.mem_normalizer_iff.1 (hLV k.2) ((ρ.symm z : ↥K) : G)
    show ((ρ.symm z : ↥K) : G) ∈ V ↔ ((k₀ * ρ.symm z * k₀⁻¹ : ↥K) : G) ∈ V
    simpa using this
  obtain ⟨hC, A, hAN, hAc, hAf⟩ := good_of_data hVg2 hVg16 hx5 hxN
  have hC' : K ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    intro g hg
    obtain ⟨hgK, hgC⟩ := hg
    let g' : ↥K := ⟨g, hgK⟩
    have hcomm : ∀ u ∈ Vg, ρ g' * u = u * ρ g' := by
      intro u hu
      have hu' : ρ.symm u ∈ V' := (hmemVg u).1 hu
      have h1 : ((ρ.symm u : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 hu'
      have h2 : ((ρ.symm u : ↥K) : G) * g = g * ((ρ.symm u : ↥K) : G) :=
        Subgroup.mem_centralizer_iff.1 hgC _ h1
      have h3 : ρ.symm u * g' = g' * ρ.symm u := Subtype.ext h2
      have h4 := congrArg ρ h3
      simpa [map_mul] using h4.symm
    have h5 := hC (ρ g') hcomm
    have h6 : g' ∈ V' := by
      have := (hmemVg (ρ g')).1 h5
      simpa using this
    exact Subgroup.mem_subgroupOf.1 h6
  have hQV : Q ≤ V := by
    intro q hq
    have hqL : q ∈ L := hQL hq
    have hqK : q ∈ K := hLK hqL
    have hqC : q ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      let l : ↥L := ⟨q, hqL⟩
      have hα1 : α l = 1 := (hαQ l).2 hq
      have hvq : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hqL) v).1 hv
      have h := hβ l ⟨v, hv⟩ ⟨q * v * q⁻¹, hvq⟩ rfl
      have e1 : ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = 1 := by
        rw [hα1]; rfl
      rw [e1, Delta5.vact_one] at h
      have h7 : (⟨q * v * q⁻¹, hvq⟩ : ↥V) = ⟨v, hv⟩ :=
        β.injective (Multiplicative.toAdd.injective h)
      have h2 : q * v * q⁻¹ = v := congrArg Subtype.val h7
      calc v * q = (q * v * q⁻¹) * q := by rw [h2]
        _ = q * v := by group
    exact hC' ⟨hqK, hqC⟩
  have hQeq : Q = V := le_antisymm hQV hVQ
  have hSV : S₀ ≤ Subgroup.normalizer (V : Set G) := by
    intro s hs
    have := normalizer_le_normalizer_Q hQL hQ2 α hα hαQ (hSL hs)
    rwa [hQeq] at this
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (V : Set G) with hX
  have hXchar : CharTwo X := Kc3Gen.charTwo_normalizer hT hTK hV2 hVK hC'
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hLX : L ⊔ S₀ ≤ X :=
    sup_le (le_inf (hLK.trans le_sup_left) hLV) (le_inf (hST.trans le_sup_right) hSV)
  obtain ⟨S₁, hS₀S₁, hS₁⟩ := Kc3Gen.exists_sylowTwoOf_le (X := X) (le_sup_right.trans hLX) hS
  refine ⟨X, S₁, hXchar, hLX, inf_le_left, hS₁, hS₀S₁, ?_⟩
  have hNA : ∀ a₁ ∈ A, ∀ z : ↥K, z ∈ V' ↔ ρ.symm a₁ * z * (ρ.symm a₁)⁻¹ ∈ V' := by
    intro a₁ ha₁ z
    have h := Subgroup.mem_normalizer_iff.1 (hAN ha₁) (ρ z)
    rw [hmemVg, hmemVg] at h
    have e : ρ.symm (a₁ * ρ z * a₁⁻¹) = ρ.symm a₁ * z * (ρ.symm a₁)⁻¹ := by
      simp [map_mul, map_inv]
    rw [e] at h
    simpa using h
  let Ag : Subgroup G := (A.map ρ.symm.toMonoidHom).map K.subtype
  have hAgK : Ag ≤ K := Subgroup.map_subtype_le _
  have hAgmem : ∀ a ∈ Ag, ∃ a₁ ∈ A, ((ρ.symm a₁ : ↥K) : G) = a := by
    rintro a ⟨a', ⟨a₁, ha₁, rfl⟩, rfl⟩
    exact ⟨a₁, ha₁, rfl⟩
  have hAgN : Ag ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    obtain ⟨a₁, ha₁, rfl⟩ := hAgmem a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hv' : (⟨v, hVK hv⟩ : ↥K) ∈ V' := Subgroup.mem_subgroupOf.2 hv
      have := (hNA a₁ ha₁ _).1 hv'
      exact Subgroup.mem_subgroupOf.1 this
    · intro hv
      have hvK : v ∈ K := by
        have h1 : ((ρ.symm a₁ : ↥K) : G)⁻¹ * (((ρ.symm a₁ : ↥K) : G) * v * ((ρ.symm a₁ : ↥K) : G)⁻¹) *
            ((ρ.symm a₁ : ↥K) : G) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem (ρ.symm a₁).2) (hVK hv)) (ρ.symm a₁).2
        have e : ((ρ.symm a₁ : ↥K) : G)⁻¹ * (((ρ.symm a₁ : ↥K) : G) * v *
            ((ρ.symm a₁ : ↥K) : G)⁻¹) * ((ρ.symm a₁ : ↥K) : G) = v := by group
        rwa [e] at h1
      have := (hNA a₁ ha₁ ⟨v, hvK⟩).2 (Subgroup.mem_subgroupOf.2 hv)
      exact Subgroup.mem_subgroupOf.1 this
  have hAgcard : Nat.card Ag = 16 := by
    show Nat.card ((A.map ρ.symm.toMonoidHom).map K.subtype) = 16
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective ρ.symm.injective, hAc]
  have hAgf : ∀ a ∈ Ag, (∀ v ∈ V, a * v * a⁻¹ = v) → a = 1 := by
    intro a ha hcomm
    obtain ⟨a₁, ha₁, rfl⟩ := hAgmem a ha
    have : a₁ = 1 := by
      apply hAf a₁ ha₁
      intro u hu
      have hu' : ρ.symm u ∈ V' := (hmemVg u).1 hu
      have h1 := hcomm ((ρ.symm u : ↥K) : G) (Subgroup.mem_subgroupOf.1 hu')
      have h2 : ρ.symm a₁ * ρ.symm u * (ρ.symm a₁)⁻¹ = ρ.symm u := Subtype.ext h1
      have h3 := congrArg ρ h2
      simpa [map_mul, map_inv] using h3
    rw [this, map_one]
    rfl
  have hAgX : Ag ≤ X := le_inf (hAgK.trans le_sup_left) hAgN
  have h16 : 16 ∣ Nat.card (rhoY V X hXV β).range := by
    let ρX := rhoY V X hXV β
    let ψ : ↥(Ag.subgroupOf X) →* MulAut Dm := ρX.comp (Ag.subgroupOf X).subtype
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hcomm : ∀ v ∈ V, (((a : ↥X) : ↥X) : G) * v * (((a : ↥X) : ↥X) : G)⁻¹ = v := by
        intro v hv
        have hw := rhoY_spec V X hXV β (a : ↥X) (β ⟨v, hv⟩)
        have h1 : ρX (a : ↥X) = 1 := ha
        rw [h1, MulAut.one_apply, MulEquiv.symm_apply_apply] at hw
        exact hw.symm
      have h2 := hAgf ((a : ↥X) : G) (Subgroup.mem_subgroupOf.1 a.2) hcomm
      apply Subtype.ext
      apply Subtype.ext
      exact h2
    have hcardAg' : Nat.card (Ag.subgroupOf X) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAgX).toEquiv, hAgcard]
    have hψcard : Nat.card ψ.range = 16 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, hcardAg']
    have hle : ψ.range ≤ ρX.range := by
      rintro _ ⟨a, rfl⟩
      exact ⟨(a : ↥X), rfl⟩
    have h3 := Subgroup.card_dvd_of_le hle
    rw [hψcard] at h3
    exact h3
  exact not_subnormal_of_big_image (le_sup_left.trans hLX) hXV α hα β hβ hS₁ h16

theorem kc3For_l5
    : Kc3For Kc3L5 := kc3For_of_simple isoInv_l5 kc3ForS_l5

end CFSG.QuasithinUnique.A5
