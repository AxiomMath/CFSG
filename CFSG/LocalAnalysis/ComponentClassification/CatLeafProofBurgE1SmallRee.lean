module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Ree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ReeCoset
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ coe_frobeniusΓ_pow
  frobeniusΓ_pow exists_eq_conj_mul_frobeniusΓ_pow)

theorem trace_conj_units_map_entrywiseHom
    {τ : Tag} {L : Type} [Field L] (g y : ModGL τ L) (σ : L ≃+* L) :
    LinearMap.trace L (RootModule τ L)
        ((g * Units.map (entrywiseHom σ.toRingHom) y * g⁻¹ : ModGL τ L) :
          Module.End L (RootModule τ L)) =
      σ (LinearMap.trace L (RootModule τ L) (y : Module.End L (RootModule τ L))) := by
  rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj, units_map_entrywiseHom_eq_baseChangeGL,
    RankThree.Chevalley.trace_baseChangeGL]
  rfl

theorem mod_eq_zero_of_frobenius_fixes_reeTorus_traces
    {K : Type} [Field K] [Finite K] [CharP K 3] {a k : ℕ} (hK : Nat.card K = 3 ^ (2 * a + 1))
    (h : ∀ s : Kˣ, ((frobeniusEquiv K 3) ^ k) (LinearMap.trace K (RootModule Tag.G2 K)
        ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
          Module.End K (RootModule Tag.G2 K))) =
      LinearMap.trace K (RootModule Tag.G2 K)
        ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
          Module.End K (RootModule Tag.G2 K))) :
    k % (2 * a + 1) = 0 := by
  have hσpow : ∀ c : K, ((frobeniusEquiv K 3) ^ k) c = c ^ 3 ^ (k % (2 * a + 1)) := by
    intro c
    have e : 3 ^ k = Nat.card K ^ (k / (2 * a + 1)) * 3 ^ (k % (2 * a + 1)) := by
      rw [hK, ← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [frobeniusEquiv_three_pow_apply, e, pow_mul, pow_natCard_pow_eq_self]
  by_contra hk
  refine g2TorusExp_frobenius_absurd hK (Nat.mod_lt _ (by omega)) hk _ hσpow fun s => ?_
  have h1 := h s
  rw [trace_smallReeTorusElt, map_add, map_ofNat, map_sum] at h1
  exact add_left_cancel h1

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] {a : ℕ}

theorem eq_one_of_fixes_fixedSubgroup_conj_smallReeH
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hh₀ : smallReeH a K (-1) ∈ ReeTag.G2.reeGamma K a) (β : MulAut (ReeTag.G2.reeGamma K a))
    (hβ : Odd (orderOf β))
    (hfix : ∀ x ∈ fixedSubgroup (MulAut.conj
      (⟨smallReeH a K (-1), hh₀⟩ : ReeTag.G2.reeGamma K a)), β x = x) : β = 1 := by
  set h₀ : ReeTag.G2.reeGamma K a := ⟨smallReeH a K (-1), hh₀⟩
  have hHΓ : ∀ s : Kˣ, smallReeH a K s ∈ ReeTag.G2.reeGamma K a := fun s =>
    (Subgroup.mem_inf.1 (smallReeH_mem hK s)).2
  have hHfix : ∀ s : Kˣ, β ⟨smallReeH a K s, hHΓ s⟩ = ⟨smallReeH a K s, hHΓ s⟩ := by
    intro s
    refine hfix _ ?_
    change h₀ * ⟨smallReeH a K s, hHΓ s⟩ * h₀⁻¹ = ⟨smallReeH a K s, hHΓ s⟩
    refine Subtype.ext ?_
    change smallReeH a K (-1) * smallReeH a K s * (smallReeH a K (-1))⁻¹ = smallReeH a K s
    rw [smallReeH_inv, ← smallReeH_mul, ← smallReeH_mul, mul_comm (-1 : Kˣ) s, mul_assoc,
      mul_inv_cancel, mul_one]
  obtain ⟨g, k, hgk⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK β
  have hk : k % (2 * a + 1) = 0 := by
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    refine mod_eq_zero_of_frobenius_fixes_reeTorus_traces hK fun s => ?_
    have hx : smallReeH a K s ∈ adjointGroup ReeTag.G2.tag K :=
      (ReeTag.mem_reeGamma.1 (hHΓ s)).1
    have hFrx : ((ReeTag.G2.finiteFrobeniusAut K ^ k) ⟨smallReeH a K s, hx⟩ :
        ModGL ReeTag.G2.tag K) =
          Units.map (entrywiseHom ((frobeniusEquiv K 3) ^ k).toRingHom) (smallReeH a K s) :=
      coe_G2_finiteFrobeniusAut_pow k _
    have h1 : ((β ⟨smallReeH a K s, hHΓ s⟩ : ReeTag.G2.reeGamma K a) :
        ModGL ReeTag.G2.tag K) = (g : ModGL ReeTag.G2.tag K) *
          Units.map (entrywiseHom ((frobeniusEquiv K 3) ^ k).toRingHom) (smallReeH a K s) *
            (g : ModGL ReeTag.G2.tag K)⁻¹ := by
      rw [hgk, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_frobeniusΓ_pow k ⟨smallReeH a K s, hHΓ s⟩ hx, hFrx]
    rw [hHfix s] at h1
    have h2 := congrArg (fun y : ModGL ReeTag.G2.tag K =>
      LinearMap.trace K (RootModule ReeTag.G2.tag K) (y : Module.End K _)) h1
    simp only at h2
    rw [trace_conj_units_map_entrywiseHom] at h2
    exact h2.symm
  have hFr : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ k = 1 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hk
    rw [hm, pow_mul, frobeniusΓ_pow hK, one_pow]
  have hβg : β = MulAut.conj g := by rw [hgk, hFr, mul_one]
  have hgC : g ∈ fixedSubgroup (MulAut.conj h₀) := by
    have h1 := hfix h₀ (by change h₀ * h₀ * h₀⁻¹ = h₀; group)
    rw [hβg, MulAut.conj_apply] at h1
    change h₀ * g * h₀⁻¹ = g
    calc h₀ * g * h₀⁻¹ = g * h₀ * g⁻¹ * g * h₀⁻¹ := by rw [h1]
      _ = g := by group
  have hgZ : (⟨g, hgC⟩ : fixedSubgroup (MulAut.conj h₀)) ∈
      Subgroup.center (fixedSubgroup (MulAut.conj h₀)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := hfix y y.2
    rw [hβg, MulAut.conj_apply] at h1
    refine Subtype.ext ?_
    change (y : ReeTag.G2.reeGamma K a) * g = g * y
    calc (y : ReeTag.G2.reeGamma K a) * g = g * y * g⁻¹ * g := by rw [h1]
      _ = g * y := by group
  have hinj : Function.Injective (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzZ : z ∈ Subgroup.center (ReeTag.G2.reeGamma K a) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h3 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma K a) => φ x) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc x * z = z * x * z⁻¹ * z := by rw [h3]
        _ = z * x := by group
    rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hzZ
    exact hzZ
  have hgodd' : Odd (orderOf g) := by
    rw [← orderOf_injective _ hinj g, ← hβg]
    exact hβ
  have hgodd : Odd (orderOf (⟨g, hgC⟩ : fixedSubgroup (MulAut.conj h₀))) := by
    rw [← Subgroup.orderOf_coe]
    exact hgodd'
  have hO : pPrimeCore 2 (fixedSubgroup (MulAut.conj h₀)) = ⊥ := by
    let e : fixedSubgroup (MulAut.conj h₀) ≃* smallReeInvCentralizer a K :=
      ((fixedSubgroup (MulAut.conj h₀)).equivMapOfInjective _
        (ReeTag.G2.reeGamma K a).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_fixedSubgroup_conj _ h₀))
    have h1 := pPrimeCore_map_iso 2 e.symm
    rw [pPrimeCore_smallReeInvCentralizer ha hK, Subgroup.map_bot] at h1
    exact h1.symm
  have hle : Subgroup.zpowers (⟨g, hgC⟩ : fixedSubgroup (MulAut.conj h₀)) ≤
      pPrimeCore 2 (fixedSubgroup (MulAut.conj h₀)) :=
    le_pPrimeCore_of_normal_coprime (Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hgZ))
      (by rw [Nat.card_zpowers]; exact Nat.coprime_two_left.2 hgodd)
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have hg1 : g = 1 := by
    have h1 := congrArg Subtype.val hle
    exact h1
  rw [hβg, hg1, map_one]

theorem burgE1SmallReeInput_holds
    :
    ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime] (a : ℕ), 1 ≤ a →
      Nat.card K = 3 ^ (2 * a + 1) → ∀ t : ReeTag.G2.reeGamma K a, orderOf t = 2 →
        ∀ β : MulAut (ReeTag.G2.reeGamma K a), Odd (orderOf β) →
          MulAut.conj t * β = β * MulAut.conj t →
            (∀ x ∈ fixedSubgroup (MulAut.conj t), β x = x) → β = 1 := by
  intro K _ _ _ a ha hK t ht β hβ _ hfix
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have ht' : orderOf (t : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 t t.2 ht'
  set g' : ReeTag.G2.reeGamma K a := ⟨g, hgΓ⟩
  have hh₀ : smallReeH a K (-1) ∈ ReeTag.G2.reeGamma K a :=
    hgt ▸ mul_mem (mul_mem hgΓ t.2) (inv_mem hgΓ)
  set h₀ : ReeTag.G2.reeGamma K a := ⟨smallReeH a K (-1), hh₀⟩
  have ht₀ : t = g'⁻¹ * h₀ * g' := by
    have hgh : g' * t * g'⁻¹ = h₀ := Subtype.ext hgt
    rw [← hgh]
    group
  have hfix' : ∀ x ∈ fixedSubgroup (MulAut.conj h₀),
      (MulAut.conj g' * β * (MulAut.conj g')⁻¹) x = x := by
    intro x hx
    have hx₀ : h₀ * x * h₀⁻¹ = x := hx
    have hx' : (MulAut.conj g')⁻¹ x ∈ fixedSubgroup (MulAut.conj t) := by
      change t * ((MulAut.conj g')⁻¹ x) * t⁻¹ = (MulAut.conj g')⁻¹ x
      rw [← map_inv, MulAut.conj_apply, inv_inv, ht₀]
      calc g'⁻¹ * h₀ * g' * (g'⁻¹ * x * g') * (g'⁻¹ * h₀ * g')⁻¹ =
          g'⁻¹ * (h₀ * x * h₀⁻¹) * g' := by group
        _ = g'⁻¹ * x * g' := by rw [hx₀]
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ hx', MulAut.apply_inv_self]
  have hβ' : Odd (orderOf (MulAut.conj g' * β * (MulAut.conj g')⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hβ
  have h1 := eq_one_of_fixes_fixedSubgroup_conj_smallReeH ha hK hh₀ _ hβ' hfix'
  calc β = (MulAut.conj g')⁻¹ * (MulAut.conj g' * β * (MulAut.conj g')⁻¹) * MulAut.conj g' := by
        group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

end CFSG.ComponentClassification.CatLeafProof
