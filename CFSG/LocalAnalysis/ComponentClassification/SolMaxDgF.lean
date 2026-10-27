module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgFLift
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgFPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgE

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem DgF.false_of_diag_core [Finite X] {β c t a x' : X} {M' Y : Subgroup X}
    (hc : orderOf c = 2) (ht : orderOf t = 2) (ha : orderOf a = 2)
    (hcβ : c * β = β * c) (htβ : t * β = β * t) (hac : a * c = c * a) (hat : a * t = t * a)
    (hM'Y : M' ≤ centralizer ({β} : Set X))
    (hM'pc : IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))))
    (hne : M'.map (MulAut.conj c).toMonoidHom ≠ M')
    (htc' : M'.map (MulAut.conj t).toMonoidHom = M'.map (MulAut.conj c).toMonoidHom)
    {ψ : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)}
    {ρ' : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)} (hρ' : IsPermActionZ ψ ρ')
    (haMM : a ∈ M' ⊔ M'.map (MulAut.conj c).toMonoidHom) (haN : a ∈ normalizer (M' : Set X))
    (h3 : (ρ' ⟨a, haN⟩).supportᶜ.card = 3)
    (hYodd : Odd (Nat.card Y)) (hYN : Y ≤ normalizer (M' : Set X))
    (hYa : Y ≤ centralizer ({a} : Set X))
    (hYn : ∀ g : X, g * a = a * g → g * β = β * g → ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hzt : ∀ (z : X) (hz : z ∈ Y), z * t = t * z → ρ' ⟨z, hYN hz⟩ = 1)
    (hx' : x' ∈ Y) (hx'c : x' * c = c * x') (hρx' : ρ' ⟨x', hYN hx'⟩ ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcβ' : c ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr hcβ
  obtain ⟨hM'cY, hM'cpc⟩ := isPComponent_conj hM'Y hM'pc hcβ'
  have hcak : M'.map (MulAut.conj c).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M' :=
    GSThmB.B5a.le_coreActionKernel_of_ne hM'Y hM'cY hM'pc hM'cpc hne.symm
  have hρcak : ∀ (g : X) (hg : g ∈ UnbalancedLayer.coreActionKernel M'), ρ' ⟨g, hg.1⟩ = 1 :=
    fun g hg => DgF.eq_one_of_mem_coreActionKernel hρ' (by norm_num) hg
  have hconjc : ∀ m ∈ M', c⁻¹ * m * c ∈ M'.map (MulAut.conj c).toMonoidHom := fun m hm =>
    ⟨m, hm, by simp [MulAut.conj_apply, hcinv]⟩
  have htcN : t * c ∈ normalizer (M' : Set X) := by
    have h1 : M'.map (MulAut.conj (t * c)).toMonoidHom =
        (M'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h2 : M'.map (MulAut.conj (t * c)).toMonoidHom = M' := by
      rw [h1, ← htc', map_conj_map_conj_of_mul_self ht2]
    exact mem_normalizer_iff_map_conj_eq.mpr h2
  set σ := ρ' ⟨a, haN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    convert map_one ρ'
    exact Subtype.ext ha2
  have hσ4 : σ.support.card = 4 := by
    have h1 := Finset.card_compl σ.support
    have h2 := Finset.card_le_univ σ.support
    rw [Fintype.card_fin] at h1 h2
    omega
  set ζ := ρ' ⟨x', hYN hx'⟩ with hζdef
  have hx'a : x' * a = a * x' := mem_centralizer_singleton_iff.mp (hYa hx')
  have hζσ : ζ * σ = σ * ζ := by
    rw [hζdef, hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hx'a
  have hζodd : Odd (orderOf ζ) := by
    have h1 : orderOf ζ ∣ orderOf x' := by
      have := orderOf_map_dvd ρ' (⟨x', hYN hx'⟩ : ↥(normalizer (M' : Set X)))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf x' ∣ Nat.card Y := by
      have := orderOf_dvd_natCard (⟨x', hx'⟩ : Y)
      rwa [Subgroup.orderOf_mk] at this
    exact (hYodd.of_dvd_nat h2).of_dvd_nat h1
  have hζD := DgF.fixes_of_odd_commute hσ2 hσ4 hζσ hζodd
  have hζF : ∀ v ∉ σ.supportᶜ, ζ v = v := fun v hv =>
    hζD v (by rwa [Finset.mem_compl, not_not] at hv)
  have hζ3 : ζ ^ 3 = 1 := DgF.pow_three_of_odd h3 hζF hζodd
  have hpres : ∀ π : Perm (Fin 7), π * σ = σ * π → ∀ v, π v ∈ σ.supportᶜ ↔ v ∈ σ.supportᶜ := by
    intro π hπ v
    rw [Finset.mem_compl, Finset.mem_compl, apply_mem_support_iff_of_commute hπ]
  set τ := ρ' ⟨t * c, htcN⟩ with hτdef
  have htca : t * c * a = a * (t * c) := by
    rw [mul_assoc, ← hac, ← mul_assoc, ← hat, mul_assoc]
  have hτσ : τ * σ = σ * τ := by
    rw [hτdef, hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htca
  have hτζ := (DgF.conj_eq_or_eq_inv h3 (hpres τ hτσ) hζF hζ3).1
  obtain ⟨g, hgM, hga, hgconj⟩ : ∃ (g : X) (hgM : g ∈ M'), g * a = a * g ∧
      ρ' ⟨g, le_normalizer hgM⟩ * τ * ζ * τ⁻¹ * (ρ' ⟨g, le_normalizer hgM⟩)⁻¹ = ζ := by
    rcases hτζ with h | h
    · refine ⟨1, one_mem _, by group, ?_⟩
      have h1 : ρ' ⟨1, le_normalizer (one_mem M')⟩ = 1 := map_one ρ'
      rw [h1, one_mul, inv_one, mul_one, h]
    · obtain ⟨w, hwA, hw2, wF, hwF, hwFeq, hwFs⟩ :=
        DgF.exists_sqrt hσ2 hσ4 (by rw [h3]; norm_num)
      have hwσ : w * σ = σ * w := by rw [← hw2]; group
      have hwζ : w * ζ * w⁻¹ = ζ⁻¹ :=
        (DgF.conj_eq_or_eq_inv h3 (hpres w hwσ) hζF hζ3).2 wF hwF hwFeq hwFs
      obtain ⟨g, hgM, hga, hρg⟩ := DgF.exists_lift_sqrt hρ' hcak haMM haN ha2 hwA hw2
      refine ⟨g, hgM, hga, ?_⟩
      rw [hρg]
      calc w * τ * ζ * τ⁻¹ * w⁻¹ = w * (τ * ζ * τ⁻¹) * w⁻¹ := by group
        _ = (w * ζ * w⁻¹)⁻¹ := by rw [h]; group
        _ = ζ := by rw [hwζ, inv_inv]
  obtain ⟨w, hwdef⟩ : ∃ w, ρ' ⟨g, le_normalizer hgM⟩ = w := ⟨_, rfl⟩
  rw [hwdef] at hgconj
  have hgβ : g * β = β * g := mem_centralizer_singleton_iff.mp (hM'Y hgM)
  have hsa : g * t * g⁻¹ * a = a * (g * t * g⁻¹) :=
    ((((show Commute g a from hga).mul_left (show Commute t a from hat.symm)).mul_left
      (show Commute g a from hga).inv_left)).eq
  have hsβ : g * t * g⁻¹ * β = β * (g * t * g⁻¹) :=
    ((((show Commute g β from hgβ).mul_left (show Commute t β from htβ)).mul_left
      (show Commute g β from hgβ).inv_left)).eq
  have hs2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hsY : ∀ y ∈ Y, g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹ ∈ Y := hYn _ hsa hsβ
  have hcY : ∀ y ∈ Y, c⁻¹ * y * c ∈ Y := fun y hy => by
    have h1 := hYn c⁻¹ (by rw [hcinv]; exact hac.symm) (by rw [hcinv]; exact hcβ) y hy
    rwa [inv_inv] at h1
  have hgY : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y := fun y hy => by
    have h1 := hYn g⁻¹ (show Commute g⁻¹ a from (show Commute g a from hga).inv_left).eq
      (show Commute g⁻¹ β from (show Commute g β from hgβ).inv_left).eq y hy
    rwa [inv_inv] at h1
  have hcg1 : c⁻¹ * g * c ∈ UnbalancedLayer.coreActionKernel M' := hcak (hconjc g hgM)
  have hcg2 : c⁻¹ * g⁻¹ * c ∈ UnbalancedLayer.coreActionKernel M' :=
    hcak (hconjc g⁻¹ (inv_mem hgM))
  have hct : c⁻¹ * t ∈ normalizer (M' : Set X) := by
    have h1 : c⁻¹ * t = (t * c)⁻¹ := by rw [mul_inv_rev, htinv]
    rw [h1]
    exact inv_mem htcN
  have hρct : ρ' ⟨c⁻¹ * t, hct⟩ = τ⁻¹ := by
    have h1 : (⟨c⁻¹ * t, hct⟩ : ↥(normalizer (M' : Set X))) = ⟨t * c, htcN⟩⁻¹ :=
      Subtype.ext (by change c⁻¹ * t = (t * c)⁻¹; rw [mul_inv_rev, htinv])
    rw [h1, map_inv, ← hτdef]
  have hform1 : ∀ (y : X) (hy : y ∈ Y),
      ρ' ⟨g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹, hYN (hsY y hy)⟩ =
        w * τ * ρ' ⟨c⁻¹ * y * c, hYN (hcY y hy)⟩ * τ⁻¹ * w⁻¹ := by
    intro y hy
    have h1 : (⟨g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹, hYN (hsY y hy)⟩ :
        ↥(normalizer (M' : Set X))) =
        ⟨g, le_normalizer hgM⟩ * ⟨t * c, htcN⟩ * ⟨c⁻¹ * g⁻¹ * c, hcg2.1⟩ *
          ⟨c⁻¹ * y * c, hYN (hcY y hy)⟩ * ⟨c⁻¹ * g * c, hcg1.1⟩ * ⟨t * c, htcN⟩⁻¹ *
            ⟨g, le_normalizer hgM⟩⁻¹ :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    rw [h1]
    simp only [map_mul, map_inv]
    rw [hρcak _ hcg2, hρcak _ hcg1, mul_one, mul_one, hwdef, ← hτdef]
  have hform2 : ∀ (y : X) (hy : y ∈ Y),
      ρ' ⟨c⁻¹ * (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹) * c, hYN (hcY _ (hsY y hy))⟩ =
        τ⁻¹ * w⁻¹ * ρ' ⟨y, hYN hy⟩ * w * τ := by
    intro y hy
    have h1 : (⟨c⁻¹ * (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹) * c, hYN (hcY _ (hsY y hy))⟩ :
        ↥(normalizer (M' : Set X))) =
        ⟨c⁻¹ * g * c, hcg1.1⟩ * ⟨c⁻¹ * t, hct⟩ * (⟨g, le_normalizer hgM⟩⁻¹ * ⟨y, hYN hy⟩ *
          ⟨g, le_normalizer hgM⟩) * ⟨c⁻¹ * t, hct⟩⁻¹ * ⟨c⁻¹ * g * c, hcg1.1⟩⁻¹ :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    rw [h1]
    simp only [map_mul, map_inv]
    rw [hρcak _ hcg1, hρct, hwdef]
    group
  let K₀ : Subgroup X :=
    { carrier := {y | ∃ hy : y ∈ Y, ρ' ⟨y, hYN hy⟩ = 1 ∧ ρ' ⟨c⁻¹ * y * c, hYN (hcY y hy)⟩ = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx1, hx2⟩ ⟨hy, hy1, hy2⟩
        refine ⟨mul_mem hx hy, ?_, ?_⟩
        · have h1 : (⟨x * y, hYN (mul_mem hx hy)⟩ : ↥(normalizer (M' : Set X))) =
              ⟨x, hYN hx⟩ * ⟨y, hYN hy⟩ := rfl
          rw [h1, map_mul, hx1, hy1, mul_one]
        · have h1 : (⟨c⁻¹ * (x * y) * c, hYN (hcY _ (mul_mem hx hy))⟩ :
              ↥(normalizer (M' : Set X))) =
              ⟨c⁻¹ * x * c, hYN (hcY x hx)⟩ * ⟨c⁻¹ * y * c, hYN (hcY y hy)⟩ :=
            Subtype.ext (by simp only [coe_mul]; group)
          rw [h1, map_mul, hx2, hy2, mul_one]
      one_mem' := ⟨one_mem _, map_one ρ', by
        have h1 : (⟨c⁻¹ * 1 * c, hYN (hcY 1 (one_mem _))⟩ : ↥(normalizer (M' : Set X))) = 1 :=
          Subtype.ext (by simp)
        rw [h1, map_one]⟩
      inv_mem' := by
        rintro x ⟨hx, hx1, hx2⟩
        refine ⟨inv_mem hx, ?_, ?_⟩
        · have h1 : (⟨x⁻¹, hYN (inv_mem hx)⟩ : ↥(normalizer (M' : Set X))) = ⟨x, hYN hx⟩⁻¹ :=
            rfl
          rw [h1, map_inv, hx1, inv_one]
        · have h1 : (⟨c⁻¹ * x⁻¹ * c, hYN (hcY _ (inv_mem hx))⟩ : ↥(normalizer (M' : Set X))) =
              ⟨c⁻¹ * x * c, hYN (hcY x hx)⟩⁻¹ := Subtype.ext (by simp only [coe_inv]; group)
          rw [h1, map_inv, hx2, inv_one] }
  have hK₀Y : K₀ ≤ Y := fun y hy => hy.1
  have hK₀odd : Odd (Nat.card K₀) := hYodd.of_dvd_nat (Subgroup.card_dvd_of_le hK₀Y)
  have hK₀s : ∀ k ∈ K₀, g * t * g⁻¹ * k * (g * t * g⁻¹)⁻¹ ∈ K₀ := by
    rintro k ⟨hk, hk1, hk2⟩
    refine ⟨hsY k hk, ?_, ?_⟩
    · rw [hform1 k hk, hk2]
      group
    · rw [hform2 k hk, hk1]
      group
  have hcx' : c⁻¹ * x' * c = x' := by
    rw [mul_assoc, hx'c, ← mul_assoc, inv_mul_cancel, one_mul]
  have hζc : ρ' ⟨c⁻¹ * x' * c, hYN (hcY x' hx')⟩ = ζ := by
    have h1 : (⟨c⁻¹ * x' * c, hYN (hcY x' hx')⟩ : ↥(normalizer (M' : Set X))) =
        ⟨x', hYN hx'⟩ := Subtype.ext hcx'
    rw [h1, hζdef]
  have hgconj' : τ⁻¹ * w⁻¹ * ζ * w * τ = ζ := by
    calc τ⁻¹ * w⁻¹ * ζ * w * τ = τ⁻¹ * w⁻¹ * (w * τ * ζ * τ⁻¹ * w⁻¹) * w * τ := by
          rw [hgconj]
      _ = ζ := by group
  have hx's : x'⁻¹ * (g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹) ∈ K₀ := by
    have hmem : x'⁻¹ * (g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹) ∈ Y :=
      mul_mem (inv_mem hx') (hsY x' hx')
    refine ⟨hmem, ?_, ?_⟩
    · have h1 : (⟨x'⁻¹ * (g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹), hYN hmem⟩ :
          ↥(normalizer (M' : Set X))) =
          ⟨x', hYN hx'⟩⁻¹ * ⟨g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹, hYN (hsY x' hx')⟩ := rfl
      rw [h1, map_mul, map_inv, hform1 x' hx', hζc, ← hζdef, hgconj, inv_mul_cancel]
    · have h1 : (⟨c⁻¹ * (x'⁻¹ * (g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹)) * c, hYN (hcY _ hmem)⟩ :
          ↥(normalizer (M' : Set X))) =
          ⟨c⁻¹ * x' * c, hYN (hcY x' hx')⟩⁻¹ *
            ⟨c⁻¹ * (g * t * g⁻¹ * x' * (g * t * g⁻¹)⁻¹) * c, hYN (hcY _ (hsY x' hx'))⟩ :=
        Subtype.ext (by simp only [coe_mul, coe_inv]; group)
      rw [h1, map_mul, map_inv, hform2 x' hx', hζc, ← hζdef, hgconj', inv_mul_cancel]
  obtain ⟨k, hkK, hkc⟩ := exists_commute_of_mem_coset hK₀odd hs2 hK₀s hx's
  obtain ⟨hkY, hk1, -⟩ := hkK
  have hzY : x' * k ∈ Y := mul_mem hx' hkY
  have hρz : ρ' ⟨x' * k, hYN hzY⟩ = ζ := by
    have h1 : (⟨x' * k, hYN hzY⟩ : ↥(normalizer (M' : Set X))) = ⟨x', hYN hx'⟩ * ⟨k, hYN hkY⟩ :=
      rfl
    rw [h1, map_mul, hk1, mul_one, hζdef]
  have hz'Y : g⁻¹ * (x' * k) * g ∈ Y := hgY _ hzY
  have hz't : g⁻¹ * (x' * k) * g * t = t * (g⁻¹ * (x' * k) * g) := by
    calc g⁻¹ * (x' * k) * g * t = g⁻¹ * ((x' * k) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (x' * k)) * g := by rw [← hkc]
      _ = t * (g⁻¹ * (x' * k) * g) := by group
  have h1 := hzt _ hz'Y hz't
  have h2 : (⟨g⁻¹ * (x' * k) * g, hYN hz'Y⟩ : ↥(normalizer (M' : Set X))) =
      ⟨g, le_normalizer hgM⟩⁻¹ * ⟨x' * k, hYN hzY⟩ * ⟨g, le_normalizer hgM⟩ := rfl
  rw [h2, map_mul, map_mul, map_inv, hρz, hwdef] at h1
  apply hρx'
  calc ζ = w * (w⁻¹ * ζ * w) * w⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem signalizerDiagInvertedInput_holds : SignalizerDiagInvertedInput := by
  intro X _ _ β c t a x' M' _ hc ht ha _ hcβ htβ _ hac hat hM'Y hM'pc hne htc' ψ ρ' hρ' haMM haN
    h3 hON hzt hx' hx'c hρx'
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  refine DgF.false_of_diag_core hc ht ha hcβ htβ hac hat hM'Y hM'pc hne htc' hρ' haMM haN h3
    ?_ hON ?_ ?_ hzt hx' hx'c hρx'
  · have h1 : Odd (Nat.card ((pPrimeCore 2 ↥Ca).map Ca.subtype)) := by
      rw [card_map_of_injective Ca.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  · exact inf_le_left.trans (map_subtype_le _)
  · intro g hga hgβ y hy
    obtain ⟨hyO, hyβ⟩ := mem_inf.mp hy
    have hgCa : g ∈ Ca := mem_centralizer_singleton_iff.mpr hga
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca) hgCa) y).mp
        hyO
    · have hgβ' : g ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr hgβ
      exact mul_mem (mul_mem hgβ' hyβ) (inv_mem hgβ')

end CFSG.ComponentClassification.SolMax
