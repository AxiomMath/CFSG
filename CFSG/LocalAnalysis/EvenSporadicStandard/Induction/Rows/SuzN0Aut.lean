module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverStd
public import CFSG.Sporadic.SuzOddCore.SmallAut

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Cover
open scoped commutatorElement

section Aut


theorem suz_autFixing {Y : Type} [Group Y] (Ψ : Y →* Equiv.Perm (Fin 1782))
    (hinj : Function.Injective Ψ) (hΨM : ∀ y, Ψ y ∈ suzM) (hΨR : ∀ m ∈ suzM, ∃ y, Ψ y = m)
    (Ñ : Subgroup Y) (d : Equiv.Perm (Fin 1782)) (hd : d ∈ suzM)
    (hr : ∀ i < 4, ∃ n ∈ Ñ, Ψ n = d * rElt i * d⁻¹) (hw : ∃ n ∈ Ñ, Ψ n = d * wElt * d⁻¹) :
    Group.IsSolvable ↥(autFixing Ñ) ∧
      (∀ A : Subgroup ↥(autFixing Ñ), IsPGroup 2 A → (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ 4) ∧
      (∀ β ∈ autFixing Ñ, ∃ y : Y, β = MulAut.conj y) := by
  obtain ⟨-, -, -, -, h, hhM, hconj, S, hSF, hS⟩ := Certificates.certificate27216
  let ψ : Y ≃* ↥suzM := MulEquiv.ofBijective (Ψ.codRestrict suzM hΨM)
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun y => by
      obtain ⟨x, hx⟩ := hΨR y y.2
      exact ⟨x, Subtype.ext hx⟩⟩
  let κ : ↥suzT ≃* MulAut ↥suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  let Θ : MulAut Y →* Equiv.Perm (Fin 1782) :=
    suzT.subtype.comp (κ.symm.toMonoidHom.comp (MulAut.congr ψ).toMonoidHom)
  have hΘinj : Function.Injective Θ :=
    suzT.subtype_injective.comp (κ.symm.injective.comp (MulAut.congr ψ).injective)
  have hΘT : ∀ β, Θ β ∈ suzT := fun β => (κ.symm (MulAut.congr ψ β)).2
  have hΘact : ∀ (β : MulAut Y) (y : Y), Θ β * Ψ y * (Θ β)⁻¹ = Ψ (β y) := by
    intro β y
    set τ : ↥suzT := κ.symm (MulAut.congr ψ β) with hτdef
    have hτ : suzConjT τ = MulAut.congr ψ β := κ.apply_symm_apply _
    have h2 := congrArg (fun γ : MulAut ↥suzM => ((γ (ψ y) : ↥suzM) : Equiv.Perm (Fin 1782))) hτ
    simp only [suzConjT_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h2
    exact h2
  have hcommN : ∀ β ∈ autFixing Ñ, ∀ n ∈ Ñ, Θ β * Ψ n = Ψ n * Θ β := by
    intro β hβ n hn
    have h1 := hΘact β n
    rw [hβ n hn] at h1
    calc Θ β * Ψ n = Θ β * Ψ n * (Θ β)⁻¹ * Θ β := by group
      _ = Ψ n * Θ β := by rw [h1]
  set c : Equiv.Perm (Fin 1782) := d * h with hcdef
  have hscan : ∀ β ∈ autFixing Ñ, ∃ s ∈ S, Θ β = c * s * c⁻¹ := by
    intro β hβ
    refine centralizer_surv hhM hconj hS hd (hΘT β) (fun i hi => ?_) ?_
    · obtain ⟨n, hn, hnΨ⟩ := hr i hi
      have := hcommN β hβ n hn
      rwa [hnΨ] at this
    · obtain ⟨n, hn, hnΨ⟩ := hw
      have := hcommN β hβ n hn
      rwa [hnΨ] at this
  have hcM : c ∈ suzM := suzM.mul_mem hd hhM
  let Θ' : ↥(autFixing Ñ) →* Equiv.Perm (Fin 1782) := Θ.comp (autFixing Ñ).subtype
  have hΘ'inj : Function.Injective Θ' := hΘinj.comp (autFixing Ñ).subtype_injective
  let cj : Equiv.Perm (Fin 1782) →* Equiv.Perm (Fin 1782) := (MulAut.conj c).toMonoidHom
  have hcj : ∀ g, cj g = c * g * c⁻¹ := fun g => rfl
  have hcjinj : Function.Injective cj := (MulAut.conj c).injective
  let Gs : Set (Equiv.Perm (Fin 1782)) := cj '' S
  let T₂ : Set (Equiv.Perm (Fin 1782)) := {s | s ∈ S ∧ s * s = 1}
  let Sq : Set (Equiv.Perm (Fin 1782)) := cj '' T₂
  have hX : ∀ x, Θ' x ∈ Gs := by
    intro x
    obtain ⟨s, hs, he⟩ := hscan x x.2
    exact ⟨s, hs, by rw [hcj]; exact he.symm⟩
  have hsq1 : ∀ s : Equiv.Perm (Fin 1782), cj s * cj s = 1 → s * s = 1 := fun s hs =>
    hcjinj (by rw [map_mul, map_one]; exact hs)
  have hcomm : ∀ a ∈ Gs, ∀ b ∈ Gs, a * a = 1 → b * b = 1 → a * b = b * a := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ ha hb
    rw [← map_mul, ← map_mul, hSF.invol s hs t ht (hsq1 s ha) (hsq1 t hb)]
  have hder : ∀ a ∈ Gs, ∀ b ∈ Gs, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have h1 := hSF.comm s hs t ht
    rw [commutatorElement_def] at h1
    have h2 := congrArg cj h1
    simpa only [map_mul, map_inv, map_one] using h2
  have hSq : ∀ g ∈ Gs, g * g = 1 → g ∈ Sq := by
    rintro _ ⟨s, hs, rfl⟩ hg
    exact ⟨s, ⟨hs, hsq1 s hg⟩, rfl⟩
  have hn : Sq.ncard ≤ 4 := (Set.ncard_image_le (Set.toFinite _)).trans hSF.card
  have hpow : ∀ x, Θ' x * Θ' x = 1 ∨ Θ' x * Θ' x * Θ' x = 1 := by
    intro x
    obtain ⟨s, hs, he⟩ := hX x
    rw [← he]
    rcases hSF.pow s hs with h2 | h3
    · exact Or.inl (by rw [← map_mul, h2, map_one])
    · exact Or.inr (by rw [← map_mul, ← map_mul, h3, map_one])
  have hsq2 : ∀ A : Subgroup ↥(autFixing Ñ), IsPGroup 2 A → ∀ x ∈ A, x * x = 1 := by
    intro A hA x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hA) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases hpow x with h2 | h3
    · exact hΘ'inj (by rw [map_mul, map_one]; exact h2)
    · have h3' : orderOf (Θ' x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa [pow_succ] using h3)
      rw [orderOf_injective Θ' hΘ'inj x, hk] at h3'
      have hk0 : k = 0 := by
        by_contra hne
        have : 2 ∣ 3 := (dvd_pow_self 2 hne).trans h3'
        omega
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      rw [hk, mul_one]
  refine ⟨AutBound.smallSub_isSolvable Θ' Gs hcomm hder hΘ'inj hX, fun A hA => ⟨hsq2 A hA, ?_⟩, ?_⟩
  · exact (AutBound.smallSub_elemBound Θ' Gs Sq hSq (Set.toFinite _) hΘ'inj hX A (hsq2 A hA)).trans
      hn
  · intro β hβ
    have hTM : Θ β ∈ suzM := by
      obtain ⟨s, hs, he⟩ := hscan β hβ
      rw [he]
      exact suzM.mul_mem (suzM.mul_mem hcM (hSF.mem s hs)) (suzM.inv_mem hcM)
    have hmem : (⟨Θ β, hΘT β⟩ : ↥suzT) ∈ suzM.subgroupOf suzT := hTM
    have hmap : suzConjT ⟨Θ β, hΘT β⟩ ∈ (suzM.subgroupOf suzT).map suzConjT :=
      Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
    rw [suzConjT_map_suzM] at hmap
    obtain ⟨m, hm⟩ := hmap
    have hκ : suzConjT ⟨Θ β, hΘT β⟩ = MulAut.congr ψ β := κ.apply_symm_apply _
    rw [hκ] at hm
    refine ⟨ψ.symm m, (MulAut.congr ψ).injective ?_⟩
    rw [← hm]
    ext z
    simp [MulAut.conj_apply]

end Aut

end CFSG.EvenSporadicStandard.SuzN0
