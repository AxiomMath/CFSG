module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Facts

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier

@[expose] def ClassFacts (L : Type) [Group L] : Prop :=
  ∀ zbar : L ⧸ center L, orderOf zbar = 2 →
    (∃ φ : MulAut (L ⧸ center L), φ * φ = MulAut.conj zbar ∧
      ∀ c ∈ centralizer ({zbar} : Set (L ⧸ center L)), Odd (orderOf c) → φ c = c) →
    (∀ α : MulAut (L ⧸ center L), ∃ q : L ⧸ center L, α zbar = q * zbar * q⁻¹) ∧
      Odd (centralizer ({zbar} : Set (L ⧸ center L))).index

section Model


theorem card_centralizer_of_fixCard_170 (z : ↥hsP) (hz : orderOf z = 2)
    (hf : fixCard (z : Equiv.Perm (Fin 3850)) = 170) :
    Nat.card (centralizer ({z} : Set ↥hsP)) = 7680 := by
  have hz' : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨g, hg, hzg⟩ := exists_conj_hsT1_of_fixCard z.2 hz' hf
  obtain ⟨-, -, hC1, -, -⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  have ht1 : hsT1 ∈ hsP := (mem_inf.1 HSStd.hsT1_mem_hsC1).1
  let t₁ : ↥hsP := ⟨hsT1, ht1⟩
  let g₁ : ↥hsP := ⟨g, hg⟩
  have hz1 : z = g₁ * t₁ * g₁⁻¹ := Subtype.ext hzg
  have hcent : centralizer ({z} : Set ↥hsP) =
      (centralizer ({t₁} : Set ↥hsP)).map (MulAut.conj g₁).toMonoidHom := by
    ext x
    rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨g₁⁻¹ * x * g₁, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      rw [mem_centralizer_singleton_iff]
      rw [hz1] at hx
      calc g₁⁻¹ * x * g₁ * t₁ = g₁⁻¹ * (x * (g₁ * t₁ * g₁⁻¹)) * g₁ := by group
        _ = g₁⁻¹ * ((g₁ * t₁ * g₁⁻¹) * x) * g₁ := by rw [hx]
        _ = t₁ * (g₁⁻¹ * x * g₁) := by group
    · rintro ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff] at hy
      rw [hz1]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g₁ * y * g₁⁻¹ * (g₁ * t₁ * g₁⁻¹) = g₁ * (y * t₁) * g₁⁻¹ := by group
        _ = g₁ * (t₁ * y) * g₁⁻¹ := by rw [hy]
        _ = g₁ * t₁ * g₁⁻¹ * (g₁ * y * g₁⁻¹) := by group
  have hmap : (centralizer ({t₁} : Set ↥hsP)).map hsP.subtype = hsC1 := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hyP, hyc⟩
      exact ⟨⟨y, hyP⟩, Subtype.ext hyc, rfl⟩
  rw [hcent, Subgroup.card_map_of_injective (MulAut.conj g₁).injective,
    ← Subgroup.card_map_of_injective hsP.subtype_injective, hmap]
  exact hC1

theorem odd_index_centralizer_of_fixCard_170 (z : ↥hsP) (hz : orderOf z = 2)
    (hf : fixCard (z : Equiv.Perm (Fin 3850)) = 170) :
    Odd (centralizer ({z} : Set ↥hsP)).index := by
  have h1 := Subgroup.index_mul_card (centralizer ({z} : Set ↥hsP))
  rw [card_centralizer_of_fixCard_170 z hz hf, card_hsP] at h1
  have : (centralizer ({z} : Set ↥hsP)).index = 5775 := by omega
  rw [this]
  decide

end Model

section Transport


theorem classFacts_of_equiv {L : Type} [Group L] (f : L ⧸ center L ≃* hsP) : ClassFacts L := by
  intro zbar hz ⟨φ, hφ2, hφ⟩
  set z : ↥hsP := f zbar with hzdef
  have hz' : orderOf z = 2 := by rw [hzdef, MulEquiv.orderOf_eq]; exact hz
  have hφ'2 : MulAut.congr f φ * MulAut.congr f φ = MulAut.conj z := by
    rw [← map_mul, hφ2, congr_conj]
  have hφ' : ∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → MulAut.congr f φ c = c := by
    intro c hc hodd
    have hc' : f.symm c ∈ centralizer ({zbar} : Set (L ⧸ center L)) := by
      have hc2 : c * f zbar = f zbar * c := by
        have := mem_centralizer_singleton_iff.1 hc
        simpa [hzdef] using this
      rw [mem_centralizer_singleton_iff]
      apply f.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc2
    have hodd' : Odd (orderOf (f.symm c)) := by rwa [MulEquiv.orderOf_eq]
    change f (φ (f.symm c)) = c
    rw [hφ _ hc' hodd', MulEquiv.apply_symm_apply]
  have hz170 : fixCard (z : Equiv.Perm (Fin 3850)) = 170 :=
    fixCard_eq_170_of_tight z hz' _ hφ'2 hφ'
  have hzP : orderOf (z : Equiv.Perm (Fin 3850)) = 2 := by rw [Subgroup.orderOf_coe]; exact hz'
  refine ⟨fun α => ?_, ?_⟩
  · obtain ⟨e, he, -⟩ := hs_full_automorphism_model
    obtain ⟨ρ, hρ⟩ := e.surjective (MulAut.congr f α)
    have h1 : ((MulAut.congr f α z : ↥hsP) : Equiv.Perm (Fin 3850)) =
        (ρ : Equiv.Perm (Fin 3850)) * z * (ρ : Equiv.Perm (Fin 3850))⁻¹ := by
      rw [← hρ]; exact he ρ z
    have h2 : fixCard ((MulAut.congr f α z : ↥hsP) : Equiv.Perm (Fin 3850)) = 170 := by
      rw [h1, fixCard_conj]; exact hz170
    have h3 : orderOf (MulAut.congr f α z : ↥hsP) = 2 := by
      rw [MulEquiv.orderOf_eq]; exact hz'
    have h3' : orderOf ((MulAut.congr f α z : ↥hsP) : Equiv.Perm (Fin 3850)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact h3
    obtain ⟨g₁, hg₁, hg₁e⟩ := exists_conj_hsT1_of_fixCard (MulAut.congr f α z).2 h3' h2
    obtain ⟨g₂, hg₂, hg₂e⟩ := exists_conj_hsT1_of_fixCard z.2 hzP hz170
    obtain ⟨h, hh⟩ := conj_of_perm_conj (a := MulAut.congr f α z) (b := z) hg₁ hg₂ hg₁e hg₂e
    refine ⟨f.symm h, ?_⟩
    apply f.injective
    have h4 : f (α zbar) = MulAut.congr f α z := by
      change f (α zbar) = f (α (f.symm z))
      rw [hzdef, MulEquiv.symm_apply_apply]
    rw [h4, hh, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · have hidx := odd_index_centralizer_of_fixCard_170 z hz' hz170
    have hmap : (centralizer ({zbar} : Set (L ⧸ center L))).map f.toMonoidHom =
        centralizer ({z} : Set ↥hsP) := by
      ext x
      rw [Subgroup.mem_map, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_centralizer_singleton_iff] at hy
        simp only [MulEquiv.coe_toMonoidHom, hzdef]
        rw [← map_mul, ← map_mul, hy]
      · intro hx
        refine ⟨f.symm x, ?_, by simp⟩
        rw [mem_centralizer_singleton_iff]
        apply f.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hx
    have h5 : (centralizer ({z} : Set ↥hsP)).index =
        (centralizer ({zbar} : Set (L ⧸ center L))).index := by
      rw [← hmap]; exact Subgroup.index_map_equiv _ f
    rw [← h5]
    exact hidx

theorem classFacts_of_isSporadic_hs
    {L : Type} [Group L] (hq : IsSporadic (L ⧸ center L) .HS) : ClassFacts L := by
  obtain ⟨ψ⟩ := hq
  have ψ' : L ⧸ center L ≃* NativeSporadic.HS := ψ
  exact classFacts_of_equiv (ψ'.trans hsPermEquiv)

end Transport

end CFSG.EvenSporadicStandard.TwoHS
