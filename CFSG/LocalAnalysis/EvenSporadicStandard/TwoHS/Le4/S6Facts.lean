module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Cover

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier

@[expose] def TightCoverFacts (L : Type) [Group L] : Prop :=
  ∀ zbar : L ⧸ center L, orderOf zbar = 2 →
    (∃ φ : MulAut (L ⧸ center L), φ * φ = MulAut.conj zbar ∧
      ∀ c ∈ centralizer ({zbar} : Set (L ⧸ center L)), Odd (orderOf c) → φ c = c) →
    (∀ l : L, (l : L ⧸ center L) = zbar → l * l = 1) ∧
      ∃ w : L ⧸ center L, w * w = zbar ∧
        (∀ φ : MulAut (L ⧸ center L), φ * φ = MulAut.conj zbar →
          (∀ c ∈ centralizer ({zbar} : Set (L ⧸ center L)), Odd (orderOf c) → φ c = c) →
            φ = MulAut.conj w ∨ φ = MulAut.conj w⁻¹) ∧
        ∃ x p : L, x * x = 1 ∧ (∀ l : L, (l : L ⧸ center L) = zbar → x * l = l * x) ∧
          (x : L ⧸ center L) * w * (x : L ⧸ center L)⁻¹ = w⁻¹ ∧
          (x : L ⧸ center L) = (p : L ⧸ center L) * zbar * (p : L ⧸ center L)⁻¹ ∧
          ∀ l : L, (l : L ⧸ center L) = w → x * l * (x * l) ≠ 1

theorem congr_conj {A B : Type*} [Group A] [Group B] (f : A ≃* B) (a : A) :
    MulAut.congr f (MulAut.conj a) = MulAut.conj (f a) := by
  ext b
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem tightCoverFacts_of_isSporadic_hs
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] (hZ : Nat.card (center L) = 2)
    (hq : IsSporadic (L ⧸ center L) .HS) : TightCoverFacts L := by
  obtain ⟨ψ⟩ := hq
  have ψ' : L ⧸ center L ≃* NativeSporadic.HS := ψ
  let f : L ⧸ center L ≃* hsP := ψ'.trans hsPermEquiv
  let q : L →* hsP := f.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hqs : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    ext x
    simp only [MonoidHom.mem_ker, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  have hqf : ∀ l : L, q l = f (l : L ⧸ center L) := fun l => rfl
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
  obtain ⟨hlift, w', hww, huniq, x, p, hxx, hxcomm, hxw, hxp, hxwl⟩ :=
    s6_cover_data hqs hker hZ z hz' hz170
  refine ⟨fun l hl => hlift l (by rw [hqf, hl]), f.symm w', ?_, ?_, x, p, hxx, ?_, ?_, ?_, ?_⟩
  · apply f.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hww, hzdef]
  · intro φ₁ h1 h2
    have h1' : MulAut.congr f φ₁ * MulAut.congr f φ₁ = MulAut.conj z := by
      rw [← map_mul, h1, congr_conj]
    have h2' : ∀ c ∈ centralizer ({z} : Set ↥hsP), Odd (orderOf c) → MulAut.congr f φ₁ c = c := by
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
      change f (φ₁ (f.symm c)) = c
      rw [h2 _ hc' hodd', MulEquiv.apply_symm_apply]
    rcases huniq _ h1' h2' with h | h
    · left
      apply (MulAut.congr f).injective
      rw [h, congr_conj, MulEquiv.apply_symm_apply]
    · right
      apply (MulAut.congr f).injective
      have hinv : f ((f.symm w')⁻¹) = w'⁻¹ := by rw [map_inv, MulEquiv.apply_symm_apply]
      rw [h, congr_conj, hinv]
  · intro l hl
    exact hxcomm l (by rw [hqf, hl])
  · apply f.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hxw
  · apply f.injective
    rw [map_mul, map_mul, map_inv]
    exact hxp
  · intro l hl
    exact hxwl l (by rw [hqf, hl, MulEquiv.apply_symm_apply])

end CFSG.EvenSporadicStandard.TwoHS
