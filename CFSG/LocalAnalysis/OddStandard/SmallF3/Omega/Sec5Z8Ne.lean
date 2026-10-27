module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5z8_sq_ne (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (hSq : Asc82FactSqReflQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    {t' y : G} (ht' : t' ∈ conjClassIn (centralizer ({z} : Set G)) t) (ht'S : t' ∈ S)
    (hne : t' ≠ t) (hyS : y ∈ S) : y * y ≠ t' ∧ y * y ≠ t' * z := by
  have ht'0 : t' ∈ conjClassIn (centralizer ({z} : Set G)) t := ht'
  obtain ⟨k, hk, hkt⟩ := ht'
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hk
  have htz : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 h.mem_S)).symm
  have hz' : k * z * k⁻¹ = z := by rw [hkz]; group
  have hz'' : k⁻¹ * z * k = z := by
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [hkz]
      _ = z := by group
  have ht'z : t' * z = z * t' := by
    calc t' * z = (k * t * k⁻¹) * (k * z * k⁻¹) := by rw [hkt, hz']
      _ = k * (t * z) * k⁻¹ := by group
      _ = k * (z * t) * k⁻¹ := by rw [htz]
      _ = (k * z * k⁻¹) * (k * t * k⁻¹) := by group
      _ = z * t' := by rw [hz', hkt]
  have ht'c : t' * t = t * t' :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 ht'S)
  have ht'C : t' ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ht'c
  have hkt' : (k⁻¹)⁻¹ * t * k⁻¹ = t' := by rw [inv_inv, ← hkt]
  have ht'2 : orderOf t' = 2 := by
    rw [hkt]
    rw [show k * t * k⁻¹ = (k⁻¹)⁻¹ * t * k⁻¹ by rw [inv_inv]]
    rw [orderOf_conjugate_eq, h.involution]
  have ht't'1 : t' * t' = 1 := by
    have h1 := pow_orderOf_eq_one t'
    rwa [ht'2, pow_two] at h1
  have hty : ∃ α : ℤˣ, InducesTypeSome L t' 6 (-1) 1 α := by
    rcases h55 G t L S z h.toSec5Ctx with h5 | h5
    · exact absurd h5 h.nconj
    · have h5' := h5 (k⁻¹) (by rw [hkt']; exact ht'C)
        (by rw [hkt']; exact hne)
      rwa [hkt'] at h5'
  have ht'N : t' ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB t' ht'C
  have hQ := hs.pk.q
  have ht'Q : t' ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) :=
    sec5z_conj_cent_le_centralizer hy h55 h58d hFB h4 h.toSec5Ctx h.nconj hQ ht'0 ht'c
  have hyN : y ∈ normalizer (L : Set G) := sec5p510_S_le_normalizer hy h.toSec5Ctx hyS
  have hyz : y * z = z * y := h.central y hyS
  exact hSq G L z h.toSec5Setting.isOm6Z2 h.pocket (twoCoreIn K₁) (twoCoreIn K₂)
    hQ.le₁ hQ.le₂ hQ.iso₁ hQ.iso₂ hQ.comm hQ.card hQ.center hQ.not_central t' ht'N ht't'1
    ht'z hty ht'Q y hyN hyz

end CFSG.OddStandard.SmallF3.Omega
