module

public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.KGroups.TwoA7Cyclic

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem cyclic_cent_quaternion4 : ∀ y : QuaternionGroup 4, y * y ≠ 1 →
    ∃ g : QuaternionGroup 4, g * y = y * g ∧ ∀ x : QuaternionGroup 4, x * y = y * x →
      ∃ k : Fin 16, g ^ (k : ℕ) = x := by
  decide +kernel

section NotF

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem cyclic_of_centralizing
    (h : IsDoubleCoverA7 π z) {c : E} (hcsq : c * c ≠ 1)
    {R : Subgroup E} (hR : IsPGroup 2 R) (hcR : c ∈ R) (hRc : ∀ x ∈ R, x * c = c * x) :
    IsCyclic R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨eP⟩ := sylow_quaternion h P
  set y : QuaternionGroup 4 := eP ⟨c, hRP hcR⟩ with hy
  have hysq : y * y ≠ 1 := by
    intro h1
    apply hcsq
    have := eP.injective (by rw [map_mul, map_one]; exact h1 :
      eP (⟨c, hRP hcR⟩ * ⟨c, hRP hcR⟩ : ↥(P : Subgroup E)) = eP 1)
    exact congrArg Subtype.val this
  obtain ⟨g, hgy, hg⟩ := cyclic_cent_quaternion4 y hysq
  have hmem : ∀ x : ↥R, eP (Subgroup.inclusion hRP x) ∈ Subgroup.zpowers g := by
    intro x
    have hcomm : eP (Subgroup.inclusion hRP x) * y = y * eP (Subgroup.inclusion hRP x) := by
      rw [hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hRc x x.2)
    obtain ⟨k, hk⟩ := hg _ hcomm
    exact ⟨(k : ℤ), by simpa using hk⟩
  let f : ↥R →* ↥(Subgroup.zpowers g) :=
    ((eP.toMonoidHom.comp (Subgroup.inclusion hRP)).codRestrict (Subgroup.zpowers g) hmem)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : eP (Subgroup.inclusion hRP a) = eP (Subgroup.inclusion hRP b) :=
      congrArg Subtype.val hab
    exact Subgroup.inclusion_injective hRP (eP.injective h1)
  exact isCyclic_of_injective f hf

theorem cyclic_two_subgroup_centralizer
    (h : IsDoubleCoverA7 π z) {c : E}
    (hc2 : IsPGroup 2 (zpowers c)) (hcsq : c * c ≠ 1) {R : Subgroup E} (hR : IsPGroup 2 R)
    (hRc : ∀ x ∈ R, x * c = c * x) : IsCyclic R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xc : Subgroup E := Subgroup.centralizer ({c} : Set E) with hXc
  have hle : R ≤ Xc := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hRc x hx)
  have hcX : c ∈ Xc := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set cX : ↥Xc := ⟨c, hcX⟩ with hcXdef
  have hRb : IsPGroup 2 (R.subgroupOf Xc) :=
    IsPGroup.of_surjective hR (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  obtain ⟨S, hRS⟩ := hRb.exists_le_sylow
  have hcen : cX ∈ Subgroup.center ↥Xc := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hzn : (Subgroup.zpowers cX).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hcen)
  have hz2 : IsPGroup 2 (Subgroup.zpowers cX) := by
    have hcard : Nat.card (Subgroup.zpowers cX) = Nat.card (Subgroup.zpowers c) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hcXdef, Subgroup.orderOf_mk]
    obtain ⟨n, hn⟩ := hc2.exists_card_eq
    exact IsPGroup.of_card (by rw [hcard, hn])
  have hcS : cX ∈ (S : Subgroup ↥Xc) := hz2.le_sylow_of_normal S (Subgroup.mem_zpowers cX)
  set S' : Subgroup E := (S : Subgroup ↥Xc).map Xc.subtype with hS'
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map Xc.subtype
  have hcS' : c ∈ S' := ⟨cX, hcS, rfl⟩
  have hS'c : ∀ x ∈ S', x * c = c * x := by
    rintro _ ⟨x, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 x.2
  have hcyc : IsCyclic S' := cyclic_of_centralizing h hcsq hS'2 hcS' hS'c
  have hRS' : R ≤ S' := fun x hx => ⟨⟨x, hle hx⟩, hRS hx, rfl⟩
  exact isCyclic_of_injective (Subgroup.inclusion hRS') (Subgroup.inclusion_injective hRS')

theorem cyclic_sylow_of_centralizing
    (h : IsDoubleCoverA7 π z) {c : E}
    (hc2 : IsPGroup 2 (zpowers c)) (hcsq : c * c ≠ 1) (X : Subgroup E)
    (hXc : ∀ x ∈ X, x * c = c * x) (R : Sylow 2 ↥X) :
    IsCyclic ↥(R : Subgroup ↥X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (R.map X.subtype) := R.isPGroup'.map X.subtype
  have hcyc := cyclic_two_subgroup_centralizer h hc2 hcsq hR2 (by
    rintro _ ⟨x, -, rfl⟩
    exact hXc x x.2)
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective (R : Subgroup ↥X) X.subtype X.subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective (R : Subgroup ↥X) X.subtype X.subtype_injective).injective

omit [Finite E] in
theorem fixed_conj_comm (c : E) : ∀ x ∈ fixedSubgroup E (MulAut.conj c), x * c = c * x := by
  intro x hx
  have h1 : MulAut.conj c x = x := hx
  rw [MulAut.conj_apply] at h1
  calc x * c = (c * x * c⁻¹) * c := by rw [h1]
    _ = c * x := by group

theorem conj1
    (h : IsDoubleCoverA7 π z) (hcen : ∀ w : E, w ∈ Subgroup.center E ↔ (w = 1 ∨ w = z))
    (c : E) (hc : c ∉ Subgroup.center E) :
    ¬ IsFAutomorphism E (MulAut.conj c) := by
  intro hf
  obtain ⟨-, -, -, ⟨k, hk⟩, hcomp⟩ := hf
  have hc2 := isPGroup_zpowers_of_orderOf_conj h hk
  have hcsq : c * c ≠ 1 := by
    intro h1
    exact hc ((hcen c).2 (h.eq_one_or_eq_z_of_sq_eq_one h1))
  exact not_components_of_cyclic_sylow
    (fun R => cyclic_sylow_of_centralizing h hc2 hcsq _ (fixed_conj_comm c) R) hcomp

theorem conj2
    (h : IsDoubleCoverA7 π z) (hcen : ∀ w : E, w ∈ Subgroup.center E ↔ (w = 1 ∨ w = z))
    (φ : MulAut E) (hf : IsFAutomorphism E φ) : φ * φ = 1 := by
  by_contra hφ
  obtain ⟨-, -, -, ⟨k, hk⟩, hcomp⟩ := hf
  have hsq : h.autPerm φ * h.autPerm φ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]
  obtain ⟨q, hq⟩ := h.surjective ⟨_, hsq⟩
  have hqφ : MulAut.conj q = φ * φ := by
    apply h.autPerm_injective
    rw [autPerm_conj, map_mul, hq]
  have hqz : q ∉ Subgroup.center E := by
    intro hqc
    apply hφ
    rw [← hqφ]
    ext x
    have := Subgroup.mem_center_iff.1 hqc x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← this, mul_inv_cancel_right]
  have hqord : ∃ j : ℕ, orderOf (MulAut.conj q) = 2 ^ j := by
    have h1 : (MulAut.conj q) ^ (2 ^ k) = 1 := by
      rw [hqφ, ← pow_two, ← pow_mul, mul_comm, pow_mul, ← hk, pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hqord
  have hq2 := isPGroup_zpowers_of_orderOf_conj h hj
  have hqsq : q * q ≠ 1 := by
    intro h1
    exact hqz ((hcen q).2 (h.eq_one_or_eq_z_of_sq_eq_one h1))
  have hXq : ∀ x ∈ fixedSubgroup E φ, x * q = q * x := by
    intro x hx
    have h1 : φ x = x := hx
    have h2 : MulAut.conj q x = x := by
      rw [hqφ, MulAut.mul_apply, h1, h1]
    rw [MulAut.conj_apply] at h2
    calc x * q = (q * x * q⁻¹) * q := by rw [h2]
      _ = q * x := by group
  exact not_components_of_cyclic_sylow
    (fun R => cyclic_sylow_of_centralizing h hq2 hqsq _ hXq R) hcomp

theorem conj6
    (h : IsDoubleCoverA7 π z) (hcen : ∀ w : E, w ∈ Subgroup.center E ↔ (w = 1 ∨ w = z))
    (c : E) (hc : c ∉ Subgroup.center E) (hcc : c * c ∈ Subgroup.center E)
    (W : Subgroup E) (hW : IsPGroup 2 W) (hWc : ∀ w ∈ W, c * w = w * c) : IsCyclic W := by
  have hcsq : c * c ≠ 1 := by
    intro h1
    exact hc ((hcen c).2 (h.eq_one_or_eq_z_of_sq_eq_one h1))
  have hcz : c * c = z := by
    rcases (hcen _).1 hcc with h1 | h1
    · exact absurd h1 hcsq
    · exact h1
  have h4 : c ^ (2 ^ 2) = 1 := by
    have h4' : c ^ 4 = 1 := by
      calc c ^ 4 = c ^ 2 * c ^ 2 := by rw [← pow_add]
        _ = (c * c) * (c * c) := by rw [pow_two]
        _ = 1 := by rw [hcz]; exact h.sq_eq_one
    simpa using h4'
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h4)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  exact cyclic_two_subgroup_centralizer h hc2 hcsq hW (fun x hx => (hWc x hx).symm)

end NotF

end CFSG.GH74.KGroups.TwoA7
