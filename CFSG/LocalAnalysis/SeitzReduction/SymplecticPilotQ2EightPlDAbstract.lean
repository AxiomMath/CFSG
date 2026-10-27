module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEAbstract

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup

section ConjL

variable {G Mg Mn H : Type*} [Group G] [Group Mg] [Group Mn] [Group H] {ι : Type*}
  (ext : ι → Mn →* Mg) (Φ : ι → Mn →* G) (iota : H →* Mg) (ε : H →* G)

@[expose] noncomputable def plDConjL {P : Type*} [Group P] (k : ι) (g' : Mn)
    (hiota : Function.Injective iota) (p : P →* Mg)
    (hp : ∀ x, (ext k g')⁻¹ * p x * ext k g' ∈ iota.range) : P →* G :=
  (MulAut.conj (Φ k g')).toMonoidHom.comp (ε.comp
    ((MonoidHom.ofInjective hiota).symm.toMonoidHom.comp
      (((MulAut.conj (ext k g')⁻¹).toMonoidHom.comp p).codRestrict _ fun x => by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv] using hp x)))

variable {ext Φ iota ε}

theorem plDConjL_apply {P : Type*} [Group P] {k : ι} {g' : Mn} (hiota : Function.Injective iota)
    {p : P →* Mg} (hp : ∀ x, (ext k g')⁻¹ * p x * ext k g' ∈ iota.range) (x : P) {h : H}
    (hh : iota h = (ext k g')⁻¹ * p x * ext k g') :
    plDConjL ext Φ iota ε k g' hiota p hp x = Φ k g' * ε h * (Φ k g')⁻¹ := by
  have h1 : (MonoidHom.ofInjective hiota).symm
      ((((MulAut.conj (ext k g')⁻¹).toMonoidHom.comp p).codRestrict _ fun x => by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv] using hp x) x) = h := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, hh]
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  simp only [plDConjL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h1]

theorem plDConjL_one_value {k : ι} (h : H) : Φ k 1 * ε h * (Φ k 1)⁻¹ = ε h := by
  rw [map_one, one_mul, inv_one, mul_one]

theorem plDConjL_value_comm (hA : PEAligned ext Φ) (hN : PENormal ext Φ iota ε)
    (hiota : Function.Injective iota) {k : ι} {g' z' : Mn} {h h₀ : H}
    (hz : ext k z' = iota h₀) (hcomm : ext k g' * ext k z' = ext k z' * ext k g')
    (hh : iota h = (ext k g')⁻¹ * ext k z' * ext k g') :
    Φ k g' * ε h * (Φ k g')⁻¹ = ε h₀ := by
  have hhh : h = h₀ := by
    apply hiota
    rw [hh, ← hz, mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hz1 : Φ k z' = ε h₀ := hN k z' h₀ hz
  have hconj : ext k (g' * z' * g'⁻¹) = ext k z' := by
    rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]
  have h2 : Φ k (g' * z' * g'⁻¹) = Φ k z' := hA k k _ _ hconj
  rw [hhh, ← hz1, ← map_inv, ← map_mul, ← map_mul, h2]

theorem plDConjL_value_trans (hA : PEAligned ext Φ) (hN : PENormal ext Φ iota ε) {k i : ι}
    {y : H} (hy : iota y ∈ (ext k).range) {g' m_g m_z : Mn} {h : H} {z : Mg}
    (hg : ext i m_g = (iota y)⁻¹ * ext k g' * iota y) (hh : iota h = (ext k g')⁻¹ * z * ext k g')
    (hz : ext i m_z = (iota y)⁻¹ * z * iota y) :
    Φ k g' * ε h * (Φ k g')⁻¹ = ε y * Φ i m_z * (ε y)⁻¹ := by
  have hagree : ε 1 * Φ k g' * (ε 1)⁻¹ = ε y * Φ i m_g * (ε y)⁻¹ := by
    refine peTrans_value_eq hA hN (i := k) (i' := i) (y := 1) (y' := y) ?_ (x := ext k g') ?_ hg
    · rw [inv_one, one_mul]
      exact hy
    · rw [map_one, inv_one, one_mul, mul_one]
  rw [map_one, one_mul, inv_one, mul_one] at hagree
  have hmh : ext i (m_g⁻¹ * m_z * m_g) = (iota y)⁻¹ * iota h * iota y := by
    rw [map_mul, map_mul, map_inv, hg, hz, hh]
    group
  have hN1 : ε y * Φ i (m_g⁻¹ * m_z * m_g) * (ε y)⁻¹ = ε h :=
    peTrans_value_iota hN hmh
  rw [← hN1, hagree, map_mul, map_mul, map_inv]
  group

end ConjL

end CFSG.SeitzReduction.SymplecticPilot
