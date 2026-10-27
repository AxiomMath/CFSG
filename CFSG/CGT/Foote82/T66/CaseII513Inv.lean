module

public import CFSG.CGT.Foote82.T66.CaseIICent
public import CFSG.CGT.Foote82.T66.CaseIIRho

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem orderOf_conj_z (x : GLV V) : orderOf (x * z * x⁻¹) = 2 := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, c.orderOf_z]

theorem orderOf_phi_conj {x : GLV V} (hxH : x * z * x⁻¹ ∈ HH G L v) :
    orderOf ((c.phi ⟨x * z * x⁻¹, hxH⟩ : ↥(omegaMinusTwo 2)) : GL I6 (ZMod 2)) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, c.orderOf_conj_z]

theorem card_ne_576 (hs : CaseIISplit) (hG9 : CaseIIG9) {x : GLV V} (hxG : x ∈ G)
    (hxH : x * z * x⁻¹ ∈ HH G L v) :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer
      {((c.phi ⟨x * z * x⁻¹, hxH⟩ : ↥(omegaMinusTwo 2)) : GL I6 (ZMod 2))}) ≠ 576 := by
  intro h576
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, β, ad⟩ := c.exists_ad hs
  have hL := c.data.L_iso
  set y : ↥(HH G L v) := ⟨x * z * x⁻¹, hxH⟩ with hy
  set w : GL I6 (ZMod 2) := ((c.phi y : ↥(omegaMinusTwo 2)) : GL I6 (ZMod 2)) with hw
  set C := omegaMinusTwo 2 ⊓ Subgroup.centralizer ({w} : Set (GL I6 (ZMod 2))) with hC
  have hwC : w ∈ C := ⟨(c.phi y).2, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  let e₂ : ↥C →* GLV V := (MulAut.conj x⁻¹).toMonoidHom.comp ((HH G L v).subtype.comp
    (c.phi.symm.toMonoidHom.comp (Subgroup.inclusion (inf_le_left : C ≤ omegaMinusTwo 2))))
  have he₂ : ∀ a : ↥C, e₂ a =
      x⁻¹ * ((c.phi.symm ⟨a, a.2.1⟩ : ↥(HH G L v)) : GLV V) * x := by
    intro a
    simp only [e₂, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    rfl
  have he₂i : Function.Injective e₂ := by
    intro a b hab
    rw [he₂, he₂] at hab
    have h1 : ((c.phi.symm ⟨a, a.2.1⟩ : ↥(HH G L v)) : GLV V) =
        ((c.phi.symm ⟨b, b.2.1⟩ : ↥(HH G L v)) : GLV V) := by
      simpa using hab
    have h2 := c.phi.symm.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hCz : ∀ a : ↥C, e₂ a ∈ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) := by
    intro a
    rw [he₂]
    set h := (c.phi.symm ⟨a, a.2.1⟩ : ↥(HH G L v)) with hh
    have hhG : (h : GLV V) ∈ G := c.H_le_G h.2
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hxG) hhG) hxG, ?_⟩
    show x⁻¹ * ↑h * x ∈ Subgroup.centralizer ({z} : Set (GLV V))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : h * y = y * h := by
      apply c.phi.injective
      rw [map_mul, map_mul, hh, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      have ha : (a : GL I6 (ZMod 2)) * w = w * a :=
        (Subgroup.mem_centralizer_singleton_iff.1 a.2.2)
      simpa [hw] using ha
    have hc : (h : GLV V) * (x * z * x⁻¹) = (x * z * x⁻¹) * h := congrArg Subtype.val hcomm
    calc x⁻¹ * ↑h * x * z = x⁻¹ * (↑h * (x * z * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * z * x⁻¹) * ↑h) * x := by rw [hc]
      _ = z * (x⁻¹ * ↑h * x) := by group
  let e₁ : ↥C →* ↥(Subgroup.normalizer (L : Set (GLV V))) :=
    e₂.codRestrict _ fun a => c.centralizer_le_normalizer (hCz a)
  have he₁ : ∀ a : ↥C, ((e₁ a : ↥(Subgroup.normalizer (L : Set (GLV V)))) : GLV V) = e₂ a :=
    fun a => rfl
  let f := (ad.rho hL).comp e₁
  have hfy : f ⟨w, hwC⟩ = 1 := by
    show ad.rho hL (e₁ ⟨w, hwC⟩) = 1
    rw [ad.rho_eq_one_iff hL, he₁, he₂]
    have e : ((c.phi.symm ⟨w, (⟨w, hwC⟩ : ↥C).2.1⟩ : ↥(HH G L v)) : GLV V) = x * z * x⁻¹ := by
      have : (⟨w, (⟨w, hwC⟩ : ↥C).2.1⟩ : ↥(omegaMinusTwo 2)) = c.phi y := rfl
      rw [this, MulEquiv.symm_apply_apply]
    rw [e, show x⁻¹ * (x * z * x⁻¹) * x = z by group]
    exact c.z_mem_K.2
  have hw2 : orderOf w = 2 := c.orderOf_phi_conj hxH
  have hker := hG9 w hwC hw2 h576 f hfy
  have hle : f.ker.map e₂ ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨(hCz a).1, ?_⟩
    have h1 : ad.rho hL (e₁ a) = 1 := ha
    rw [ad.rho_eq_one_iff hL, he₁] at h1
    exact h1
  have h1 := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) e₂ he₂i f.ker
  have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hle
  rw [c.rank] at h2
  omega

theorem conj_of_inv (hs : CaseIISplit) (hG1 : CaseIIG1) (hG9 : CaseIIG9) (hG12 : CaseIIG12)
    {x : GLV V} (hxG : x ∈ G) (hxH : x * z * x⁻¹ ∈ HH G L v) {ℓ : GLV V} (hℓ : ℓ ∈ L)
    (hℓ2 : orderOf ℓ = 2) : ∃ y ∈ G, ℓ = y * z * y⁻¹ := by
  have h576 := c.card_ne_576 hs hG9 hxG hxH
  set y : ↥(HH G L v) := ⟨x * z * x⁻¹, hxH⟩ with hy
  set w : GL I6 (ZMod 2) := ((c.phi y : ↥(omegaMinusTwo 2)) : GL I6 (ZMod 2)) with hw
  have hw2 : orderOf w = 2 := c.orderOf_phi_conj hxH
  have hℓH : ℓ ∈ HH G L v := c.L_le_H hℓ
  have hx' : psiGL ψ ⟨ℓ, c.L_le_H₁ hℓ⟩ ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer
      {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))},
      omegaMinusTwo 2 ⊓ Subgroup.centralizer
      {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))}⁆ := by
    rw [c.XL_eq hG1, c.mem_XL_iff]
    exact ⟨ℓ, hℓ, rfl⟩
  have hx'2 : orderOf (psiGL ψ ⟨ℓ, c.L_le_H₁ hℓ⟩) = 2 := by
    rw [orderOf_injective _ psiGL_injective, Subgroup.orderOf_mk, hℓ2]
  obtain ⟨g', hg'Ω, hg'⟩ := hG12 _ (ψ ⟨z, c.z_mem⟩).2 c.orderOf_psi_z c.data.ψ_z w (c.phi y).2
    hw2 h576 _ hx' hx'2
  set h' : ↥(HH G L v) := c.phi.symm ⟨g', hg'Ω⟩ with hh'
  refine ⟨h' * x, G.mul_mem (c.H_le_G h'.2) hxG, ?_⟩
  have key : h' * y * h'⁻¹ = ⟨ℓ, hℓH⟩ := by
    apply c.phi.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, hh', MulEquiv.apply_symm_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hw, hg', c.phi_coe]
    rfl
  have key' := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy] at key'
  rw [← key']
  group

end Ctx

end CaseII

end CFSG.CGT.Foote82
