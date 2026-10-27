module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure Ctx (G L : Subgroup (GLV V)) (z : GLV V) (v : V) (H₁ : Subgroup (GLV V))
    (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : Prop where
  std : StdForm G L z
  rank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1
  hv : v ∈ commSpace (Subgroup.zpowers z) ⊤
  data : CaseIIData G L z v H₁ ψ

abbrev HH (G L : Subgroup (GLV V)) (v : V) : Subgroup (GLV V) :=
  normalClosure (layerIn (G ⊓ vFix v)) L

abbrev KK (G L : Subgroup (GLV V)) : Subgroup (GLV V) :=
  G ⊓ Subgroup.centralizer (L : Set (GLV V))

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem omega_le_O : omegaMinusTwo 2 ≤ orthogonalMinus 2 (ZMod 2) 1 1 :=
  Subgroup.commutator_le_self _

theorem conj_mem_omega {o w : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (ho : o ∈ orthogonalMinus 2 (ZMod 2) 1 1) (hw : w ∈ omegaMinusTwo 2) :
    o * w * o⁻¹ ∈ omegaMinusTwo 2 := by
  have hmap := Subgroup.map_subtype_commutator (orthogonalMinus 2 (ZMod 2) 1 1)
  have hw2 : w ∈ (commutator ↥(orthogonalMinus 2 (ZMod 2) 1 1)).map
      (orthogonalMinus 2 (ZMod 2) 1 1).subtype := hmap ▸ hw
  obtain ⟨w', hw', hw'w⟩ := hw2
  have hn : (commutator ↥(orthogonalMinus 2 (ZMod 2) 1 1)).Normal := inferInstance
  have hc := hn.conj_mem w' hw' ⟨o, ho⟩
  have : o * w * o⁻¹ =
      (orthogonalMinus 2 (ZMod 2) 1 1).subtype (⟨o, ho⟩ * w' * ⟨o, ho⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← hw'w]
    rfl
  rw [this]
  have h2 := Subgroup.mem_map_of_mem (orthogonalMinus 2 (ZMod 2) 1 1).subtype hc
  rw [hmap] at h2
  exact h2

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem H₁_le_G : H₁ ≤ G := c.data.le.trans inf_le_left

theorem mem_H_iff {x : GLV V} (hx : x ∈ H₁) :
    x ∈ HH G L v ↔
      ((ψ ⟨x, hx⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) ∈
        omegaMinusTwo 2 := by
  show x ∈ normalClosure (layerIn (G ⊓ vFix v)) L ↔ _
  rw [← c.data.ψ_H]
  constructor
  · rintro ⟨h, hh, hhx⟩
    have hh' : h = ⟨x, hx⟩ := Subtype.ext hhx
    subst hh'
    simpa [Subgroup.mem_subgroupOf] using hh
  · intro hψ
    exact ⟨⟨x, hx⟩, by simpa [Subgroup.mem_subgroupOf] using hψ, rfl⟩

theorem H_le : HH G L v ≤ H₁ := by
  show normalClosure (layerIn (G ⊓ vFix v)) L ≤ H₁
  rw [← c.data.ψ_H]
  exact Subgroup.map_subtype_le _

theorem H_le_G : HH G L v ≤ G := c.H_le.trans c.H₁_le_G

theorem L_le_H : L ≤ HH G L v := le_normalClosure _ _

theorem L_le_G : L ≤ G := c.L_le_H.trans c.H_le_G

theorem z_mem : z ∈ H₁ := c.data.z_mem

theorem z_mem_G : z ∈ G := c.H₁_le_G c.z_mem

theorem orderOf_z : orderOf z = 2 := c.std.orderOf_s

theorem z_mul_z : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [c.orderOf_z, sq] at h
  exact h

theorem comm_z {l : GLV V} (hl : l ∈ L) : l * z = z * l := by
  have h := (c.std.extremal.setup.component.1 hl).2
  exact (Subgroup.mem_centralizer_iff.1 h z (Subgroup.mem_zpowers z)).symm

theorem z_mem_K : z ∈ KK G L :=
  ⟨c.z_mem_G, Subgroup.mem_centralizer_iff.2 fun l hl => c.comm_z hl⟩

theorem conj_mem_H {h x : GLV V} (hh : h ∈ H₁) (hx : x ∈ HH G L v) :
    h * x * h⁻¹ ∈ HH G L v := by
  have hx₁ : x ∈ H₁ := c.H_le hx
  have hm : h * x * h⁻¹ ∈ H₁ := H₁.mul_mem (H₁.mul_mem hh hx₁) (H₁.inv_mem hh)
  rw [c.mem_H_iff hm]
  have e : ψ ⟨h * x * h⁻¹, hm⟩ = ψ ⟨h, hh⟩ * ψ ⟨x, hx₁⟩ * (ψ ⟨h, hh⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [e]
  exact conj_mem_omega (ψ ⟨h, hh⟩).2 ((c.mem_H_iff hx₁).1 hx)

@[expose] noncomputable def phiHom : ↥(HH G L v) →* ↥(omegaMinusTwo 2) where
  toFun h := ⟨ψ ⟨h, c.H_le h.2⟩, (c.mem_H_iff (c.H_le h.2)).1 h.2⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    have : (⟨1, c.H_le (HH G L v).one_mem⟩ : ↥H₁) = 1 := rfl
    rw [this, map_one]
    rfl
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have : (⟨(a : GLV V) * b, c.H_le (a * b).2⟩ : ↥H₁) =
        ⟨a, c.H_le a.2⟩ * ⟨b, c.H_le b.2⟩ := rfl
    rw [this, map_mul]
    rfl

theorem phiHom_coe (h : ↥(HH G L v)) :
    ((c.phiHom h : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
      ((ψ ⟨h, c.H_le h.2⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
        GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := rfl

theorem phiHom_bijective : Function.Bijective c.phiHom := by
  constructor
  · intro a b hab
    have h1 : (ψ ⟨a, c.H_le a.2⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) = ψ ⟨b, c.H_le b.2⟩ := by
      apply Subtype.ext
      have := congrArg Subtype.val hab
      rwa [phiHom_coe, phiHom_coe] at this
    have h2 := ψ.injective h1
    exact Subtype.ext (Subtype.mk.inj h2)
  · intro w
    obtain ⟨h, hh⟩ := ψ.surjective ⟨w, omega_le_O w.2⟩
    have hH : (h : GLV V) ∈ HH G L v := by
      rw [c.mem_H_iff h.2]
      have : ψ ⟨h, h.2⟩ = ⟨w, omega_le_O w.2⟩ := hh
      rw [this]
      exact w.2
    refine ⟨⟨h, hH⟩, Subtype.ext ?_⟩
    rw [phiHom_coe]
    exact congrArg Subtype.val hh

@[expose] noncomputable def phi : ↥(HH G L v) ≃* ↥(omegaMinusTwo 2) :=
  MulEquiv.ofBijective c.phiHom c.phiHom_bijective

theorem phi_coe (h : ↥(HH G L v)) :
    ((c.phi h : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
      ((ψ ⟨h, c.H_le h.2⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
        GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := rfl

theorem split (hs : CaseIISplit) : IsCompl (commSpace (HH G L v) ⊤) (fixedSpace (HH G L v)) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := c.data.natural
  exact hs V (HH G L v) c.phi β hβs hβk fun h w w' hw => by
    rw [phi_coe]
    exact hβe ⟨h, c.H_le h.2⟩ w w' hw

end Ctx

end CaseII

end CFSG.CGT.Foote82
