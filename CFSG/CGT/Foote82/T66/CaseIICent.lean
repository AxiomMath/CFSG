module

import CFSG.LargeExtraspecial.S5Comp
import CFSG.HardMathSupport.Dickson.Bal207.D42Triality
public import CFSG.CGT.Foote82.T66.CaseIIU

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

section General

variable {Γ : Type*} [Group Γ]

theorem card_sup_mul_card_inf [Finite Γ] {A B : Subgroup Γ}
    (h : A ≤ Subgroup.normalizer (B : Set Γ)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  set N := Subgroup.normalizer (B : Set Γ) with hN
  have hB : B ≤ N := Subgroup.le_normalizer
  have hAB : A ⊔ B ≤ N := sup_le h hB
  have h1 := Subgroup.relIndex_sup_right (H := A.subgroupOf N) (K := B.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := B.subgroupOf N)
    (K := A.subgroupOf N ⊔ B.subgroupOf N)
  have h3 := Subgroup.relIndex_mul_card (H := B.subgroupOf N) (K := A.subgroupOf N)
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  have eA : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have eB : Nat.card ↥(B.subgroupOf N) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have eAB : Nat.card ↥(A.subgroupOf N ⊔ B.subgroupOf N) = Nat.card ↥(A ⊔ B) := by
    rw [← Subgroup.subgroupOf_sup h hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have eI : Nat.card ↥(B.subgroupOf N ⊓ A.subgroupOf N) = Nat.card ↥(A ⊓ B) := by
    have : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h)).toEquiv
  rw [eAB, eB] at h2
  rw [eI, eA] at h3
  rw [← h2, ← h3]
  ring

theorem map_conj_eq_self {M : Subgroup Γ} {x : Γ} (hx : x ∈ M) :
    M.map (MulAut.conj x).toMonoidHom = M := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    show x * m * x⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hx hm) (M.inv_mem hx)
  · intro m hm
    refine ⟨x⁻¹ * m * x, M.mul_mem (M.mul_mem (M.inv_mem hx) hm) hx, ?_⟩
    show x * (x⁻¹ * m * x) * x⁻¹ = m
    group

theorem mem_normalizer_of_map_eq {L : Subgroup Γ} {x : Γ}
    (h : L.map (MulAut.conj x).toMonoidHom = L) : x ∈ Subgroup.normalizer (L : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ L.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := by
      have h2 : x * y' * x⁻¹ = x * y * x⁻¹ := hyy
      simpa using h2
    rwa [← this]

end General

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem isComponentOf_Cz : IsComponentOf L (G ⊓ Subgroup.centralizer ({z} : Set (GLV V))) :=
  c.std.component_of_inv z c.z_mem_G c.orderOf_z c.z_mem_K.2

theorem centralizer_le_normalizer :
    G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) ≤ Subgroup.normalizer (L : Set (GLV V)) := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : GLV V →* GLV V := (MulAut.conj x).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj x).injective
  have hcomp := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.isComponentOf_map_of_injective
    hfi c.isComponentOf_Cz
  rw [map_conj_eq_self hx] at hcomp
  refine mem_normalizer_of_map_eq ?_
  by_contra hne
  have hle : L.map f ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    intro y hy
    refine ⟨(hcomp.1 hy).1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    exact (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp
      c.isComponentOf_Cz hne hy hl).symm
  have h1 : 2 ≤ CFSG.Open.pRank 2 (L.map f) :=
    c.two_le_pRank_L.trans (CFSG.SectionRank.pRank_le_map (by norm_num) f hfi L)
  have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hle
  rw [c.rank] at h2
  omega

end Ctx

end CaseII

end CFSG.CGT.Foote82
