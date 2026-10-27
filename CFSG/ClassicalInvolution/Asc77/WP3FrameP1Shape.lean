module

import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieD

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

@[expose] def ChainShapeData {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) : Prop :=
  D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧
    (D.tag i₁ = .PSL ∨ D.tag i₁ = .PSU) ∧ (D.rank i₁ = 3 ∨ D.rank i₁ = 4)

theorem chainShape_iff :
    ChainShape p f Ω z ↔ ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z, ChainShapeData D :=
  Iff.rfl

theorem chainShape_of_local (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hs : ∃ D : LocalLieSystemAt p f Ω z, ChainShapeData D) : ChainShape p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_exact hex hcls)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      (∃ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ChainShapeData D) →
      ∃ D : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
        (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ChainShapeData D := by
    intro S₁ S₂ h
    subst h
    exact id
  exact key _ _ h.symm hs

theorem chainShape_of_localShapeA (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (h : LocalShapeA p f 2 Ω z) :
    ChainShape p f Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact chainShape_of_local hex hcls ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, Or.inl ht₁,
    Or.inl (by omega)⟩

theorem chainShape_of_localShapeU (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (h : LocalShapeU p f 2 Ω z) :
    ChainShape p f Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact chainShape_of_local hex hcls ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, Or.inr ht₁,
    Or.inl (by omega)⟩

theorem exactLayer_eq_centLayer_of_exact (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) : exactLayer Ω z = centLayer Ω z := by
  unfold exactLayer centLayer
  rw [centMembers_exactFamily, exactFamily_eq_centMembers_of_exact hex hcls]

theorem oddCoreIn_exactLayer_central (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hp1 : LocalOddCentral Ω {z}) :
    ∀ o ∈ oddCoreIn (exactLayer Ω z), ∀ y ∈ exactLayer Ω z, o * y = y * o := by
  have hY : exactLayer Ω z = centLayer Ω z := exactLayer_eq_centLayer_of_exact hex hcls
  rw [hY]
  intro o ho y hy
  obtain ⟨o', ho', rfl⟩ := ho
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hp1 ho') ⟨y, hy⟩).symm

end Shape

section Member

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem oddQuotMk_eq_of_comp₀ {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w)
    {R : Subgroup (compModel C.D C.i₀).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag C.i₀) (compModel C.D C.i₀).D)
    (hmod : R.map (C.psi C.i₀) = modOdd z (exactCore z N)) :
    oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = oddQuotMk z ⟨z, ChainLift.hzC⟩ := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hzE : z ∈ exactCore z C.K := C.involution_mem_exactCore ⟨C.hK, C.hKtq⟩ hKcl
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := ChainLift.hzC
  obtain ⟨R_K, hR_K, hmodK⟩ := C.K_comp
  obtain ⟨g, hg⟩ := C.single C.i₀ (Or.inl C.tag₀) R hR R_K hR_K
  have hzbmem : oddQuotMk z ⟨z, hzC⟩ ∈ R_K.map (C.psi C.i₀) :=
    hmodK ▸ oddQuotMk_mem_modOdd hzE hzC
  obtain ⟨r, hrR, hr⟩ := hzbmem
  rw [hg] at hrR
  obtain ⟨r₀, hr₀, rfl⟩ := hrR
  have hcen := oddQuotMk_central hzC (C.psi C.i₀ g)
  have hr₀z : C.psi C.i₀ r₀ = oddQuotMk z ⟨z, hzC⟩ := by
    have h1 : C.psi C.i₀ ((MulAut.conj g).toMonoidHom r₀) = oddQuotMk z ⟨z, hzC⟩ := hr
    have h2 : (MulAut.conj g).toMonoidHom r₀ = g * r₀ * g⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc C.psi C.i₀ r₀ = (C.psi C.i₀ g)⁻¹ * (C.psi C.i₀ g * C.psi C.i₀ r₀ *
          (C.psi C.i₀ g)⁻¹) * C.psi C.i₀ g := by group
      _ = (C.psi C.i₀ g)⁻¹ * oddQuotMk z ⟨z, hzC⟩ * C.psi C.i₀ g := by rw [h1]
      _ = oddQuotMk z ⟨z, hzC⟩ := by rw [mul_assoc, hcen, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzbN : oddQuotMk z ⟨z, hzC⟩ ∈ modOdd z (exactCore z N) := by
    rw [← hmod, ← hr₀z]
    exact ⟨r₀, hr₀, rfl⟩
  have hzbsq : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext C.hKz.sq
    rw [this, map_one]
  have hzb1 : oddQuotMk z ⟨z, hzC⟩ ≠ 1 := fun h =>
    C.hKz.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))
  have hU := C.isUniqueInvolution_modOdd hN hw
  exact ((hU.unique _ hzbN hzbsq).resolve_left hzb1).symm

theorem exists_fund_i₁ (hex : ExactMembers Ω) (hp1 : LocalOddCentral Ω {z}) {M : Subgroup G}
    {w : G} (hM : M ∈ tqMembers Ω z) (hw : IsClassicalMember p f M w) (hzw : z ≠ w) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
      R.map (C.psi C.i₁) = modOdd z (exactCore z M) := by
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hM
  rcases C.eq_i₀_or_i₁ j with rfl | rfl
  · exfalso
    have heq := C.oddQuotMk_eq_of_comp₀ hM hw hR hmod
    have hwY : w ∈ exactLayer Ω z := exactCore_le_exactLayer hM (C.involution_mem_exactCore hM hw)
    have hwsq := (isCentralInvolution_of_isClassicalMember hw).sq
    obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY C.z_mem_exactLayer hwsq C.hKz.sq heq
    have hc := oddCoreIn_exactLayer_central hex C.hΩ.classical hp1 o ho z C.z_mem_exactLayer
    apply hzw
    rw [hwo, hc]
    group
  · exact ⟨R, hR, hmod⟩

end ChainCtx

end Member

end CFSG.ClassicalInvolution.Asc77
