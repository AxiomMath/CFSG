module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Def
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4

section Class

variable {F : Type} [Field F] [Finite F]

theorem card_Lsub (hodd : Odd (Nat.card F)) : Nat.card (Lsub F) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  rw [← Nat.card_congr (LEquiv F).toEquiv]
  have h := (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.GH74.Generic.S3.card_center_sl2 h2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = _
  omega

theorem exists_conj_u1_of_big (hodd : Odd (Nat.card F)) {K : Type} [Group K]
    (φ : K ≃* StatedProj (StatedSp 2 F)) {u : K} (hu : orderOf u = 2) {P' : Subgroup K}
    (hP'u : P' ≤ centralizer ({u} : Set K)) (hperf : ⁅P', P'⁆ = P')
    (hbig : Nat.card F * (Nat.card F ^ 2 - 1) / 2 < Nat.card ↥P') :
    ∃ g : StatedProj (StatedSp 2 F), g⁻¹ * φ u * g = u1 F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hφu : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  obtain ⟨g, hg | hg⟩ := exists_conj_of_orderOf_eq_two hodd hφu
  · exact ⟨g, hg⟩
  · exfalso
    set c : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹ with hc
    set M : Subgroup (StatedProj (StatedSp 2 F)) := P'.map (c.toMonoidHom.comp φ.toMonoidHom) with hM
    have hinj : Function.Injective (c.toMonoidHom.comp φ.toMonoidHom) := c.injective.comp φ.injective
    have hcφu : c (φ u) = u2 F := by
      rw [hc, MulAut.conj_apply]
      simpa using hg
    have hMu : M ≤ centralizer ({u2 F} : Set (StatedProj (StatedSp 2 F))) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpu : p * u = u * p := Subgroup.mem_centralizer_singleton_iff.1 (hP'u hp)
      change c (φ p) * u2 F = u2 F * c (φ p)
      rw [← hcφu, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hpu]
    have hMperf : ⁅M, M⁆ = M := by
      rw [hM, ← Subgroup.map_commutator, hperf]
    have hML := perfect_le_L h2 hMu hMperf
    have hcard : Nat.card ↥M = Nat.card ↥P' := Subgroup.card_map_of_injective hinj
    have h3 : Nat.card ↥M ≤ Nat.card ↥(Lsub F) := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hML)
    rw [hcard, card_Lsub hodd] at h3
    omega


theorem exists_conj_of_automorphism (hodd : Odd (Nat.card F)) {G : Type} [Group G]
    (e : G ≃* StatedProj (StatedSp 2 F)) {u : G} (hu : orderOf u = 2) {P' : Subgroup G}
    (hP'u : P' ≤ centralizer ({u} : Set G)) (hperf : ⁅P', P'⁆ = P')
    (hbig : Nat.card F * (Nat.card F ^ 2 - 1) / 2 < Nat.card ↥P') (α : G ≃* G) :
    ∃ k : G, α u = k * u * k⁻¹ := by
  obtain ⟨g₁, hg₁⟩ := exists_conj_u1_of_big hodd e hu hP'u hperf hbig
  have hαu : orderOf (α u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hαP : P'.map α.toMonoidHom ≤ centralizer ({α u} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpu : p * u = u * p := Subgroup.mem_centralizer_singleton_iff.1 (hP'u hp)
    change α p * α u = α u * α p
    rw [← map_mul, ← map_mul, hpu]
  have hαperf : ⁅P'.map α.toMonoidHom, P'.map α.toMonoidHom⁆ = P'.map α.toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hαcard : Nat.card ↥(P'.map α.toMonoidHom) = Nat.card ↥P' :=
    Subgroup.card_map_of_injective α.injective
  obtain ⟨g₂, hg₂⟩ := exists_conj_u1_of_big hodd e hαu hαP hαperf (hαcard ▸ hbig)
  refine ⟨e.symm (g₂ * g₁⁻¹), e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h1 : e u = g₁ * u1 F * g₁⁻¹ := by rw [← hg₁]; group
  have h2 : e (α u) = g₂ * u1 F * g₂⁻¹ := by rw [← hg₂]; group
  rw [h2, h1]
  group


end Class

section Leaf

variable {X : Type} [Group X]

theorem perfect_subgroupOf {K : Subgroup X} {P' : Subgroup X} (hPK : P' ≤ K) (hperf : ⁅P', P'⁆ = P') :
    ⁅P'.subgroupOf K, P'.subgroupOf K⁆ = P'.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPK, hperf]


theorem sp4Fusion : Sp4Fusion := by
  intro X _ _ K q u hset x
  have : K.Normal := hset.normal
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := hset.psp4
  have hodd : Odd (Nat.card F) := hFq ▸ hset.odd
  obtain ⟨P', hP'le, hperf, hcard⟩ := hset.big
  have hP'K : P' ≤ K := hP'le.trans inf_le_left
  have hP'u : P' ≤ centralizer ({u} : Set X) := hP'le.trans inf_le_right
  let uK : ↥K := ⟨u, hset.mem⟩
  have huK : orderOf uK = 2 := by
    rw [← hset.inv]
    exact (Subgroup.orderOf_coe uK).symm
  have hPu : P'.subgroupOf K ≤ centralizer ({uK} : Set ↥K) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpu : (p : X) * u = u * (p : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hP'u (Subgroup.mem_subgroupOf.1 hp))
    exact Subtype.ext hpu
  have hcardK : Nat.card F * (Nat.card F ^ 2 - 1) / 2 < Nat.card ↥(P'.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv, hFq]
    exact hcard
  obtain ⟨k, hk⟩ := exists_conj_of_automorphism hodd e huK hPu (perfect_subgroupOf hP'K hperf) hcardK
    (MulAut.conjNormal x)
  refine ⟨(k : X), k.2, ?_⟩
  have := congrArg Subtype.val hk
  simpa [uK] using this

end Leaf

end CFSG.GH74.GLS.Stage2.Local.P34
