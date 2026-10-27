module

public import CFSG.LocalAnalysis.SteinbergSFBothTrivialClosureSetupBase
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure
open scoped MatrixGroups

section PreBar

variable {G : Type*} [Group G]

def preBar (X : Subgroup G) (Nb : Subgroup (BarM X)) : Subgroup G :=
  (Nb.comap (barMap X)).map (normalizer (X : Set G)).subtype

variable {X : Subgroup G} {Nb : Subgroup (BarM X)}

theorem mem_preBar {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ preBar X Nb ↔ barMap X ⟨g, hg⟩ ∈ Nb := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem preBar_le_normalizer : preBar X Nb ≤ normalizer (X : Set G) := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

theorem preBar_conj [Nb.Normal] {g n : G} (hg : g ∈ normalizer (X : Set G))
    (hn : n ∈ preBar X Nb) : g * n * g⁻¹ ∈ preBar X Nb := by
  have hn' := preBar_le_normalizer hn
  have hgn : g * n * g⁻¹ ∈ normalizer (X : Set G) := mul_mem (mul_mem hg hn') (inv_mem hg)
  refine (mem_preBar hgn).mpr ?_
  have e : barMap X ⟨g * n * g⁻¹, hgn⟩ =
      barMap X ⟨g, hg⟩ * barMap X ⟨n, hn'⟩ * (barMap X ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact Subgroup.Normal.conj_mem inferInstance _ ((mem_preBar hn').mp hn) _

noncomputable def preBarEquiv (X : Subgroup G) (Nb : Subgroup (BarM X)) :
    ↥(Nb.comap (barMap X)) ≃* ↥(preBar X Nb) :=
  Subgroup.equivMapOfInjective _ (normalizer (X : Set G)).subtype
    (normalizer (X : Set G)).subtype_injective

noncomputable def preBarHom {H : Type*} [Group H] (ρ : Nb →* H) : ↥(preBar X Nb) →* H :=
  (ρ.comp (((barMap X).comp (Nb.comap (barMap X)).subtype).codRestrict Nb fun m => m.2)).comp
    (preBarEquiv X Nb).symm.toMonoidHom

theorem preBarHom_apply {H : Type*} [Group H] (ρ : Nb →* H) {g : G}
    (hg : g ∈ normalizer (X : Set G)) (h : g ∈ preBar X Nb) :
    preBarHom ρ ⟨g, h⟩ = ρ ⟨barMap X ⟨g, hg⟩, (mem_preBar hg).mp h⟩ := by
  have e : (preBarEquiv X Nb).symm ⟨g, h⟩ = ⟨⟨g, hg⟩, (mem_preBar hg).mp h⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [preBarHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e]
  rfl

end PreBar

section Hom

variable {G : Type*} [Group G] {k : Type} [Field k] [Finite k] [CharP k 2]

theorem exists_preBarHom {m : ℕ} (hk : Nat.card k = 2 ^ m) {X V : Subgroup G} (hXV : X ≤ V)
    {Nb : Subgroup (BarM X)} (ψ : Nb ≃* SL(2, k))
    (hSyl : ∃ P : Sylow 2 Nb, (P : Subgroup Nb).map Nb.subtype = barSub X V) :
    ∃ π : ↥(preBar X Nb) →* SL(2, k), Function.Surjective π ∧
      (∀ n : preBar X Nb, π n = 1 ↔ (n : G) ∈ X) ∧
      ∀ n : preBar X Nb, (n : G) ∈ V ↔ π n ∈ CFSG.Timmesfeld.upperUnipotent k := by
  obtain ⟨P, hP⟩ := hSyl
  have hPcard : Nat.card (P.map ψ.toMonoidHom) = Nat.card k := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact CFSG.LocalAnalysis.EvenBN.Common.card_sylow_two_eq ψ P
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_conj_eq_upperUnipotent hk hPcard
  set ρ : ↥(preBar X Nb) →* SL(2, k) := preBarHom ψ.toMonoidHom with hρ
  have hρapply : ∀ (n : G) (hn : n ∈ normalizer (X : Set G)) (h : n ∈ preBar X Nb),
      ρ ⟨n, h⟩ = ψ ⟨barMap X ⟨n, hn⟩, (mem_preBar hn).mp h⟩ := fun n hn h =>
    preBarHom_apply ψ.toMonoidHom hn h
  refine ⟨(MulAut.conj g).toMonoidHom.comp ρ, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨y, hy⟩ := ψ.surjective ((MulAut.conj g).symm s)
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (y : BarM X)
    have hmem : (m' : G) ∈ preBar X Nb := (mem_preBar m'.2).mpr (by
      change barMap X m' ∈ Nb
      rw [QuotientGroup.mk'_apply, hm']
      exact y.2)
    refine ⟨⟨m', hmem⟩, ?_⟩
    rw [MonoidHom.comp_apply, hρapply _ m'.2 hmem]
    have : (⟨barMap X ⟨(m' : G), m'.2⟩, (mem_preBar m'.2).mp hmem⟩ : Nb) = y := by
      apply Subtype.ext
      change barMap X m' = y
      rw [QuotientGroup.mk'_apply, hm']
    rw [this, hy]
    exact (MulAut.conj g).apply_symm_apply s
  · intro n
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      hρapply _ (preBar_le_normalizer n.2) n.2, MulEquiv.map_eq_one_iff]
    rw [Subtype.ext_iff, OneMemClass.coe_one, barMap_eq_one_iff]
  · intro n
    have hn := preBar_le_normalizer n.2
    rw [MonoidHom.comp_apply, hρapply _ hn n.2]
    have hU : ∀ s : SL(2, k), (MulAut.conj g).toMonoidHom s ∈ CFSG.Timmesfeld.upperUnipotent k ↔
        s ∈ P.map ψ.toMonoidHom := by
      intro s
      rw [← hg]
      constructor
      · rintro ⟨h, hh, hhs⟩
        have : h = s := (MulAut.conj g).injective hhs
        rw [← this]
        exact hh
      · intro hs
        exact ⟨s, hs, rfl⟩
    rw [hU]
    constructor
    · intro hV
      have h1 : barMap X ⟨(n : G), hn⟩ ∈ barSub X V := (mem_barSub_iff hXV _).mpr hV
      rw [← hP] at h1
      obtain ⟨x, hx, hxe⟩ := h1
      refine ⟨x, hx, ?_⟩
      have : x = ⟨barMap X ⟨(n : G), hn⟩, (mem_preBar hn).mp n.2⟩ := Subtype.ext hxe
      rw [this]
      rfl
    · rintro ⟨x, hx, hxe⟩
      have hx' : x = ⟨barMap X ⟨(n : G), hn⟩, (mem_preBar hn).mp n.2⟩ := ψ.injective hxe
      have h1 : barMap X ⟨(n : G), hn⟩ ∈ barSub X V := by
        rw [← hP]
        exact ⟨x, hx, by rw [hx']; rfl⟩
      exact (mem_barSub_iff hXV ⟨(n : G), hn⟩).mp h1

end Hom

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
