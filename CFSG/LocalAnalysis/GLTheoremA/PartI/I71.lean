module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

@[expose] def IsPOmegaEightPlusOdd (S : Type) [Group S] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p ≠ 2 ∧
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)

@[expose] def KDOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ P T : Subgroup (MulAut S), IsPGroup p P → IsPGroup 2 T →
        P ≤ Subgroup.normalizer (T : Set (MulAut S)) →
        (⁅T, P⁆ : Subgroup (MulAut S)) ≤ inner S ∨ (p = 3 ∧ IsPOmegaEightPlusOdd S)

@[expose] def I117D4UsedAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (J S : Subgroup G), GLAIsBmax 3 B → IsEssential 3 B x →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → IsPOmegaEightPlusOdd (PSimple 3 J) → IsPGroup 2 S →
    S ≤ Subgroup.centralizer ({x} : Set G) → S ≤ Subgroup.normalizer (J : Set G) →
    B ≤ Subgroup.normalizer (S : Set G) → (⁅S, B⁆ : Subgroup G) = S →
    ∀ s ∈ S, InducesInnerMod 3 J s

variable {G : Type} [Group G] [Finite G]

section Aux

private theorem isCatalogGroup_center_quotient {Y : Type*} [Group Y] (hY : CFSG.Open.IsKGroup Y)
    (hq : CFSG.Open.IsQuasisimple Y) : IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  refine hY.isCatalogGroup_of_surjective ⊤
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq)
    ((QuotientGroup.mk' (Subgroup.center Y)).comp (⊤ : Subgroup Y).subtype) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩

private theorem inducesInnerMod_of_inner {p : ℕ} {J : Subgroup G}
    [Group.IsPerfect (PQuot p J)] {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : centerQuotientHom (PQuot p J) (barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) ∈
      inner (PSimple p J)) : InducesInnerMod p J g := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) m
  have hu : barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = MulAut.conj u :=
    (centerQuotientHom_injective (PQuot p J)) (hm.symm.trans (centerQuotient_conj u).symm)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ with hγ
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = g⁻¹ * y * g := fun y => by
    change (g⁻¹ : G) * y * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

end Aux

theorem i71UsedAt_of_kd (hOut : KDOut) (hD4 : I117D4UsedAt G) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : I71UsedAt G p := by
  intro B x J S hB hx hJ hBJ hS hSC hSJ hBS hSB s hs
  have hC : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one hsimple hnonab hx.2.1
  have hKC : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hKP hC
  have hKJ : CFSG.Open.IsKGroup ↥J := CFSG.Open.IsKGroup.of_le hKC hJ.1
  have hKq : CFSG.Open.IsKGroup (PQuot p J) := CFSG.Open.IsKGroup.quotient hKJ _
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : Group.IsPerfect (PQuot p J) := ⟨hq.1⟩
  have hsimple₀ : IsSimpleGroup (PSimple p J) := hq.2
  have hnonab₀ : ∃ a b : PSimple p J, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcat₀ : IsCatalogGroup (PSimple p J) := isCatalogGroup_center_quotient hKq hq
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := hSJ
  have hBN : B ≤ Subgroup.normalizer (J : Set G) := hBJ
  set N : Subgroup G := Subgroup.normalizer (J : Set G) with hN
  set φ : ↥N →* MulAut (PSimple p J) :=
    (centerQuotientHom (PQuot p J)).comp (barAut p J) with hφ
  have hBnorm : B.subgroupOf N ≤ Subgroup.normalizer (S.subgroupOf N : Set ↥N) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    exact (Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hb))
      (t : G)).1 (Subgroup.mem_subgroupOf.1 ht)
  have hSB' : (⁅S.subgroupOf N, B.subgroupOf N⁆ : Subgroup ↥N) = S.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSN,
      Subgroup.map_subgroupOf_eq_of_le hBN]
    exact hSB
  have hTp : IsPGroup 2 ((S.subgroupOf N).map φ) := hS.comap_subtype.map φ
  have hPp : IsPGroup p ((B.subgroupOf N).map φ) :=
    (isPGroup_of_isElemAbelian hB.1).comap_subtype.map φ
  have hPT : (B.subgroupOf N).map φ ≤
      Subgroup.normalizer (((S.subgroupOf N).map φ : Subgroup (MulAut (PSimple p J))) :
        Set (MulAut (PSimple p J))) :=
    (Subgroup.map_mono hBnorm).trans (Subgroup.le_normalizer_map φ)
  have hTT : (⁅(S.subgroupOf N).map φ, (B.subgroupOf N).map φ⁆ :
      Subgroup (MulAut (PSimple p J))) = (S.subgroupOf N).map φ := by
    rw [← Subgroup.map_commutator, hSB']
  rcases hOut (PSimple p J) hsimple₀ hnonab₀ hcat₀ p hp hp2 _ _ hPp hTp hPT with h | ⟨hp3, hD⟩
  ·
    have hsN : s⁻¹ ∈ N := N.inv_mem (hSN hs)
    have hsT : φ ⟨s⁻¹, hsN⟩ ∈ (S.subgroupOf N).map φ :=
      ⟨⟨s⁻¹, hsN⟩, Subgroup.mem_subgroupOf.2 (S.inv_mem hs), rfl⟩
    rw [← hTT] at hsT
    exact inducesInnerMod_of_inner (hSN hs) (h hsT)
  ·
    subst hp3
    exact hD4 B x J S hB hx hJ hBJ hD hS hSC hSJ hBS hSB s hs

end CFSG.LocalAnalysis.GLTheoremA
