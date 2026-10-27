module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

section Centralizer

variable {G : Type*} [Group G]

theorem centralizer_map_mulAut (α : MulAut G) (H : Subgroup G) :
    centralizer ((H.map α.toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map α.toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨α.symm g, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    have := mem_centralizer_iff.1 hg (α h) ⟨h, hh, rfl⟩
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := mem_centralizer_iff.1 hc h hh
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]

theorem nonempty_centralizer_map_mulAut (α : MulAut G) (H : Subgroup G) :
    Nonempty (centralizer ((H.map α.toMonoidHom : Subgroup G) : Set G) ≃*
      centralizer (H : Set G)) := by
  rw [centralizer_map_mulAut]
  exact ⟨((centralizer (H : Set G)).equivMapOfInjective _ α.injective).symm⟩

end Centralizer

section F6


variable {K : Type} [Field K]

theorem psiF4_rootR : psiF4 rootR = rootS := by decide +kernel

theorem map_conj_weylRepC_rootSL2 (w : WeylGroup .F4) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    (rootSL2 K γ).map (MulAut.conj (weylRepC K w)).toMonoidHom = rootSL2 K (w • γ) := by
  rw [rootSL2_eq_sup hγ, Subgroup.map_sup, map_conj_weylRepC_rootGroup w hγ,
    map_conj_weylRepC_rootGroup w (IsRoot.neg hγ), smul_neg, rootSL2_eq_sup (IsRoot.smul hγ w)]

theorem map_graphAutF4_rootSL2R [Finite K] [CharP K ReeTag.F4.prime] :
    (rootSL2 K rootR).map (graphAutF4 K).toMonoidHom = rootSL2 K rootS := by
  rw [rootSL2_eq_sup isRoot_rootR, Subgroup.map_sup, map_graphAutF4_rootGroup isRoot_rootR,
    map_graphAutF4_rootGroup (IsRoot.neg isRoot_rootR), psiF4_neg isRoot_rootR, psiF4_rootR,
    rootSL2_eq_sup isRoot_rootS]

theorem nonempty_centralizer_rootSL2_rootR [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    Nonempty (centralizer (rootSL2 K rootR : Set (adjointGroup .F4 K)) ≃* C3Levi K) := by
  rw [rootSL2_rootR, centralizer_rootSL2R_eq_C3Levi hq]
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_centralizer_rootSL2_rootS [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    Nonempty (centralizer (rootSL2 K rootS : Set (adjointGroup .F4 K)) ≃* C3Levi K) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  rw [← map_graphAutF4_rootSL2R]
  obtain ⟨e1⟩ := nonempty_centralizer_map_mulAut (graphAutF4 K) (rootSL2 K rootR)
  obtain ⟨e2⟩ := nonempty_centralizer_rootSL2_rootR (K := K) hq
  exact ⟨e1.trans e2⟩

theorem factF6 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : FactF6 K := by
  intro γ hγ
  rcases iform_self_eq_two_or_four hγ with hs | hl
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootS hγ hs
    have h1 := map_conj_weylRepC_rootSL2 (K := K) w hγ
    rw [hw] at h1
    obtain ⟨e1⟩ := nonempty_centralizer_map_mulAut (MulAut.conj (weylRepC K w)) (rootSL2 K γ)
    rw [h1] at e1
    obtain ⟨e2⟩ := nonempty_centralizer_rootSL2_rootS (K := K) hq
    exact ⟨e1.symm.trans e2⟩
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootR hγ hl
    have h1 := map_conj_weylRepC_rootSL2 (K := K) w hγ
    rw [hw] at h1
    obtain ⟨e1⟩ := nonempty_centralizer_map_mulAut (MulAut.conj (weylRepC K w)) (rootSL2 K γ)
    rw [h1] at e1
    obtain ⟨e2⟩ := nonempty_centralizer_rootSL2_rootR (K := K) hq
    exact ⟨e1.symm.trans e2⟩

end F6

section F7


theorem factF7 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) : FactF7 K := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨hord, hnf, ⟨Θ, hΘ, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  refine ⟨ReeTag.F4.finiteExceptionalAut K, fun β => ?_, fun n hn => ?_⟩
  · obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf β
    exact ⟨g, k, hgk⟩
  · have h1 : Θ (ReeTag.F4.finiteExceptionalAut K ^ n) =
        Multiplicative.ofAdd (n : ZMod (2 * f)) :=
      hΘ _ 1 n (by rw [map_one, one_mul])
    have h2 : ReeTag.F4.finiteExceptionalAut K ^ n ∈ Θ.ker := by
      rw [hker]
      exact hn
    rw [MonoidHom.mem_ker, h1, ofAdd_eq_one, ZMod.natCast_eq_zero_iff] at h2
    obtain ⟨k, rfl⟩ := h2
    have hφ1 : ReeTag.F4.finiteExceptionalAut K ^ (2 * f) = 1 := hord ▸ pow_orderOf_eq_one _
    show (ReeTag.F4.finiteExceptionalAut K : MulAut (adjointGroup ReeTag.F4.tag K)) ^ (2 * f * k) = 1
    rw [pow_mul, hφ1, one_pow]

end F7

section OutD


theorem isSolvable_outer_C3Levi {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) :
    Group.IsSolvable (Outer (C3Levi K)) := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have hf := one_le_of_natCard_eq_two_pow hK
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp 3 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have h := CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 3 K hadm hK
  have h2 := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.classical_model_schreier
    (le_refl 3) h
  exact (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
    (c3LeviCenterQuotientEquiv K)).2.1 h2.2

end OutD

end CFSG.SeitzReduction.F4Pilot
