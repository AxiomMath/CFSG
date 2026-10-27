module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

theorem quot_pPrimeCore_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty ((A ⧸ pPrimeCore 2 A) ≃* (B ⧸ pPrimeCore 2 B)) :=
  ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

theorem hat_equiv_of_subnormal_of_simple {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    (hAB : A ≤ B) (hA : A.IsSubnormal) (hB : IsSimpleGroup (↥B ⧸ pPrimeCore 2 ↥B))
    (hnt : Nontrivial (↥A ⧸ pPrimeCore 2 ↥A)) :
    Nonempty ((↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥B ⧸ pPrimeCore 2 ↥B)) := by
  set N : Subgroup ↥B := pPrimeCore 2 ↥B with hN
  set L : Subgroup ↥B := A.subgroupOf B with hL
  have hLsn : L.IsSubnormal := hA.subgroupOf
  let φ : ↥L →* ↥B ⧸ N := (QuotientGroup.mk' N).comp L.subtype
  have hker : φ.ker = pPrimeCore 2 ↥L := ker_restrict_eq_pPrimeCore hLsn
  have hrange : φ.range.IsSubnormal := by
    have : φ.range = L.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact hLsn.map (QuotientGroup.mk'_surjective N)
  have e₁ : Nonempty ((↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥L ⧸ pPrimeCore 2 ↥L)) :=
    quot_pPrimeCore_congr (Subgroup.subgroupOfEquivOfLe hAB).symm
  obtain ⟨e₁⟩ := e₁
  rcases hrange.eq_bot_or_top_of_isSimpleGroup hB with h0 | h1
  · exfalso
    have hkerTop : φ.ker = ⊤ := by
      rw [eq_top_iff]
      intro l _
      have : φ l ∈ φ.range := ⟨l, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this
    rw [hker] at hkerTop
    have hsub : Subsingleton (↥L ⧸ pPrimeCore 2 ↥L) := by
      rw [hkerTop]
      exact QuotientGroup.subsingleton_quotient_top
    have : Nontrivial (↥L ⧸ pPrimeCore 2 ↥L) := e₁.injective.nontrivial
    exact not_subsingleton (↥L ⧸ pPrimeCore 2 ↥L) hsub
  · have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp h1
    exact ⟨e₁.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj))⟩


theorem Jx_le_cen {G : Type} [Group G] (y : G) : Jx y ≤ centralizer ({y} : Set G) :=
  sSup_le fun _ hL => hL.1

theorem component_equiv_hat_of_simple {G : Type} [Group G] [Finite G] {y : G}
    (hJ : IsSimpleGroup (↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y)))
    {K : Subgroup (CentralizerBar y)} (hK : IsComponent K) :
    Nonempty (↥K ≃* (↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y))) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := exists_pComponent_of_component hK
  have hJC : Jx y ≤ centralizer ({y} : Set G) := Jx_le_cen y
  have hK₀J : K₀ ≤ Jx y := le_sSup hK₀
  have hK₀C : K₀ ≤ centralizer ({y} : Set G) := hK₀.1
  obtain ⟨_, -, hsn, -, -⟩ := hK₀.2
  have hAB : K₀.subgroupOf (centralizer ({y} : Set G)) ≤ (Jx y).subgroupOf (centralizer ({y} : Set G)) :=
    fun x hx => hK₀J hx
  obtain ⟨eJ⟩ := quot_pPrimeCore_congr (Subgroup.subgroupOfEquivOfLe hJC)
  obtain ⟨eK⟩ := quot_pPrimeCore_congr (Subgroup.subgroupOfEquivOfLe hK₀C)
  have hB : IsSimpleGroup (↥((Jx y).subgroupOf (centralizer ({y} : Set G))) ⧸
      pPrimeCore 2 ↥((Jx y).subgroupOf (centralizer ({y} : Set G)))) := eJ.isSimpleGroup_congr.2 hJ
  have hnt : Nontrivial (↥(K₀.subgroupOf (centralizer ({y} : Set G))) ⧸
      pPrimeCore 2 ↥(K₀.subgroupOf (centralizer ({y} : Set G)))) := by
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have h1 : Nontrivial (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := e.symm.injective.nontrivial
    exact eK.symm.injective.nontrivial
  obtain ⟨e'⟩ := hat_equiv_of_subnormal_of_simple hAB hsn hB hnt
  exact ⟨e.symm.trans (eK.symm.trans (e'.trans eJ))⟩

end CFSG.GH74.GLS.Stage2.Local.Prop28
