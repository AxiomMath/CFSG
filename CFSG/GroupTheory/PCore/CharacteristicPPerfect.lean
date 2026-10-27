module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

theorem le_pCoreOf_of_perfect_of_not_commutative [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hQ : ¬ ∀ x y : ↥(pCoreOf p P), x * y = y * x)
    (hperf : ⁅P, P⁆ = P)
    (hmax : ∀ N : Subgroup G, pCoreOf p P ≤ N → N ≤ P → (N.subgroupOf P).Normal →
      N = pCoreOf p P ∨ N = P) :
    P ⊓ Subgroup.centralizer (pCoreOf p P : Set G) ≤ pCoreOf p P := by
  classical
  set Q : Subgroup G := pCoreOf p P with hQdef
  have hQnc : ¬ ∀ x y : ↥Q, x * y = y * x := by
    simpa only [hQdef] using hQ
  set C : Subgroup G := P ⊓ Subgroup.centralizer (Q : Set G) with hCdef
  have hQP : Q ≤ P := pCoreOf_le (r := p) P
  have hCP : C ≤ P := inf_le_left
  have hQnorm : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (le_normalizer_pCoreOf (r := p) P)
  have hCnorm : (C.subgroupOf P).Normal := by
    have hPN : P ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf (r := p) P
    have hcent : ((Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).Normal :=
      Subgroup.normal_subgroupOf_centralizer_normalizer (Q : Set G)
    have hcomap := hcent.comap (Subgroup.inclusion hPN)
    rw [Subgroup.comap_inclusion_subgroupOf] at hcomap
    simpa only [hCdef, Subgroup.inf_subgroupOf_left] using hcomap
  have hNnorm : ((Q ⊔ C).subgroupOf P).Normal := by
    rw [Subgroup.subgroupOf_sup hQP hCP]
    exact Subgroup.sup_normal (Q.subgroupOf P) (C.subgroupOf P)
  have hNle : Q ⊔ C ≤ P := sup_le hQP hCP
  rcases hmax (Q ⊔ C) le_sup_left hNle hNnorm with hN | hN
  ·
    change C ≤ Q
    simpa only [hN] using (le_sup_right : C ≤ Q ⊔ C)
  ·
    exfalso
    have hPsup : Q ⊔ C = P := hN
    let Csub : Subgroup ↥P := C.subgroupOf P
    haveI hCsubNorm : Csub.Normal := hCnorm
    haveI hperfP : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
    haveI hperfQ : Group.IsPerfect (↥P ⧸ Csub) := inferInstance
    have hquotp : IsPGroup p (↥P ⧸ Csub) := by
      have hQp : IsPGroup p (Q.subgroupOf P) :=
        (pCoreOf_isPGroup (r := p) P).of_equiv
          (Subgroup.subgroupOfEquivOfLe hQP).symm
      have hsup : Q.subgroupOf P ⊔ Csub = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQP hCP, hPsup]
        exact Subgroup.subgroupOf_self P
      have hker : Csub ≤ (QuotientGroup.mk' Csub).ker := by
        intro x hx
        rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx
      have hCmap : Csub.map (QuotientGroup.mk' Csub) = ⊥ :=
        (Subgroup.map_eq_bot_iff Csub).mpr hker
      have hmap : (Q.subgroupOf P).map (QuotientGroup.mk' Csub) = ⊤ := by
        calc (Q.subgroupOf P).map (QuotientGroup.mk' Csub)
            = (Q.subgroupOf P).map (QuotientGroup.mk' Csub) ⊔
                Csub.map (QuotientGroup.mk' Csub) := by
              rw [hCmap, sup_bot_eq]
          _ = ((Q.subgroupOf P) ⊔ Csub).map (QuotientGroup.mk' Csub) := by
              rw [Subgroup.map_sup]
          _ = ⊤ := by
              rw [hsup, Subgroup.map_top,
                MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Csub)]
      have htop : IsPGroup p (⊤ : Subgroup (↥P ⧸ Csub)) := by
        rw [← hmap]
        exact hQp.map (QuotientGroup.mk' Csub)
      exact htop.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent (↥P ⧸ Csub) := hquotp.isNilpotent
    by_cases htriv : Subsingleton (↥P ⧸ Csub)
    ·
      have hCtop : Csub = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have h1 : (QuotientGroup.mk x : ↥P ⧸ Csub) = 1 := Subsingleton.elim _ _
        exact (QuotientGroup.eq_one_iff x).mp h1
      have hPC : P ≤ C := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥P) ∈ Csub := hCtop ▸ Subgroup.mem_top _
        simpa only [Csub, Subgroup.mem_subgroupOf] using hx'
      have hQC : Q ≤ Subgroup.centralizer (Q : Set G) := by
        intro q hq
        exact (hPC (hQP hq)).2
      have hcommQ : ∀ x y : ↥Q, x * y = y * x := by
        intro x y
        refine Subtype.ext ?_
        have h := (Subgroup.mem_centralizer_iff.mp (hQC x.2)) (y : G) y.2
        exact h.symm
      exact hQnc hcommQ
    · haveI : Nontrivial (↥P ⧸ Csub) := not_subsingleton_iff_nontrivial.mp htriv
      exact Group.IsPerfect.not_isNilpotent (↥P ⧸ Csub) hnil

end CFSG.GroupTheory
