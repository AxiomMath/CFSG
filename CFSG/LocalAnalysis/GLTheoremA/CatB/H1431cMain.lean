module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.LocalAnalysis.GLTheoremA (pQuotHom isQuasisimple_pQuot_of_glaPComponent
  glaPComponent_map_pQuotHom i1431_pSimple_equiv_barImage i1431_le_sup_of_centMod
  i1431_isElemAbelian_zpowers chev_barAut_eq_one_iff_centMod isElemAbelian_commute)

theorem catalogIs_of_mulEquiv' {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs S Q) : catalogIs T Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem catalogIs_of_index {S : Type} [Group S] {i : TauCeti.CFSGIndex}
    (f : S ≃* i.Group) {Q : TauCeti.CFSGIndex → Prop} (hQi : Q i) : catalogIs S Q :=
  ⟨i, hQi, ⟨f⟩⟩

theorem in84_i1431_of_facts (hLie : I1431LieS) (hAlt : I1431AltS) (hSpor : I1431SporS)
    (hF4 : I1431InspF42) (hSp68 : I1431InspSp68) (hSp492 : I1431InspSp492) (hL2 : I1431InspL2)
    (hHN : I1431InspHN) (hMult : I1431MultS) (G : Type) [Group G] [Finite G] :
    S8.L84.I1431At G := by
  intro X B K J d y hX hBX hB hrk hK hBN hcex hd hJ hT hnot hy hIa
  obtain ⟨c, hcB, hc1, hcK⟩ := hcex
  obtain ⟨Ia, hIaC, hIaT⟩ := hIa
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hd3 : d ^ 3 = 1 := hB.2 d hd
  have hy3 : y ^ 3 = 1 := hB.2 y hy
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hBN hd
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hBN hy
  have hdP : IsPGroup 3 (Subgroup.zpowers d) :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_isPGroup_of_elemAbelian (i1431_isElemAbelian_zpowers hd3)
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_isPGroup_of_elemAbelian (i1431_isElemAbelian_zpowers hy3)
  have hKK : CFSG.Open.IsKGroup ↥K := hX.of_le hK.1
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hO : GLAPPrimeCore 3 (PQuot 3 K) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hRkY : RkY (PQuot 3 K) :=
    rkY_of_centMod ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp (K ⊔ B)).trans hrk)
      hB hcB hc1 hcK
  set ξ : MulAut (PQuot 3 K) := barAut 3 K ⟨d, hdN⟩ with hξdef
  set τy : MulAut (PQuot 3 K) := barAut 3 K ⟨y, hyN⟩ with hτydef
  have hξ3 : ξ ^ 3 = 1 := by
    have h : (⟨d, hdN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hd3
    rw [hξdef, ← map_pow, h, map_one]
  have hτy3 : τy ^ 3 = 1 := by
    have h : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hy3
    rw [hτydef, ← map_pow, h, map_one]
  have hξ1 : ξ ≠ 1 := by
    intro h1
    have hCM : CentMod 3 K d := (chev_barAut_eq_one_iff_centMod (p := 3) hdN).1 h1
    exact hnot (i1431_le_sup_of_centMod hp hK hdP hCM hJ)
  have hJbar : GLAPComponent 3 (fixSubgroup ξ) (imgK K J) := glaPComponent_map_pQuotHom hp hdN hdP hJ
  obtain ⟨eJ⟩ := i1431_pSimple_equiv_barImage hp hdN hdP hJ
  have hJtype : catalogIs (PSimple 3 (imgK K J)) S8.L84.isType1430 :=
    catalogIs_of_mulEquiv' eJ hT.1
  have hSp48 : catalogIs (PSimple 3 (imgK K J)) S8.L84.isSp48 →
      ∃ τ : MulAut (PQuot 3 K), τ ^ 3 = 1 ∧ Commute τ ξ ∧ ¬ InnerOnMod 3 (imgK K J) τ ∧ RkTau τ := by
    intro hsp
    obtain ⟨e', he', hnI⟩ := hT.2 (catalogIs_of_mulEquiv' eJ.symm hsp)
    have heN : e' ∈ Subgroup.normalizer (K : Set G) := hBN he'
    have hed : e' * d = d * e' := isElemAbelian_commute hB he' hd
    refine ⟨barAut 3 K ⟨e', heN⟩, ?_, ?_, ?_, ?_⟩
    · have h : (⟨e', heN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
        Subtype.ext (hB.2 e' he')
      rw [← map_pow, h, map_one]
    · have hc : Commute (⟨e', heN⟩ : Subgroup.normalizer (K : Set G)) ⟨d, hdN⟩ :=
        Subtype.ext hed
      exact hc.map (barAut 3 K)
    · intro hinn
      exact hnI (innerOnMod_imp_inducesInnerMod heN hed hJ hinn)
    · exact rkTau_barAut
        ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp (K ⊔ B)).trans hrk)
        hB hcB hc1 hcK he' heN
  have hJT : I1431JType ξ (imgK K J) := ⟨hJtype, hSp48⟩
  have hIaK : Ia ≤ K := hIaC.1.trans inf_le_left
  have hIaBar : GLAPComponent 3 (fixSubgroup τy) (imgK K Ia) := glaPComponent_map_pQuotHom hp hyN hyP hIaC
  obtain ⟨eIa⟩ := pQuot_equiv_imgK hIaK
  have hIaT' : S8.IsTypeWithCenter 3 (imgK K Ia) S8.isA6 1 :=
    isTypeWithCenter_of_pQuot_equiv (H := PQuot 3 K) (X := Ia) (Y := imgK K Ia) eIa hIaT
  have hKq : CFSG.Open.IsKGroup (PQuot 3 K) := hKK.quotient _
  obtain ⟨i, ⟨fi⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKq hQ
  unfold S8.L84.SpA12Type
  cases i with
  | cyclic p hp' =>
    exfalso
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      (PQuot 3 K) hQ
    apply hab
    apply fi.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have h12 : n = 12 := hAlt (PQuot 3 K) hQ hO hRkY n (catalogIs_of_index fi rfl) ξ hξ3 hξ1
      (imgK K J) hJbar hJT
    subst h12
    refine ⟨Or.inr (catalogIs_of_index fi rfl), ?_⟩
    rw [hMult (PQuot 3 K) hQ hO (catalogIs_of_index fi (Or.inr rfl)), Subgroup.card_bot]
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.HN :=
      hSpor (PQuot 3 K) hQ hO hRkY s (catalogIs_of_index fi rfl) ξ hξ3 hξ1 (imgK K J) hJbar hJT
    subst hs
    exact absurd hIaT' (hHN (PQuot 3 K) hQ hO (catalogIs_of_index fi rfl) τy hτy3 (imgK K Ia) hIaBar)
  | lie l =>
    obtain ⟨j, hj, ⟨fj⟩⟩ := hLie (PQuot 3 K) hQ hO hRkY (catalogIs_of_index fi trivial) ξ hξ3 hξ1
      (imgK K J) hJbar hJT
    rcases hj with h1 | h2 | h3 | h4 | h5
    · refine ⟨Or.inl ⟨j, h1, ⟨fj⟩⟩, ?_⟩
      rw [hMult (PQuot 3 K) hQ hO ⟨j, Or.inl h1, ⟨fj⟩⟩, Subgroup.card_bot]
    · exact absurd hIaT' (hF4 (PQuot 3 K) hQ hO ⟨j, h2, ⟨fj⟩⟩ τy hτy3 (imgK K Ia) hIaBar)
    · exact absurd hIaT' (hSp68 (PQuot 3 K) hQ hO ⟨j, h3, ⟨fj⟩⟩ τy hτy3 (imgK K Ia) hIaBar)
    · exact absurd hIaT' (hSp492 (PQuot 3 K) hQ hO ⟨j, h4, ⟨fj⟩⟩ τy hτy3 (imgK K Ia) hIaBar)
    · exact absurd hIaT' (hL2 (PQuot 3 K) hQ hO ⟨j, h5, ⟨fj⟩⟩ τy hτy3 (imgK K Ia) hIaBar)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
