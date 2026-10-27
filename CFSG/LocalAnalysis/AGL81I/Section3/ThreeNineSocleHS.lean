module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleCore
import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDA6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverHolds

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbeddingD2 (hsOR0 hsOUA2 hsOUB2 hsOW0)
open CFSG.RankThree.Native (hs100P)

theorem nonempty_mulEquiv_hsOUA2
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 5 7) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .HS)
    (hDK : D ≤ K) : Nonempty (↥X₁ ≃* ↥CFSG.AGLEmbeddingD2.hsOUA2) := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e
  have hcK : Nat.card ↥K = 44352000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hout5 : ¬ 5 ∣ Nat.card (Outer ↥K) := fun h5 => by
    have := Nat.le_of_dvd hO0 h5
    omega
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  have hF := CFSG.AGLEmbeddingD2.hsU35Facts
  have hR0P : hsOR0 ≤ hs100P :=
    hF.R0_le_UA.trans (hF.UA_le_UA2.trans CFSG.AGLEmbeddingD2.hsOUA2_le)
  have hPc : Nat.card hs100P = 44352000 := CFSG.RankThree.Native.card_hs100P
  obtain ⟨θ⟩ : Nonempty (↥K ≃* ↥hs100P) := ⟨e.trans CFSG.RankThree.Native.hs100Equiv⟩
  obtain ⟨Ebar, -, hEc, -, hN⟩ := h.exists_barE hZ hout5
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  have hNS := hN S S.isPGroup' hES
  have hSc : Nat.card ((S : Subgroup ↥K).map θ.toMonoidHom) = 5 ^ 3 := by
    rw [Subgroup.card_map_of_injective θ.injective, Sylow.card_eq_multiplicity, hcK,
      SporCent.factorization_eq_of_pow_dvd (e := 3) Nat.prime_five (by norm_num) (by norm_num)
        (by norm_num)]
  have hR₀c : Nat.card (hsOR0.subgroupOf hs100P) = 5 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0P).toEquiv, hF.card_R0]
    norm_num
  have hSidx : ¬ 5 ∣ (((S : Subgroup ↥K).map θ.toMonoidHom).subgroupOf ⊤).index := by
    change ¬ 5 ∣ ((S : Subgroup ↥K).map θ.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h1 := ((S : Subgroup ↥K).map θ.toMonoidHom).card_mul_index
    rw [hSc, hPc] at h1
    have h2 : ((S : Subgroup ↥K).map θ.toMonoidHom).index = 354816 := by omega
    rw [h2]
    norm_num
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq (L := ⊤) le_top
    le_top (IsPGroup.of_card hSc) (IsPGroup.of_card hR₀c) hSidx (by rw [hSc, hR₀c])
  set φ : ↥K ≃* ↥hs100P := θ.trans (MulAut.conj l) with hφ
  have hSφ : (S : Subgroup ↥K).map φ.toMonoidHom = hsOR0.subgroupOf hs100P := by
    rw [← hl, Subgroup.map_map]
    rfl
  set Y : Subgroup (Equiv.Perm (Fin 100)) :=
    ((X₁.subgroupOf K).map φ.toMonoidHom).map hs100P.subtype with hYdef
  have hYc : Nat.card Y = Nat.card (X₁.subgroupOf K) := by
    rw [hYdef, Subgroup.card_map_of_injective hs100P.subtype_injective,
      Subgroup.card_map_of_injective φ.injective]
  have hYP : Y ≤ hs100P := Subgroup.map_subtype_le _
  have hNY : hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y := by
    rintro x ⟨hxP, hxN⟩
    have hx : (⟨x, hxP⟩ : ↥hs100P) ∈
        Subgroup.normalizer ((hsOR0.subgroupOf hs100P : Subgroup ↥hs100P) : Set ↥hs100P) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hR0P]
      exact Subgroup.mem_subgroupOf.mpr hxN
    rw [← hSφ, ← Subgroup.map_equiv_normalizer_eq] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    have hkx' : φ k = ⟨x, hxP⟩ := hkx
    exact ⟨φ k, ⟨k, hNS hk, rfl⟩, by rw [hkx']; rfl⟩
  have hcases : Y = hsOUA2 ∨ Y = hsOUB2 := by
    rcases CFSG.AGLEmbeddingD2.hs100P_normalizer_overgroups Y hNY hYP with hY | hY | hY | hY
    · exfalso
      have hc : Nat.card (X₁.subgroupOf K) = 2000 := by
        rw [← hYc, hY, ← CFSG.AGLEmbeddingD2.hsON0_eq_normalizer, CFSG.AGLEmbeddingD2.card_hsON0]
      obtain ⟨hd1, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
      rw [hc] at hd1
      norm_num at hd1
    · exact Or.inl hY
    · exact Or.inr hY
    · exfalso
      have hc : Nat.card (X₁.subgroupOf K) = Nat.card ↥K := by rw [← hYc, hY, hPc, hcK]
      refine h.not_K_le fun x hx => ?_
      have : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K := by
        rw [Subgroup.card_eq_iff_eq_top] at hc
        rw [hc]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨e3⟩ : Nonempty (↥Y ≃* ↥hsOUA2) := by
    rcases hcases with hY | hY
    · exact ⟨MulEquiv.subgroupCongr hY⟩
    · exact ⟨(MulEquiv.subgroupCongr (hY.trans CFSG.AGLEmbeddingD2.hsOUB2_eq_map)).trans
        (hsOUA2.equivMapOfInjective _ (MulAut.conj hsOW0).injective).symm⟩
  have e1 : ↥X₁ ≃* ↥(X₁.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hX₁K).symm
  have e2 : ↥(X₁.subgroupOf K) ≃* ↥Y :=
    ((X₁.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (((X₁.subgroupOf K).map φ.toMonoidHom).equivMapOfInjective hs100P.subtype
        hs100P.subtype_injective)
  exact ⟨(e1.trans e2).trans e3⟩

theorem socle_of_hs
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 5 7) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .HS)
    (hDK : D ≤ K) :
    IsSimpleGroup ↥(oPPrimeHull 7 X₁) ∧
      Subgroup.centralizer (oPPrimeHull 7 X₁ : Set X) ⊓ K = ⊥ := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_hsOUA2 h hs hDK
  obtain ⟨e⟩ := hs
  have hF := CFSG.AGLEmbeddingD2.hsU35Facts
  let N := CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2
  have hNc : Nat.card N = 126000 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF.UA_le_UA2).toEquiv).trans hF.card_UA
  have hNidx : N.index = 2 := by
    have h1 := N.card_mul_index
    rw [hNc, hF.card_UA2] at h1
    omega
  have hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hNidx
  have hNsimple : IsSimpleGroup ↥N :=
    @MulEquiv.isSimpleGroup _ _ _ _ hF.simple
      (Subgroup.subgroupOfEquivOfLe hF.UA_le_UA2)
  obtain ⟨T₀, hT, hn, hsT, ⟨eNT⟩, hidx⟩ :=
    SporCent.exists_normal_of_mulEquiv ψ N hNnormal hNsimple
  have hTc : Nat.card ↥T₀ = 126000 := (Nat.card_congr eNT.toEquiv).trans hNc
  have hidx2 : (T₀.subgroupOf X₁).index = 2 := hidx.trans hNidx
  refine socle_of_index_two h hDK hT hn hsT ?_ ?_ hidx2 ?_
  · rw [hTc]
    norm_num
  · rw [hTc]
    norm_num
  · intro z hz hdiv
    rw [hTc] at hdiv
    rcases CFSG.ComponentClassification.HSFLit.card_centralizer_of_HS e hz with h | h <;>
      rw [h] at hdiv <;> norm_num at hdiv

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
