module

public import CFSG.ClassicalInvolution.Q3.TL4S289ZA
public import CFSG.ClassicalInvolution.Q3.TL4S289Lie
public import CFSG.ClassicalInvolution.Q3.TL4S289Exit
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9V
public import CFSG.ClassicalInvolution.Q3.TL4S289Lnk

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace S289

theorem mem_normalizer_of_map {Q Z : Type} [Group Q] [Group Z] {N L : Subgroup Q} (e : ↥N ≃* Z)
    (hLN : L ≤ N) (hn : ((L.subgroupOf N).map e.toMonoidHom).Normal) {x : Q} (hx : x ∈ N) :
    x ∈ Subgroup.normalizer (L : Set Q) := by
  have key : ∀ g (hg : g ∈ N), ∀ y ∈ L, g * y * g⁻¹ ∈ L := by
    intro g hg y hy
    have hz : g * y * g⁻¹ ∈ N := N.mul_mem (N.mul_mem hg (hLN hy)) (N.inv_mem hg)
    refine mem_of_map_mem e hz ?_
    have e1 : (⟨g * y * g⁻¹, hz⟩ : ↥N) = ⟨g, hg⟩ * ⟨y, hLN hy⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    exact hn.conj_mem _ ⟨⟨y, hLN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩ _
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun h => ?_⟩
  have h1 := key x⁻¹ (N.inv_mem hx) _ h
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

end S289

section CitL


namespace S289

theorem natCard_linkGrp_lt {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hL : TightLargeHypR r n Y R S t) :
    Nat.card ↥(linkGrp R t) < n := by
  have hz := hL.datum.isUniqueInvolution_core
  have hx : ∃ g : Y, g * t ≠ t * g := by
    by_contra hcon
    have htc : t ∈ Subgroup.center Y :=
      Subgroup.mem_center_iff.mpr fun g => by
        by_contra h
        exact hcon ⟨g, h⟩
    rw [hL.center, Subgroup.mem_bot] at htc
    exact hz.ne_one htc
  exact (Subgroup.card_le_card_group _).trans_lt
    ((natCard_secQuot_lt (Ω := CoreAssembly.conjClass (tightCore R)) hx).trans_eq hL.card)

end S289

end CitL

section Cit3


variable {n : ℕ}

theorem tightStar289ZFreeR_of
    (hα : ∀ (M : Type) [Group M] [Finite M],
      ((IsSimpleGroup M ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
          (LieModel M .PSL 3 p f ∨ LieModel M .PSU 3 p f)) ∨
        (Group.IsPerfect M ∧ NativeSporadic.IsSporadic (M ⧸ Subgroup.center M) .M12)) →
      ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
        ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
          (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥)
    (hI : SecIdExitS3Ident n) : TightStar289ZFreeR 3 n := by
  intro Y _ _ R S t hL _ _ hcase J K'' u w hF _ L hLc hm _
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u w
  have huΛ := S289.u_mem_linkLayer hL hF
  have hwΛ := S289.w_mem_linkLayer hL hF
  have hutC : u ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer huΛ
  have hwtC : w ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer hwΛ
  have huN' : oddQuotMk t ⟨u, hutC⟩ ∈ modOdd t (linkLayer R t) := oddQuotMk_mem_modOdd huΛ hutC
  have hwN' : oddQuotMk t ⟨w, hwtC⟩ ∈ modOdd t (linkLayer R t) := oddQuotMk_mem_modOdd hwΛ hwtC
  have hLN := S289.le_modOdd_of_frame hL hF hLc hm
  have hncl := hF.not_mem_closure hL
  have hct : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hcu : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htu : u ≠ t := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  have htw : w ≠ t := fun e => hncl (e ▸ hct)
  have huw1 : u * w ≠ 1 := fun e => hncl ((eq_inv_of_mul_eq_one_right e) ▸ Subgroup.inv_mem _ hcu)
  have huwt : u * w ≠ t := fun e => hncl (by
    rw [show w = u⁻¹ * t by rw [← e]; group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcu) hct)
  have huwB := Subgroup.mul_mem _ hm3.2.1 hm3.2.2
  have huwC : u * w ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hutC hwtC
  have hmu := hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.1 hF.invJ.ne_one htu hutC)
  have hmw := hm _ (oddQuotMk_mem_modOdd hm3.2.2 hwtC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one hm3.2.2 hF.invK.ne_one htw hwtC)
  have hmuw : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩ * y ≠
      y * (oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩) := by
    rw [← map_mul]
    exact hm _ (oddQuotMk_mem_modOdd huwB huwC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.1 ht.ne_one huwB huw1 huwt huwC)
  set e := S289.linkVtxEquiv hL with he
  have hC : IsComponent ((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv e (LocalCores.component_overgroup hLc hLN)
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hJm := subgroupOf_mem_linkRestrict (t := t) hF.memJ
  have hau := S289.isUniqueInvolution_link_u hL hF
  set eL : ↥L ≃* ↥((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hLN).symm.trans
      ((L.subgroupOf (modOdd t (linkLayer R t))).equivMapOfInjective e.toMonoidHom e.injective)
    with heL
  obtain ⟨htr, -, hkind⟩ := hcase
  have hlie : SecIdLieS3 (restrictFamily (coreLinkFam R t) (linkGrp R t)) ∨
      SecIdLieS4 (restrictFamily (coreLinkFam R t) (linkGrp R t)) →
      alphaOf (inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set Y)))) = ⊥ := by
    intro hk
    obtain ⟨hq, hAOFI⟩ := S289.lie_facts_of hk
    have hLeq := S289.eq_of_isQuasisimple linkLayerAt_le_centralizer
      (fun _ hc _ hy => conj_mem_linkLayer hL hc hy)
      (LocalCores.isQuasisimple_of_mulEquiv (linkLayerEquiv hL).symm hq) hLc hLN
    have hAOFL : Q3NM.AutOddFreeInner ↥L :=
      Q3CH.autOddFreeInner_of_mulEquiv (e.symm.trans (MulEquiv.subgroupCongr hLeq.symm)) hAOFI
    exact S289.alphaOf_eq_bot_of_innerFree hB hutC hwtC hAOFL (by rw [hLeq]; exact huN')
      (by rw [hLeq]; exact hwN') hmu
  rcases hkind with hk | hk | hk | hk | hk | hk | hk
  · exact hlie (Or.inl hk)
  · exact hlie (Or.inr hk)
  ·
    obtain ⟨L₀, hL₀n, hinv, htype⟩ := hI _ (S289.natCard_linkGrp_lt hL) _ hΦ
      (oddCore_linkGrp_eq_bot hL) omegaGen_linkRestrict htr hk
    have hau' := hinv _ hJm _ hau
    have hmuC : ∃ c ∈ (L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom,
        e ⟨oddQuotMk t ⟨u, hutC⟩, huN'⟩ * c ≠ c * e ⟨oddQuotMk t ⟨u, hutC⟩, huN'⟩ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hne⟩ := hmu
      exact hne (S289.commute_of_map e hLN huN' hcon y hy)
    have hCeq := S289.eq_of_le_of_exitType hC htype (S289.le_of_moved hL₀n hC hau' hmuC)
    have huL : oddQuotMk t ⟨u, hutC⟩ ∈ L := S289.mem_of_map_mem e huN' (by rw [hCeq]; exact hau')
    have hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L := S289.mem_of_map_mem e hwN' (by
      rw [hCeq]
      exact hinv _ (subgroupOf_mem_linkRestrict (t := t) hF.memK) _
        (S289.isUniqueInvolution_link_w hL hF))
    let eF : ↥L ≃* ↥L₀ := eL.trans (MulEquiv.subgroupCongr hCeq)
    have hLk : (IsSimpleGroup ↥L ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
          (LieModel ↥L .PSL 3 p f ∨ LieModel ↥L .PSU 3 p f)) ∨
        (Group.IsPerfect ↥L ∧ NativeSporadic.IsSporadic (↥L ⧸ Subgroup.center ↥L) .M12) := by
      rcases htype with ⟨hs, p, f, hp, hp2, hk'⟩ | ⟨-, he12⟩
      · exact Or.inl ⟨eF.isSimpleGroup, p, f, hp, hp2,
          hk'.imp (LieType.CurtisTits.lieModel_of_mulEquiv eF.symm)
            (LieType.CurtisTits.lieModel_of_mulEquiv eF.symm)⟩
      · exact Or.inr ⟨hLc.1.1, Nonempty.map
          (fun e12 => (QuotientGroup.congr _ _ eF (Subgroup.map_center_eq eF)).trans e12) he12⟩
    exact S289.alphaOf_eq_bot_of_innerFour hB hutC hwtC (hα ↥L hLk) huL hwL hmu hmw hmuw
  · exact (S289.e8_not_isComponent hk.1 hC).elim
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmu
    exact hne (S289.commute_of_map e hLN huN'
      (S289.e64_commute omegaGen_linkRestrict hk.1 hC hJm hau) y hy)
  · have hAOFL : Q3NM.AutOddFree ↥L :=
      Q3NM.AutOddFree.of_mulEquiv eL.symm (S289.sp6_autOddFree hk.2.1 hC)
    have hS : IsSimpleGroup (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t)) :=
      Vtx.isSimpleGroup_of_exLie (Or.inl hk.2.1)
    exact S289.alphaOf_eq_bot_of_autFree hB hAOFL hm3.2.1 hutC
      (S289.mem_normalizer_of_map e hLN (S289.normal_of_simple_quot hS hC) huN') hmu
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmu
    exact hne (S289.commute_of_map e hLN huN' (S289.wNormal_commute hΦ.hyp hk.1 hC hJm hau) y hy)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
