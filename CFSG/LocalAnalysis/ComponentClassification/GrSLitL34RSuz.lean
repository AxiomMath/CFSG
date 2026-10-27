module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCheck

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace L34RSuz

theorem pPrimeCore_fixedSubgroup_eq_bot
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.Carrier .Suz) {σ : MulAut Q}
    (hσ : ∀ y, σ (σ y) = y) : pPrimeCore 2 (fixedSubgroup σ) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS, hna⟩ := hQ
  have : IsSimpleGroup (Q ⧸ center Q) := hS
  have hZmap : (center Q).map σ.toMonoidHom = center Q :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  set π := QuotientGroup.mk' (center Q) with hπ
  set σ' : MulAut (Q ⧸ center Q) := QuotientGroup.congr (center Q) (center Q) σ hZmap
    with hσ'def
  have hσ'π : ∀ x, π (σ x) = σ' (π x) := fun x => rfl
  have hσ'2 : ∀ y, σ' (σ' y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) y
    rw [← hσ'π, ← hσ'π, hσ]
  have hOS : pPrimeCore 2 (fixedSubgroup σ') = ⊥ := by
    by_cases h1 : σ' = 1
    · have hO : pPrimeCore 2 (Q ⧸ center Q) = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 (Q ⧸ center Q)) with h | h
        · exact h
        · exfalso
          have hodd : Odd (Nat.card (pPrimeCore 2 (Q ⧸ center Q))) :=
            Nat.coprime_two_left.mp pPrimeCore_coprime_card
          have hc : Nat.card (Blueprint.NativeSporadic.Carrier .Suz) = 448345497600 :=
            Sporadic.Suz.card_Suz
          rw [h, card_top, Nat.card_congr e.toEquiv, hc] at hodd
          exact Nat.not_odd_iff_even.mpr ⟨224172748800, by norm_num⟩ hodd
      have htop : fixedSubgroup σ' = ⊤ := by
        rw [eq_top_iff]
        intro y _
        change σ' y = y
        rw [h1]
        rfl
      rw [htop, CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 ⊤
        Subgroup.IsSubnormal.top, hO, bot_subgroupOf]
    · have hord : orderOf σ' = 2 :=
        orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hσ'2 y) h1
      have h := CatLeaf.oddCore_fixedSubgroup_eq_bot_of_mulAut hna
        (CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Suz
          hna e) hord
      rwa [Sporadic.HeldB.oddCore_eq_pPrimeCore_two'] at h
  have hnorm : (((fixedSubgroup σ).map π).subgroupOf (fixedSubgroup σ')).Normal :=
    LocalAnalysis.ComponentInitial.fixedImage_normal (QuotientGroup.ker_mk' (center Q)).le
      (QuotientGroup.mk'_surjective (center Q)) hσ hσ'π
  set I := ((fixedSubgroup σ).map π).subgroupOf (fixedSubgroup σ') with hIdef
  have hOI : pPrimeCore 2 ↥I = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 I hnorm.isSubnormal, hOS,
      bot_subgroupOf]
  have hπC : ∀ x : fixedSubgroup σ, (π.comp (fixedSubgroup σ).subtype) x ∈ fixedSubgroup σ' :=
    fun x => by
      have hx : σ x = x := x.2
      change σ' (π x) = π x
      rw [← hσ'π, hx]
  set f₀ := (π.comp (fixedSubgroup σ).subtype).codRestrict (fixedSubgroup σ') hπC with hf₀
  have hfI : ∀ x, f₀ x ∈ I := fun x => mem_subgroupOf.mpr ⟨x, x.2, rfl⟩
  set f := f₀.codRestrict I hfI with hf
  have hfs : Function.Surjective f := by
    rintro ⟨⟨y, hy⟩, hyI⟩
    obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp hyI
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hmap : (pPrimeCore 2 (fixedSubgroup σ)).map f ≤ ⊥ :=
    hOI ▸ GrSLit.map_pPrimeCore_le_pPrimeCore f hfs
  rw [eq_bot_iff]
  intro c hc
  have hfc : f c = 1 := mem_bot.mp (hmap (mem_map_of_mem f hc))
  have hcZ : ((c : fixedSubgroup σ) : Q) ∈ center Q := by
    have h := congrArg (fun z : ↥I => ((z : fixedSubgroup σ') : Q ⧸ center Q)) hfc
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨k, hk⟩ := hZ ⟨_, hcZ⟩
  have h1 : orderOf ((c : fixedSubgroup σ) : Q) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have h2 : orderOf ((c : fixedSubgroup σ) : Q) ∣ Nat.card (pPrimeCore 2 (fixedSubgroup σ)) := by
    have h := orderOf_dvd_natCard (⟨c, hc⟩ : pPrimeCore 2 (fixedSubgroup σ))
    rwa [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 (fixedSubgroup σ))) :=
    Nat.Coprime.pow_left k pPrimeCore_coprime_card
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [mem_bot]
  exact Subtype.ext (orderOf_eq_one_iff.mp h3)

end L34RSuz

theorem suzDoubleCoverL34Input_of_centerGe
    (hGe : GSThmB.CF24cCenterGe) : SuzDoubleCoverL34Input := by
  intro Q _ _ hQ hZ _ ⟨e⟩ σ hσ P hPF hP _ htype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : fixedSubgroup σ = CatFactsL4U4.OutInv.fixSub σ := by
    ext x
    exact Iff.rfl
  have hOC := L34RSuz.pPrimeCore_fixedSubgroup_eq_bot hQ hZ e hσ
  rw [hfix] at hOC hPF hP
  obtain ⟨hs, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2
    (P.subgroupOf (CatFactsL4U4.OutInv.fixSub σ))).1 hP
  have hcore : pPrimeCore 2 ↥(P.subgroupOf (CatFactsL4U4.OutInv.fixSub σ)) = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hs
    rw [hOC, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    exact h1
  have hP'q : IsQuasisimple ↥(P.subgroupOf (CatFactsL4U4.OutInv.fixSub σ)) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)).1 hq
  have hPc : IsComponent (P.subgroupOf (CatFactsL4U4.OutInv.fixSub σ)) := ⟨hP'q, hs⟩
  let eP := subgroupOfEquivOfLe hPF
  have hPq : IsQuasisimple ↥P := LocalCores.isQuasisimple_of_mulEquiv eP hP'q
  have hPO : pPrimeCore 2 ↥P = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eP, hcore, Subgroup.map_bot]
  have hZP : Open.fusionZStar ↥P = center ↥P :=
    GrS5.fusionZStar_eq_center_of_le hPq.1.commutator_eq_top (by rw [hPO]; exact bot_le)
  have hle : (center ↥P).map P.subtype ≤ center Q :=
    hGe Q hQ hZ ⟨e⟩ σ (MulEquiv.ext hσ) P hPF hPc
      (LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZP) htype)
  have hZ6 : Nat.card (center Q) ∣ 6 := by
    let q : Q →* Blueprint.NativeSporadic.Suz :=
      e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : q.ker = center Q := by
      ext x
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
      rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h := RankTwoSporadic.Suz.suzMultiplierSix Q hQ.1 q hq hker.le
    rwa [hker] at h
  have hZ2 : Nat.card (center Q) ≤ 2 := by
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    rw [hk] at hZ6 ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ k + 2 by omega)).trans hZ6
      omega
  have hZP2 : Nat.card (center ↥P) ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective P.subtype_injective] at h1
    omega
  rw [hZP]
  by_contra hr
  push Not at hr
  obtain ⟨A, -, hA4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (show 2 ≤ pRank 2 ↥(center ↥P) by omega)
  have := Subgroup.card_le_card_group A
  omega

theorem suzDoubleCoverL34Input_holds :
    SuzDoubleCoverL34Input :=
  suzDoubleCoverL34Input_of_centerGe GSThmB.cf24CenterGe

end CFSG.ComponentClassification.GrSLit
