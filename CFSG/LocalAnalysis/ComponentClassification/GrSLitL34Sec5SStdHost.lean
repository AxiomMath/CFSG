module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCyclic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourDefs
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.Quasithin.SteinbergCFIndexThreeComponentTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.Sporadic.Recognition.ONMultiplierCert
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

private theorem center_eq_bot_of_l316 {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 2 (center X))
    (h316 : Blueprint.LieModel (X ⧸ center X) .PSL 3 2 4) : center X = ⊥ := by
  classical
  obtain ⟨-, F, hFfield, hFfinite, hFcard, ⟨eS⟩⟩ :=
    h316.statedClassicalModel_of_ne_zero (by norm_num)
  let fieldF : Field F := hFfield
  let finiteF : Finite F := hFfinite
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 16 := by
    rw [Fintype.card_eq_nat_card, hFcard]
    norm_num
  have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) = 3 := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier
      (k := F) (n := 3) le_rfl (by omega)
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hcard]
    norm_num
  have hcongr : (X ⧸ center X) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    eS.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have hcardX : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (X ⧸ center X)) = 3 := by
    rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr hcongr]
    exact hcardM
  have hodd : Odd (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (X ⧸ center X))) := by
    rw [hcardX]
    norm_num
  exact (CFSG.GH74.Generic.noTwoCover_of_odd_hopfMultiplier (X := X ⧸ center X) hodd)
    X hX hZ ⟨MulEquiv.refl _⟩

section Host

theorem isComponent_or_swap_of_isComponent_centralizer_l34
    (hcat : L34CyclicProperFixedCatalog) (hGe : GSThmB.CF24cCenterGe)
    (hSuz6 : RankTwoL3Four.SuzMultiplierSix)
    {Y : Type} [Group Y] [Finite Y]
    (hK : SectionRank.IsKGroupCat Y) (hO : pPrimeCore 2 Y = ⊥) {t : Y} (ht : orderOf t = 2)
    {D : Subgroup Y} (hDt : D ≤ centralizer ({t} : Set Y))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set Y))))
    (hDL : Blueprint.LieModel (↥D ⧸ center ↥D) .PSL 3 2 2)
    {w : Y} (hwD : w ∈ D) (hwc : ∀ d ∈ D, w * d = d * w) (hw : orderOf w = 4)
    (hwZ : ∀ y : Y, w * w * y = y * (w * w))
    (hZD : ∀ c ∈ D, (∀ d ∈ D, c * d = d * c) → orderOf c = 2 → c = w * w) :
    IsComponent D ∨
      ∃ Q : Subgroup Y, IsComponent Q ∧ Q.map (MulAut.conj t).toMonoidHom ≠ Q ∧
        D ≤ Q ⊔ Q.map (MulAut.conj t).toMonoidHom := by
  classical
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hDE : D ≤ layer Y := CFSG.SeitzReduction.isComponent_centralizer_le_layer hO ht2 hDt hD
  obtain ⟨Q, hQ, -, hDle, -, -, hfix, -⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_le_layer ht2 hDt hD hDE
  by_cases hQt : Q.map (MulAut.conj t).toMonoidHom = Q
  · have hDQ : D ≤ Q := (hfix hQt).1
    have hDcompQ : IsComponent (D.subgroupOf (Q ⊓ centralizer ({t} : Set Y))) := (hfix hQt).2
    by_cases hDQeq : D = Q
    · rw [← hDQeq] at hQ
      exact Or.inl hQ
    · exfalso
      have htnorm : t ∈ Subgroup.normalizer (Q : Set Y) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQt
      let σ : MulAut ↥Q := Q.normalizerMonoidHom ⟨t, htnorm⟩
      have hσapply : ∀ x : ↥Q, ((σ x : ↥Q) : Y) = t * (x : Y) * t⁻¹ :=
        fun x => Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨t, htnorm⟩ x
      have htt : t * t = 1 := by rw [← sq]; exact ht2
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hσ2 : σ * σ = 1 := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        change ((σ (σ x) : ↥Q) : Y) = ((x : ↥Q) : Y)
        rw [hσapply, hσapply]
        calc t * (t * (x : Y) * t⁻¹) * t⁻¹ = (t * t) * (x : Y) * (t⁻¹ * t⁻¹) := by group
          _ = x := by rw [htt, hti, htt]; group
      have hσ : ∀ y, σ (σ y) = y := fun y => by
        have h := congrArg (fun f : MulAut ↥Q => f y) hσ2
        simpa using h
      let C : Subgroup Y := centralizer ({t} : Set Y)
      let P : Subgroup ↥Q := D.subgroupOf Q
      let K : Subgroup Y := Q ⊓ C
      have hPF : P ≤ fixedSubgroup σ := by
        rintro x hx
        change σ x = x
        apply Subtype.ext
        rw [hσapply]
        have hxD : ((x : ↥Q) : Y) ∈ D := Subgroup.mem_subgroupOf.mp hx
        have hxc : ((x : ↥Q) : Y) ∈ C := hDt hxD
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxc
        calc t * (x : Y) * t⁻¹ = (x : Y) * t * t⁻¹ := by rw [← hcomm]
          _ = (x : Y) := by group
      have hσfixCent : ∀ x : ↥Q, σ x = x → ((x : ↥Q) : Y) ∈ C := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hval : t * (x : Y) * t⁻¹ = (x : Y) := by
          have h := congrArg Subtype.val hx
          rwa [hσapply] at h
        calc (x : Y) * t = (t * (x : Y) * t⁻¹) * t := by rw [hval]
          _ = t * (x : Y) := by group
      let eAmb : ↥(fixedSubgroup σ) ≃* ↥K :=
        { toFun := fun x => ⟨((x : ↥Q) : Y), by
            exact Subgroup.mem_inf.mpr ⟨(x : ↥Q).2, hσfixCent x x.2⟩⟩
          invFun := fun y => ⟨⟨((y : ↥K) : Y), (Subgroup.mem_inf.mp (y : ↥K).2).1⟩, by
            apply Subtype.ext
            simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
            rw [hσapply]
            have hyC : ((y : ↥K) : Y) ∈ C := (Subgroup.mem_inf.mp (y : ↥K).2).2
            have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hyC
            calc t * ((y : ↥K) : Y) * t⁻¹ = ((y : ↥K) : Y) * t * t⁻¹ := by rw [← hcomm]
              _ = ((y : ↥K) : Y) := by group⟩
          left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun y => by apply Subtype.ext; rfl
          map_mul' := fun x y => rfl }
      have hmapL : (P.subgroupOf (fixedSubgroup σ)).map eAmb.toMonoidHom = D.subgroupOf K := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          change ((x : ↥Q) : Y) ∈ D
          exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
        · intro hy
          have hyD : ((y : ↥K) : Y) ∈ D := Subgroup.mem_subgroupOf.mp hy
          have hyK : ((y : ↥K) : Y) ∈ K := (y : ↥K).2
          have hyQ : ((y : ↥K) : Y) ∈ Q := (Subgroup.mem_inf.mp hyK).1
          refine ⟨⟨⟨((y : ↥K) : Y), hyQ⟩, ?_⟩, ?_, ?_⟩
          · apply Subtype.ext
            simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
            rw [hσapply]
            have hyC : ((y : ↥K) : Y) ∈ C := (Subgroup.mem_inf.mp hyK).2
            have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hyC
            calc t * ((y : ↥K) : Y) * t⁻¹ = ((y : ↥K) : Y) * t * t⁻¹ := by rw [← hcomm]
              _ = ((y : ↥K) : Y) := by group
          · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hyD)
          · apply Subtype.ext
            rfl
      have hL1comp : IsComponent (P.subgroupOf (fixedSubgroup σ)) :=
        ((CFSG.LocalCores.component_isomorphism eAmb).1 _).mpr (by
          rw [hmapL]
          exact hDcompQ)
      have hPp : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) :=
        (CFSG.LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2
          Nat.prime_two (CFSG.FeitThompson.isSolvable_of_odd_natCard _
            (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card))).1 _ hL1comp
      have hPq : IsQuasisimple ↥P :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPF) hL1comp.1
      have hPne : P ≠ ⊤ := by
        intro hPtop
        apply hDQeq
        apply le_antisymm hDQ
        intro q hq
        have hqP : (⟨q, hq⟩ : ↥Q) ∈ P := by rw [hPtop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hqP
      have hPqGW : CFSG.GorensteinWalter.IsQuasisimple ↥P :=
        ⟨CFSG.LocalCores.isQuasisimple_nontrivial hPq, hPq.1.commutator_eq_top, hPq.2.1⟩
      have hPO : pPrimeCore 2 ↥P ≤ center ↥P :=
        CFSG.GorensteinWalter.pPrimeCore_le_center_of_isQuasisimple hPqGW
      have hZP : Open.fusionZStar ↥P = center ↥P :=
        CFSG.ComponentClassification.GrSLit.GrS5.fusionZStar_eq_center_of_le
          hPq.1.commutator_eq_top hPO
      let eP : ↥P ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDQ
      have htype : IsL34Type (↥P ⧸ Open.fusionZStar ↥P) :=
        Blueprint.LieModel.of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hZP).trans
            (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv eP)).symm hDL
      have htype' : Blueprint.LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 :=
        Blueprint.LieModel.of_mulEquiv
          (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv eP).symm hDL
      have hwword : orderOf (w * w) = 2 := by
        have hw4 : w ^ 4 = 1 := by
          have h := pow_orderOf_eq_one w
          rwa [hw] at h
        have hww2 : (w * w) ^ 2 = 1 := by
          have hsq : w * w = w ^ 2 := by rw [sq]
          rw [hsq, ← pow_mul, show 2 * 2 = 4 by norm_num]
          exact hw4
        have hwwne : w * w ≠ 1 := by
          intro h
          have h2 : w ^ 2 = 1 := by rw [sq]; exact h
          have h1 : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
          rw [hw] at h1
          omega
        exact orderOf_eq_prime hww2 hwwne
      have hrank : CFSG.pRank 2 ↥(Open.fusionZStar ↥P) ≤ 1 := by
        rw [CFSG.pRank_congr_of_mulEquiv (MulEquiv.subgroupCongr hZP) 2]
        let uP : ↥P := ⟨⟨w * w, hDQ (mul_mem hwD hwD)⟩, mul_mem hwD hwD⟩
        have huPcent : uP ∈ center ↥P := by
          rw [Subgroup.mem_center_iff]
          intro p
          apply Subtype.ext
          apply Subtype.ext
          exact (hwZ (p : Y)).symm
        let u : ↥(center ↥P) := ⟨uP, huPcent⟩
        have huord : orderOf u = 2 := by
          rw [← Subgroup.orderOf_coe u, ← Subgroup.orderOf_coe uP,
            ← Subgroup.orderOf_coe (uP : ↥Q)]
          simpa [uP] using hwword
        have huniq : ∀ t' : ↥(center ↥P), orderOf t' = 2 → t' = u := by
          intro t' ht'
          have ht'P : orderOf (t' : ↥P) = 2 := (Subgroup.orderOf_coe t').trans ht'
          have hmem : eP (t' : ↥P) ∈ center ↥D := by
            rw [← Subgroup.map_center_eq eP]
            exact Subgroup.mem_map_of_mem eP.toMonoidHom t'.2
          have hcenD : ∀ d ∈ D,
              ((eP (t' : ↥P) : ↥D) : Y) * d = d * ((eP (t' : ↥P) : ↥D) : Y) := by
            intro d hd
            exact (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hmem ⟨d, hd⟩)).symm
          have hordD : orderOf ((eP (t' : ↥P) : ↥D) : Y) = 2 := by
            rw [Subgroup.orderOf_coe (eP (t' : ↥P))]
            rw [MulEquiv.orderOf_eq eP (t' : ↥P)]
            exact ht'P
          have ht'Y : ((eP (t' : ↥P) : ↥D) : Y) = w * w :=
            hZD _ (eP (t' : ↥P)).2 hcenD hordD
          have ht'Y' : ((t' : ↥P) : Y) = w * w := ht'Y
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          rw [ht'Y']
        exact CFSG.GH74.GLS.IVK.Lifted.pRank_two_le_one_of_unique_involution huord huniq
      have hwQmem : w ∈ Q := hDQ hwD
      have hwwQmem : w * w ∈ Q := mul_mem hwQmem hwQmem
      have hwwDmem : w * w ∈ D := mul_mem hwD hwD
      have hwwQcent : (⟨w * w, hwwQmem⟩ : ↥Q) ∈ center ↥Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        apply Subtype.ext
        exact (hwZ (q : Y)).symm
      have hwwordQ : orderOf (⟨w * w, hwwQmem⟩ : ↥Q) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨w * w, hwwQmem⟩ : ↥Q)]
        exact hwword
      have hcases := hcat ↥Q hQ.1
        (CFSG.Quasithin.SteinbergCF.isPGroup_center_of_isComponent hO hQ)
        (by
          let simpleQ : IsSimpleGroup (↥Q ⧸ center ↥Q) := hQ.1.2.1
          exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK Q
            (QuotientGroup.mk' (center ↥Q)) (QuotientGroup.mk'_surjective _))
        σ hσ P hPF hPp hPne htype hrank
      rcases hcases with hSuz | hON | hL316
      ·
        have hfixEq : fixedSubgroup σ = CFSG.ComponentClassification.CatFactsL4U4.OutInv.fixSub σ := by
          ext x
          exact Iff.rfl
        have hPF' : P ≤ CFSG.ComponentClassification.CatFactsL4U4.OutInv.fixSub σ := by
          rw [← hfixEq]
          exact hPF
        have hL1comp' : IsComponent
            (P.subgroupOf (CFSG.ComponentClassification.CatFactsL4U4.OutInv.fixSub σ)) := by
          rw [← hfixEq]
          exact hL1comp
        obtain ⟨e⟩ := hSuz
        have hZle : (center ↥P).map P.subtype ≤ center ↥Q :=
          hGe ↥Q hQ.1
            (CFSG.Quasithin.SteinbergCF.isPGroup_center_of_isComponent hO hQ)
            ⟨e⟩ σ (MulEquiv.ext hσ) P hPF' hL1comp' htype'
        have hwPcent : (⟨⟨w, hwQmem⟩, hwD⟩ : ↥P) ∈ center ↥P := by
          rw [Subgroup.mem_center_iff]
          intro p
          apply Subtype.ext
          apply Subtype.ext
          exact (hwc (p : Y) (Subgroup.mem_subgroupOf.mp p.2)).symm
        have hwQcent : (⟨w, hwQmem⟩ : ↥Q) ∈ center ↥Q :=
          hZle (Subgroup.mem_map_of_mem P.subtype hwPcent)
        have hwQord : orderOf (⟨w, hwQmem⟩ : ↥Q) = 4 := by
          rw [← Subgroup.orderOf_coe (⟨w, hwQmem⟩ : ↥Q)]
          exact hw
        have hwQordC : orderOf (⟨⟨w, hwQmem⟩, hwQcent⟩ : ↥(center ↥Q)) = 4 := by
          rw [← Subgroup.orderOf_coe (⟨⟨w, hwQmem⟩, hwQcent⟩ : ↥(center ↥Q))]
          exact hwQord
        have h4 : 4 ∣ Nat.card (center ↥Q) := by
          rw [← hwQordC]
          exact orderOf_dvd_natCard _
        let q : ↥Q →* Blueprint.NativeSporadic.Suz :=
          e.toMonoidHom.comp (QuotientGroup.mk' (center ↥Q))
        have hq : Function.Surjective q :=
          e.surjective.comp (QuotientGroup.mk'_surjective _)
        have hker : q.ker = center ↥Q := by
          ext x
          rw [MonoidHom.mem_ker]
          change e (QuotientGroup.mk' (center ↥Q) x) = 1 ↔ _
          rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have hZ6ker : Nat.card q.ker ∣ 6 := hSuz6 ↥Q hQ.1.1 q hq hker.le
        have hZ6 : Nat.card (center ↥Q) ∣ 6 := by
          rwa [hker] at hZ6ker
        exact absurd (h4.trans hZ6) (by norm_num)
      ·
        obtain ⟨e⟩ := hON
        have hZbot : center ↥Q = ⊥ :=
          CFSG.Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate hQ.1.1
            (CFSG.Quasithin.SteinbergCF.isPGroup_center_of_isComponent hO hQ) e
        rw [hZbot] at hwwQcent
        have hww1 : w * w = 1 := by
          have h := Subgroup.mem_bot.mp hwwQcent
          simpa using congrArg Subtype.val h
        rw [hww1, orderOf_one] at hwword
        omega
      ·
        have hZbot : center ↥Q = ⊥ :=
          center_eq_bot_of_l316 hQ.1
            (CFSG.Quasithin.SteinbergCF.isPGroup_center_of_isComponent hO hQ) hL316
        rw [hZbot] at hwwQcent
        have hww1 : w * w = 1 := by
          have h := Subgroup.mem_bot.mp hwwQcent
          simpa using congrArg Subtype.val h
        rw [hww1, orderOf_one] at hwword
        omega
  · exact Or.inr ⟨Q, hQ, hQt, hDle⟩

end Host

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
