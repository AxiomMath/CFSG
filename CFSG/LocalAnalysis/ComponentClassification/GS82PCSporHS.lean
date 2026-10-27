module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporSuz
public import CFSG.Milestones.ASVolI.I2Covers
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.TwoHSNoPowFour
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.TwoAltEightPowFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporHS
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


section Model

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.GSThmB.CovHS

theorem hs_outer_no_small {β : MulAut hsP} (hβ : β * β = 1)
    (hout : β ∉ OuterAutomorphisms.inner hsP) {M : Subgroup hsP}
    (hM : CFSG.Assembly.IsComponentOf M (fixSub β)) (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) :
    False := by
  have hι : Function.Injective hsP.subtype := Subtype.val_injective
  obtain ⟨eAut, heAut, hinner, -⟩ := hs_full_automorphism_model
  obtain ⟨x, hx⟩ := eAut.surjective β
  have hxι : ∀ z : hsP, ((β z : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * z * (x : Equiv.Perm (Fin 3850))⁻¹ := fun z => by
    rw [← hx, heAut x z, Subgroup.coe_inv]
  have hfix : (fixSub β).map hsP.subtype =
      hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850))) := by
    ext w
    simp only [mem_map, mem_inf, mem_fixSub, coe_subtype, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have h1 := hxι z
      rw [hz] at h1
      calc (z : Equiv.Perm (Fin 3850)) * x = (x * z * (x : Equiv.Perm (Fin 3850))⁻¹) * x := by
            rw [← h1]
        _ = x * z := by group
    · rintro ⟨hw, hwc⟩
      refine ⟨⟨w, hw⟩, Subtype.ext ?_, rfl⟩
      rw [hxι]
      calc (x : Equiv.Perm (Fin 3850)) * w * (x : Equiv.Perm (Fin 3850))⁻¹ =
          (w * x) * (x : Equiv.Perm (Fin 3850))⁻¹ := by rw [hwc]
        _ = w := by group
  have hM' : CFSG.Assembly.IsComponentOf (M.map hsP.subtype)
      (hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850)))) := by
    rw [← hfix]
    exact (isComponentOf_map_iff hι).2 hM
  have hMt' : Cov.SmallQ (↥(M.map hsP.subtype) ⧸ center ↥(M.map hsP.subtype)) :=
    smallQ_of_equiv (quotCenterEquiv (M.equivMapOfInjective _ hι)) hMt
  have hxx : x * x = 1 := eAut.injective (by rw [map_mul, hx, hβ, map_one])
  have hxP : (x : Equiv.Perm (Fin 3850)) ∉ hsP := by
    intro hxP
    apply hout
    rw [← hinner, ← hx]
    exact mem_map_of_mem _ (show x ∈ hsP.subgroupOf hsR from hxP)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxP (one_mem _)
  have hxo : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin 3850)) x.2 hxo
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hfx : (MulAut.conj g⁻¹).toMonoidHom (x : Equiv.Perm (Fin 3850)) = tp 3850 r.rep := by
    rw [hxg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB : CFSG.Assembly.IsComponentOf ((M.map hsP.subtype).map (MulAut.conj g⁻¹).toMonoidHom)
      (hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) := by
    have h := (isComponentOf_map_iff hfinj).2 hM'
    rwa [map_conj_inf_centralizer hsP (hsP.inv_mem hg), Set.image_singleton, hfx] at h
  have hBt := smallQ_of_equiv
    (quotCenterEquiv ((M.map hsP.subtype).equivMapOfInjective _ hfinj)) hMt'
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · dsimp only at hB
    exact hsC1_no_component hB
  · dsimp only at hxg
    exact hxP (by rw [hxg]; exact hsP.mul_mem (hsP.mul_mem hg t2_mem) (hsP.inv_mem hg))
  · dsimp only at hB
    have hC : CFSG.QuasithinUnique.Id2519.HSAut.outerC =
        hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) := rfl
    rw [← hC] at hB
    exact outerC_no_small hB hBt
  · dsimp only at hB
    exact c4_no_component hB

end Model

theorem card_sylow_of_card {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (R : Sylow p G)
    {k m : ℕ} (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) : Nat.card R = p ^ k := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hidx := (R : Subgroup G).index_mul_card
  have hnd := R.not_dvd_index
  rw [hj, hG] at hidx
  rw [hj]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · exfalso
    apply hnd
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d + 1 := ⟨k - j - 1, by omega⟩
    have h1 : R.index * p ^ j = p ^ j * (p ^ (d + 1) * m) := by rw [hidx]; ring
    have h2 : R.index = p ^ (d + 1) * m :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) (by rw [mul_comm]; exact h1)
    rw [h2, pow_succ]
    exact Dvd.dvd.mul_right (dvd_mul_left p _) m
  · rfl
  · exfalso
    apply hm
    obtain ⟨d, rfl⟩ : ∃ d, j = k + d + 1 := ⟨j - k - 1, by omega⟩
    have h1 : p ^ k * (R.index * p ^ (d + 1)) = p ^ k * m := by rw [← hidx]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) h1
    rw [← h2, pow_succ]
    exact Dvd.dvd.mul_left (dvd_mul_left p _) _

theorem card_of_lieModel_psl_two_five {X : Type} [Group X] (hL : LieModel X .PSL 2 5 1) :
    Nat.card X = 60 := by
  have ha := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL
  obtain ⟨-, h1, -⟩ := CatLeafProof.lieOrderFormulasInput X .PSL 2 5 1 ha hL
  have hd : CatLeaf.lieOrderDivisor .PSL 2 (5 ^ 1) = 2 := by decide
  have hn : CatLeaf.lieOrderNumerator .PSL 2 (5 ^ 1) = 120 := by decide
  rw [hd, hn] at h1
  omega

theorem mem_center_of_center_map_eq_bot {Y : Type} [Group Y] (hO : pPrimeCore 2 Y = ⊥)
    {T : Subgroup Y} (hZP : center (T.map (rho Y)) = ⊥) {x : T} (hx : x ∈ center T) :
    (x : Y) ∈ center Y := by
  rw [← ker_rho hO, MonoidHom.mem_ker]
  have h1 : (rho Y).subgroupMap T x ∈ center (T.map (rho Y)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := (rho Y).subgroupMap_surjective T y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hx y)]
  rw [hZP, mem_bot] at h1
  exact congrArg Subtype.val h1

theorem false_of_hs (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hfree : CatalogueU.SporadicOddCoreFree .HS)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .HS) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  have hna := nonabelian_quot h.quasisimple h.oddCore
  set e' := (quotEquiv h.oddCore).trans e
  obtain ⟨σ, hI⟩ := exists_image_of_oddCore h hTtop (oddCore_fixed_eq_bot hfree hna e')
  obtain ⟨hd, hin, hout⟩ := SporTable.comp_data hMcard hfree hna e' hI.proper
  obtain ⟨eT⟩ := hI.fus
  set P := T.map (rho Y) with hPdef
  have hZT : Open.fusionZStar T = center T :=
    fusionZStar_eq_center_of_quasisimple hI.quasiT (by
      have := LocalCores.isQuasisimple_nontrivial hI.quasiT
      rw [hI.oddCoreT]; exact bot_ne_top)
  have hZP : Open.fusionZStar P = center P :=
    fusionZStar_eq_center_of_quasisimple hI.quasiP (by
      have := LocalCores.isQuasisimple_nontrivial hI.quasiP
      rw [hI.oddCoreP]; exact bot_ne_top)
  set c := Nat.card (T ⧸ center T) with hcdef
  have hcP : Nat.card (P ⧸ Open.fusionZStar P) = c := by
    rw [hcdef, hI.card]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZP).toEquiv
  have hcT : Nat.card (T ⧸ Open.fusionZStar T) = c :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZT).toEquiv
  have hrow_in : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range → c = 360 := fun hσ => by
    have := hin hσ
    rw [hcP] at this
    exact this
  have hrow_out : σ ∉ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range →
      c = 20160 ∨ c ∣ 1920 := fun hσ => by
    have := hout hσ
    rw [hcP] at this
    exact this
  have hperf : Group.IsPerfect Y := h.quasisimple.1
  have hZY : center Y ≠ ⊥ := by
    intro hb
    rw [hb] at hZ
    simp at hZ
  have hcent : ∀ d : Quot Y, orderOf d = 2 → Nat.card (centralizer ({d} : Set (Quot Y))) ≤ 7680 :=
    fun d hd => by
      rcases GrSLit.L34R.hs_card_centralizer e' hd with h1 | h1 <;> omega
  have hZP1 : 20160 ≤ c → center P = ⊥ := by
    intro hc
    by_contra hne
    have h2 : IsPGroup 2 (center P) := isPGroup_center_of_pPrimeCore_eq_bot hI.oddCoreP
    have : Nontrivial (center P) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact absurd (Subgroup.eq_bot_of_card_eq _ hk) hne
    obtain ⟨d, hdo⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hdo' : orderOf (((d : P) : Quot Y)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hdo]
    have hle : P ≤ centralizer ({((d : P) : Quot Y)} : Set (Quot Y)) := by
      intro x hx
      rw [mem_centralizer_singleton_iff]
      have := mem_center_iff.mp d.2 ⟨x, hx⟩
      exact congrArg Subtype.val this
    have h3 := Subgroup.card_le_of_le hle
    have h4 : Nat.card (P ⧸ center P) ≤ Nat.card P := by
      have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
      have h6 : 0 < Nat.card (center P) := Nat.card_pos
      nlinarith
    have h7 : Nat.card (P ⧸ center P) = c := by rw [hcdef, hI.card]
    have := hcent _ hdo'
    omega
  have hpow : ∀ w : Y, w ^ 4 ∈ center Y → w ^ 4 ≠ 1 → False := fun w hw hw1 =>
    CatFC.pow_four_ne_of_doubleCover_hs hperf hZ ⟨e⟩ hw hw1 w rfl
  rcases h.typC with ⟨τ, n, p, f, hp, hp2, -, hLm⟩ | ⟨n, hn, hA⟩ | ⟨hL, hEA⟩
  ·
    have hLm' := Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZT) hLm
    by_cases hσ : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · have h360 := hrow_in hσ
      rcases SporLie.tuple_of_dvd_360 hp2 hLm' (h360 ▸ dvd_rfl) with ht9 | ht5
      · simp only [Prod.mk.injEq] at ht9
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht9
        obtain ⟨t, hSL, hw⟩ := exists_sl2Facts hGA hGC hI.quasiT
          (isPGroup_center_of_pPrimeCore_eq_bot hI.oddCoreT) hI.centerT hp hp2 hLm'
        obtain ⟨w, hw4⟩ := hw rfl rfl
        have hw4' : (w : Y) ^ 4 = (t : Y) := by rw [← Subgroup.coe_pow, hw4]
        by_cases ht : (t : Y) ∈ center Y
        ·
          exact hpow w (hw4' ▸ ht) (by rw [hw4']; exact fun h1 => hSL.ne_one (Subtype.ext h1))
        ·
          set s : Y ⧸ center Y := QuotientGroup.mk' (center Y) (t : Y) with hsdef
          have hs1 : s ≠ 1 := by
            rw [hsdef, ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
            exact ht
          have hs2 : s ^ 2 = 1 := by
            rw [hsdef, ← map_pow, sq, ← Subgroup.coe_mul, hSL.mul_self, Subgroup.coe_one,
              map_one]
          have hcase : NativeSporadic.IsSporadic (Y ⧸ center Y) .HS := ⟨e⟩
          have hb := (ASVolI.burnsideI22P5_part_5 h.quasisimple hZY
            (Or.inr (Or.inr (Or.inr hcase)))).2.1.1
          have h2c : ASVolI.ChIJK.IsTwoCentralInvolution s := by
            by_contra hnot
            obtain ⟨k, hk4, hks⟩ := hb s hs2 hs1 hnot
            have hk : (t : Y)⁻¹ * k ∈ center Y := by
              rw [← QuotientGroup.eq]
              exact hks.symm
            have hz2 : ((t : Y)⁻¹ * k) ^ 2 = 1 := by
              have h1 : orderOf (⟨(t : Y)⁻¹ * k, hk⟩ : center Y) ∣ 2 :=
                hZ ▸ orderOf_dvd_natCard _
              rw [Subgroup.orderOf_mk] at h1
              exact orderOf_dvd_iff_pow_eq_one.1 h1
            have hkt : k = (t : Y) * ((t : Y)⁻¹ * k) := by group
            have hk2 : k ^ 2 = 1 := by
              have hcomm : Commute (t : Y) ((t : Y)⁻¹ * k) := mem_center_iff.mp hk (t : Y)
              rw [hkt, hcomm.mul_pow, hz2, mul_one, sq, ← Subgroup.coe_mul, hSL.mul_self,
                Subgroup.coe_one]
            have := orderOf_dvd_of_pow_eq_one hk2
            rw [hk4] at this
            norm_num at this
          obtain ⟨-, -, Q, hsQ, hQ⟩ := h2c
          have hcardHS : Nat.card (Y ⧸ center Y) = 2 ^ 9 * 86625 := by
            rw [Nat.card_congr (e.trans Sporadic.Schreier.hsPermEquiv).toEquiv,
              Sporadic.Schreier.card_hsP]
            norm_num
          have hQcard := card_sylow_of_card Q hcardHS (by norm_num)
          have hQle : (Q : Subgroup (Y ⧸ center Y)) ≤ centralizer ({s} : Set (Y ⧸ center Y)) :=
            fun x hx => mem_centralizer_singleton_iff.mpr (hQ x hx)
          have hC7680 : Nat.card (centralizer ({s} : Set (Y ⧸ center Y))) = 7680 := by
            have h1 := Subgroup.card_dvd_of_le hQle
            rw [hQcard] at h1
            rcases GrSLit.L34R.hs_card_centralizer e (by
              rw [orderOf_eq_prime hs2 hs1]) with h2 | h2 <;> rw [h2] at h1 ⊢ <;> norm_num at h1
          set f := (QuotientGroup.mk' (center Y)).subgroupMap T
          have hfker : f.ker = ⊥ := by
            rw [eq_bot_iff]
            intro x hx
            rw [MonoidHom.mem_ker] at hx
            have hxZ : (x : Y) ∈ center Y := by
              have h1 : QuotientGroup.mk' (center Y) (x : Y) = 1 := congrArg Subtype.val hx
              rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
            have hxT : x ∈ center T := by
              rw [mem_center_iff]
              intro y
              exact Subtype.ext (mem_center_iff.mp hxZ y)
            rcases hSL.eq_of_mem_center hxT with h1 | h1
            · rw [h1]; exact one_mem _
            · exact absurd (h1 ▸ hxZ) ht
          have hTcard : Nat.card (T.map (QuotientGroup.mk' (center Y))) = Nat.card T := by
            have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
            rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
              ((QuotientGroup.mk' (center Y)).subgroupMap_surjective T)).toEquiv, hfker,
              Subgroup.card_bot, mul_one] at h1
            exact h1.symm
          have hT720 : Nat.card T = 720 := by
            have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
            rw [hSL.card_center, ← hcdef, hrow_in hσ] at h1
            exact h1
          have hTle : T.map (QuotientGroup.mk' (center Y)) ≤
              centralizer ({s} : Set (Y ⧸ center Y)) := by
            rintro _ ⟨x, hx, rfl⟩
            rw [mem_centralizer_singleton_iff, hsdef, ← map_mul, ← map_mul]
            have h1 := mem_center_iff.mp hSL.mem_center ⟨x, hx⟩
            have h2 : (x : Y) * (t : Y) = (t : Y) * x := congrArg Subtype.val h1
            rw [h2]
          have h1 := Subgroup.card_dvd_of_le hTle
          rw [hTcard, hT720, hC7680] at h1
          norm_num at h1
      · simp only [Prod.mk.injEq] at ht5
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht5
        have := card_of_lieModel_psl_two_five hLm'
        rw [← hcdef, hrow_in hσ] at this
        norm_num at this
    · rcases hrow_out hσ with h20160 | h1920
      · have hO := HarrisLit.T1.SporRow.oddLieOrder_of_lieModel hp hp2 hLm'
        rw [← hcdef, h20160] at hO
        exact HarrisLit.T1.SporRow.not_oddLieOrder_L34 hO
      · have ht := SporLie.tuple_of_dvd_1920 hp2 hLm' h1920
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        set θ : Quot Y ≃* Sporadic.Schreier.hsP := e'.trans Sporadic.Schreier.hsPermEquiv
        have hβ2 : MulAut.congr θ σ * MulAut.congr θ σ = 1 := by
          rw [← map_mul, show σ * σ = 1 from MulEquiv.ext fun y => hI.proper.1 y, map_one]
        have hβout : MulAut.congr θ σ ∉ OuterAutomorphisms.inner Sporadic.Schreier.hsP := by
          rintro ⟨q, hq⟩
          apply hσ
          refine ⟨θ.symm q, ?_⟩
          apply (MulAut.congr θ).injective
          rw [← hq]
          ext x
          simp [MulAut.congr_apply]
        have hfixeq : (fixedSubgroup σ).map θ.toMonoidHom =
            Sporadic.Schreier.fixSub (MulAut.congr θ σ) := by
          ext y
          rw [mem_map_equiv, Sporadic.Schreier.mem_fixSub,
            LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
          have hc : MulAut.congr θ σ y = θ (σ (θ.symm y)) := rfl
          rw [hc]
          constructor
          · intro hy
            rw [hy, MulEquiv.apply_symm_apply]
          · intro hy
            apply θ.injective
            rw [hy, MulEquiv.apply_symm_apply]
        have hM : CFSG.Assembly.IsComponentOf (P.map θ.toMonoidHom)
            (Sporadic.Schreier.fixSub (MulAut.congr θ σ)) := by
          rw [← hfixeq]
          exact (LocalAnalysis.ComponentInitial.isComponentOf_map_iff θ.injective).2
            ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
              hI.proper.2.1).2 hI.compP)
        have eTP : T ⧸ center T ≃* P ⧸ center P :=
          (QuotientGroup.quotientMulEquivOfEq hZT).symm.trans
            (eT.trans (QuotientGroup.quotientMulEquivOfEq hZP))
        have ePM := GSThmB.CovHS.quotCenterEquiv (P.equivMapOfInjective θ.toMonoidHom θ.injective)
        exact hs_outer_no_small hβ2 hβout hM (Or.inl ⟨5, 1, by norm_num, by norm_num, le_rfl,
          by norm_num, Blueprint.LieModel.of_mulEquiv (eTP.trans ePM) hLm'⟩)
  ·
    obtain ⟨hqA, hcardA, ⟨eA⟩⟩ := hA
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcn : c = n.factorial / 2 := by
      rw [← hcT, card_fusionZStar_eq, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup, Fintype.card_fin]
    have h7 : Nat.factorial 7 / 2 ≤ n.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le hn)
    have h2520 : Nat.factorial 7 / 2 = 2520 := by decide
    by_cases hσ : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · have := hrow_in hσ
      omega
    rcases hrow_out hσ with h20160 | h1920
    · have hn8 : n = 8 := eq_eight_of_factorial_div_two (hcn ▸ h20160)
      subst hn8
      have hZP' := hZP1 (by omega)
      set eO := equivQuotOddCore hI.oddCoreT
      have eZ : T ⧸ center T ≃* (T ⧸ pPrimeCore 2 T) ⧸ center (T ⧸ pPrimeCore 2 T) :=
        QuotientGroup.congr _ _ eO (Subgroup.map_center_eq eO)
      have hcardT : Nat.card (center T) = 2 := by
        have h1 : Nat.card (center T) = Nat.card (center (T ⧸ pPrimeCore 2 T)) := by
          rw [← Subgroup.map_center_eq eO, Subgroup.card_map_of_injective eO.injective]
        rw [h1, hcardA]
      have hAT : GH74.GLS.IsDoubleCoverOfAlt T 8 := ⟨hI.quasiT, hcardT, ⟨eZ.trans eA⟩⟩
      obtain ⟨z₀, hz₀⟩ : ∃ z₀ : center T, z₀ ≠ 1 := by
        have : Nontrivial (center T) := by
          rw [← Finite.one_lt_card_iff_nontrivial, hcardT]
          norm_num
        exact exists_ne 1
      obtain ⟨w, hw⟩ := CatFC.exists_pow_four_eq_of_doubleCover_alt8 hAT z₀.2
        (fun h1 => hz₀ (Subtype.ext h1))
      have hz₀Y := mem_center_of_center_map_eq_bot h.oddCore hZP' z₀.2
      have hw' : (w : Y) ^ 4 = ((z₀ : T) : Y) := by rw [← Subgroup.coe_pow, hw]
      exact hpow w (hw' ▸ hz₀Y) (by
        rw [hw']
        intro h1
        exact hz₀ (Subtype.ext (Subtype.ext h1)))
    · have := Nat.le_of_dvd (by norm_num) h1920
      omega
  ·
    have h20160 : c = 20160 := by
      rw [← hcT, card_fusionZStar_eq]
      exact OddStandard.GlueL34.card_eq_of_lieModel_psl34 hL
    have hZP' := hZP1 (by omega)
    have hcard : Nat.card (center T) ≤ 2 := by
      rw [← hZ, ← Subgroup.card_map_of_injective T.subtype_injective]
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact mem_center_of_center_map_eq_bot h.oddCore hZP' hx
    set eO := equivQuotOddCore hI.oddCoreT
    have hcard' : Nat.card (center (T ⧸ pPrimeCore 2 T)) ≤ 2 := by
      rw [← Subgroup.map_center_eq eO, Subgroup.card_map_of_injective eO.injective]
      exact hcard
    exact hEA (isElementaryAbelian_center_of_card_le_two hcard')

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
