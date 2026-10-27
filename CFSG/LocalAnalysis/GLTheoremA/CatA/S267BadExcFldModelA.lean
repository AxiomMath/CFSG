module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldTwoLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldConc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (range_rootSL2_of_isRoot)
open scoped commutatorElement


variable {τ : Tag} {K : Type} [Field K]

theorem modelAGen_frame [Finite K] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpQ : p ∣ Nat.card K ^ 2 - 1) :
    ModelGen.ModelAGen p (frameSize τ) ↥(adjointGroup τ K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hd := hrRootData_of hτ
  set X := ↥(adjointGroup τ K)
  obtain ⟨A₀, hA₀⟩ := exists_orderOf_eq_sl2 hp hpQ
  have hA₀p : A₀ ^ p = 1 := hA₀ ▸ pow_orderOf_eq_one A₀
  have hA₀1 : A₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA₀
    exact hp.one_lt.ne hA₀
  set E := frameHom hτ (K := K) hA₀p with hE
  have hEinj : Function.Injective E := frameHom_injective hτ hodd hA₀
  set i₀ := frame0 τ with hi₀
  set i₁ := frame1 hτ with hi₁
  have hi₁₀ : i₁ ≠ i₀ := frame1_ne_frame0 hτ
  set π : Multiplicative (ZMod p) × Multiplicative (ZMod p) →*
      (Fin (frameSize τ) → Multiplicative (ZMod p)) :=
    (MonoidHom.mulSingle (fun _ => Multiplicative (ZMod p)) i₀).coprod
      (MonoidHom.mulSingle (fun _ => Multiplicative (ZMod p)) i₁) with hπ
  have hπapp : ∀ u, π u = Pi.mulSingle i₀ u.1 * Pi.mulSingle i₁ u.2 := fun u => rfl
  have hπinj : Function.Injective π := by
    intro u v h
    have h0 := congrFun h i₀
    have h1 := congrFun h i₁
    rw [hπapp, hπapp] at h0 h1
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi₁₀,
      Pi.mulSingle_eq_of_ne hi₁₀.symm, mul_one, one_mul] at h0 h1
    exact Prod.ext h0 h1
  have hEπ : ∀ u, E (π u) = frameFactor (τ := τ) (K := K) hA₀p i₀ u.1 *
      frameFactor (τ := τ) (K := K) hA₀p i₁ u.2 := fun u => by
    rw [hπapp, map_mul, frameHom_mulSingle, frameHom_mulSingle]
  set A : Subgroup X := E.range with hA
  set A₁ : Subgroup X := (frameFactor (τ := τ) (K := K) hA₀p i₀).range with hA₁
  set A₁₂ : Subgroup X := (E.comp π).range with hA₁₂
  set J : Subgroup X := (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) with hJ
  set t : X := frameSL2 τ K i₀ (HSL (-1)) with ht
  have hAr : A = ⨆ i, (frameFactor (τ := τ) (K := K) hA₀p i).range := range_frameHom hτ hA₀p
  have hJq : CFSG.Open.IsQuasisimple ↥(rootSpan τ K (perpRoots τ)) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact isQuasisimple_perpLevi_F4 hK2
    · exact isQuasisimple_perpLevi_E6 hK2
    · exact isQuasisimple_perpLevi_E7 hK2
    · exact isQuasisimple_perpLevi_E8 hK2
  have hpJ : p ∣ Nat.card ↥(rootSpan τ K (perpRoots τ)) := by
    have hmem := coe_frameSL2_mem_perp (K := K) hτ hi₁₀ A₀
    have hord : orderOf ((frameSL2 τ K i₁ A₀ : X) : ModGL τ K) = p := by
      rw [Subgroup.orderOf_coe, orderOf_injective _ (frameSL2_injective i₁), hA₀]
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  have eJ : ↥J ≃* ↥(rootSpan τ K (perpRoots τ)) :=
    Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)
  have hJXq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv eJ.symm hJq
  have hpJX : p ∣ Nat.card ↥J := by rw [Nat.card_congr eJ.toEquiv]; exact hpJ
  have hfac0 : ∀ s, ∀ j ∈ rootSpan τ K (perpRoots τ),
      ((frameFactor (τ := τ) (K := K) hA₀p i₀ s : X) : ModGL τ K) * j =
        j * ((frameFactor (τ := τ) (K := K) hA₀p i₀ s : X) : ModGL τ K) := fun s j hj => by
    rw [frameFactor_apply]
    exact frameSL2_zero_commute_perp hτ _ hj
  have htcomm : ∀ B : SL2 K, frameSL2 τ K i₀ B * t = t * frameSL2 τ K i₀ B := fun B => by
    rw [ht, ← map_mul, ← map_mul, HSL_neg_one_mul_comm]
  have hL₁₂J : rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) ≤ rootSpan τ K (perpRoots τ) :=
    rootSpan_mono fun β hβ => ⟨hβ.1, hβ.2 _ (highNode_mem_frameTwoNodes hτ)⟩
  have hfac1 : ∀ s, ∀ l ∈ rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)),
      ((frameFactor (τ := τ) (K := K) hA₀p i₁ s : X) : ModGL τ K) * l =
        l * ((frameFactor (τ := τ) (K := K) hA₀p i₁ s : X) : ModGL τ K) := fun s l hl => by
    rw [frameFactor_apply, coe_frameSL2, frameRoot_frame1 hτ]
    have hmem : rootSL2 τ K (frameTwoRoot τ) (sl2PowHom hA₀p s) ∈
        (rootSL2 τ K (frameTwoRoot τ)).range := ⟨_, rfl⟩
    rw [range_rootSL2_of_isRoot (isRoot_frameTwoRoot hτ)] at hmem
    have h1 := rootSubgroup_frameTwo_le_centralizer (K := K) hτ (Or.inl rfl)
    have h2 := rootSubgroup_frameTwo_le_centralizer (K := K) hτ (Or.inr rfl)
    rw [one_smul] at h1
    rw [neg_one_smul] at h2
    exact (Subgroup.mem_centralizer_iff.1 (sup_le h1 h2 hmem) l hl).symm
  refine ⟨A, A₁, A₁₂, J, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      change (x : X) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := by
        funext i
        apply Multiplicative.toAdd.injective
        rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, ZMod.natCast_self,
          zero_mul]
      rw [this, map_one]
  ·
    rw [hA, card_range_of_injective' hEinj, Nat.card_pi, card_multiplicative_zmod,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ·
    rintro _ ⟨s, rfl⟩
    refine ⟨(s, 1), ?_⟩
    rw [MonoidHom.comp_apply, hEπ, map_one, mul_one]
  ·
    rintro _ ⟨u, rfl⟩
    exact ⟨π u, rfl⟩
  ·
    have hinj : Function.Injective (frameFactor (τ := τ) (K := K) hA₀p i₀) :=
      (frameSL2_injective i₀).comp (sl2PowHom_injective hA₀)
    rw [hA₁, card_range_of_injective' hinj, card_multiplicative_zmod]
  ·
    have hinj : Function.Injective (E.comp π) := hEinj.comp hπinj
    rw [hA₁₂, card_range_of_injective' hinj, Nat.card_prod, card_multiplicative_zmod, sq]
  ·
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf _ hp _
      (rootSpan_le_adjointGroup K _) ?_ ?_ hJq hpJ
    · rintro l hl _ ⟨s, rfl⟩
      exact (hfac0 s l hl).symm
    · intro g hg hcomm l hl
      have hgc := hcomm (frameFactor (τ := τ) (K := K) hA₀p i₀ (Multiplicative.ofAdd 1)) ⟨_, rfl⟩
      rw [frameFactor_apply, sl2PowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one,
        coe_frameSL2_frame0 hτ] at hgc
      have hC : ∀ c : (AlgebraicClosure K)ˣ, c ≠ 1 → c ^ 2 ≠ 1 →
          toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) c) ≤
            toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) (-1)) :=
        fun c hc1 hc2 => toralCentralizer_mulSingle_le hc1 hc2 hd.abs_le hd.highRoot_highNode (-1)
      have hgt := centralizer_rootSL2_highRoot_le hτ hp hp2 hpK hA₀p hA₀1 hC
        (Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩)
      exact (Subgroup.mem_normalizer_iff.1 (toralCentralizer_neg_one_le_normalizer hK2 hd.abs_le
        hd.eq_highRoot hd.highRoot_highNode hd.iform_eq_zero_iff hd.exists_nbr hgt) l).1 hl
  ·
    rw [hAr]
    refine iSup_le fun i => ?_
    by_cases hi : i = i₀
    · subst hi
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      rintro _ ⟨s, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subtype.ext (hfac0 s j (Subgroup.mem_subgroupOf.1 hj)).symm
    · refine le_trans ?_ (Subgroup.le_normalizer (H := J))
      rintro _ ⟨s, rfl⟩
      rw [hJ, Subgroup.mem_subgroupOf, frameFactor_apply]
      exact coe_frameSL2_mem_perp hτ hi _
  ·
    intro a ha hcm
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨-, hcomm⟩ := hcm
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp hJXq
      hpJX (MulAut.conj (E x)).toMonoidHom fun j hj => by
        have h1 := hcomm (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers (E x)))
        have h2 := (GLAPPrimeCoreOf p J).inv_mem h1
        rw [commutatorElement_inv, commutatorElement_def] at h2
        exact h2
    have hkey : ∀ i, i ≠ i₀ → ∀ B : SL2 K,
        A₀ ^ (Multiplicative.toAdd (x i)).val * B *
          (A₀ ^ (Multiplicative.toAdd (x i)).val)⁻¹ = B := by
      intro i hi B
      have hmem : frameSL2 τ K i B ∈ J := by
        rw [hJ, Subgroup.mem_subgroupOf]
        exact coe_frameSL2_mem_perp hτ hi B
      have h1 := hfix _ hmem
      change E x * frameSL2 τ K i B * (E x)⁻¹ = frameSL2 τ K i B at h1
      rw [frameHom_conj_frameSL2] at h1
      exact frameSL2_injective i h1
    have hx1 : ∀ i, i ≠ i₀ → x i = 1 := by
      intro i hi
      set C := A₀ ^ (Multiplicative.toAdd (x i)).val with hC
      have hcen : C ∈ Subgroup.center (SL2 K) :=
        mem_center_of_commute_uSL_vSL (mul_inv_eq_iff_eq_mul.1 (hkey i hi (uSL 1)))
          (mul_inv_eq_iff_eq_mul.1 (hkey i hi (vSL 1)))
      have hCp : C ^ p = 1 := by rw [hC, ← pow_mul, mul_comm, pow_mul, hA₀p, one_pow]
      have h1 := orderOf_dvd_of_pow_eq_one (eq_one_of_mem_center_sl2_of_pow hodd hcen hCp)
      rw [hA₀] at h1
      have h0 : (Multiplicative.toAdd (x i)).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact (ZMod.val_eq_zero _).1 h0
    refine ⟨x i₀, ?_⟩
    have hx : x = Pi.mulSingle i₀ (x i₀) := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, hx1 i hi]
    rw [hx, frameHom_mulSingle, Pi.mulSingle_eq_same]
  ·
    refine glaPLayer_perpJ_inf_frameTwo_ne_bot hτ hK2 hp hp2 hpK hA₀ ?_ ?_ ?_
    · refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
      rw [MonoidHom.comp_apply, hEπ]
      change frameFactor (τ := τ) (K := K) hA₀p i₀ (Multiplicative.ofAdd 1) *
        frameFactor (τ := τ) (K := K) hA₀p i₁ 1 = _
      rw [MonoidHom.map_one (frameFactor (τ := τ) (K := K) hA₀p i₁), mul_one, frameFactor_apply,
        sl2PowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]
    · refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
      rw [MonoidHom.comp_apply, hEπ]
      change frameFactor (τ := τ) (K := K) hA₀p i₀ 1 *
        frameFactor (τ := τ) (K := K) hA₀p i₁ (Multiplicative.ofAdd 1) = _
      rw [MonoidHom.map_one (frameFactor (τ := τ) (K := K) hA₀p i₀), one_mul, frameFactor_apply,
        sl2PowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one]
    · rintro _ ⟨u, rfl⟩ l hl
      rw [MonoidHom.comp_apply, hEπ, Subgroup.coe_mul]
      calc ((frameFactor (τ := τ) (K := K) hA₀p i₀ u.1 : X) : ModGL τ K) *
            ((frameFactor (τ := τ) (K := K) hA₀p i₁ u.2 : X) : ModGL τ K) * l
          = ((frameFactor (τ := τ) (K := K) hA₀p i₀ u.1 : X) : ModGL τ K) *
            (l * ((frameFactor (τ := τ) (K := K) hA₀p i₁ u.2 : X) : ModGL τ K)) := by
              rw [mul_assoc, hfac1 u.2 l hl]
        _ = l * ((frameFactor (τ := τ) (K := K) hA₀p i₀ u.1 : X) : ModGL τ K) *
            ((frameFactor (τ := τ) (K := K) hA₀p i₁ u.2 : X) : ModGL τ K) := by
              rw [← mul_assoc, hfac0 u.1 l (hL₁₂J hl)]
        _ = _ := by rw [mul_assoc]
  ·
    intro h1
    have h2 : HSL (-1 : Kˣ) = 1 := by
      apply frameSL2_injective i₀
      rw [map_one]
      exact h1
    have h3 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h2
    simp [coe_HSL] at h3
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 h3)
  ·
    rw [ht, ← map_pow, HSL_pow, show ((-1 : Kˣ) ^ 2) = 1 by norm_num, HSL_one, map_one]
  ·
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    exact (frameSL2_zero_commute_perp (K := K) hτ (HSL (-1)) (Subgroup.mem_subgroupOf.1 hj)).symm
  ·
    rw [hAr]
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, frameFactor_apply]
    by_cases hi : i = i₀
    · subst hi
      exact htcomm _
    · rw [ht]
      exact frameSL2_commute hτ hi _ _

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_adjointGroup_of_inner {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpQ : p ∣ Nat.card K ^ 2 - 1) (hS : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hBle : Nat.card B ≤ p ^ (frameSize τ + 1)) (eX : ↥(adjointGroup τ K) ≃* PSimple p S) :
    S267ConcA p S B := by
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  set φ : ↥(adjointGroup τ K) →* Ω := S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hn : 3 ≤ frameSize τ := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  exact ModelGen.concA_of_modelAGen hp hn hS hcore hZ hB hBC hBle φ hφ hφS
    (modelAGen_frame hτ hK2 hp hp2 (natCast_ne_zero_of_dvd_sq_sub_one hp hpQ) hpQ)

section Heads


theorem concA_badExcCore_F4_of_inner {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.F4 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBle : Nat.card B ≤ p ^ (frameSize .F4 + 1)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_F4] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .F4 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier hK5).2
    rw [Nat.card_of_subsingleton
      (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .F4 K))]
    exact hp.not_dvd_one)
  exact concA_of_adjointGroup_of_inner (Or.inl rfl) hK2 hp hp2 hpK hS hcore hZ hB hBC hBle eX

theorem concA_badExcCore_E6_of_inner {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hdvd1 : ¬ p ∣ Q.card - 1)
    (hBle : Nat.card B ≤ p ^ (frameSize .E6 + 1)) : S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hpK1 : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .E6 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact fun h => hpK1 (h.trans (Nat.gcd_dvd_right 3 _)))
  exact concA_of_adjointGroup_of_inner (Or.inr (Or.inl rfl)) hK2 hp hp2 hpK hS hcore hZ hB hBC
    hBle eX

theorem concA_badExcCore_E7_of_inner {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E7 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBle : Nat.card B ≤ p ^ (frameSize .E7 + 1)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E7] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .E7 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h.trans (Nat.gcd_dvd_left 2 _))))
  exact concA_of_adjointGroup_of_inner (Or.inr (Or.inr (Or.inl rfl))) hK2 hp hp2 hpK hS hcore hZ
    hB hBC hBle eX

theorem concA_badExcCore_E8_of_inner {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E8 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBle : Nat.card B ≤ p ^ (frameSize .E8 + 1)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E8] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .E8 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_hopfMultiplier hK5).2
    rw [Nat.card_of_subsingleton
      (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .E8 K))]
    exact hp.not_dvd_one)
  exact concA_of_adjointGroup_of_inner (Or.inr (Or.inr (Or.inr rfl))) hK2 hp hp2 hpK hS hcore hZ
    hB hBC hBle eX

end Heads

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
