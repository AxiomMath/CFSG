module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.PartTwo.Census.Exceptional
  CFSG.RankThree.CentralCover CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One.SplitCentralizer
open CFSG.SeitzReduction.F4Pilot

private theorem dvd_two_pow_sub_one_of_orderOf {k : Type} [Field k] [Finite k] {f p : ℕ}
    (hk : Nat.card k = 2 ^ f) {t : kˣ} (ht : orderOf t = p) : p ∣ 2 ^ f - 1 := by
  have hdvd : p ∣ Nat.card kˣ := by
    rw [← ht]
    exact orderOf_dvd_natCard t
  rwa [Nat.card_units, hk] at hdvd

private theorem te6WA_le_centralizer_te6SL2_three {K F : Type} [Field K] [Field F] [Finite F]
    (θ : K →+* K) (j : F →+* K) (hj : ∀ x, θ (j x) = j x)
    (g A : Matrix.SpecialLinearGroup (Fin 2) F) :
    te6WA θ j hj g ≤
      Subgroup.centralizer ({te6SL2 θ j hj 3 A} : Set ↥(fixedGroup K θ)) := by
  rw [te6WA]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (zpowers_te6SL2_commute (θ := θ) (j := j) (hj := hj) (g := g)
      (i := 0) (i' := 3) (by decide) hx A).eq
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (zpowers_te6SL2_commute (θ := θ) (j := j) (hj := hj) (g := g)
      (i := 1) (i' := 3) (by decide) hx A).eq
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (zpowers_te6SL2_commute (θ := θ) (j := j) (hj := hj) (g := g)
      (i := 2) (i' := 3) (by decide) hx A).eq

private lemma exists_pxt_lift {f p : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p)
    {A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hAmap : A₁.map (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) =
      thetaTorusP (f := f) t ⊔
        (R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f)) :
    ∃ (pxtC : C0 f) (x : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))),
      pxtC ∈ thetaTorusP (f := f) t ∧ pxtC ≠ 1 ∧ x ∈ A₁ ∧
      (twistedIsogenyC hf (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) x = pxtC ∧ x ≠ 1 := by
  classical
  haveI hTfin : Finite ↥(thetaTorusP (f := f) t) := Subtype.finite
  haveI hTfintype : Fintype ↥(thetaTorusP (f := f) t) := Fintype.ofFinite _
  have hTcard : 1 < Fintype.card ↥(thetaTorusP (f := f) t) := by
    rw [← Nat.card_eq_fintype_card, card_thetaTorusP hf hk ht]
    exact hp.one_lt
  obtain ⟨pxt, hpxt_ne'⟩ := Fintype.exists_ne_of_one_lt_card hTcard
    (1 : ↥(thetaTorusP (f := f) t))
  let pxtC : C0 f := (pxt : C0 f)
  have hpxt_mem : pxtC ∈ thetaTorusP (f := f) t := pxt.2
  have hpxt_ne : pxtC ≠ 1 := by
    intro h1
    exact hpxt_ne' (Subtype.ext (by simpa [pxtC] using h1))
  have hxmem : pxtC ∈ A₁.map (twistedIsogenyC hf
      (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
      (frobQ 2 f) (fun c => frobQ_apply 2 f c)) := by
    rw [hAmap]
    exact Subgroup.mem_sup_left hpxt_mem
  obtain ⟨x, hxA, hxπ⟩ := Subgroup.mem_map.mp hxmem
  have hx1 : x ≠ 1 := by
    intro h1
    exact hpxt_ne (by rw [← hxπ, h1, map_one])
  exact ⟨pxtC, x, hpxt_mem, hpxt_ne, hxA, hxπ, hx1⟩

private lemma exists_zLevi_lift {f p : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p)
    {A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hAmap : A₁.map (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) =
      thetaTorusP (f := f) t ⊔
        (R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f))
    {pxtC : C0 f} (hpxt_mem : pxtC ∈ thetaTorusP (f := f) t)
    {x : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hxA : x ∈ A₁)
    (hxπ : (twistedIsogenyC hf (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
      (frobQ 2 f) (fun c => frobQ_apply 2 f c)) x = pxtC) :
    ∃ (z : ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (zL : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) (pzt : C0 f),
      z ∈ A₁ ∧
      (twistedIsogenyC hf (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) z = pzt ∧
      zL = zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c) ∧
      (pzt : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = zL ∧
      z ∉ Subgroup.zpowers x := by
  classical
  let zL : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)) :=
    zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
  have hzL_mem : zL ∈ R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c) :=
    zLevi_mem h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
  let pzt : C0 f := ⟨zL, R3Levi_le_C0 h p hp hp2 ζ hζ hζbar
    (fun c => frobQ_apply 2 f c) hzL_mem⟩
  have hpzt_mem : pzt ∈
      (R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f) :=
    Subgroup.mem_subgroupOf.mpr hzL_mem
  have hzmem : pzt ∈ A₁.map (twistedIsogenyC hf
      (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
      (frobQ 2 f) (fun c => frobQ_apply 2 f c)) := by
    rw [hAmap]
    exact Subgroup.mem_sup_right hpzt_mem
  obtain ⟨z, hzA, hzπ⟩ := Subgroup.mem_map.mp hzmem
  have hzx : z ∉ Subgroup.zpowers x := by
    intro hzpx
    have hπz : pzt ∈ Subgroup.zpowers pxtC := by
      have h := Subgroup.mem_map_of_mem (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) hzpx
      rwa [MonoidHom.map_zpowers, hzπ, hxπ] at h
    have hzT : pzt ∈ thetaTorusP (f := f) t :=
      (Subgroup.zpowers_le.mpr hpxt_mem) hπz
    have hzD : (pzt : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ DLevi f :=
      (R3Levi_le_su6Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)) hpzt_mem
    have hinf : pzt ∈ thetaTorusP (f := f) t ⊓ (DLevi f).subgroupOf (C0 f) :=
      ⟨hzT, Subgroup.mem_subgroupOf.mpr hzD⟩
    rw [thetaTorusP_inf_DLevi_eq_bot hf hk t, Subgroup.mem_bot] at hinf
    have hzL1 : zL = 1 := by
      have hval : (pzt : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = 1 := by
        simpa using congrArg (fun w : C0 f => (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
          hinf
      simpa [pzt] using hval
    have hord : orderOf zL = p :=
      orderOf_zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
    rw [hzL1, orderOf_one] at hord
    exact hp.ne_one hord.symm
  exact ⟨z, zL, pzt, hzA, hzπ, rfl, rfl, hzx⟩

private lemma su6Levi_layer_data {f p : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] {t : kˣ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : orderOf t = p) {pxtC : C0 f} (hpxt_mem : pxtC ∈ thetaTorusP (f := f) t)
    (hpxt_ne : pxtC ≠ 1) (J : Subgroup (C0 f))
    (hJdef : J = (DLevi f).subgroupOf (C0 f)) :
    J ≤ Subgroup.centralizer ({pxtC} : Set (C0 f)) ∧
      (J.subgroupOf (Subgroup.centralizer ({pxtC} : Set (C0 f)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card J := by
  classical
  have hxW : pxtC ∈ (W0 f k).subgroupOf (C0 f) :=
    thetaTorusP_le_thetaTorus hf hk t hpxt_mem
  have hJx : J ≤ Subgroup.centralizer ({pxtC} : Set (C0 f)) := by
    intro n hn
    have hn' : n ∈ (DLevi f).subgroupOf (C0 f) := by simpa [hJdef] using hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    exact congrArg (fun w : C0 f => (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
      (commute_thetaTorus_su6Levi hf hk hxW hn').symm
  have hJn : (J.subgroupOf (Subgroup.centralizer ({pxtC} : Set (C0 f)))).Normal := by
    simpa [hJdef] using su6Levi_subgroupOf_centralizer_normal hf hk hxW hpxt_ne
  have hJx' : (DLevi f).subgroupOf (C0 f) ≤ Subgroup.centralizer ({pxtC} : Set (C0 f)) := by
    simpa [hJdef] using hJx
  have hJqExp : CFSG.IsQuasisimple ↥((DLevi f).subgroupOf (C0 f)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJx')
      (isQuasisimple_su6Levi_subgroupOf_centralizer hf hk hxW hpxt_ne)
  have hJqNat : CFSG.IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hJdef).symm hJqExp
  have hJq : CFSG.Open.IsQuasisimple ↥J := ⟨Group.isPerfect_def.mp hJqNat.1, hJqNat.2.1⟩
  have hpJExp : p ∣ Nat.card ((DLevi f).subgroupOf (C0 f)) := by
    have hpq : p ∣ 2 ^ f - 1 := dvd_two_pow_sub_one_of_orderOf hk ht
    have h := dvd_card_su6Levi_subgroupOf_centralizer hf hk hxW hpxt_ne hp hp2 (Or.inl hpq)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJx').toEquiv] at h
  have hpJ : p ∣ Nat.card J := by
    rwa [Nat.card_congr (MulEquiv.subgroupCongr hJdef).toEquiv]
  exact ⟨hJx, hJn, hJq, hpJ⟩

private lemma QLevi_layer_data {f p : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] [NeZero p] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {zL : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))} {pzt : C0 f}
    (hzL : zL = zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c))
    (hpzt : (pzt : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = zL)
    (Q : Subgroup (C0 f))
    (hQdef : Q = (QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf
      (C0 f)) :
    Q ≤ (DLevi f).subgroupOf (C0 f) ∧
      Q ≤ Subgroup.centralizer ({pzt} : Set (C0 f)) ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  classical
  have hQC0 : QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c) ≤ C0 f :=
    (QLevi_le_su6Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).trans
      (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup (frobQ 2 f))
  have hQJ : Q ≤ (DLevi f).subgroupOf (C0 f) := by
    intro q hq
    have hq' : q ∈ (QLevi h p hp hp2 ζ hζ hζbar
        (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f) := by simpa [hQdef] using hq
    exact Subgroup.mem_subgroupOf.mpr
      (QLevi_le_su6Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
        (Subgroup.mem_subgroupOf.mp hq'))
  have hQz : Q ≤ Subgroup.centralizer ({pzt} : Set (C0 f)) := by
    intro q hq
    have hq' : q ∈ (QLevi h p hp hp2 ζ hζ hζbar
        (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f) := by simpa [hQdef] using hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
      (QLevi_le_centralizer_zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
        (Subgroup.mem_subgroupOf.mp hq'))
    rw [← hzL, ← hpzt] at hcomm
    exact hcomm
  let eQ : ↥Q ≃* ↥((QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf
      (TwistedE6Pilot.su6Levi (frobQ 2 f))) := by
    rw [hQdef]
    exact (Subgroup.subgroupOfEquivOfLe hQC0).trans
      (Subgroup.subgroupOfEquivOfLe
        (QLevi_le_su6Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c))).symm
  have hQqNat : CFSG.IsQuasisimple ↥Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm
      (isQuasisimple_QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c))
  have hQq : CFSG.Open.IsQuasisimple ↥Q := ⟨Group.isPerfect_def.mp hQqNat.1, hQqNat.2.1⟩
  have hpQ : p ∣ Nat.card Q := by
    rw [Nat.card_congr eQ.toEquiv]
    exact dvd_card_QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
  exact ⟨hQJ, hQz, hQq, hpQ⟩

private lemma QLevi_layer_normal {f p : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {zL : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))} {pzt : C0 f}
    (hzL : zL = zLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c))
    (hpzt : (pzt : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = zL)
    {J Q : Subgroup (C0 f)} (hJdef : J = (DLevi f).subgroupOf (C0 f))
    (hQdef : Q = (QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf
      (C0 f)) (hQJ : Q ≤ J)
    (hQz : Q ≤ Subgroup.centralizer ({pzt} : Set (C0 f))) :
    (Q.subgroupOf (J ⊓ Subgroup.centralizer ({pzt} : Set (C0 f)))).Normal := by
  classical
  have hle : Q ≤ J ⊓ Subgroup.centralizer ({pzt} : Set (C0 f)) := le_inf hQJ hQz
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
  intro gg hgg
  have hggJ : gg ∈ J := (Subgroup.mem_inf.mp hgg).1
  have hggC : gg ∈ Subgroup.centralizer ({pzt} : Set (C0 f)) := (Subgroup.mem_inf.mp hgg).2
  have hggJ' : gg ∈ (DLevi f).subgroupOf (C0 f) := by simpa [hJdef] using hggJ
  have hgz : (gg : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      Subgroup.centralizer ({zL} : Set (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hggC ⊢
    have h := congrArg (fun w : C0 f => (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
      hggC
    simp only [Subgroup.coe_mul] at h
    rwa [hpzt] at h
  rw [hzL] at hgz
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have hqL : (q : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c) := by
      have hq' : q ∈ (QLevi h p hp hp2 ζ hζ hζbar
          (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f) := by simpa [hQdef] using hq
      exact Subgroup.mem_subgroupOf.mp hq'
    have h := QLevi_conj_mem h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
      (Subgroup.mem_subgroupOf.mp hggJ') hgz hqL
    simpa [hQdef] using Subgroup.mem_subgroupOf.mpr h
  · intro hq
    have hgginv : gg⁻¹ ∈ J ⊓ Subgroup.centralizer ({pzt} : Set (C0 f)) :=
      ⟨Subgroup.inv_mem _ hggJ, Subgroup.inv_mem _ hggC⟩
    have hgginvJ : gg⁻¹ ∈ (DLevi f).subgroupOf (C0 f) := by simpa [hJdef] using
      (Subgroup.mem_inf.mp hgginv).1
    have hgginvC : gg⁻¹ ∈ Subgroup.centralizer ({pzt} : Set (C0 f)) :=
      (Subgroup.mem_inf.mp hgginv).2
    have hgz' : ((gg⁻¹ : C0 f) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        Subgroup.centralizer ({zL} : Set (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hgginvC ⊢
      have h := congrArg (fun w : C0 f => (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
        hgginvC
      simp only [Subgroup.coe_mul] at h
      rwa [hpzt] at h
    have hqL : (((gg * q * gg⁻¹ : C0 f) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∈
        QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c) := by
      have hq' : (gg * q * gg⁻¹) ∈ (QLevi h p hp hp2 ζ hζ hζbar
          (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f) := by simpa [hQdef] using hq
      exact Subgroup.mem_subgroupOf.mp hq'
    rw [hzL] at hgz'
    have h := QLevi_conj_mem h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)
      (Subgroup.mem_subgroupOf.mp hgginvJ) hgz' hqL
    rw [hQdef]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have heq : ((gg⁻¹ : C0 f) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (((gg * q * gg⁻¹ : C0 f) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) *
        (((gg⁻¹ : C0 f) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))⁻¹ =
        (q : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [heq] at h

private lemma le_centralizer_of_mul_inv_mem_center {H : Type} [Group H] {F : Subgroup H}
    {x y : H} (hFy : F ≤ Subgroup.centralizer ({y} : Set H))
    (hc : x * y⁻¹ ∈ Subgroup.center H) :
    F ≤ Subgroup.centralizer ({x} : Set H) := by
  intro ff hff
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcf : (x * y⁻¹) * ff = ff * (x * y⁻¹) :=
    ((Subgroup.mem_center_iff.mp hc) ff).symm
  have hyf : y * ff = ff * y :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hFy hff)).symm
  have hx_eq : x = (x * y⁻¹) * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hx_eq]
  calc ff * ((x * y⁻¹) * y) = (ff * (x * y⁻¹)) * y := by group
    _ = ((x * y⁻¹) * ff) * y := by rw [← hcf]
    _ = (x * y⁻¹) * (ff * y) := by group
    _ = (x * y⁻¹) * (y * ff) := by rw [← hyf]
    _ = ((x * y⁻¹) * y) * ff := by group

private lemma twistedIsogeny_ker_surj {f : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f) :
    (twistedIsogenyC hf (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)).ker =
        Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) ∧
      Function.Surjective (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) := by
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  exact ⟨CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf
      (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf) (frobQ 2 f) hσ,
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf
      (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf) (frobQ 2 f) hσ⟩

private lemma exists_te6WA_data {f q : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] (hj : ∀ x,
      frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
        algebraMap k (GaloisField 2 (2 * f)) x)
    {g : Matrix.SpecialLinearGroup (Fin 2) k} (hq : q.Prime) (hg : orderOf g = q) :
    ∃ F : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      F = te6WA (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj g ∧
      IsElemAbelian q F ∧ Nat.card F = q ^ 3 ∧ 3 ≤ CFSG.Open.pRank q F := by
  have hF2 : ringChar k = 2 := ringChar.eq k 2
  let F : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    te6WA (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj g
  have hFe : IsElemAbelian q F :=
    isElemAbelian_te6WA (θ := frobQ 2 f) (j := algebraMap k (GaloisField 2 (2 * f))) hj hF2 hg
  have hFcard : Nat.card F = q ^ 3 :=
    card_te6WA (θ := frobQ 2 f) (j := algebraMap k (GaloisField 2 (2 * f))) hj hF2 hg
  exact ⟨F, rfl, hFe, hFcard, CFSG.SectionRank.le_pRank hq.one_lt le_rfl hFe hFcard⟩

private lemma concl165Avoid_of_twE6_layers {H K : Type} [Group H] [Finite H] [Group K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (π : H →* K) (hsurj : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) {A₁ : Subgroup H} (hA : IsElemAbelian p A₁)
    {x z : H} (hxA : x ∈ A₁) (hzA : z ∈ A₁) (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {pxtC pzt : K} (hxπ : π x = pxtC) (hzπ : π z = pzt)
    {J Q : Subgroup K} (hJx : J ≤ Subgroup.centralizer ({pxtC} : Set K))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({pxtC} : Set K))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({pzt} : Set K))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({pzt} : Set K))).Normal)
    (hQq : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    {F : Subgroup H} (hFe : IsElemAbelian q F) (hFx : F ≤ Subgroup.centralizer ({x} : Set H))
    (hFW : F.map π ≤ J) (hF3 : 3 ≤ CFSG.Open.pRank q F) (hFZ : F ⊓ π.ker = ⊥) :
    Concl165Avoid H p q A₁ π.ker := by
  have hJx' : J ≤ Subgroup.centralizer ({π x} : Set K) := by rw [hxπ]; exact hJx
  have hJn' : (J.subgroupOf (Subgroup.centralizer ({π x} : Set K))).Normal := by
    rw [hxπ]; exact hJn
  have hQz' : Q ≤ Subgroup.centralizer ({π z} : Set K) := by rw [hzπ]; exact hQz
  have hQn' : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({π z} : Set K))).Normal := by
    rw [hzπ]; exact hQn
  exact concl165Avoid_of_central_lift hp π hsurj hker hA hxA hzA hx1 hzx hJx' hJn' hJq hpJ
    hQJ hQz' hQn' hQq hpQ hFe hFx (hFW.trans Subgroup.le_normalizer) hF3 hFZ

private theorem concl165Avoid_twE6_model_of_orderOf {f p q : ℕ} {k : Type} [Field k]
    [Finite k] [CharP k 2] [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f)
    (hj : ∀ x, frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
      algebraMap k (GaloisField 2 (2 * f)) x)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p)
    (g : Matrix.SpecialLinearGroup (Fin 2) k) (hg : orderOf g = q)
    {A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian p A₁)
    (hAmap : A₁.map (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) =
      thetaTorusP (f := f) t ⊔
        (R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f)) :
    Concl165Avoid ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) p q A₁
      (Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  classical
  let Kb := GaloisField 2 (2 * f)
  let H := ↥(fixedGroup Kb (frobQ 2 f))
  let π : H →* C0 f := twistedIsogenyC hf
    (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
    (frobQ 2 f) (fun c => frobQ_apply 2 f c)
  obtain ⟨hker, hsurj⟩ := twistedIsogeny_ker_surj (f := f) (k := k) hf
  haveI hHfin : Finite H := Subtype.finite
  obtain ⟨F, hFdef, hFe, -, hF3⟩ := exists_te6WA_data (f := f) (q := q) hj hq hg
  obtain ⟨pxtC, x, hpxt_mem, hpxt_ne, hxA, hxπ, hx1⟩ :=
    exists_pxt_lift (f := f) (k := k) (p := p) (A₁ := A₁) hf hk hp hp2 h hζ hζbar ht hAmap
  obtain ⟨z, zL, pzt, hzA, hzπ, hzLdef, hpzt, hzx⟩ :=
    exists_zLevi_lift (f := f) (k := k) (p := p) (A₁ := A₁) hf hk hp hp2 h hζ hζbar ht
      hAmap hpxt_mem hxA hxπ
  let J : Subgroup (C0 f) := (DLevi f).subgroupOf (C0 f)
  obtain ⟨hJx, hJn, hJq, hpJ⟩ :=
    su6Levi_layer_data (f := f) (k := k) hf hk hp hp2 ht hpxt_mem hpxt_ne J rfl
  let Q : Subgroup (C0 f) :=
    (QLevi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f)
  obtain ⟨hQJ, hQz, hQq, hpQ⟩ :=
    QLevi_layer_data (f := f) (k := k) (p := p) hf hk hp hp2 h hζ hζbar hzLdef hpzt Q rfl
  have hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({pzt} : Set (C0 f)))).Normal :=
    QLevi_layer_normal (f := f) (k := k) (p := p) hp hp2 h hζ hζbar hzLdef hpzt rfl rfl hQJ hQz
  have hxT : ((pxtC : C0 f) : ModGL TwistTag.E6.tag Kb) ∈
      E6GraphLevi.thetaTorus (algebraMap k Kb) :=
    Subgroup.mem_subgroupOf.mp (thetaTorusP_le_thetaTorus hf hk t hpxt_mem)
  obtain ⟨a, ha⟩ := (E6GraphLevi.mem_thetaTorus (algebraMap k Kb)).1 hxT
  let y : H := te6SL2 (frobQ 2 f) (algebraMap k Kb) hj 3 (HSL a)
  have hπy : π y = π x := by
    refine Subtype.ext ?_
    rw [CFSG.SeitzReduction.F4Pilot.coe_twistedIsogenyC]
    rw [show e6IsogenyT Kb (((te6SL2 (frobQ 2 f) (algebraMap k Kb) hj 3 (HSL a) :
        fixedGroup Kb (frobQ 2 f)) : e6Data_valid.minGroup Kb)) =
        e6Isogeny Kb (((te6SL2 (frobQ 2 f) (algebraMap k Kb) hj 3 (HSL a) :
        fixedGroup Kb (frobQ 2 f)) : e6Data_valid.minGroup Kb)) from rfl]
    rw [e6Isogeny_te6SL2_three_HSL hf hj a, E6GraphLevi.thetaTorusHom_apply, hxπ]
    exact ha
  have hFy : F ≤ Subgroup.centralizer ({y} : Set H) := by
    rw [hFdef]
    exact te6WA_le_centralizer_te6SL2_three (θ := frobQ 2 f)
      (j := algebraMap k Kb) hj g (HSL a)
  have hc : x * y⁻¹ ∈ Subgroup.center H := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπy, mul_inv_cancel]
  have hFx : F ≤ Subgroup.centralizer ({x} : Set H) :=
    le_centralizer_of_mul_inv_mem_center hFy hc
  have hFW : F.map π ≤ J := by
    rw [hFdef]
    simpa [J, π] using map_te6WA_le_su6Levi (f := f) (k := k) hf hj g
  have hFZ : F ⊓ π.ker = ⊥ := by
    rw [hFdef]
    rw [show π.ker = Subgroup.center H from by simpa [π] using hker]
    exact CFSG.LocalAnalysis.GLTheoremA.te6WA_inf_center_eq_bot
      (θ := frobQ 2 f) (j := algebraMap k Kb) (hj := hj) (ringChar.eq k 2)
  have hconcl : Concl165Avoid H p q A₁ π.ker :=
    concl165Avoid_of_twE6_layers hp π (by simpa [π] using hsurj)
      (le_of_eq (by simpa [π] using hker)) hA hxA hzA hx1 hzx hxπ hzπ hJx hJn hJq hpJ
      hQJ hQz hQn hQq hpQ hFe hFx hFW hF3 hFZ
  have hkerc : π.ker = Subgroup.center H := by simpa [π] using hker
  rw [hkerc] at hconcl
  simpa only [H, Kb] using hconcl

theorem concl165Avoid_twE6_model {f p q : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hj : ∀ x, frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
      algebraMap k (GaloisField 2 (2 * f)) x)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hqd : q ∣ 2 ^ f + 1)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p)
    {A₁ : Subgroup ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian p A₁)
    (hAmap : A₁.map (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) =
      thetaTorusP (f := f) t ⊔
        (R3Levi h p hp hp2 ζ hζ hζbar (fun c => frobQ_apply 2 f c)).subgroupOf (C0 f)) :
    Concl165Avoid ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) p q A₁
      (Subgroup.center ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  have hcard : Nat.card k = Nat.card (GaloisField 2 f) := by
    rw [hk, GaloisField.card 2 f (by omega)]
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_ringEquiv_of_natCard_eq hcard
  obtain ⟨g₀, hg₀⟩ := exists_orderOf_eq_prime_sl2 (n := f) hf hq hqd
  let g : Matrix.SpecialLinearGroup (Fin 2) k :=
    Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom g₀
  have hg : orderOf g = q := by
    rw [← hg₀]
    refine orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom) ?_ g₀
    intro A B hAB
    ext i j
    have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) i j) hAB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h
    exact e.symm.injective h
  exact concl165Avoid_twE6_model_of_orderOf hf hk hj hp hp2 hq h hζ hζbar ht g hg hA hAmap

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
