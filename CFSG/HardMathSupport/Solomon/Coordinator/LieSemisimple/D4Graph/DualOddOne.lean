module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllMain
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRot
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Crit
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.TitsQuot
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.TitsPolar
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Layer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


section G2Class

variable {K : Type} [Field K] [Finite K]

theorem fixSub_eq_fixSubgroup {Y : Type} [Group Y] (α : MulAut Y) : fixSub α = fixSubgroup α := by
  ext y
  rfl

theorem perfectInLayer_fieldActor {p : ℕ} [CharP K p] (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    PerfectInLayer (fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  obtain ⟨hsimple, hnc⟩ := d4_trialityFieldImage_self_simple (K := K) hp2 σ
  have hJC := d4_trialityFieldImage_self_le σ
  have hFJ : (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ σ := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hx, rfl⟩
  let e : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(trialityFieldImage σ σ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr hFJ)
  haveI := hsimple
  refine perfectInLayer_of_isSimpleGroup _ e.isSimpleGroup ?_
  by_contra hcon
  push Not at hcon
  exact hnc fun a b => by
    have h1 := congrArg e (hcon (e.symm a) (e.symm b))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

end G2Class


section A2Toral

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem a2_eq_bot_or_isSolvable (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∀ (N : Subgroup ↥(fixSubgroup φ)) [N.Normal],
      N = ⊥ ∨ Group.IsSolvable (↥(fixSubgroup φ) ⧸ N) := by
  have hFD := a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.toCore.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.toCore.cube_apply)
  have hF : ∀ (N : Subgroup ↥(foldFix (a2Phi h φ))) [N.Normal],
      N = ⊥ ∨ Group.IsSolvable (↥(foldFix (a2Phi h φ)) ⧸ N) := by
    intro N _
    exact hFD.eq_bot_or_isSolvable_quotient hgen (fun g _ hcomm => a2_hZ h hcomm)
      (fun x hx => a2_hz h φ hφ x hx) (a2_hC h φ hφ) N
  let e : ↥(foldFix (a2Phi h φ)) ≃* ↥(fixSubgroup φ) :=
    ((MulEquiv.subgroupMap (a2Equiv h) (foldFix (a2Phi h φ))).trans
      (MulEquiv.subgroupCongr (a2_foldFix_map h φ hφ))).trans
      (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup φ))
  exact eq_bot_or_isSolvable_quotient_of_equiv e hF

end A2Toral


section A2Class

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem perfectInLayer_a2 (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    PerfectInLayer φ := by
  haveI : Finite ↥(fixSubgroup φ) := inferInstance
  refine perfectInLayer_of_noAbel_of_solvable_quotient φ ?_ ?_
  · intro N hN hc
    exact a2_noAbel_fixSub h φ hφ N hN (fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2))
  · intro N _
    exact a2_eq_bot_or_isSolvable h φ hφ N

end A2Class


section EllQ1

open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups
open scoped Matrix MatrixGroups

theorem ellQ1_conj_toral (h : RotLang) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hnM : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ (y₀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (d : Kˣ),
      MulAut.conj y₀ * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y₀)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
        Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    have : p = 4 := by omega
    subst this
    norm_num at hp
  have : CharP K p := by
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = p ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  set L := AlgebraicClosure K with hL
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega : f ≠ 0) p)
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  set ι := triEmb K σ L with hι
  have hn'M := triEmb_mem_monomial (L := L) hnM
  have hn'T := triEmb_not_mem_torus (L := L) hnT
  have hFn : twistHom TwistTag.D4 L Fr (ι n) = ι n := triEmb_fixed Fr hcomm n
  have hN3 : n * δ n * δ (δ n) = 1 := by rw [← normSeq_three]; exact hN
  have hcyc : ι n * ((diagramMap TwistTag.D4 L)⁻¹ * ι n * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * ι n *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
    have e1 : ι (δ n) = (diagramMap TwistTag.D4 L)⁻¹ * ι n * diagramMap TwistTag.D4 L :=
      triEmb_fieldActor Fr hcomm n
    have e2 : ι (δ (δ n)) = (diagramMap TwistTag.D4 L)⁻¹ * ι (δ n) * diagramMap TwistTag.D4 L :=
      triEmb_fieldActor Fr hcomm (δ n)
    have := congrArg ι hN3
    rw [map_mul, map_mul, map_one, e2, e1] at this
    exact this
  have hx3 := cube_of_cocycle hcyc
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨ι n, hn'M⟩ ∈ relWeylTwist TwistTag.D4 := by
    refine weyl_mem_rel_of hn'M fun k w hk hxe => ?_
    have hFx : MapsRootLines (twistHom TwistTag.D4 L Fr (ι n)) (weylTwist TwistTag.D4 w) := by
      rw [hxe, map_mul, twistHom_canonicalRep]
      exact mapsRootLines_mul_canonicalRep (twistHom_mem_torusGroup TwistTag.D4 L Fr hk) _
    rw [hFn] at hFx
    have hxw : MapsRootLines (ι n) w := by
      rw [hxe]
      exact mapsRootLines_mul_canonicalRep hk w
    exact (mem_relWeylTwist TwistTag.D4).2 (hFx.unique hxw)
  have hA := exists_cube_root_unit (L := L) (three_ne_zero_of_charP hp hp3)
  have he3 : ((p ^ f : ℕ) : ℤ) % 3 = 1 := by
    generalize p ^ f = q at hq ⊢
    omega
  obtain ⟨b, hb3, hb1, y, hyG, hyF, hy⟩ := ell_main_L (ellFrame_one f hq2) he3 hn'M hn'T hw hx3
    hFn hA (fun b hb3 hb1 ζ hζ h1 h2 => (h p f hp5 hf L b hb3 hb1 ζ hζ h1 h2).1 hq)
  have hyr : y ∈ (ι).range := by
    rw [hι, triEmb_range hp hf hK hσ Fr hFr]
    exact Subgroup.mem_inf.2 ⟨hyG, hyF⟩
  obtain ⟨y₀, rfl⟩ := hyr
  have hψ : ∀ u, ι (δ u) = (diagramMap TwistTag.D4 L)⁻¹ * ι u * diagramMap TwistTag.D4 L :=
    fun u => triEmb_fieldActor Fr hcomm u
  have hs := ell_psi_toral δ ι hψ y₀ n b hy
  have hd3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hq3 : (p ^ f) % 3 = 1 := hq
    generalize p ^ f = q at hq3 ⊢
    obtain ⟨m, rfl⟩ : ∃ m, q = 3 * m + 1 := ⟨q / 3, by omega⟩
    have : (3 * m + 1) ^ 3 - 1 = 3 * (9 * m ^ 3 + 9 * m ^ 2 + 3 * m) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [this]
    exact dvd_mul_right _ _
  obtain ⟨d₀, hd₀3, hd₀1⟩ := exists_cube_root_unit_finite hd3K
  obtain ⟨d, hd3, hd1, hdb⟩ := exists_unit_map_eq_cube_root (L := L) hd₀3 hd₀1 hb3 hb1
  have hdσ : Units.map σ.toRingHom.toMonoidHom d = d := by
    refine Units.ext ?_
    show σ (d : K) = (d : K)
    rw [hσ]
    have hq3 : (p ^ f) % 3 = 1 := hq
    have hd3' : (d : K) ^ 3 = 1 := by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hd3
    generalize p ^ f = q at hq3 ⊢
    obtain ⟨m, rfl⟩ : ∃ m, q = 3 * m + 1 := ⟨q / 3, by omega⟩
    rw [pow_succ, pow_mul, hd3', one_pow, one_mul]
  have hmem := tup1_mem_graphFixedRootGroup hp hp2 hK σ hσ hdσ
  set s := y₀ * n * (δ y₀)⁻¹ with hsdef
  have hsd : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (tup1 d) := by
    have hι1 : ι s = ι ⟨_, hmem⟩ := by
      rw [hs, hι, triEmb_rootDiagUnit (v := (⟨_, hmem⟩ :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) rfl]
      congr 1
      funext i
      fin_cases i
      · exact (map_one _).symm
      · exact (map_one _).symm
      · exact hdb.symm
      · exact (map_one _).symm
    exact congrArg Subtype.val (triEmb_injective hι1)
  have hconj := conj_twist_eq δ y₀ n
  exact ⟨y₀, s, d, hconj, hdσ, hd3, hd1, hsd⟩

end EllQ1


section Odd1

open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem perfectInLayer_of_conj_eq {Y : Type*} [Group Y] (y : Y) {φ ψ : MulAut Y}
    (h : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ) (hψ : PerfectInLayer ψ) :
    PerfectInLayer φ := by
  have h1 := perfectInLayer_conj (MulAut.conj y)⁻¹ ψ hψ
  have e : (MulAut.conj y)⁻¹ * ψ * ((MulAut.conj y)⁻¹)⁻¹ = φ := by
    rw [← h]
    group
  rwa [e] at h1

theorem perfectInLayer_cocycle_q1 (hRot : RotLang) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    PerfectInLayer (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine perfectInLayer_of_conj_eq y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine perfectInLayer_of_conj_eq y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
      have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
      exact perfectInLayer_fieldActor hp2 σ (ringEquiv_cube_apply_eq hK hσ)
    · exact perfectInLayer_a2 (a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1) _
        (a2_hφ_of_class hsd)
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral hRot hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    refine perfectInLayer_of_conj_eq y₀ hconj ?_
    exact perfectInLayer_a2 (a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1) _
      (a2_hφ_of_class hsd)

theorem outer_three_odd_one {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    {K₃ : Type} [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    PerfectInLayer φ := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K₃ hK₃ Fr hFr φ hφord hφ
  · rw [hφ']
    exact perfectInLayer_cocycle_q1 rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr g hg
  · have h := perfectInLayer_cocycle_q1 rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr g hg
    rw [← hφ'] at h
    exact (perfectInLayer_inv_iff φ).1 h

end Odd1

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
