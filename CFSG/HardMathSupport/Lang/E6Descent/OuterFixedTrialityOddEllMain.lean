module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllField
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Line
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddChar
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllFrame
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinus

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

theorem ell_psi_toral {Y : Type*} [Group Y] (δ : MulAut Y) {L : Type} [Field L] [IsAlgClosed L]
    (ψ : Y →* ModGL TwistTag.D4.tag L)
    (hψ : ∀ u, ψ (δ u) = (diagramMap TwistTag.D4 L)⁻¹ * ψ u * diagramMap TwistTag.D4 L)
    (y₀ n : Y) (b : Lˣ)
    (h : ψ y₀ * (ψ n * (diagramMap TwistTag.D4 L)⁻¹) * (ψ y₀)⁻¹ = rotElt b) :
    ψ (y₀ * n * (δ y₀)⁻¹) = rootDiagUnit TwistTag.D4.tag (tup1 b) := by
  rw [map_mul, map_mul, map_inv, hψ]
  rw [rotElt_eq] at h
  calc ψ y₀ * ψ n * ((diagramMap TwistTag.D4 L)⁻¹ * ψ y₀ * diagramMap TwistTag.D4 L)⁻¹
      = (ψ y₀ * (ψ n * (diagramMap TwistTag.D4 L)⁻¹) * (ψ y₀)⁻¹) * diagramMap TwistTag.D4 L := by
        group
    _ = _ := by rw [h]; group

theorem tup1_mem_graphFixedRootGroup {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {d : Kˣ} (hd : Units.map σ.toRingHom.toMonoidHom d = d) :
    rootDiagUnit TwistTag.D4.tag (tup1 d) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hpar : ringChar K = 2 ∨ ∃ m, Odd m ∧ ∀ c, σ c = c ^ m := Or.inr ⟨p ^ f, hodd, hσ⟩
  refine rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar ?_
  intro i
  fin_cases i
  · show (1 : Kˣ) = Units.map σ.toRingHom.toMonoidHom 1
    exact (map_one _).symm
  · show (1 : Kˣ) = Units.map σ.toRingHom.toMonoidHom 1
    exact (map_one _).symm
  · exact hd.symm
  · show (1 : Kˣ) = Units.map σ.toRingHom.toMonoidHom 1
    exact (map_one _).symm

theorem ellQ1Bound_of_rotLang (h : RotLang) : EllQ1Bound := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ n hnM hnT hN
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
  rw [card_fixedSubgroup_of_conj_eq y₀ hconj]
  have hcard := d4OuterThreeA2Toral_card hp hp2 hf hq hK hσ hdσ hd3 hd1 hsd
  rw [← card_fixSub_eq_card_fixedSubgroup, hcard]
  exact a2_order_dvd_G2 (Nat.one_le_pow _ _ hp.pos)

theorem minusEllBound_of_rotLang (h : RotLang) : MinusEllBound := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ n hn hN
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    have : p = 4 := by omega
    subst this
    norm_num at hp
  obtain ⟨L, _, _, _, _, g₀, hg₀, hnM, hnT⟩ := hn
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := id hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm := d4Minus_hcomm hσ Fr hFr
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega : f ≠ 0) p)
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hn'M : ψ n ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [hψdef, d4MinusPsi_apply]
    exact hnM
  have hn'T : ψ n ∉ torusGroup TwistTag.D4.tag L := by
    rw [hψdef, d4MinusPsi_apply]
    exact hnT
  have hn'F : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n :=
    ((d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F (ψ n)).1 ⟨n, rfl⟩).2
  have hFn : twistHomOppHom Fr (ψ n) = ψ n := by
    rw [twistHomOppHom_apply]
    exact hn'F
  have hψ : ∀ u, ψ (δ u) = (diagramMap TwistTag.D4 L)⁻¹ * ψ u * diagramMap TwistTag.D4 L :=
    fun u => d4MinusPsi_fieldActor Fr hcomm hg₀P u
  have hN3 : n * δ n * δ (δ n) = 1 := by rw [← normSeq_three]; exact hN
  have hcyc : ψ n * ((diagramMap TwistTag.D4 L)⁻¹ * ψ n * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * ψ n *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
    have e1 := hψ n
    have e2 := hψ (δ n)
    have := congrArg ψ hN3
    rw [map_mul, map_mul, map_one, e2, e1] at this
    exact this
  have hx3 := cube_of_cocycle hcyc
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨ψ n, hn'M⟩ ∈ relWeylTwist TwistTag.D4 :=
    weyl_mem_rel_of hn'M fun k w hk hxe => d4MnFL_relWeylTwist_of_fixed Fr hk hxe hn'F
  have hA := exists_cube_root_unit (L := L) (three_ne_zero_of_charP hp hp3)
  have he3 : (-((p ^ f : ℕ) : ℤ)) % 3 = 1 := by
    generalize p ^ f = q at hq ⊢
    omega
  obtain ⟨b, hb3, hb1, y, hyG, hyF, hy⟩ := ell_main_L (ellFrame_two f hq2) he3 hn'M hn'T hw hx3
    hFn hA (fun b hb3 hb1 ζ hζ h1 h2 => by
      obtain ⟨z, hz, hzeq⟩ := (h p f hp5 hf L b hb3 hb1 ζ hζ h1 h2).2 hq
      exact ⟨z, hz, by rw [twistHomOppHom_apply]; exact hzeq⟩)
  have hyr : y ∈ ψ.range := by
    rw [hψdef]
    refine (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F y).2 ⟨hyG, ?_⟩
    have := hyF
    rw [twistHomOppHom_apply] at this
    exact this
  obtain ⟨y₀, rfl⟩ := hyr
  have hs := ell_psi_toral δ ψ hψ y₀ n b hy
  set s := y₀ * n * (δ y₀)⁻¹ with hsdef
  have hsT : D4MinusToral p f hp K σ s := by
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, g₀, b, hg₀, hb3, hb1, ?_⟩
    have h1 := hs
    rw [hψdef, d4MinusPsi_apply] at h1
    calc triEmb K σ L s = g₀ * (g₀⁻¹ * triEmb K σ L s * g₀) * g₀⁻¹ := by group
      _ = _ := by rw [h1]; rfl
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hconj := conj_twist_eq δ y₀ n
  have hcn : (MulAut.conj n * δ) ^ 3 = 1 := by
    rw [conj_mul_pow_eq, hN, hψ3, map_one, one_mul]
  have hcs : (MulAut.conj s * δ) ^ 3 = 1 := by
    rw [← hconj, conj_pow, hcn]
    group
  have hNs := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcs
  rw [card_fixedSubgroup_of_conj_eq y₀ hconj]
  exact minusToralBound p f hp hp2 hp3 hf hq K hK σ hσ s hsT hNs

open CFSG.HardMathSupport.Lang.Coordinator in
theorem outerFixedOrder_odd_of_rotLang (h : RotLang) :
    OuterFixedOrderTrialityThreeChar (5 ≤ ·) :=
  outerFixedOrder_odd_aux (ellQ1Bound_of_rotLang h) minusToralBound (minusEllBound_of_rotLang h)

end CFSG.HardMathSupport.Lang.E6Descent
