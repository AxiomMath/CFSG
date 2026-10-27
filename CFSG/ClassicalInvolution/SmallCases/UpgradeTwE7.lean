module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwDatum
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

variable {p f r e : ℕ} [Fact p.Prime] [Fact r.Prime]

theorem e7_exists_conj_eq_rootDiagUnit_of_isClassicalMember_cross (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hr2 : r ≠ 2) (he : 1 ≤ e)
    {L : Subgroup ↥(adjointGroup .E7 (GaloisField r e))}
    {z : ↥(adjointGroup .E7 (GaloisField r e))} (h : IsClassicalMember p f L z) :
    ∃ (g : ↥(adjointGroup .E7 (GaloisField r e))) (b : Fin Tag.E7.rank → (GaloisField r e)ˣ),
      (∀ i, b i = 1 ∨ b i = -1) ∧
        ((g * z * g⁻¹ : ↥(adjointGroup .E7 (GaloisField r e))) :
          ModGL .E7 (GaloisField r e)) = rootDiagUnit .E7 b := by
  classical
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : NeZero e := ⟨by omega⟩
  have hoddK : Odd (Nat.card (GaloisField r e)) := odd_card_galoisField hr2 he
  have hcardK : Nat.card (GaloisField r e) = r ^ e := GaloisField.card r e (by omega)
  set K := GaloisField r e with hK_def
  have : Fintype K := Fintype.ofFinite K
  set k := AlgebraicClosure K with hk_def
  set ι := algebraMap K k with hι
  have : CharP k r := charP_of_injective_algebraMap (algebraMap K k).injective r
  set Fr := iterateFrobenius k r e with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hcardK]
  set x := baseChangeGL ι (z : ModGL .E7 K) with hx_def
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hoddK k Fr hFr
  have hinj : Function.Injective (baseChangeGL (τ := .E7) ι) := baseChangeGL_injective ι
  have hF1 : frobTwistGL .E7 k r e 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1) =
      adjointGroup .E7 k ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  have hxR : x ∈ fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1) := by
    rw [hRR]
    exact hHR (Subgroup.mem_map_of_mem _ z.2)
  have hz2 : (z : ModGL .E7 K) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [h.orderOf_eq_two] at this
    exact congrArg Subtype.val this
  have hx2 : x ^ 2 = 1 := by
    rw [hx_def, ← map_pow, hz2, map_one]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨rp, hrp, l, hl, -, hQfin, g₁, hg₁G, hconj, hcoc, hcomp⟩ :=
    isFiniteToralTwistReduction_of_reps_exact r hr2 (e := e) he (map_conj_one_adjointGroup _ k)
      1 (fun b hb => by
        rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign r e hb, one_mul, inv_one,
          mul_one]
        rfl)
      e7SignDiagramReps h7.permChar_eq h7.exists_rep h7.coe_kernelPosStabilizer
      (finite_fixedPointsIn_frobTwistGL r he le_rfl (map_one _) (one_pow 1)) hxR hx2
  by_cases hl0 : l = []
  ·
    subst hl0
    set χ := signMaskChar .E7 rp.mask with hχ
    set a := signCharTuple (k := k) χ with ha_def
    have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
    have hFg : Units.map (entrywiseHom Fr) g₁ = g₁ := by
      have h1 : g₁ * (frobTwistGL .E7 k r e 1 g₁)⁻¹ = 1 := hcoc
      rw [hF1] at h1
      exact (mul_inv_eq_one.1 h1).symm
    obtain ⟨c, u, hu, hgc⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hg₁G hFg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hu
    have hgc' : g₁ = baseChangeGL ι (rootDiagUnit .E7 c) * baseChangeGL ι g' := hgc
    have hcomm : baseChangeGL ι (rootDiagUnit .E7 c) * rootDiagUnit .E7 a =
        rootDiagUnit .E7 a * baseChangeGL ι (rootDiagUnit .E7 c) := by
      rw [baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hux : baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ = rootDiagUnit .E7 a := by
      have h1 : g₁ * x * g₁⁻¹ = baseChangeGL ι (rootDiagUnit .E7 c) *
          (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
            (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ := by
        rw [hgc']
        group
      rw [hconj] at h1
      calc baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ =
          (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ *
            (baseChangeGL ι (rootDiagUnit .E7 c) *
              (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
                (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹) *
                  baseChangeGL ι (rootDiagUnit .E7 c) := by group
        _ = (baseChangeGL ι (rootDiagUnit .E7 c))⁻¹ * rootDiagUnit .E7 a *
            baseChangeGL ι (rootDiagUnit .E7 c) := by rw [← h1]
        _ = rootDiagUnit .E7 a := by
            rw [mul_assoc, ← hcomm]
            group
    set b : Fin Tag.E7.rank → Kˣ := fun i => if a i = 1 then 1 else -1 with hb_def
    have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
      by_cases h1 : a i = 1 <;> simp [hb_def, h1]
    have hab : (fun i => Units.map ι.toMonoidHom (b i)) = a := by
      funext i
      by_cases h1 : a i = 1
      · simp [hb_def, h1]
      · have h2 : a i = -1 := (ha i).resolve_left h1
        rw [h2]
        simp only [hb_def, h1, ↓reduceIte]
        exact Units.ext (by simp)
    refine ⟨⟨g', hg'⟩, b, hb, ?_⟩
    change g' * (z : ModGL .E7 K) * g'⁻¹ = rootDiagUnit .E7 b
    apply hinj
    rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit, hab]
    exact hux
  ·
    exfalso
    have hmask := mask_eq_two_or_three_of_ne_nil hrp hl hl0
    set φ : ↥(adjointGroup .E7 K) →* ModGL .E7 k :=
      (baseChangeGL ι).comp (adjointGroup .E7 K).subtype with hφ_def
    have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
    set Y := (adjointGroup .E7 K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} with hY_def
    have hY : ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1)⁆ ⊓
          Subgroup.centralizer {x} = Y := by
      rw [hRR, hder]
    have hmap : (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K))).map φ = Y := by
      ext y
      simp only [hY_def, Subgroup.mem_map, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨⟨c, c.2, rfl⟩, ?_⟩
        have h1 := congrArg (fun w : ↥(adjointGroup .E7 K) => baseChangeGL ι (w : ModGL .E7 K)) hc
        simp only [Subgroup.coe_mul, map_mul] at h1
        exact h1
      · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
        refine ⟨⟨c, hc⟩, ?_, rfl⟩
        apply Subtype.ext
        apply hinj
        change baseChangeGL ι c * x = x * baseChangeGL ι c at hcx
        simp only [Subgroup.coe_mul, map_mul]
        exact hcx
    have hLC : L ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K)) :=
      isSubnormal_le h.subnormal
    have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
    have hP := isPComponent_two_of_isClassicalMember h4 h
    let eC : ↥(Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K))) ≃* ↥Y :=
      (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
    have hPY : CFSG.IsPComponent 2 ((L.map φ).subgroupOf Y) := by
      have h1 := isPComponent_map_of_isPComponent 2 eC hP
      have h2 : (L.subgroupOf (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K)))).map
          eC.toMonoidHom = (L.map φ).subgroupOf Y := by
        ext y
        simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c.1, hc, rfl⟩
        · rintro ⟨w, hw, hwy⟩
          refine ⟨⟨w, hLC hw⟩, hw, Subtype.ext ?_⟩
          exact hwy
      rwa [h2] at h1
    have hLR : L.map φ ≤ ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k r e 1)⁆ ⊓
          Subgroup.centralizer {x} := by
      rw [hY, ← hmap]
      exact Subgroup.map_mono hLC
    have hPR := isPComponent_subgroupOf_of_eq hY hPY
    obtain ⟨hQle, hQcomp⟩ := hcomp 2 Nat.prime_two (L.map φ) ⟨hLR, hPR⟩
    obtain ⟨n7, -, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) r hr2 e he
    have hne : (kernelRoots (signMaskChar .E7 rp.mask)).Nonempty := by
      rcases hmask with hm | hm
      · rw [hm]
        exact e7_kernelRoots_nonempty_two
      · rw [hm]
        exact e7_kernelRoots_nonempty_three
    obtain ⟨Dd, hDχ, hDe, ⟨eqv⟩⟩ := exists_datum_mulEquiv_exact r hr2
      (isAlgebraic_zmod_of_isAlgClosure r K k) he (Or.inr (Or.inr rfl)) (ρ := 1)
      (fun _ _ => rfl) (fun _ _ => rfl) (h7.theta rp hrp l hl)
      (fun γ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ)
      (mul_mem (wordWeylMatrix_mem_normalizer l) (one_mem _))
      (map_conj_wordWeylMatrix_mul l (map_conj_one_adjointGroup _ k)) (n7 rp hrp l hl) hne
    have hXfin : Finite Dd.totalFixedGroup := Finite.of_equiv _ eqv.symm.toEquiv
    let φ' : ↥L ≃* ↥(((L.map φ).map (MulAut.conj g₁).toMonoidHom).subgroupOf
        (fixedPointsIn (torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (signMaskChar .E7 rp.mask)))
          (frobTwistGL .E7 k r e (wordWeylMatrix .E7 k l * 1)))) :=
      (L.equivMapOfInjective φ hφ).trans (((L.map φ).equivMapOfInjective _
        (MulAut.conj g₁).injective).trans (Subgroup.subgroupOfEquivOfLe hQle).symm)
    obtain ⟨eY⟩ := h.nonempty_equiv
    obtain ⟨J', O₀, hO₀, hA, -⟩ := exists_orbits_singleton_of_isPComponent_of_mulEquiv_cross Dd
      hXfin eqv hQcomp φ' (classicalInvolutionOddCore L)
      (CFSG.ComponentClassification.OddCore.odd_card L) (F₂ := GaloisField p f) hodd eY
    have hnon : ∀ β ∈ kernelRoots Dd.χ, ∃ γ ∈ kernelRoots Dd.χ, iform β γ = 1 := by
      rw [hDχ]
      rcases hmask with hm | hm
      · rw [hm]
        exact e7_forall_exists_iform_two
      · rw [hm]
        exact e7_forall_exists_iform_three
    obtain ⟨i₀, hi₀⟩ := J'.2
    have hi₀J : i₀ ∈ (J' : Set (KernelComponent Dd.χ)) := by
      rw [← hi₀]
      exact Dd.self_mem_classOrbit i₀
    obtain ⟨⟨α, hα⟩, hαi⟩ := Quotient.exists_rep i₀
    have hΨ := isRootComponent_componentRoots (χ := Dd.χ) i₀
    obtain ⟨-, -, β₀, hβ₀, -⟩ := exists_smul_simpleRoot hΨ (α := α) ⟨hα, hαi⟩
    exact false_of_orthogonal_simpleRoots (Or.inr (Or.inr (Or.inl rfl))) i₀ hβ₀
      (simpleRoots_orthogonal_of_orbits_eq Dd hA hi₀J) hnon

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits in
theorem card_eq_of_isClassicalMember_e7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hr2 : r ≠ 2) (he : 1 ≤ e)
    [Finite ↥(e7Data_valid.minGroup (GaloisField r e))]
    {L : Subgroup ↥(e7Data_valid.minGroup (GaloisField r e))}
    {z : ↥(e7Data_valid.minGroup (GaloisField r e))} (h : IsClassicalMember p f L z) :
    Nat.card (GaloisField r e) = p ^ f := by
  obtain ⟨hodd, -⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : NeZero e := ⟨by omega⟩
  have hoddK : Odd (Nat.card (GaloisField r e)) := odd_card_galoisField hr2 he
  have hqs := isQuasisimple_e7 (GaloisField r e)
  have hθ := e7Isogeny_surjective (GaloisField r e)
  have hker : (e7Isogeny (GaloisField r e)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField r e))
  have h2 : (2 : GaloisField r e) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_card hoddK)
  have hz : e7Isogeny (GaloisField r e) z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := exists_two_involutions_minGroup e7Data_valid
      (GaloisField r e) h2 (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) (by simp)
    by_cases h' : y₁ = z
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd h hzc hy₂
        (fun h'' => hne (h'.trans h''.symm))
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd h hzc hy₁ h'
  have hL' := isClassicalMember_map_central (e7Isogeny (GaloisField r e)) hθ hker hodd h hz
  obtain ⟨g, b, hb, hgz⟩ :=
    e7_exists_conj_eq_rootDiagUnit_of_isClassicalMember_cross hp2 hq hr2 he hL'
  have hL'' := isClassicalMember_map_conj hodd hL' g
  exact card_eq_of_isClassicalMember_toral hp2 hq hoddK b hb hgz hL''

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal in
theorem classicalMemberParametersAt_e7 : ClassicalMemberParametersAt p f .E7 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .E7 0 r e hr).K :=
    ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField r e)) :=
    hfin
  have hcard := card_eq_of_isClassicalMember_e7 hp2 hq hr2 he (L := L) (z := z) hL
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
  exact ⟨rfl, Or.inl rfl⟩

end CFSG.ClassicalInvolution.Upgrade
