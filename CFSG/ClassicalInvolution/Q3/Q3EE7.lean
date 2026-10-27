module

public import CFSG.ClassicalInvolution.Q3.Q3EE7Twist
public import CFSG.ClassicalInvolution.Q3.Q3EReduce
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsToral
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcRoots

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Balance
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.LieType.HighestRoot
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Toral

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem adjoint_derivedSeries_two_eq_bot_of_conj (hK2 : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    {w : ↥(adjointGroup τ K)} (g : ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hgb : ((g * w * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) = rootDiagUnit τ b)
    {N : Subgroup ↥(adjointGroup τ K)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set ↥(adjointGroup τ K))))
    (hsolv : Group.IsSolvable N) (hodd : IsOddGenerated N) : derivedSeries ↥N 2 = ⊥ := by
  have : Finite (ModGL τ K) := finite_modGL
  set w' : ↥(adjointGroup τ K) := g * w * g⁻¹ with hw'
  let f : ↥(adjointGroup τ K) →* ModGL τ K :=
    (adjointGroup τ K).subtype.comp (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (adjointGroup τ K).subtype_injective.comp
    (MulAut.conj g).injective
  have hCeq : (Subgroup.centralizer ({w} : Set ↥(adjointGroup τ K))).map f =
      toralCentralizer τ K b := by
    have h1 := map_centralizer_singleton_mulEquiv₃ (MulAut.conj g) w
    have h2 := CFSG.ClassicalInvolution.ModelFacts.centralizer_eq_subgroupOf_toralCentralizer
      (τ := τ) b w' hgb
    have h3 : (MulAut.conj g) w = w' := by rw [MulAut.conj_apply]
    rw [h3] at h1
    rw [show f = (adjointGroup τ K).subtype.comp (MulAut.conj g).toMonoidHom from rfl,
      ← Subgroup.map_map, h1, h2, Subgroup.map_subgroupOf_eq_of_le
      (CFSG.ClassicalInvolution.ModelFacts.toralCentralizer_le_adjointGroup b)]
  have hJs : IsSubnormal (N.map f) (toralCentralizer τ K b) := by
    rw [← hCeq]
    exact CFSG.ClassicalInvolution.ModelFacts.isSubnormal_map f hNs
  have hJC : N.map f ≤ toralCentralizer τ K b := CFSG.ClassicalInvolution.isSubnormal_le hJs
  have hsolvJ : Group.IsSolvable ↥(N.map f) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective N f hf).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective N f hf).symm.injective
  exact derivedSeries_eq_bot_of_map f hf
    (derivedSeries_two_eq_bot_of_toral hK2 h5 hb hJC hJs hsolvJ (hodd.map f hf))

end Toral

section Adjoint

variable {p f : ℕ} [Fact p.Prime]


theorem e7_adjoint_derived (hp2 : p ≠ 2) (hf1 : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    {z : ↥(adjointGroup .E7 (GaloisField p f))} (hz2 : z * z = 1)
    {N : Subgroup ↥(adjointGroup .E7 (GaloisField p f))}
    (hNs : IsSubnormal N (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 (GaloisField p f)))))
    (hsolv : Group.IsSolvable N) (hNodd : IsOddGenerated N) : derivedSeries ↥N 2 = ⊥ := by
  classical
  have hcardK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hKodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcardK]
    exact (Nat.Prime.eq_two_or_odd' Fact.out |>.resolve_left hp2).pow
  have : Finite (ModGL .E7 (GaloisField p f)) := finite_modGL
  set K := GaloisField p f with hK_def
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := CFSG.ClassicalInvolution.Upgrade.ringChar_ne_two_of_odd_card hKodd
  have h5K : 5 ≤ Nat.card K := by rw [hcardK]; exact h5
  set k := AlgebraicClosure K with hk_def
  set ι := algebraMap K k with hι
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hcardK]
  set x := baseChangeGL ι (z : ModGL .E7 K) with hx_def
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hKodd k Fr hFr
  have hinj : Function.Injective (baseChangeGL (τ := .E7) ι) := baseChangeGL_injective ι
  have hF1 : frobTwistGL .E7 k p f 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1) =
      adjointGroup .E7 k ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  have hxR : x ∈ fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1) := by
    rw [hRR]
    exact hHR (Subgroup.mem_map_of_mem _ z.2)
  have hz2' : (z : ModGL .E7 K) ^ 2 = 1 := by
    have : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    exact congrArg Subtype.val this
  have hx2 : x ^ 2 = 1 := by
    rw [hx_def, ← map_pow, hz2', map_one]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, hg₁G, hconj, hcoc, hcomp⟩ :=
    isFiniteToralTwistReduction_of_reps_exact p hp2 (e := f) hf1 (map_conj_one_adjointGroup _ k)
      1 (fun b hb => by
        rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p f hb, one_mul, inv_one,
          mul_one]
        rfl)
      e7SignDiagramReps h7.permChar_eq h7.exists_rep h7.coe_kernelPosStabilizer
      (finite_fixedPointsIn_frobTwistGL p hf1 le_rfl (map_one _) (one_pow 1)) hxR hx2
  by_cases hl0 : l = []
  ·
    subst hl0
    set χ := signMaskChar .E7 r.mask with hχ
    set a := signCharTuple (k := k) χ with ha_def
    have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
    have hFg : Units.map (entrywiseHom Fr) g₁ = g₁ := by
      have h1 : g₁ * (frobTwistGL .E7 k p f 1 g₁)⁻¹ = 1 := hcoc
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
    have hgb : ((⟨g', hg'⟩ * z * (⟨g', hg'⟩ : ↥(adjointGroup .E7 K))⁻¹ :
        ↥(adjointGroup .E7 K)) : ModGL .E7 K) = rootDiagUnit .E7 b := by
      change g' * (z : ModGL .E7 K) * g'⁻¹ = rootDiagUnit .E7 b
      apply hinj
      rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit, hab]
      exact hux
    exact adjoint_derivedSeries_two_eq_bot_of_conj hK2 h5K ⟨g', hg'⟩ b hb hgb hNs hsolv hNodd
  ·
    have hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k :=
      isAlgebraic_zmod_of_isAlgClosure p K k
    set φ : ↥(adjointGroup .E7 K) →* ModGL .E7 k :=
      (baseChangeGL ι).comp (adjointGroup .E7 K).subtype with hφ_def
    have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
    set Y := (adjointGroup .E7 K).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} with hY_def
    have hY : ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1)⁆ ⊓
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
    have hJsub : IsSubnormal (N.map φ) (⁅fixedPointsIn (adjointGroup .E7 k)
        (frobTwistGL .E7 k p f 1), fixedPointsIn (adjointGroup .E7 k)
          (frobTwistGL .E7 k p f 1)⁆ ⊓ Subgroup.centralizer {x}) := by
      have h1 := CFSG.ComponentClassification.Components.chain_map φ hNs
      rw [hmap] at h1
      rw [hY]
      exact h1
    have hJsolv : Group.IsSolvable ↥(N.map φ) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (N.equivMapOfInjective φ hφ).symm.toMonoidHom)
        (N.equivMapOfInjective φ hφ).symm.injective
    exact derivedSeries_eq_bot_of_map φ hφ
      (e7_twisted_derived hp2 hf1 (by omega) hk rfl
        (finite_fixedPointsIn_frobTwistGL p hf1 le_rfl (map_one _) (one_pow 1)) hr hl hl0 hg₁G
        hconj hcoc hJsub hJsolv (hNodd.map φ hφ))

end Adjoint

section Tag

variable {r e : ℕ} [Fact r.Prime]

theorem false_of_isClassicalMember3_e7 (hr2 : r ≠ 2) (he : 1 ≤ e) (h5 : 5 ≤ r ^ e)
    [Finite ↥(e7Data_valid.minGroup (GaloisField r e))] {X : Type} [Group X] [Finite X]
    (ψ : ↥(e7Data_valid.minGroup (GaloisField r e)) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    False := by
  set F := GaloisField r e with hF
  have hqs := isQuasisimple_e7 F
  have hθs := e7Isogeny_surjective F
  have hθker : (e7Isogeny F).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one F)
  have hXq : CFSG.Open.IsQuasisimple X := by
    obtain ⟨k, hk⟩ := hψ z
    exact CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqs hψ ⟨k, by rw [hk]; exact h.ne_one⟩)
  refine false_of_isClassicalMember3_of_central_cover (e7Isogeny F) hθs hθker ψ hψ hker ?_ h
    (h.not_mem_center_of_quasisimple hXq)
  intro w hw N _ hNs hsolv hodd
  exact e7_adjoint_derived hr2 he h5 hw hNs hsolv hodd

theorem classicalMemberParameters3At_E7 : ClassicalMemberParameters3At .E7 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .E7 0 r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite ↥(e7Data_valid.minGroup (GaloisField r e)) := hfin
  exact false_of_isClassicalMember3_e7 hr2 hadm.2.1
    (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

end Tag

end CFSG.ClassicalInvolution.Q3
