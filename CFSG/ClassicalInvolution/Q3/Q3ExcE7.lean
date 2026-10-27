module

public import CFSG.ClassicalInvolution.Q3.Q3ExcE7Tw
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6

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

variable {p f : ℕ} [Fact p.Prime]

theorem e7_involution_cases (hp2 : p ≠ 2) (hf1 : 1 ≤ f) (hq3 : p ^ f = 3)
    (z : ↥(adjointGroup .E7 (GaloisField p f))) (hz2 : z * z = 1) :
    (∃ (g : ↥(adjointGroup .E7 (GaloisField p f)))
        (b : Fin Tag.E7.rank → (GaloisField p f)ˣ), (∀ i, b i = 1 ∨ b i = -1) ∧
        ((g * z * g⁻¹ : ↥(adjointGroup .E7 (GaloisField p f))) :
          ModGL .E7 (GaloisField p f)) = rootDiagUnit .E7 b) ∨
      (oddCoreIn (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 (GaloisField p f)))) = ⊥ ∧
        ∀ L : Subgroup ↥(adjointGroup .E7 (GaloisField p f)), IsClassicalMember3 L z →
          classicalInvolutionOddCore L = ⊥ → False) := by
  classical
  have hcardK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by rw [hcardK, hq3]; decide
  have : Finite (ModGL .E7 (GaloisField p f)) := finite_modGL
  set K := GaloisField p f with hK_def
  have : Fintype K := Fintype.ofFinite K
  set k := AlgebraicClosure K with hk_def
  set ι := algebraMap K k with hι
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hcardK]
  set x := baseChangeGL ι (z : ModGL .E7 K) with hx_def
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hodd k Fr hFr
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
    left
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
    refine ⟨⟨g', hg'⟩, b, hb, ?_⟩
    change g' * (z : ModGL .E7 K) * g'⁻¹ = rootDiagUnit .E7 b
    apply hinj
    rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit, hab]
    exact hux
  ·
    right
    have hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k :=
      isAlgebraic_zmod_of_isAlgClosure p K k
    obtain ⟨hA, hB⟩ := e7_twisted_core hp2 hf1 hq3 hk
      (finite_fixedPointsIn_frobTwistGL p hf1 le_rfl (map_one _) (one_pow 1)) hr hl hl0 hg₁G
      hconj hcoc
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
    refine ⟨?_, ?_⟩
    · set O := oddCoreIn (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K))) with hO
      have hOle : O ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K)) := oddCoreIn_le _
      have hOY : O.map φ ≤ Y := by
        rw [← hmap]
        exact Subgroup.map_mono hOle
      have hnorm : ∀ y ∈ ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1),
          fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p f 1)⁆ ⊓
            Subgroup.centralizer {x}, ∀ n ∈ O.map φ, y * n * y⁻¹ ∈ O.map φ := by
        rw [hY, ← hmap]
        rintro _ ⟨c, hc, rfl⟩ _ ⟨o, ho, rfl⟩
        have h := conj_mem_oddCoreIn hc ho
        have h2 := Subgroup.mem_map_of_mem φ h
        rw [map_mul, map_mul, map_inv] at h2
        exact h2
      have hodd : Odd (Nat.card (O.map φ)) := by
        rw [← Nat.card_congr (O.equivMapOfInjective φ hφ).toEquiv]
        exact odd_card_oddCoreIn _
      exact (Subgroup.map_eq_bot_iff_of_injective O hφ).1 (hA (O.map φ) (by rw [hY]; exact hOY)
        hnorm hodd)
    · intro L hL hO
      obtain ⟨e₀⟩ := hL.nonempty_equiv_sl2 hO
      have hLC : L ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 K)) :=
        isSubnormal_le hL.subnormal
      have hLY : L.map φ ≤ Y := by
        rw [← hmap]
        exact Subgroup.map_mono hLC
      have hLsub : IsSubnormal (L.map φ) Y := by
        have h1 := CFSG.ComponentClassification.Components.chain_map φ hL.subnormal
        rwa [hmap] at h1
      exact hB (L.map φ) (by rw [hY]; exact hLY)
        ⟨e₀.symm.trans (L.equivMapOfInjective φ hφ)⟩ (by rw [hY]; exact hLsub)

section Main

theorem exc3_exists_conj_rootGroup_of_member_E7
    {L : Subgroup ↥(adjointGroup .E7 (GaloisField 3 1))}
    {z : ↥(adjointGroup .E7 (GaloisField 3 1))} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ (g : ↥(adjointGroup .E7 (GaloisField 3 1))) (b : Fin Tag.E7.rank → (GaloisField 3 1)ˣ)
      (γ : Fin Tag.E7.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L = (rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-γ)).map
          (MulAut.conj g⁻¹).toMonoidHom ∧
        componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup .E7 (GaloisField 3 1) γ ⊔ rootSubgroup .E7 (GaloisField 3 1) (-γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have : Finite (ModGL .E7 (GaloisField 3 1)) := finite_modGL
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  obtain ⟨g, b, hb, hgz⟩ : ∃ (g : ↥(adjointGroup .E7 (GaloisField 3 1)))
      (b : Fin Tag.E7.rank → (GaloisField 3 1)ˣ), (∀ i, b i = 1 ∨ b i = -1) ∧
      ((g * z * g⁻¹ : ↥(adjointGroup .E7 (GaloisField 3 1))) :
        ModGL .E7 (GaloisField 3 1)) = rootDiagUnit .E7 b := by
    rcases e7_involution_cases (p := 3) (f := 1) (by norm_num) le_rfl (by norm_num) z hz2 with
      h1 | ⟨-, h2⟩
    · exact h1
    · exact absurd h (fun h' => h2 L h' hO)
  have hL' : IsClassicalMember3 (Generic.conjSub g L) (g * z * g⁻¹) := h.conj g
  have hO' : classicalInvolutionOddCore (Generic.conjSub g L) = ⊥ :=
    oddCore_eq_bot_of_equiv ((L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm) hO
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b (g * z * g⁻¹) hgz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := .E7) b
  have hL'C : Generic.conjSub g L ≤ Subgroup.centralizer
      ({g * z * g⁻¹} : Set ↥(adjointGroup .E7 (GaloisField 3 1))) := isSubnormal_le hL'.subnormal
  obtain ⟨e⟩ := hL'.nonempty_equiv_sl2 hO'
  let eL : SL(2, ZMod 3) ≃*
      ↥((Generic.conjSub g L).map (adjointGroup .E7 (GaloisField 3 1)).subtype) :=
    e.symm.trans ((Generic.conjSub g L).equivMapOfInjective
      (adjointGroup .E7 (GaloisField 3 1)).subtype
      (adjointGroup .E7 (GaloisField 3 1)).subtype_injective)
  have hLX : (Generic.conjSub g L).map (adjointGroup .E7 (GaloisField 3 1)).subtype ≤
      toralCentralizer .E7 (GaloisField 3 1) b := by
    rintro _ ⟨x, hx, rfl⟩
    have := hCz ▸ hL'C hx
    exact Subgroup.mem_subgroupOf.1 this
  have hsub : IsSubnormal ((Generic.conjSub g L).map (adjointGroup .E7 (GaloisField 3 1)).subtype)
      (toralCentralizer .E7 (GaloisField 3 1) b) := by
    have h1 := CFSG.ComponentClassification.Components.chain_map
      (adjointGroup .E7 (GaloisField 3 1)).subtype hL'.subnormal
    rwa [hCz, Subgroup.map_subgroupOf_eq_of_le hXC] at h1
  have hU' := fun i j (hi : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard)
      (hj : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) j).ncard) =>
    exc3_small_unique hK (uniqIsolated_E7 (maskChar (signTupleBits b))) i j hi hj
  obtain ⟨γ, hγ, h1, h2⟩ := exc3_exists_rankOne_of_member hK3 hb hU' eL hLX hsub
  refine ⟨g, b, γ, hγ, ?_, h2⟩
  have hL'eq := eq_rootGroup_sup_of_map_eq (rootOperatorFamily .E7) hγ.1 (h1.trans h2)
  have hLL : L = (Generic.conjSub g L).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp only [Generic.conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
    · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
      convert hx' using 1
      group
  rw [hLL, hL'eq]

theorem exc3_oddCore_centralizer_eq_bot_E7
    {z : ↥(adjointGroup .E7 (GaloisField 3 1))} (hz2 : z * z = 1) :
    oddCoreIn (Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 (GaloisField 3 1)))) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have : Finite (ModGL .E7 (GaloisField 3 1)) := finite_modGL
  rcases e7_involution_cases (p := 3) (f := 1) (by norm_num) le_rfl (by norm_num) z hz2 with
    ⟨g, b, hb, hgz⟩ | ⟨h2, -⟩
  · refine oddCoreIn_centralizer_eq_bot_of_mulEquiv
      (MulAut.conj g : ↥(adjointGroup .E7 (GaloisField 3 1)) ≃*
        ↥(adjointGroup .E7 (GaloisField 3 1))) z ?_
    have hz' : ((MulAut.conj g) z : ↥(adjointGroup .E7 (GaloisField 3 1))) = g * z * g⁻¹ := rfl
    rw [hz']
    have hCz := centralizer_eq_subgroupOf_toralCentralizer b (g * z * g⁻¹) hgz
    have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := .E7) b
    set O := oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} :
      Set ↥(adjointGroup .E7 (GaloisField 3 1)))) with hO
    have hN := exc3_oddNormal_eq_bot hK3 hb
      (N := O.map (adjointGroup .E7 (GaloisField 3 1)).subtype) (by
        rintro _ ⟨x, hx, rfl⟩
        have := hCz ▸ oddCoreIn_le _ hx
        exact Subgroup.mem_subgroupOf.1 this) (by
        rintro x hxX _ ⟨n, hn, rfl⟩
        have hxC : (⟨x, hXC hxX⟩ : ↥(adjointGroup .E7 (GaloisField 3 1))) ∈
            Subgroup.centralizer ({g * z * g⁻¹} :
              Set ↥(adjointGroup .E7 (GaloisField 3 1))) := by
          rw [hCz]
          exact Subgroup.mem_subgroupOf.2 hxX
        exact ⟨⟨x, hXC hxX⟩ * n * ⟨x, hXC hxX⟩⁻¹, conj_mem_oddCoreIn hxC hn, rfl⟩) (by
        rw [Subgroup.card_map_of_injective (adjointGroup .E7 (GaloisField 3 1)).subtype_injective]
        exact odd_card_oddCoreIn _)
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (adjointGroup .E7 (GaloisField 3 1)).subtype_injective).mp hN
  · exact h2

theorem exc3_e7_mem_fundamentalSubgroups (hadm : StatedLieAdmissible .E7 0 3 1)
    [Finite ↥(e7Data_valid.minGroup (GaloisField 3 1))]
    (hZ2 : IsPGroup 2 (Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 3 1))))
    {L : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1))}
    {z : ↥(e7Data_valid.minGroup (GaloisField 3 1))} (hL : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    L ∈ Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField 3 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hqs := isQuasisimple_e7 (GaloisField 3 1)
  have hθ := e7Isogeny_surjective (GaloisField 3 1)
  have hker : (e7Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField 3 1))
  have h2 : IsPGroup 2 (e7Isogeny (GaloisField 3 1)).ker := hZ2.to_le hker
  have hz : e7Isogeny (GaloisField 3 1) z ≠ 1 := fun h1 =>
    exc3_false_of_central_involution (open_isQuasisimple hqs) hL hO
      (hker (MonoidHom.mem_ker.2 h1))
  obtain ⟨hL', hO'⟩ := exc3_isClassicalMember3_map _ hθ hker hL hO hz
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exc3_exists_conj_rootGroup_of_member_E7 hL' hO'
  have hlong := isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  have hlongγ : Generic.IsLongestRoot (e7Datum (GaloisField 3 1)) γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ.1)
  obtain ⟨g', hg'⟩ := hθ g⁻¹
  set A := (e7Datum (GaloisField 3 1)).rootGroup γ with hA
  set B := (e7Datum (GaloisField 3 1)).rootGroup (-γ) with hB
  have hAmap : A.map (e7Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) γ :=
    map_e7Isogeny_rootGroup _ hγ.1
  have hBmap : B.map (e7Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-γ) :=
    map_e7Isogeny_rootGroup _ (IsRoot.neg hγ.1)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := exc3_minGroup_rootGroup_pow_three e7Data_valid _ hK3 γ
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := exc3_minGroup_rootGroup_pow_three e7Data_valid _ hK3 (-γ)
  have hconj3 : ∀ C : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1)),
      (∀ x ∈ C, x ^ 3 = 1) → ∀ x ∈ C.map (MulAut.conj g').toMonoidHom, x ^ 3 = 1 := by
    rintro C hC _ ⟨x, hx, rfl⟩
    show (g' * x * g'⁻¹) ^ 3 = 1
    rw [conj_pow, hC x hx]
    group
  have hRgen := exc3_closure_pow_three_eq_top (hconj3 A hA3) (hconj3 B hB3)
  set R' := A.map (MulAut.conj g').toMonoidHom ⊔ B.map (MulAut.conj g').toMonoidHom with hR'
  have hRθ : (A ⊔ B).map (e7Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) γ ⊔
        rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-γ) := by
    rw [Subgroup.map_sup, hAmap, hBmap]
  have hconjmap : ∀ H : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1)),
      (H.map (MulAut.conj g').toMonoidHom).map (e7Isogeny (GaloisField 3 1)) =
        (H.map (e7Isogeny (GaloisField 3 1))).map (MulAut.conj g⁻¹).toMonoidHom := by
    intro H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv, hg']
  have hRsup : R' = (A ⊔ B).map (MulAut.conj g').toMonoidHom := (Subgroup.map_sup A B _).symm
  have hLmap : L.map (e7Isogeny (GaloisField 3 1)) = R'.map (e7Isogeny (GaloisField 3 1)) := by
    rw [hRsup, hconjmap, hRθ]
    exact hLeq
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hO
  have hLR : L = R' :=
    exc3_eq_of_map_eq hker h2 (exc3_closure_pow_three_of_equiv e.symm) hRgen hLmap
  exact ⟨g', γ, Or.inl hlongγ, by rw [hLR, hRsup]; rfl⟩

theorem classicalMembersFundamental3Tag_E7 : ClassicalMembersFundamental3Tag .E7 := by
  intro n hp hFT hadm L z hL hO
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, hZ2⟩ := modelFiniteCenterTwoGroup3 .E7 0 hp hFT hadm
  have : Finite ↥(e7Data_valid.minGroup (GaloisField 3 1)) := hfin
  exact exc3_e7_mem_fundamentalSubgroups hadm hZ2 hL hO

theorem simpleOddCentralizerFreeTag_E7 : SimpleOddCentralizerFreeTag .E7 := by
  intro n hp hadm s hs
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, -⟩ := modelFiniteCenterTwoGroup3 .E7 0 hp trivial hadm
  have : Finite ↥(e7Data_valid.minGroup (GaloisField 3 1)) := hfin
  have : Finite ↥(adjointGroup .E7 (GaloisField 3 1)) := inferInstance
  have hqs := isQuasisimple_e7 (GaloisField 3 1)
  have hθ := e7Isogeny_surjective (GaloisField 3 1)
  have hker : (e7Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField 3 1))
  exact exc3_simpleOddCentralizer_of_cover (e7Isogeny (GaloisField 3 1)) hθ
    (exc3_ker_eq_center _ hθ hker center_adjointGroup_eq_bot)
    (fun c hc => exc3_oddCore_centralizer_eq_bot_E7 hc) s hs

theorem oddCentralizerFreeTag_E7 : OddCentralizerFreeTag .E7 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_E7

end Main

end CFSG.ClassicalInvolution.Q3
