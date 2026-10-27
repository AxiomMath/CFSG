module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspD4
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Reduce
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign CFSG.CGT.PushingUpLit.CGT6M
open CFSG.RankThree.PartOne (ExceptionalCenterSmallPrimes)

set_option linter.unusedSectionVars false


section Data

variable {K L : Type} [Field K] [Field L]

theorem twisted_invData_of_toral {t : TwistTag} [CharP K 5] [Finite K] (hK : 5 < Nat.card K)
    (a : Fin t.foldedTag.rank) (σ : K →+* K) (hσ : ∀ c : K, (σ ^ (t.orbit a).card) c = c)
    (ι : K →+* L) (Fr : L →+* L) (hFr : ∀ c, Fr (ι c) = ι (σ c))
    (w : ↥(graphFixedRootGroup t K σ)) (b : Fin t.tag.rank → Lˣ)
    (hb : ∀ j ∈ t.orbit a, b j = -1)
    (hw : baseChangeGL ι (w : ModGL t.tag K) = rootDiagUnit t.tag b) :
    InvData ↥(graphFixedRootGroup t K σ) w := by
  obtain ⟨c₂, hc₂⟩ := exists_pair_indep hK
  have hmem : ∀ c : K, c ∈ orbitField t K σ a := fun c => mem_orbitField.2 (hσ c)
  let oX : K → ↥(graphFixedRootGroup t K σ) := fun c =>
    ⟨(orbitX t K σ a ⟨c, hmem c⟩ : ModGL t.tag K),
      graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
        (orbitX_mem_graphFixedPosUnipotent t σ a ⟨c, hmem c⟩)⟩
  have oX_add : ∀ c c' : K, oX (c + c') = oX c * oX c' := fun c c' =>
    Subtype.ext (congrArg
      (fun x : ↥(adjointGroup t.tag K) => (x : ModGL t.tag K))
      (orbitX_add (t := t) σ a ⟨c, hmem c⟩ ⟨c', hmem c'⟩))
  have oX_zero : oX 0 = 1 := by
    have h := oX_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have oX_inj : Function.Injective oX := fun c c' h => by
    have h1 : orbitX t K σ a ⟨c, hmem c⟩ = orbitX t K σ a ⟨c', hmem c'⟩ :=
      Subtype.ext (congrArg (fun x : ↥(graphFixedRootGroup t K σ) =>
        (x : ModGL t.tag K)) h)
    exact congrArg Subtype.val (orbitX_injective (t := t) σ a h1)
  have oX_pow : ∀ (n : ℕ) (c : K), oX c ^ n = oX ((n : K) * c) := by
    intro n c
    induction n with
    | zero => simp [oX_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← oX_add]
      congr 1
      push_cast
      ring
  have oX_conj : ∀ c : K, w * oX c * w⁻¹ = oX (-c) := by
    intro c
    refine Subtype.ext (baseChangeGL_injective ι ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hw]
    change _ *
        baseChangeGL ι (orbitX t K σ a ⟨c, hmem c⟩ : ModGL t.tag K) * _ =
      baseChangeGL ι (orbitX t K σ a ⟨-c, hmem (-c)⟩ : ModGL t.tag K)
    rw [baseChangeGL_orbitX hFr, baseChangeGL_orbitX hFr,
      rootDiagUnit_conj_orbitX Fr a b hb]
    congr 3
    exact Subtype.ext (map_neg ι c).symm
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have hinv : ∀ c : K, w * oX c * w⁻¹ = (oX c)⁻¹ := fun c => by
    rw [oX_conj, eq_inv_iff_mul_eq_one, ← oX_add, neg_add_cancel, oX_zero]
  refine invData_of_pair (X := oX 1) (Y := oX c₂) ?_ ?_ ?_ ?_ (hinv 1) (hinv c₂)
  · rw [oX_pow, Nat.cast_ofNat, h5, zero_mul, oX_zero]
  · rw [oX_pow, Nat.cast_ofNat, h5, zero_mul, oX_zero]
  · change oX 1 * oX c₂ = oX c₂ * oX 1
    rw [← oX_add, ← oX_add, add_comm]
  · intro i j hij
    rw [oX_pow, oX_pow, ← oX_add, ← oX_zero] at hij
    have := oX_inj hij
    exact hc₂ i j (by simpa using this)

end Data

section Orbit

abbrev e6Orbit : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩

theorem e6Orbit_mem : ∀ j : Fin TwistTag.E6.tag.rank,
    j ∈ TwistTag.E6.orbit e6Orbit ↔ j = ⟨2, by decide⟩ ∨ j = ⟨4, by decide⟩ := by
  decide

theorem e6Orbit_card : (TwistTag.E6.orbit e6Orbit).card = 2 := by decide

end Orbit

section Main

theorem twistedE6_five_invData {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (5 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (5 ^ f))
    (t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) t := by
  classical
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hodd : Odd (5 ^ f) := Odd.pow (by decide)
  have hchar : CharP K 5 := finite_field_prime_power_characteristic hp5 (by omega : 1 ≤ 2 * f)
    (by rw [hK, ← pow_mul, mul_comm])
  have hcard : 5 < Nat.card K := by
    rw [hK]
    have h1 : 5 ≤ 5 ^ f := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 5 < 5 ^ 2 := by norm_num
      _ ≤ (5 ^ f) ^ 2 := Nat.pow_le_pow_left h1 2
  set L := AlgebraicClosure K
  have : CharP L 5 := charP_of_injective_algebraMap (algebraMap K L).injective 5
  obtain ⟨-, -, hHR, hHn, -, -, -⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.E6 hp5 hf hodd K hK σ.toRingHom hσ L (iterateFrobenius L 5 f)
    (fun c => iterateFrobenius_def 5 f c)
  set ι := algebraMap K L with hι
  set Fr := iterateFrobenius L 5 f with hFr_def
  let A := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  let ι₀ : ↥A →* ModGL TwistTag.E6.tag L := (baseChangeGL ι).comp A.subtype
  have hι₀ : Function.Injective ι₀ := (baseChangeGL_injective ι).comp A.subtype_injective
  let H : Subgroup (ModGL TwistTag.E6.tag L) := A.map (baseChangeGL ι)
  have hmemH : ∀ q : ↥A, ι₀ q ∈ H := fun q => ⟨q, q.2, rfl⟩
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
    (frobTwistGL TwistTag.E6.tag L 5 f (diagramMap TwistTag.E6 L)) with hR
  have hHR' : H ≤ R := hHR
  have hconjH : ∀ g ∈ R, ∀ y ∈ H, g * y * g⁻¹ ∈ H := by
    intro g hg y hy
    have h1 := hHn.conj_mem ⟨y, hHR hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 h1
  have hxR : ι₀ t ∈ R := hHR' (hmemH t)
  have ht2' : (t : ModGL TwistTag.E6.tag K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val ht2
  have hx2 : ι₀ t ^ 2 = 1 := by
    change baseChangeGL ι (t : ModGL TwistTag.E6.tag K) ^ 2 = 1
    rw [← map_pow, ht2', map_one]
  have hx1 : ι₀ t ≠ 1 := fun h1 => ht1 (hι₀ (h1.trans (map_one ι₀).symm))
  have hk2 : ringChar L ≠ 2 := by
    rw [ringChar.eq L 5]
    norm_num
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  have hunt : ∀ r ∈ e6SignDiagramReps,
      UntwistAt (frobTwistGL TwistTag.E6.tag L 5 f (diagramMap TwistTag.E6 L))
        (signCharTuple (signMaskChar TwistTag.E6.tag r.mask)) := by
    intro r hr
    refine untwistAt_of_eq _ _ ?_
    have ha := signCharTuple_sign (k := L) (signMaskChar TwistTag.E6.tag r.mask)
    exact (exceptional_toral_centralizer_identity_component TwistTag.E6.tag L hk2 _ ha).2.2.2.2.1
      (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, -⟩ := exists_twisted_toral_reduction 5 TwistTag.E6
    (by norm_num) hf e6SignDiagramReps h6.permChar_eq h6.exists_rep hunt hxR hx2
  rw [signCharTuple_signMaskChar] at hg₁x
  have hg₁R : g₁ ∈ R := mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩
  have key : ∃ (h : ModGL TwistTag.E6.tag L) (b : Fin TwistTag.E6.tag.rank → Lˣ), h ∈ R ∧
      h * ι₀ t * h⁻¹ = rootDiagUnit TwistTag.E6.tag b ∧
      ∀ j ∈ TwistTag.E6.orbit e6Orbit, b j = -1 := by
    have hmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
      have := List.mem_map_of_mem (f := SignRep.mask) hr
      have hm : e6SignDiagramReps.map SignRep.mask = [0, 20, 2] := rfl
      rw [hm] at this
      simpa using this
    rcases hmask with hmask | hmask | hmask
    · exfalso
      apply hx1
      rw [hmask] at hg₁x
      have h0 : signMaskTuple TwistTag.E6.tag L 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : g₁ * ι₀ t * g₁⁻¹ = 1 := by
        rw [hg₁x]
        rw [h0, rootDiagUnit_one]
      exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
    · rw [hmask] at hg₁x
      refine ⟨g₁, signMaskTuple TwistTag.E6.tag L 20, hg₁R, hg₁x, ?_⟩
      intro j hj
      have hj' := (e6Orbit_mem j).1 hj
      rcases hj' with rfl | rfl <;> simp [signMaskTuple]
    · rw [hmask] at hg₁x
      let i₁ : Fin TwistTag.E6.tag.rank := ⟨1, by decide⟩
      let i₃ : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩
      set a : Fin TwistTag.E6.tag.rank → Lˣ := signMaskTuple TwistTag.E6.tag L 2 with ha
      set n₁ : ModGL TwistTag.E6.tag L := weylElt TwistTag.E6.tag L i₁ 1 with hn₁
      set n₃ : ModGL TwistTag.E6.tag L := weylElt TwistTag.E6.tag L i₃ 1 with hn₃
      have hn₁G : n₁ ∈ adjointGroup TwistTag.E6.tag L := weylElt_mem_adjointGroup i₁ 1
      have hn₃G : n₃ ∈ adjointGroup TwistTag.E6.tag L := weylElt_mem_adjointGroup i₃ 1
      have hFn₁ : frobTwistGL TwistTag.E6.tag L 5 f (diagramMap TwistTag.E6 L) n₁ = n₁ := by
        have := frobTwistGL_diagramMap_weylElt_one 5 (k := L) TwistTag.E6 f i₁
        rwa [show TwistTag.E6.perm i₁ = i₁ by decide] at this
      have hFn₃ : frobTwistGL TwistTag.E6.tag L 5 f (diagramMap TwistTag.E6 L) n₃ = n₃ := by
        have := frobTwistGL_diagramMap_weylElt_one 5 (k := L) TwistTag.E6 f i₃
        rwa [show TwistTag.E6.perm i₃ = i₃ by decide] at this
      set a' : Fin TwistTag.E6.tag.rank → Lˣ :=
        fun j => a j * a i₁ ^ (-TwistTag.E6.tag.cartan i₁ j) with ha'
      set b : Fin TwistTag.E6.tag.rank → Lˣ :=
        fun j => a' j * a' i₃ ^ (-TwistTag.E6.tag.cartan i₃ j) with hb_def
      refine ⟨n₃ * (n₁ * g₁), b, mem_fixedPointsIn.2 ⟨mul_mem hn₃G (mul_mem hn₁G hg₁G), by
        rw [map_mul, map_mul, hFn₃, hFn₁, hFg₁]⟩, ?_, ?_⟩
      · calc n₃ * (n₁ * g₁) * ι₀ t * (n₃ * (n₁ * g₁))⁻¹ =
            n₃ * (n₁ * (g₁ * ι₀ t * g₁⁻¹) * n₁⁻¹) * n₃⁻¹ := by group
          _ = n₃ * (n₁ * rootDiagUnit TwistTag.E6.tag a * n₁⁻¹) * n₃⁻¹ := by rw [hg₁x]
          _ = n₃ * rootDiagUnit TwistTag.E6.tag a' * n₃⁻¹ := by
            rw [hn₁, LieType.Chevalley.weylElt_conj_rootDiagUnit (K := L) a i₁]
          _ = rootDiagUnit TwistTag.E6.tag b := LieType.Chevalley.weylElt_conj_rootDiagUnit (K := L) a' i₃
      · intro j hj
        have hj' := (e6Orbit_mem j).1 hj
        have c12 : TwistTag.E6.tag.cartan i₁ ⟨2, by decide⟩ = 0 := by decide
        have c14 : TwistTag.E6.tag.cartan i₁ ⟨4, by decide⟩ = 0 := by decide
        have c13 : TwistTag.E6.tag.cartan i₁ i₃ = -1 := by decide
        have c32 : TwistTag.E6.tag.cartan i₃ ⟨2, by decide⟩ = -1 := by decide
        have c34 : TwistTag.E6.tag.cartan i₃ ⟨4, by decide⟩ = -1 := by decide
        have s1 : a i₁ = -1 := by
          rw [ha]; simp [signMaskTuple, i₁]
        have s2 : a ⟨2, by decide⟩ = 1 := by
          rw [ha]; simp [signMaskTuple]
        have s3 : a i₃ = 1 := by
          rw [ha]; simp [signMaskTuple, i₃]
        have s4 : a ⟨4, by decide⟩ = 1 := by
          rw [ha]; simp [signMaskTuple]
        have t3 : a' i₃ = -1 := by
          rw [ha']; simp only [c13, s1, s3]; norm_num
        have u2 : a' ⟨2, by decide⟩ = 1 := by
          rw [ha']; simp only [c12, s2, s1]; norm_num
        have u4 : a' ⟨4, by decide⟩ = 1 := by
          rw [ha']; simp only [c14, s4, s1]; norm_num
        rcases hj' with rfl | rfl
        · show a' _ * a' i₃ ^ (-TwistTag.E6.tag.cartan i₃ _) = -1
          rw [u2, t3, c32]; norm_num
        · show a' _ * a' i₃ ^ (-TwistTag.E6.tag.cartan i₃ _) = -1
          rw [u4, t3, c34]; norm_num
  obtain ⟨h, b, hhR, hhx, hb⟩ := key
  have hdb : rootDiagUnit TwistTag.E6.tag b ∈ H := by
    rw [← hhx]
    exact hconjH h hhR _ (hmemH t)
  obtain ⟨w', hw', hw'e⟩ := hdb
  let w : ↥A := ⟨w', hw'⟩
  have hw : baseChangeGL ι (w : ModGL TwistTag.E6.tag K) = rootDiagUnit TwistTag.E6.tag b := hw'e
  have hN : ∀ q : ↥A, ∃ q' : ↥A, ι₀ q' = h⁻¹ * ι₀ q * h := by
    intro q
    have h1 := hconjH h⁻¹ (inv_mem hhR) _ (hmemH q)
    rw [inv_inv] at h1
    obtain ⟨q', hq', e⟩ := h1
    exact ⟨⟨q', hq'⟩, e⟩
  have htw : ι₀ t = h⁻¹ * ι₀ w * h := by
    change baseChangeGL ι (t : ModGL TwistTag.E6.tag K) =
      h⁻¹ * baseChangeGL ι (w : ModGL TwistTag.E6.tag K) * h
    rw [hw, ← hhx]
    change ι₀ t = _
    group
  refine invData_of_conj ι₀ hι₀ h hN htw ?_
  have hFrι : ∀ c : K, Fr (ι c) = ι (σ.toRingHom c) := fun c => by
    show iterateFrobenius L 5 f (ι c) = ι (σ c)
    rw [iterateFrobenius_def, ← map_pow, ← hσ]
  have hσ2 : ∀ c : K, (σ.toRingHom ^ (TwistTag.E6.orbit e6Orbit).card) c = c := by
    intro c
    rw [e6Orbit_card]
    have : Fintype K := Fintype.ofFinite K
    have hpow : c ^ ((5 ^ f) ^ 2) = c := by
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    show σ (σ c) = c
    rw [hσ (σ c), hσ c, ← pow_mul]
    have e : 5 ^ f * 5 ^ f = (5 ^ f) ^ 2 := by ring
    rw [e]
    exact hpow
  exact twisted_invData_of_toral hcard e6Orbit σ.toRingHom hσ2 ι Fr hFrι w b hb hw

end Main

section Cover

theorem coverInv_twistedE6_charFive (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type)
    [Group Q] (hQ : ChevalleyExceptionalModel Q .twistedE6 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, σ, hσ, ⟨e0⟩⟩ := hQ
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K', hK'f, hK'fin, σ', hK'c, hσ', ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 Nat.prime_five hf
      (⟨K, hKf, hKfin, hKc, σ, hσ, ⟨e0⟩⟩ : TwistedChevalleyModel Q TwistTag.E6 (5 ^ f))
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    exact invData_of_equiv e (twistedE6_five_invData hf K' hK'c σ' hσ' (e w) hew1 hew2)
  · have hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .twistedE6 5 f :=
      ⟨hadm, K, hKf, hKfin, hKc, σ, hσ, ⟨e'.trans e0⟩⟩
    exact hECS L (isQuasisimple_of_open hq)
      (Or.inl ⟨.twistedE6, 5, f, by simp [chevalleyExceptionalTags], hmod⟩) 5 Nat.prime_five
      (by norm_num)

end Cover

end CFSG.HardMathSupport.Foote.ModuleExclusions
