module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspTrans
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Untwist
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.RankThree.PartOne (ExceptionalCenterSmallPrimes)

section OrbitConj

variable {t : TwistTag} {K : Type} [Field K]

theorem rootDiagUnit_conj_orbitX
    (σ : K →+* K) (a : Fin t.foldedTag.rank)
    (b : Fin t.tag.rank → Kˣ) (hb : ∀ j ∈ t.orbit a, b j = -1) (c : orbitField t K σ a) :
    rootDiagUnit t.tag b * (orbitX t K σ a c : ModGL t.tag K) * (rootDiagUnit t.tag b)⁻¹ =
      (orbitX t K σ a (-c) : ModGL t.tag K) := by
  rw [coe_orbitX, coe_orbitX]
  have hm : ∀ k ∈ List.range (t.orbit a).card, (t.perm ^ k) (t.orbitMin a) ∈ t.orbit a := by
    intro k hk
    have := Finset.mem_image_of_mem (fun k => (t.perm ^ k) (t.orbitMin a))
      (Finset.mem_range.2 (List.mem_range.1 hk))
    rwa [← t.orbit_eq_image_orbitMin a] at this
  have key : ∀ l : List ℕ, (∀ k ∈ l, (t.perm ^ k) (t.orbitMin a) ∈ t.orbit a) →
      rootDiagUnit t.tag b * (l.map fun k => xUnit t.tag K ((t.perm ^ k) (t.orbitMin a))
          ((σ ^ k) (c : K))).prod * (rootDiagUnit t.tag b)⁻¹ =
        (l.map fun k => xUnit t.tag K ((t.perm ^ k) (t.orbitMin a))
          ((σ ^ k) ((-c : orbitField t K σ a) : K))).prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons k l ih =>
      intro hl
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      have h1 := (root_diagonal_conjugation t.tag K b).1 ((t.perm ^ k) (t.orbitMin a))
        ((σ ^ k) (c : K))
      rw [hb _ (hl k List.mem_cons_self)] at h1
      have h2 := ih fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')
      calc rootDiagUnit t.tag b * (xUnit t.tag K ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K)) *
              (l.map fun k => xUnit t.tag K ((t.perm ^ k) (t.orbitMin a))
                ((σ ^ k) (c : K))).prod) * (rootDiagUnit t.tag b)⁻¹
          = (rootDiagUnit t.tag b * xUnit t.tag K ((t.perm ^ k) (t.orbitMin a))
                ((σ ^ k) (c : K)) * (rootDiagUnit t.tag b)⁻¹) *
              (rootDiagUnit t.tag b * (l.map fun k => xUnit t.tag K ((t.perm ^ k) (t.orbitMin a))
                ((σ ^ k) (c : K))).prod * (rootDiagUnit t.tag b)⁻¹) := by group
        _ = _ := by
          rw [h1, h2]
          simp [map_neg]
  exact key _ hm

end OrbitConj

abbrev d4Outer : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

abbrev d4Center : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩

section Data

variable {K L : Type} [Field K] [Field L]

theorem d4_invData_of_toral
    [CharP K 5] [Finite K]
    (hK : 5 < Nat.card K) (σ : K →+* K) (hσ : ∀ c : K, (σ ^ (TwistTag.D4.orbit d4Outer).card) c = c)
    (ι : K →+* L) (Fr : L →+* L) (hFr : ∀ c, Fr (ι c) = ι (σ c))
    (w : ↥(graphFixedRootGroup TwistTag.D4 K σ)) (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (hb : ∀ j ∈ TwistTag.D4.orbit d4Outer, b j = -1)
    (hw : baseChangeGL ι (w : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag b) :
    InvData ↥(graphFixedRootGroup TwistTag.D4 K σ) w := by
  obtain ⟨c₂, hc₂⟩ := exists_pair_indep hK
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ d4Outer := fun c => mem_orbitField.2 (hσ c)
  let oX : K → ↥(graphFixedRootGroup TwistTag.D4 K σ) := fun c =>
    ⟨(orbitX TwistTag.D4 K σ d4Outer ⟨c, hmem c⟩ : ModGL TwistTag.D4.tag K),
      graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ
        (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ d4Outer ⟨c, hmem c⟩)⟩
  have oX_add : ∀ c c' : K, oX (c + c') = oX c * oX c' := fun c c' =>
    Subtype.ext (congrArg
      (fun x : ↥(adjointGroup TwistTag.D4.tag K) => (x : ModGL TwistTag.D4.tag K))
      (orbitX_add (t := TwistTag.D4) σ d4Outer ⟨c, hmem c⟩ ⟨c', hmem c'⟩))
  have oX_zero : oX 0 = 1 := by
    have h := oX_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have oX_inj : Function.Injective oX := fun c c' h => by
    have h1 : orbitX TwistTag.D4 K σ d4Outer ⟨c, hmem c⟩ =
        orbitX TwistTag.D4 K σ d4Outer ⟨c', hmem c'⟩ :=
      Subtype.ext (congrArg (fun x : ↥(graphFixedRootGroup TwistTag.D4 K σ) =>
        (x : ModGL TwistTag.D4.tag K)) h)
    exact congrArg Subtype.val (orbitX_injective (t := TwistTag.D4) σ d4Outer h1)
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
        baseChangeGL ι (orbitX TwistTag.D4 K σ d4Outer ⟨c, hmem c⟩ : ModGL TwistTag.D4.tag K) * _ =
      baseChangeGL ι (orbitX TwistTag.D4 K σ d4Outer ⟨-c, hmem (-c)⟩ : ModGL TwistTag.D4.tag K)
    rw [baseChangeGL_orbitX hFr, baseChangeGL_orbitX hFr,
      rootDiagUnit_conj_orbitX Fr d4Outer b hb]
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

section Weyl

variable {K : Type} [Field K]

theorem weylElt_conj_rootDiagUnit
    {τ : Tag} (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      rootDiagUnit τ fun j => a j * a i ^ (-τ.cartan i j) := by
  have h := rootDiagUnit_conj_weylElt_one (K := K) a i
  have h2 : weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      (torusElt τ K i (a i))⁻¹ * rootDiagUnit τ a := by
    rw [eq_inv_mul_iff_mul_eq]
    calc torusElt τ K i (a i) * (weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹) =
        (rootDiagUnit τ a * weylElt τ K i 1 * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a *
          (weylElt τ K i 1)⁻¹ := by rw [h]; group
      _ = rootDiagUnit τ a := by group
  rw [h2, torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp [mul_comm, zpow_neg]

end Weyl

section Main

theorem trialityD4_five_invData
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (5 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (5 ^ f))
    (t : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) t := by
  classical
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hodd : Odd (5 ^ f) := Odd.pow (by decide)
  have hchar : CharP K 5 := finite_field_prime_power_characteristic hp5 (by omega : 1 ≤ 3 * f)
    (by rw [hK, ← pow_mul, mul_comm])
  have hcard : 5 < Nat.card K := by
    rw [hK]
    have h1 : 5 ≤ 5 ^ f := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 5 < 5 ^ 3 := by norm_num
      _ ≤ (5 ^ f) ^ 3 := Nat.pow_le_pow_left h1 3
  set L := AlgebraicClosure K
  have : CharP L 5 := charP_of_injective_algebraMap (algebraMap K L).injective 5
  obtain ⟨-, -, hHR, hHn, -, -, -⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.D4 hp5 hf hodd K hK σ.toRingHom hσ L (iterateFrobenius L 5 f)
    (fun c => iterateFrobenius_def 5 f c)
  set ι := algebraMap K L with hι
  set Fr := iterateFrobenius L 5 f with hFr_def
  let A := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let ι₀ : ↥A →* ModGL TwistTag.D4.tag L := (baseChangeGL ι).comp A.subtype
  have hι₀ : Function.Injective ι₀ := (baseChangeGL_injective ι).comp A.subtype_injective
  let H : Subgroup (ModGL TwistTag.D4.tag L) := A.map (baseChangeGL ι)
  have hmemH : ∀ q : ↥A, ι₀ q ∈ H := fun q => ⟨q, q.2, rfl⟩
  set R := fixedPointsIn (adjointGroup TwistTag.D4.tag L)
    (frobTwistGL TwistTag.D4.tag L 5 f (diagramMap TwistTag.D4 L)) with hR
  have hHR' : H ≤ R := hHR
  have hconjH : ∀ g ∈ R, ∀ y ∈ H, g * y * g⁻¹ ∈ H := by
    intro g hg y hy
    have h1 := hHn.conj_mem ⟨y, hHR hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 h1
  have hxR : ι₀ t ∈ R := hHR' (hmemH t)
  have ht2' : (t : ModGL TwistTag.D4.tag K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val ht2
  have hx2 : ι₀ t ^ 2 = 1 := by
    change baseChangeGL ι (t : ModGL TwistTag.D4.tag K) ^ 2 = 1
    rw [← map_pow, ht2', map_one]
  have hx1 : ι₀ t ≠ 1 := fun h1 => ht1 (hι₀ (h1.trans (map_one ι₀).symm))
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, -⟩ := exists_twisted_toral_reduction 5 TwistTag.D4
    (by norm_num) hf d4SignDiagramReps h4.permChar_eq h4.exists_rep (untwistAt_d4 5 (by norm_num) f)
    hxR hx2
  have hrm : r.mask = 4 := by
    rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
      rfl | hr'
    · exfalso
      apply hx1
      have h0 : signMaskTuple TwistTag.D4.tag L 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : g₁ * ι₀ t * g₁⁻¹ = 1 := by
        rw [hg₁x]
        change rootDiagUnit TwistTag.D4.tag
          (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
        rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
      exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
    · obtain rfl := List.mem_singleton.1 hr'
      rfl
  rw [hrm, signCharTuple_signMaskChar] at hg₁x
  set a : Fin TwistTag.D4.tag.rank → Lˣ := signMaskTuple TwistTag.D4.tag L 4 with ha
  set n₂ : ModGL TwistTag.D4.tag L := weylElt TwistTag.D4.tag L d4Center 1 with hn₂
  have hn₂G : n₂ ∈ adjointGroup TwistTag.D4.tag L := weylElt_mem_adjointGroup d4Center 1
  have hFn₂ : frobTwistGL TwistTag.D4.tag L 5 f (diagramMap TwistTag.D4 L) n₂ = n₂ := by
    have := frobTwistGL_diagramMap_weylElt_one 5 (k := L) TwistTag.D4 f d4Center
    rwa [show TwistTag.D4.perm d4Center = d4Center by decide] at this
  set h : ModGL TwistTag.D4.tag L := n₂ * g₁ with hh
  have hhR : h ∈ R := mem_fixedPointsIn.2 ⟨mul_mem hn₂G hg₁G, by rw [hh, map_mul, hFn₂, hFg₁]⟩
  set b : Fin TwistTag.D4.tag.rank → Lˣ :=
    fun j => a j * a d4Center ^ (-TwistTag.D4.tag.cartan d4Center j) with hb_def
  have hhx : h * ι₀ t * h⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    calc h * ι₀ t * h⁻¹ = n₂ * (g₁ * ι₀ t * g₁⁻¹) * n₂⁻¹ := by rw [hh]; group
      _ = n₂ * rootDiagUnit TwistTag.D4.tag a * n₂⁻¹ := by rw [hg₁x]
      _ = rootDiagUnit TwistTag.D4.tag b := weylElt_conj_rootDiagUnit (K := L) a d4Center
  have hcart : ∀ j : Fin TwistTag.D4.tag.rank, j ∈ TwistTag.D4.orbit d4Outer →
      TwistTag.D4.tag.cartan d4Center j = -1 := by decide
  have hbit : ∀ j : Fin TwistTag.D4.tag.rank, j ∈ TwistTag.D4.orbit d4Outer →
      4 / 2 ^ (j : ℕ) % 2 = 0 := by decide
  have ha2 : a d4Center = -1 := by simp [ha, signMaskTuple, d4Center]
  have hb : ∀ j ∈ TwistTag.D4.orbit d4Outer, b j = -1 := by
    intro j hj
    have haj : a j = 1 := by simp [ha, signMaskTuple, hbit j hj]
    simp only [hb_def, haj, hcart j hj, ha2]
    simp
  have hdb : rootDiagUnit TwistTag.D4.tag b ∈ H := by
    rw [← hhx]
    exact hconjH h hhR _ (hmemH t)
  obtain ⟨w', hw', hw'e⟩ := hdb
  let w : ↥A := ⟨w', hw'⟩
  have hw : baseChangeGL ι (w : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag b := hw'e
  have hN : ∀ q : ↥A, ∃ q' : ↥A, ι₀ q' = h⁻¹ * ι₀ q * h := by
    intro q
    have h1 := hconjH h⁻¹ (inv_mem hhR) _ (hmemH q)
    rw [inv_inv] at h1
    obtain ⟨q', hq', e⟩ := h1
    exact ⟨⟨q', hq'⟩, e⟩
  have htw : ι₀ t = h⁻¹ * ι₀ w * h := by
    change baseChangeGL ι (t : ModGL TwistTag.D4.tag K) =
      h⁻¹ * baseChangeGL ι (w : ModGL TwistTag.D4.tag K) * h
    rw [hw, ← hhx]
    change ι₀ t = _
    group
  refine invData_of_conj ι₀ hι₀ h hN htw ?_
  have hFrι : ∀ c : K, Fr (ι c) = ι (σ.toRingHom c) := fun c => by
    show iterateFrobenius L 5 f (ι c) = ι (σ c)
    rw [iterateFrobenius_def, ← map_pow, ← hσ]
  have hσ3 : ∀ c : K, (σ.toRingHom ^ (TwistTag.D4.orbit d4Outer).card) c = c := by
    intro c
    have hc3 : (TwistTag.D4.orbit d4Outer).card = 3 := by decide
    have : Fintype K := Fintype.ofFinite K
    have hpow : c ^ ((5 ^ f) ^ 3) = c := by
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [hc3]
    show σ (σ (σ c)) = c
    rw [hσ (σ (σ c)), hσ (σ c), hσ c, ← pow_mul, ← pow_mul]
    have e : 5 ^ f * (5 ^ f * 5 ^ f) = (5 ^ f) ^ 3 := by ring
    rw [e]
    exact hpow
  exact d4_invData_of_toral hcard σ.toRingHom hσ3 ι Fr hFrι w b hb hw

end Main

section Cover

theorem coverInv_trialityD4
    (hECS : ExceptionalCenterSmallPrimes) (Q : Type) [Group Q] {f : ℕ} (hf : 1 ≤ f)
    (hQ : ChevalleyExceptionalModel Q .trialityD4 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, σ, hσ, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, σ', hK'c, hσ', ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_five hf
      (⟨K, hKf, hKfin, hKc, σ, hσ, ⟨e0⟩⟩ : TwistedChevalleyModel Q TwistTag.D4 (5 ^ f))
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    exact invData_of_equiv e (trialityD4_five_invData hf K' hK'c σ' hσ' (e w) hew1 hew2)
  · have hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 5 f :=
      ⟨hadm, K, hKf, hKfin, hKc, σ, hσ, ⟨e'.trans e0⟩⟩
    exact hECS L (isQuasisimple_of_open hq)
      (Or.inl ⟨.trialityD4, 5, f, by simp [chevalleyExceptionalTags], hmod⟩) 5 Nat.prime_five
      (by norm_num)

end Cover

end CFSG.CGT.PushingUpLit.CGT6M
