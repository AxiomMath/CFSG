module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCNative
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCRoots
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCDatum

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux
open CFSG.RankThree.PartOne.KE6 (e6Nodes)
open scoped Matrix

section Forms

theorem e8nc_exp_form {L : Type} [Field L] {a : Fin Tag.E8.rank → Lˣ} (h3 : ∀ i, a i ^ 3 = 1)
    (ha1 : a ≠ 1) (hfix : ∀ v, rootChar a (r10NegC0 v) = (rootChar a v)⁻¹) :
    ∃ (ζ : Lˣ) (e : Fin Tag.E8.rank → ℕ) (x b c d : ZMod 3), orderOf ζ = 3 ∧
      (∀ i, a i = ζ ^ e i) ∧ ¬ (x = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∧
      ∀ i, ((e i : ℤ) : ZMod 3) =
        (![x, 2 * x, x, b, 2 * x, 2 * x, c, d] : Fin Tag.E8.rank → ZMod 3) i := by
  obtain ⟨ζ, e, hζ, he, hz⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_charColumn Nat.prime_three h3 ha1
  have hz3 : ∀ m : ℤ, ζ ^ m = 1 ↔ (m : ZMod 3) = 0 := fun m => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  set z : Fin Tag.E8.rank → ZMod 3 := fun i => ((e i : ℤ) : ZMod 3) with hzdef
  have hz' : z ≠ 0 := by
    intro h0
    apply hz
    funext i
    have := congrFun h0 i
    simpa [hzdef] using this
  have heq : ∀ j : Fin Tag.E8.rank, ∑ i, z i * ((r10C0Col j i : ℤ) : ZMod 3) = z j := by
    intro j
    have h1 := hfix (Pi.single j 1)
    rw [r10NegC0, r10_check_c0cols, CTTorus.rootChar_single, he j,
      CFSG.RankThree.PartOne.KE.rootChar_eq_zpow _ _ he] at h1
    have h2 : ζ ^ ((∑ i, (e i : ℤ) * r10C0Col j i) - (e j : ℤ)) = 1 := by
      have h1' : ζ ^ (-(∑ i, (e i : ℤ) * r10C0Col j i)) = ζ ^ (-(e j : ℤ)) := by
        rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, ← h1]
        congr 1
        rw [← _root_.zpow_neg]
        congr 1
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      have h4 := congrArg (fun x => x⁻¹) h1'
      simp only [_root_.zpow_neg, inv_inv] at h4
      rw [sub_eq_add_neg, _root_.zpow_add, h4, ← _root_.zpow_add]
      simp
    have h3' := (hz3 _).1 h2
    push_cast at h3'
    rw [sub_eq_zero] at h3'
    exact h3'
  set z0 := z ⟨0, by decide⟩
  set z1 := z ⟨1, by decide⟩
  set z2 := z ⟨2, by decide⟩
  set z3 := z ⟨3, by decide⟩
  set z4 := z ⟨4, by decide⟩
  set z5 := z ⟨5, by decide⟩
  set z6 := z ⟨6, by decide⟩
  set z7 := z ⟨7, by decide⟩
  have r0 := (Fin.sum_univ_eight _).symm.trans (heq ⟨0, by decide⟩)
  have r1 := (Fin.sum_univ_eight _).symm.trans (heq ⟨1, by decide⟩)
  have r2 := (Fin.sum_univ_eight _).symm.trans (heq ⟨2, by decide⟩)
  have r3 := (Fin.sum_univ_eight _).symm.trans (heq ⟨3, by decide⟩)
  have r4 := (Fin.sum_univ_eight _).symm.trans (heq ⟨4, by decide⟩)
  have r5 := (Fin.sum_univ_eight _).symm.trans (heq ⟨5, by decide⟩)
  have r6 := (Fin.sum_univ_eight _).symm.trans (heq ⟨6, by decide⟩)
  have q0 : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((1 : ℤ) : ZMod 3) +
      z3 * ((0 : ℤ) : ZMod 3) + z4 * ((0 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z0 := r0
  have q1 : z0 * ((-1 : ℤ) : ZMod 3) + z1 * ((-2 : ℤ) : ZMod 3) + z2 * ((-2 : ℤ) : ZMod 3) +
      z3 * ((-3 : ℤ) : ZMod 3) + z4 * ((-2 : ℤ) : ZMod 3) + z5 * ((-1 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z1 := r1
  have q2 : z0 * ((-1 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((-1 : ℤ) : ZMod 3) +
      z3 * ((0 : ℤ) : ZMod 3) + z4 * ((0 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z2 := r2
  have q3 : z0 * ((1 : ℤ) : ZMod 3) + z1 * ((1 : ℤ) : ZMod 3) + z2 * ((1 : ℤ) : ZMod 3) +
      z3 * ((1 : ℤ) : ZMod 3) + z4 * ((1 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z3 := r3
  have q4 : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((0 : ℤ) : ZMod 3) +
      z3 * ((0 : ℤ) : ZMod 3) + z4 * ((0 : ℤ) : ZMod 3) + z5 * ((1 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z4 := r4
  have q5 : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((0 : ℤ) : ZMod 3) +
      z3 * ((0 : ℤ) : ZMod 3) + z4 * ((-1 : ℤ) : ZMod 3) + z5 * ((-1 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z5 := r5
  have q6 : z0 * ((1 : ℤ) : ZMod 3) + z1 * ((1 : ℤ) : ZMod 3) + z2 * ((2 : ℤ) : ZMod 3) +
      z3 * ((3 : ℤ) : ZMod 3) + z4 * ((3 : ℤ) : ZMod 3) + z5 * ((2 : ℤ) : ZMod 3) +
      z6 * ((1 : ℤ) : ZMod 3) + z7 * ((0 : ℤ) : ZMod 3) = z6 := r6
  push_cast at q0 q1 q2 q3 q4 q5 q6
  obtain ⟨hs1, hs2, hs4, hs5⟩ := r10_form_solve z0 z1 z2 z3 z4 z5 z6 z7
    ⟨by linear_combination q1, by linear_combination (-1 : ZMod 3) * q0,
      by linear_combination q2, by linear_combination q3,
      by linear_combination (-1 : ZMod 3) * q4, by linear_combination q5,
      by linear_combination q6⟩
  refine ⟨ζ, e, z0, z3, z6, z7, hζ, he, ?_, fun i => ?_⟩
  · rintro ⟨hx0, hb0, hc0, hd0⟩
    apply hz'
    funext i
    obtain ⟨i, hi⟩ := i
    have hi' : i < 8 := hi
    interval_cases i
    · exact hx0
    · show z1 = 0
      rw [hs1, hx0]
      ring
    · show z2 = 0
      rw [hs2, hx0]
    · exact hb0
    · show z4 = 0
      rw [hs4, hx0]
      ring
    · show z5 = 0
      rw [hs5, hx0]
      ring
    · exact hc0
    · exact hd0
  · obtain ⟨i, hi⟩ := i
    have hi' : i < 8 := hi
    interval_cases i
    · rfl
    · exact hs1
    · exact hs2
    · rfl
    · exact hs4
    · exact hs5
    · rfl
    · rfl

theorem e8nc_line_cases {L : Type} [Field L] {a : Fin Tag.E8.rank → Lˣ} (h3 : ∀ i, a i ^ 3 = 1)
    (ha1 : a ≠ 1) (ha7 : a 7 = 1) (hfix : ∀ v, rootChar a (r10NegC0 v) = (rootChar a v)⁻¹) :
    ∃ (k : Fin 13) (ζ : Lˣ) (e : Fin Tag.E8.rank → ℕ) (c : ZMod 3), orderOf ζ = 3 ∧
      (∀ i, a i = ζ ^ e i) ∧ c ≠ 0 ∧ ∀ i, ((e i : ℤ) : ZMod 3) = c * r10LineForm k i := by
  obtain ⟨ζ, e, x, b, c, d, hζ, he, hnz, hF⟩ := e8nc_exp_form h3 ha1 hfix
  have hz3 : ∀ m : ℤ, ζ ^ m = 1 ↔ (m : ZMod 3) = 0 := fun m => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have hd : d = 0 := by
    have h1 : ζ ^ ((e 7 : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, ← he]
      exact ha7
    have h2 := (hz3 _).1 h1
    rw [hF 7] at h2
    exact h2
  subst hd
  obtain ⟨k, t, ht, hkt⟩ := r10_form_cases x b c fun h => hnz ⟨h.1, h.2.1, h.2.2, rfl⟩
  exact ⟨k, ζ, e, t, hζ, he, ht, fun i => (hF i).trans (congrFun hkt i)⟩

end Forms

section Kernel


theorem e8nc_kernel_eq {L : Type} [Field L] {a : Fin Tag.E8.rank → Lˣ} (k : Fin 13) {ζ : Lˣ}
    {e : Fin Tag.E8.rank → ℕ} {c : ZMod 3} (hζ : orderOf ζ = 3) (he : ∀ i, a i = ζ ^ e i)
    (hc : c ≠ 0) (hez : ∀ i, ((e i : ℤ) : ZMod 3) = c * r10LineForm k i) :
    rootCharKernel (weylTuple (wordW Tag.E8 (r10LineWord k))⁻¹ a) =
      r10A2pSet ∪ parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
  have hz3 : ∀ m : ℤ, ζ ^ m = 1 ↔ (m : ZMod 3) = 0 := fun m => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have hez' : ∀ i, ((e i : ℕ) : ZMod 3) = c * r10LineForm k i := fun i => by
    rw [← Int.cast_natCast]
    exact hez i
  have hμ : ∀ μ : Fin Tag.E8.rank → ℤ,
      rootChar (weylTuple (wordW Tag.E8 (r10LineWord k))⁻¹ a) μ = 1 ↔
        ∑ i, r10LineForm k i * ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) :
          ZMod 3) = 0 := by
    intro μ
    rw [rootChar_weylTuple, inv_inv, SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8,
      CFSG.RankThree.PartOne.KE.rootChar_eq_zpow _ _ he, hz3]
    push_cast
    simp_rw [hez']
    have hsum : ∑ i, c * r10LineForm k i * ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) :
        ZMod 3) = c * ∑ i, r10LineForm k i *
          ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) : ZMod 3) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum, mul_eq_zero, or_iff_right hc]
  ext μ
  change (IsRoot Tag.E8 μ ∧ _ = 1) ↔ (μ ∈ r10A2pSet ∨ μ ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8))
  rw [hμ]
  constructor
  · rintro ⟨hr, hs⟩
    rcases (r10_kernel k hr).1 hs with h | ⟨h6, h7⟩
    · exact Or.inl h
    · exact Or.inr (r10_mem_parabolicRoots_iff.2 ⟨hr, h6, h7⟩)
  · rintro (h | h)
    · have hr := r10_A2p_root μ h
      exact ⟨hr, (r10_kernel k hr).2 (Or.inl h)⟩
    · obtain ⟨hr, h6, h7⟩ := r10_mem_parabolicRoots_iff.1 h
      exact ⟨hr, (r10_kernel k hr).2 (Or.inr ⟨h6, h7⟩)⟩

theorem e8nc_kills_A2p {L : Type} [Field L] (k : Fin 13) {b : Fin Tag.E8.rank → Lˣ}
    (h3 : ∀ i, b i ^ 3 = 1) (hfix : ∀ v, rootChar b (r10NegC0 v) = (rootChar b v)⁻¹)
    (h7 : rootChar (weylTuple (wordW Tag.E8 (r10LineWord k))⁻¹ b) (Pi.single 7 1) = 1) :
    r10A2pSet ⊆ rootCharKernel (weylTuple (wordW Tag.E8 (r10LineWord k))⁻¹ b) := by
  intro β hβ
  refine ⟨r10_A2p_root β hβ, ?_⟩
  by_cases hb1 : b = 1
  · rw [hb1, rootChar_weylTuple, CTTorus.rootChar_one]
  obtain ⟨ζ, e, x, b', c, d, hζ, he, -, hF⟩ := e8nc_exp_form h3 hb1 hfix
  have hz3 : ∀ m : ℤ, ζ ^ m = 1 ↔ (m : ZMod 3) = 0 := fun m => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have hF' : ∀ i, ((e i : ℕ) : ZMod 3) =
      (![x, 2 * x, x, b', 2 * x, 2 * x, c, d] : Fin Tag.E8.rank → ZMod 3) i := fun i => by
    rw [← Int.cast_natCast]
    exact hF i
  have hμ : ∀ μ, rootChar (weylTuple (wordW Tag.E8 (r10LineWord k))⁻¹ b) μ = 1 ↔
      ∑ i, (![x, 2 * x, x, b', 2 * x, 2 * x, c, d] : Fin Tag.E8.rank → ZMod 3) i *
        ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) : ZMod 3) = 0 := by
    intro μ
    rw [rootChar_weylTuple, inv_inv, SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8,
      CFSG.RankThree.PartOne.KE.rootChar_eq_zpow _ _ he, hz3]
    push_cast
    simp_rw [hF']
    exact Iff.rfl
  exact (hμ β).2 (r10_check_A2_kill x b' c d k ((hμ _).1 h7) β hβ)

end Kernel

section Main


theorem e8nc_line_le_hyperClosure (hT : QuasiHigh5E6Cover.TwE6ThreeOpenDiag) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hs : SeitzExcOpenRest4.ThreeScope TauCeti.LieTypeIndex.E8 K)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E8 K E₀)
    (hD : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -((SeitzExcOpenRest6.Aux.wc1 *
      SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u))
    {y : adjointGroup Tag.E8 K} (hy : y ∈ E₀) (hy1 : y ≠ 1)
    {a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E8 a = diagMap D y)
    (haσ : rootChar a (Pi.single 7 1) = 1) :
    Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, -, hKq, hgood, -⟩ := hs
  have hq28 : ¬ (q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3)) := by
    rintro ⟨h2, h13⟩
    rcases hgood with hX | hX
    · apply hX
      refine Or.inr ⟨rfl, Or.inr (Or.inl ?_)⟩
      rcases h13 with h1 | h1
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hX
  set L := AlgebraicClosure K with hLdef
  set ℓ := q.p with hℓdef
  set f := q.exponent with hfdef
  haveI : Fact ℓ.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ f := q.exponent_pos
  have hKℓ : Nat.card K = ℓ ^ f := by rw [hKq, TauCeti.PrimePower.card_def]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hKℓ)
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hq1 : 3 ∣ ℓ ^ f + 1 := by
    rw [← hKℓ]
    omega
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrD : D.Fr = Fr := RingHom.ext fun c => by
    rw [D.hFr, hFrdef, iterateFrobenius_def, hKℓ]
  have hFr : ∀ x, Fr x = x ^ ℓ ^ f := fun x => iterateFrobenius_def ℓ f x
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, fun w => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq w (pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦdef
  obtain ⟨h3, hfixa⟩ := e8nc_datum_char hK hE₀.2 D hy ha
  have hfix' : ∀ v, rootChar a (r10NegC0 v) = (rootChar a v)⁻¹ := fun v => by
    rw [← r10_w_smul hD v]
    exact hfixa v
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hy1
    apply diagMap_injective D
    rw [map_one, ← ha]
    show rootDiagUnitHom Tag.E8 L 1 = 1
    exact map_one _
  have ha7 : a 7 = 1 := by
    rw [CTTorus.rootChar_single] at haσ
    exact haσ
  obtain ⟨k, ζ, e, cc, hζ, he, hcc, hez⟩ := e8nc_line_cases h3 ha1 ha7 hfix'
  set v : WeylGroup Tag.E8 := wordW Tag.E8 (r10LineWord k) with hvdef
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hVdef
  set n₀ : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L D.w with hn₀def
  set n : ModGL Tag.E8 L := V⁻¹ * n₀ * V with hndef
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E8 L := canonicalRep_mem_adjointGroup _ L v
  have hn₀m : n₀ ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L D.w
  have hnm : n ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hn₀m) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn₀ : weylQuotientHom Tag.E8 L ⟨n₀, hn₀m⟩ = D.w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep D.w)
  have hπn : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = v⁻¹ * D.w * v := by
    have : (⟨n, hnm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n₀, hn₀m⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV, hπn₀]
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrb) v
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hfixT : ∀ x : ModGL Tag.E8 L, n₀ * Φ x * n₀⁻¹ = x →
      n * Φ (V⁻¹ * x * V) * n⁻¹ = V⁻¹ * x * V := by
    intro x hx
    refine mem_twistedFixedPoints.1 ((mem_twistedFixedPoints_conj (n := n₀) hΦV).2 ?_)
    have e1 : V * (V⁻¹ * x * V) * V⁻¹ = x := by group
    rw [mem_twistedFixedPoints, e1]
    exact hx
  have hdiagfix : ∀ x : adjointGroup Tag.E8 K, n₀ * Φ (diagMap D x) * n₀⁻¹ = diagMap D x := by
    intro x
    have h := e8nc_diagMap_fixed D x
    rw [hFrD] at h
    exact h
  have hInvH : ∀ {t : ModGL Tag.E8 L}, t ∈ torusGroup Tag.E8 L →
      V⁻¹ * t * V ∈ torusGroup Tag.E8 L := by
    intro t ht
    have h := (Subgroup.mem_normalizer_iff.1
      (inv_mem (canonicalRep_mem_normalizer (R := L) v)) t).1 ht
    rwa [inv_inv] at h
  let ψ : adjointGroup Tag.E8 K →* ModGL Tag.E8 L :=
    (MulAut.conj V⁻¹).toMonoidHom.comp (diagMap D)
  have hψapp : ∀ x, ψ x = V⁻¹ * diagMap D x * V := fun x => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj V⁻¹).injective.comp (diagMap_injective D)
  have hψd : ∀ (x : adjointGroup Tag.E8 K) (b : Fin Tag.E8.rank → Lˣ),
      rootDiagUnit Tag.E8 b = diagMap D x → ψ x = rootDiagUnit Tag.E8 (weylTuple v⁻¹ b) := by
    intro x b hb
    rw [hψapp, ← hb]
    exact e8nc_conj_inv_rootDiagUnit v b
  set a' : Fin Tag.E8.rank → Lˣ := weylTuple v⁻¹ a with ha'def
  have hψy : ψ y = rootDiagUnit Tag.E8 a' := hψd y a ha
  have hker : rootCharKernel a' = r10A2pSet ∪ parabolicRoots Tag.E8 (e6Nodes Tag.E8) :=
    e8nc_kernel_eq k hζ he hcc hez
  have ha'3 : ∀ i, a' i ^ 3 = 1 := fun i => CTTorus.rootChar_pow_eq_one h3 _
  have hdiagψ : ∀ x : E₀, ∃ b, rootDiagUnit Tag.E8 b = (ψ.comp E₀.subtype) x := by
    intro x
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D x.2)
    exact ⟨weylTuple v⁻¹ b, (hψd x b hb).symm⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom' (ψ.comp E₀.subtype) hdiagψ (Pi.single 7 1)
  obtain ⟨⟨z, hzE⟩, hzy, hχz⟩ :=
    CFSG.HardMathSupport.Lang.TwE6Step3.exists_mem_ker_not_mem_zpowers hE₀ hc χ hy
  obtain ⟨bz, hbz⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hzE)
  have hψz : ψ z = rootDiagUnit Tag.E8 (weylTuple v⁻¹ bz) := hψd z bz hbz
  have hbz7 : rootChar (weylTuple v⁻¹ bz) (Pi.single 7 1) = 1 := by
    rw [← hχ ⟨z, hzE⟩ (weylTuple v⁻¹ bz) hψz.symm]
    exact hχz
  obtain ⟨hbz3, hbzfix⟩ := e8nc_datum_char hK hE₀.2 D hzE hbz
  have hzkill := e8nc_kills_A2p k hbz3 (fun u => by rw [← r10_w_smul hD u]; exact hbzfix u) hbz7
  refine native_a2e6_line_le_hyperClosure hT hf hq1 hq28 n hnm (wordW Tag.E8 (r10UWord k))
    (r10_u_mem k) (by rw [hπn]; exact r10_act_E6 k hD) (S₀ := r10A2pSet) r10_A2p_root
    (by rw [hπn]; exact r10_A2p_stable k hD) r10_A2p_orth ψ hψinj hE₀ hc ?_ hy hy1 hzE hzy ?_ ?_
    ?_ ?_
  ·
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hψapp]
      exact hInvH (diagMap_mem_torusGroup D hx)
    · rw [hψapp]
      exact hfixT _ (hdiagfix x)
  ·
    intro g hg
    have hS : parabolicRoots Tag.E8 (e6Nodes Tag.E8) ⊆ rootCharKernel a' := by
      rw [hker]
      exact Set.subset_union_right
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer a' hS hg)
    rw [hψy]
    exact h1.symm
  ·
    intro g hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer (weylTuple v⁻¹ bz) hzkill hg)
    rw [hψz]
    exact h1.symm
  ·
    intro x hxy
    have hxadj : ψ x ∈ adjointGroup Tag.E8 L := by
      rw [hψapp]
      exact mul_mem (mul_mem (inv_mem hVadj) (e8nc_diagMap_mem_adj D x)) hVadj
    have hcomm : ψ x * rootDiagUnit Tag.E8 a' = rootDiagUnit Tag.E8 a' * ψ x := by
      rw [← hψy, ← map_mul, ← map_mul, hxy]
    have hmem : ψ x ∈ toralCentralizer Tag.E8 L a' := by
      refine mem_toralCentralizer.2 ⟨hxadj, ?_⟩
      rw [← hcomm]
      group
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_E8_three L a'
      ha'3] at hmem
    refine ⟨?_, ?_⟩
    · have hmem' : ψ x ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel a') := hmem
      rw [hker] at hmem'
      exact hmem'
    · rw [hψapp]
      exact hfixT _ (hdiagfix x)
  ·
    intro P hPfin hPC hPF hPP x hx
    set P₁ : Subgroup (ModGL Tag.E8 L) := P.map (MulAut.conj V).toMonoidHom with hP₁
    haveI : Finite P := hPfin
    have hP₁fin : Finite P₁ :=
      Finite.of_surjective _ ((MulAut.conj V).toMonoidHom.subgroupMap_surjective P)
    have hP₁C : P₁ ≤ adjointGroup Tag.E8 L := by
      rintro _ ⟨w, hw, rfl⟩
      exact mul_mem (mul_mem hVadj (hPC hw)) (inv_mem hVadj)
    have hP₁F : ∀ w ∈ P₁, n₀ * Units.map (entrywiseHom D.Fr) w * n₀⁻¹ = w := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hFrD]
      change n₀ * Φ (V * w * V⁻¹) * n₀⁻¹ = V * w * V⁻¹
      exact mem_twistedFixedPoints.1 ((mem_twistedFixedPoints_conj (n := n₀) hΦV).1
        (mem_twistedFixedPoints.2 (hPF w hw)))
    have hP₁P : ⁅P₁, P₁⁆ = P₁ := by rw [hP₁, ← Subgroup.map_commutator, hPP]
    obtain ⟨g, hg⟩ := e8nc_diagMap_rational D P₁ hP₁fin hP₁C hP₁F hP₁P (V * x * V⁻¹) ⟨x, hx, rfl⟩
    refine ⟨g, ?_⟩
    rw [hψapp, hg]
    group

theorem e8NegCLineRest_of_twE6OpenDiag (hD : QuasiHigh5E6Cover.TwE6ThreeOpenDiag) :
    E8NegCLineRest := by
  intro K _ _ hK hs E₀ hE₀ hc _ D _ hw
  refine ⟨Pi.single 7 1, isRoot_single Tag.E8 7, ?_⟩
  rintro y hy hy1 ⟨a, ha, haσ⟩
  exact e8nc_line_le_hyperClosure hD hK hs hE₀ hc D hw hy hy1 ha haσ

end Main

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
