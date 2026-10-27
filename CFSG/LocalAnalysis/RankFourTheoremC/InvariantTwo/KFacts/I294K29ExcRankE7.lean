module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankLang
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace ExcRank

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Steinberg
  (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven)
open CFSG.RankThree.PartOne.KE (finite_fixed_subgroup_rational)


theorem exists_type_w0 {L : Type} [Field L] [IsAlgClosed L] (q : ℕ)
    (hq : 7 ∣ q - 1 ∨ 7 ∣ q + 1) (hq1 : 1 ≤ q) :
    ∃ w0 : WeylGroup Tag.E7, ∀ b : Fin Tag.E7.rank → Lˣ, (∀ i, b i ^ 7 = 1) →
      ∀ v, rootChar b v ^ q = rootChar b (w0 • v) := by
  rcases hq with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨1, fun b hb v => ?_⟩
    rw [one_smul]
    have h7 : rootChar b v ^ 7 = 1 := rootChar_pow_eq_one b hb v
    have hqm : q = 7 * m + 1 := by omega
    rw [hqm, pow_succ, pow_mul, h7, one_pow, one_mul]
  · obtain ⟨w0, hw0⟩ := exists_weyl_neg_E7
    refine ⟨w0, fun b hb v => ?_⟩
    rw [hw0 v]
    have h7 : rootChar b v ^ 7 = 1 := rootChar_pow_eq_one b hb v
    have hneg : rootChar b (-v) = (rootChar b v)⁻¹ := by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [hneg]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show q + 1 = 7 * m from hm, pow_mul, h7, one_pow]

theorem exists_toral_conj (K : Type) [Field K] [Finite K] (hK : ¬ 7 ∣ Nat.card K)
    {y : ModGL Tag.E7 K} (hy : y ∈ adjointGroup Tag.E7 K) (hy7 : y ^ 7 = 1) :
    ∃ g ∈ adjointGroup Tag.E7 (AlgebraicClosure K), ∃ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 7 = 1) ∧
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y = g * rootDiagUnit Tag.E7 a * g⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hℓ7 : ringChar K ≠ 7 := fun h => hK (by rw [hq, h]; exact dvd_pow_self 7 f.ne_zero)
  have hLchar : ringChar (AlgebraicClosure K) ≠ 7 := by
    rw [ringChar.eq (AlgebraicClosure K) (ringChar K)]
    exact hℓ7
  have hy' : baseChangeGL (algebraMap K (AlgebraicClosure K)) y ∈
      adjointGroup Tag.E7 (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hy
  have hy'7 : (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) ^ 7 = 1 := by
    rw [← map_pow, hy7, map_one]
  set y' := baseChangeGL (algebraMap K (AlgebraicClosure K)) y with hy'def
  have hBC : Subgroup.zpowers y' ≤ adjointGroup Tag.E7 (AlgebraicClosure K) :=
    (Subgroup.zpowers_le).2 hy'
  haveI hBfin' : Finite (Subgroup.zpowers y') :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨7, by norm_num, hy'7⟩)
  have hBfin : ((Subgroup.zpowers y' : Subgroup (ModGL Tag.E7 (AlgebraicClosure K))) :
      Set (ModGL Tag.E7 (AlgebraicClosure K))).Finite := Set.toFinite _
  have hBexp : ∀ x ∈ Subgroup.zpowers y', x ^ 7 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy'7, one_zpow]
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_monomial_bar (L := AlgebraicClosure K) hℓ7
    (isAlgebraic_zmod_algebraicClosure_of_finite K (ringChar K)) hBC hBfin hBexp
  have hn : c * y' * c⁻¹ ∈ monomialSubgroup Tag.E7 (AlgebraicClosure K) :=
    hc y' (Subgroup.mem_zpowers y')
  have hn7 : (c * y' * c⁻¹) ^ 7 = 1 := by rw [conj_pow, hy'7, mul_one, mul_inv_cancel]
  have hmon : MonomialToralAt Tag.E7 7 := monomialToralAt_seven_of_chainBlock
    (fun _ hγ => iform_self_E7 hγ) (chainBlockToral_E7_six_of_transitive a6ChainTransitive_E7)
  obtain ⟨g1, hg1C, hg1⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLchar hn hn7
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg1
  have hd7 : rootDiagUnit Tag.E7 a ^ 7 = 1 := by
    rw [← ha, conj_pow, hn7, mul_one, mul_inv_cancel]
  have ha7 : ∀ i, a i ^ 7 = 1 := by
    have h1 : rootDiagUnit Tag.E7 (a ^ 7) = rootDiagUnit Tag.E7 1 := by
      rw [rootDiagUnit_one, ← hd7]
      exact (rootDiagUnitHom Tag.E7 (AlgebraicClosure K)).map_pow a 7
    have h2 := CFSG.LieType.Chevalley.rootDiagUnit_injective (K := AlgebraicClosure K)
      (τ := Tag.E7) h1
    exact fun i => by simpa using congrFun h2 i
  refine ⟨(g1 * c)⁻¹, inv_mem (mul_mem hg1C hcC), a, ha7, ?_⟩
  rw [← ha]
  group

theorem exists_fixed_datum {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hq : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h7 : 7 ∣ ℓ ^ f - 1 ∨ 7 ∣ ℓ ^ f + 1)
    {y : ModGL Tag.E7 K} (hy : y ∈ adjointGroup Tag.E7 K) (hy7 : y ^ 7 = 1) :
    ∃ (g : ModGL Tag.E7 (AlgebraicClosure K)) (w0 : WeylGroup Tag.E7)
      (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ),
      g ∈ adjointGroup Tag.E7 (AlgebraicClosure K) ∧ (∀ i, a i ^ 7 = 1) ∧
      entrywiseFrobGL Tag.E7 (AlgebraicClosure K) ℓ f g =
        g * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0 ∧
      (∀ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ 7 = 1) →
        canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0 *
          entrywiseFrobGL Tag.E7 (AlgebraicClosure K) ℓ f (rootDiagUnit Tag.E7 b) *
          (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)⁻¹ =
            rootDiagUnit Tag.E7 b) ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y = g * rootDiagUnit Tag.E7 a * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq0 : 0 < ℓ ^ f := pow_pos (Fact.out : ℓ.Prime).pos f
  have hK7 : ¬ 7 ∣ ℓ ^ f := by omega
  have hK7' : ¬ 7 ∣ Nat.card K := by rw [hq]; exact hK7
  have hpq : Nat.Coprime 7 (ℓ ^ f) := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hK7
  obtain ⟨g0, hg0C, a, ha7, hy0⟩ := exists_toral_conj K hK7' hy hy7
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set Φ := entrywiseFrobGL Tag.E7 L ℓ f with hΦ
  have hFix : Φ (baseChangeGL ι y) = baseChangeGL ι y := by
    have : Fintype K := Fintype.ofFinite K
    have hcomp : (iterateFrobenius L ℓ f).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hq, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [hΦ, entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hn : (g0⁻¹ * Φ g0) * Φ (rootDiagUnit Tag.E7 a) * (g0⁻¹ * Φ g0)⁻¹ =
      rootDiagUnit Tag.E7 a := by
    have h := hFix
    rw [hy0, map_mul, map_mul, map_inv] at h
    calc (g0⁻¹ * Φ g0) * Φ (rootDiagUnit Tag.E7 a) * (g0⁻¹ * Φ g0)⁻¹
        = g0⁻¹ * (Φ g0 * Φ (rootDiagUnit Tag.E7 a) * (Φ g0)⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * rootDiagUnit Tag.E7 a * g0⁻¹) * g0 := by rw [h]
      _ = rootDiagUnit Tag.E7 a := by group
  obtain ⟨w', z1, hz1, hlang⟩ := exists_lang_datum_of_plane ℓ f hf hpq (fun _ : Unit => a)
    (fun _ i => ha7 i) hg0C (fun _ => hn)
  have hz1C := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz1)
  have hz1d : z1 * rootDiagUnit Tag.E7 a = rootDiagUnit Tag.E7 a * z1 := by
    have := hz1C.2 ()
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hg1C : g0 * z1 ∈ adjointGroup Tag.E7 L := mul_mem hg0C hz1C.1
  have hg1fix : Φ (g0 * z1) = (g0 * z1) * canonicalRep (coxeterSystem Tag.E7) L w' :=
    inv_mul_eq_iff_eq_mul.1 hlang
  have hy1 : baseChangeGL ι y = (g0 * z1) * rootDiagUnit Tag.E7 a * (g0 * z1)⁻¹ := by
    rw [hy0]
    calc g0 * rootDiagUnit Tag.E7 a * g0⁻¹
        = g0 * (z1 * rootDiagUnit Tag.E7 a) * z1⁻¹ * g0⁻¹ := by rw [hz1d]; group
      _ = (g0 * z1) * rootDiagUnit Tag.E7 a * (g0 * z1)⁻¹ := by group
  have hfixd : canonicalRep (coxeterSystem Tag.E7) L w' * Φ (rootDiagUnit Tag.E7 a) *
      (canonicalRep (coxeterSystem Tag.E7) L w')⁻¹ = rootDiagUnit Tag.E7 a := by
    have h := hFix
    rw [hy1, map_mul, map_mul, map_inv, hg1fix] at h
    calc canonicalRep (coxeterSystem Tag.E7) L w' * Φ (rootDiagUnit Tag.E7 a) *
          (canonicalRep (coxeterSystem Tag.E7) L w')⁻¹
        = (g0 * z1)⁻¹ * ((g0 * z1) * canonicalRep (coxeterSystem Tag.E7) L w' *
            Φ (rootDiagUnit Tag.E7 a) *
            ((g0 * z1) * canonicalRep (coxeterSystem Tag.E7) L w')⁻¹) * (g0 * z1) := by group
      _ = (g0 * z1)⁻¹ * ((g0 * z1) * rootDiagUnit Tag.E7 a * (g0 * z1)⁻¹) * (g0 * z1) := by
        rw [h]
      _ = rootDiagUnit Tag.E7 a := by group
  obtain ⟨w0, hw0⟩ := exists_type_w0 (L := L) (ℓ ^ f) h7 hq0
  have hchar : ∀ v, rootChar a (w' • v) = rootChar a v ^ ℓ ^ f := by
    intro v
    rw [hΦ, entrywiseFrobGL_rootDiagUnit_eq_pow] at hfixd
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (τ := Tag.E7) (K := L) a (a ^ ℓ ^ f) w').1
      hfixd.symm v
    rw [this, rootChar_pow']
  have hrig : ∀ v, rootChar a ((w0⁻¹ * w') • v) = rootChar a v := by
    intro v
    rw [mul_smul]
    have h1 : rootChar a (w0⁻¹ • (w' • v)) ^ ℓ ^ f = rootChar a v ^ ℓ ^ f := by
      rw [hw0 a ha7 (w0⁻¹ • (w' • v)), smul_inv_smul, hchar v]
    exact eq_of_pow_eq_of_coprime (rootChar_pow_eq_one a ha7 _) (rootChar_pow_eq_one a ha7 _)
      hpq h1
  have hS : w0⁻¹ * w' ∈ Subgroup.closure
      ((fun α => rootReflection α) '' familyKernel (fun _ : Unit => a)) := by
    have hmem : w0⁻¹ * w' ∈ rootCharStabilizerSubgroup a := fun v => hrig v
    have h1 := (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha7) ▸ hmem
    rw [kernelReflectionGroup_eq_closure_rootReflection] at h1
    have hset : rootCharKernel a = familyKernel (fun _ : Unit => a) := by
      ext α
      simp only [rootCharKernel, familyKernel, Set.mem_setOf_eq, forall_const]
    rwa [hset] at h1
  have hy_mem := canonicalRep_mem_familyGroup_of_closure (L := L) (fun _ : Unit => a) hS
  have hw0img : (fun α => w0 • α) '' familyKernel (fun _ : Unit => a) =
      familyKernel (fun _ : Unit => a) :=
    image_familyKernel_of_pow ℓ hpq (fun _ : Unit => a) (fun _ i => ha7 i)
      (fun _ v => (hw0 a ha7 v).symm)
  obtain ⟨z2, hz2, hz2F⟩ := exists_datum_change ℓ f hf (fun _ : Unit => a) w' w0 (g0 * z1)
    hg1fix hw0img hy_mem
  have hz2C := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz2)
  have hz2d : z2 * rootDiagUnit Tag.E7 a = rootDiagUnit Tag.E7 a * z2 := by
    have := hz2C.2 ()
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  refine ⟨g0 * z1 * z2, w0, a, mul_mem hg1C hz2C.1, ha7, hz2F, ?_, ?_⟩
  · intro b hb
    rw [hΦ, entrywiseFrobGL_rootDiagUnit_eq_pow]
    refine ((rootDiagUnit_eq_conj_canonicalRep_iff (τ := Tag.E7) (K := L) b (b ^ ℓ ^ f) w0).2
      (fun v => ?_)).symm
    rw [rootChar_pow']
    exact (hw0 b hb v).symm
  · rw [hy1]
    calc (g0 * z1) * rootDiagUnit Tag.E7 a * (g0 * z1)⁻¹
        = (g0 * z1) * (z2 * rootDiagUnit Tag.E7 a) * z2⁻¹ * (g0 * z1)⁻¹ := by
          rw [hz2d]; group
      _ = g0 * z1 * z2 * rootDiagUnit Tag.E7 a * (g0 * z1 * z2)⁻¹ := by group

theorem e7_seven_centralizer_rank (K : Type) [Field K] [Finite K]
    (hq : 7 ∣ Nat.card K - 1 ∨ 7 ∣ Nat.card K + 1)
    (y : adjointGroup Tag.E7 K) (hy : y ^ 7 = 1) :
    7 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer ({y} : Set (adjointGroup Tag.E7 K))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hq' : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : Finite (adjointGroup Tag.E7 K) := generated_group_finite Tag.E7 K
  set L := AlgebraicClosure K with hL
  haveI : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective _
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ7 : ringChar K ≠ 7 := by
    intro h
    have h7 : 7 ∣ Nat.card K := by rw [hq', h]; exact dvd_pow_self 7 f.ne_zero
    have hq0 : 0 < Nat.card K := Nat.card_pos
    omega
  have hLchar : ringChar L ≠ 7 := by
    rw [ringChar.eq L (ringChar K)]
    exact hℓ7
  have hy7 : (y : ModGL Tag.E7 K) ^ 7 = 1 := by
    have := congrArg Subtype.val hy
    simpa using this
  obtain ⟨g, w0, a, hgC, ha7, hgfix, htw, hy0⟩ :=
    exists_fixed_datum (K := K) (ℓ := ringChar K) (f := (f : ℕ)) hq' f.pos (hq' ▸ hq) y.2 hy7
  let ι : K →+* L := algebraMap K L
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq']
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  let A7 : Subgroup (Fin Tag.E7.rank → Lˣ) :=
    (powMonoidHom 7 : (Fin Tag.E7.rank → Lˣ) →* (Fin Tag.E7.rank → Lˣ)).ker
  have hA7mem : ∀ b, b ∈ A7 ↔ ∀ i, b i ^ 7 = 1 := fun b => by
    simp only [A7, MonoidHom.mem_ker, powMonoidHom_apply, funext_iff, Pi.pow_apply, Pi.one_apply]
  have hmu : Nat.card {a : Lˣ // a ^ 7 = 1} = 7 := by
    have : NeZero ((7 : ℕ) : L) :=
      ⟨by exact_mod_cast natCast_ne_zero_of_ringChar_ne (by norm_num) hLchar⟩
    obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 7
    exact (Nat.card_congr (Equiv.subtypeEquivRight fun a => (mem_rootsOfUnity 7 a).symm)).trans
      hω.card_rootsOfUnity
  have hA7card : Nat.card A7 = 7 ^ Tag.E7.rank := by
    have h1 : Nat.card A7 = Nat.card {t : Fin Tag.E7.rank → Lˣ // t ^ 7 = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun t => by
        simp only [A7, MonoidHom.mem_ker, powMonoidHom_apply])
    rw [h1, card_pi_pow_eq_one, hmu]
  have hrinj : Function.Injective (rootDiagUnitHom Tag.E7 L) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (K := L) (τ := Tag.E7)
  let T7 : Subgroup (ModGL Tag.E7 L) := A7.map (rootDiagUnitHom Tag.E7 L)
  let E : Subgroup (ModGL Tag.E7 L) := T7.map (MulAut.conj g).toMonoidHom
  have hEmem : ∀ x, x ∈ E ↔ ∃ b : Fin Tag.E7.rank → Lˣ, (∀ i, b i ^ 7 = 1) ∧
      x = g * rootDiagUnit Tag.E7 b * g⁻¹ := by
    intro x
    constructor
    · rintro ⟨t, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, (hA7mem b).1 hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨rootDiagUnit Tag.E7 b, ⟨b, (hA7mem b).2 hb, rfl⟩, rfl⟩
  have hEcard : Nat.card E = 7 ^ Tag.E7.rank := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective hrinj, hA7card]
  have hEcomm : IsMulCommutative E := by
    refine IsMulCommutative.of_comm fun x y' => Subtype.ext ?_
    obtain ⟨b, -, hb⟩ := (hEmem x.1).1 x.2
    obtain ⟨c, -, hc⟩ := (hEmem y'.1).1 y'.2
    have hbc : rootDiagUnit Tag.E7 b * rootDiagUnit Tag.E7 c =
        rootDiagUnit Tag.E7 c * rootDiagUnit Tag.E7 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    show (x : ModGL Tag.E7 L) * y' = y' * x
    rw [hb, hc]
    calc g * rootDiagUnit Tag.E7 b * g⁻¹ * (g * rootDiagUnit Tag.E7 c * g⁻¹)
        = g * (rootDiagUnit Tag.E7 b * rootDiagUnit Tag.E7 c) * g⁻¹ := by group
      _ = g * (rootDiagUnit Tag.E7 c * rootDiagUnit Tag.E7 b) * g⁻¹ := by rw [hbc]
      _ = g * rootDiagUnit Tag.E7 c * g⁻¹ * (g * rootDiagUnit Tag.E7 b * g⁻¹) := by group
  have hEexp : ∀ x ∈ E, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hEmem x).1 hx
    have h1 : rootDiagUnit Tag.E7 b ^ 7 = 1 := by
      have h2 : (rootDiagUnitHom Tag.E7 L) (b ^ 7) = (rootDiagUnitHom Tag.E7 L) b ^ 7 :=
        map_pow _ _ _
      rw [show b ^ 7 = 1 from funext hb, map_one] at h2
      exact h2.symm
    rw [conj_pow, h1, mul_one, mul_inv_cancel]
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero _ (by norm_num))
  have hEC : E ≤ adjointGroup Tag.E7 L := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := (hEmem x).1 hx
    exact mul_mem (mul_mem hgC (CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
      (rootDiagUnit_mem_torusGroup b))) (inv_mem hgC)
  have hEF : ∀ x ∈ E, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hEmem x).1 hx
    have h1 := htw b hb
    change entrywiseFrobGL Tag.E7 L (ringChar K) (f : ℕ) _ = _
    calc entrywiseFrobGL Tag.E7 L (ringChar K) (f : ℕ) (g * rootDiagUnit Tag.E7 b * g⁻¹)
        = (g * canonicalRep (coxeterSystem Tag.E7) L w0) *
            entrywiseFrobGL Tag.E7 L (ringChar K) (f : ℕ) (rootDiagUnit Tag.E7 b) *
            (g * canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgfix]
      _ = g * (canonicalRep (coxeterSystem Tag.E7) L w0 *
            entrywiseFrobGL Tag.E7 L (ringChar K) (f : ℕ) (rootDiagUnit Tag.E7 b) *
            (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit Tag.E7 b * g⁻¹ := by rw [h1]
  have hEp : IsPGroup 7 E := fun x => ⟨1, Subtype.ext (by simpa using hEexp x.1 x.2)⟩
  have hrat := (finite_fixed_subgroup_rational (τ := Tag.E7) (K := K) (L := L) 2
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr E hEC hEF).2 7 (by norm_num) (by norm_num) E le_rfl hEp
  let φ' : adjointGroup Tag.E7 K →* ModGL Tag.E7 L :=
    (baseChangeGL ι).comp (adjointGroup Tag.E7 K).subtype
  have hφ' : Function.Injective φ' := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hErange : E ≤ φ'.range := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hrat hx
    exact ⟨⟨x', hx'⟩, rfl⟩
  let E₀ : Subgroup (adjointGroup Tag.E7 K) := E.comap φ'
  have hmap : E₀.map φ' = E := Subgroup.map_comap_eq_self hErange
  have hE₀card : Nat.card E₀ = 7 ^ Tag.E7.rank := by
    have h1 : Nat.card (E₀.map φ') = Nat.card E₀ := Subgroup.card_map_of_injective hφ'
    rw [← h1, hmap, hEcard]
  have hE₀ : IsElemAbelian 7 E₀ := by
    refine ⟨⟨⟨fun a' b' => Subtype.ext (hφ' ?_)⟩⟩, fun x hx => hφ' ?_⟩
    · have := congrArg Subtype.val (hEcomm.is_comm.comm ⟨φ' a', a'.2⟩ ⟨φ' b', b'.2⟩)
      simpa using this
    · rw [map_pow, map_one]
      exact hEexp _ hx
  have hyE : φ' y ∈ E := (hEmem _).2 ⟨a, ha7, hy0⟩
  have hle : E₀ ≤ Subgroup.centralizer ({y} : Set (adjointGroup Tag.E7 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ'
    rw [map_mul, map_mul]
    have := congrArg Subtype.val (hEcomm.is_comm.comm ⟨φ' y, hyE⟩ ⟨φ' x, hx⟩)
    simpa using this.symm
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 7) hle hE₀ hE₀card
  exact this

end ExcRank

end CFSG.LocalAnalysis.RankFourTheoremC
