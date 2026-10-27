module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace ExcRank

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def TypeCover (τ : Tag) (p n q : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], ringChar L ≠ p →
    ∀ (a : Fin τ.rank → Lˣ), (∀ i, a i ^ p = 1) →
    ∀ w : WeylGroup τ, (∀ v, rootChar a (w • v) = rootChar a v ^ q) →
      ∃ w' : WeylGroup τ, (∀ v, rootChar a (w' • v) = rootChar a v ^ q) ∧
        ∃ B : Subgroup (Fin τ.rank → Lˣ), a ∈ B ∧ (∀ b ∈ B, ∀ i, b i ^ p = 1) ∧
          p ^ n ≤ Nat.card B ∧ ∀ b ∈ B, ∀ v, rootChar b (w' • v) = rootChar b v ^ q


theorem exists_toral_conj_gen {τ : Tag} {p : ℕ} (hp : p.Prime) (hmon : MonomialToralAt τ p)
    (K : Type) [Field K] [Finite K] (hK : ¬ p ∣ Nat.card K)
    {y : ModGL τ K} (hy : y ∈ adjointGroup τ K) (hyp : y ^ p = 1) :
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ p = 1) ∧
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y = g * rootDiagUnit τ a * g⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hℓp : ringChar K ≠ p := fun h => hK (by rw [hq, h]; exact dvd_pow_self p f.ne_zero)
  have hLchar : ringChar (AlgebraicClosure K) ≠ p := by
    rw [ringChar.eq (AlgebraicClosure K) (ringChar K)]
    exact hℓp
  have hy' : baseChangeGL (algebraMap K (AlgebraicClosure K)) y ∈
      adjointGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hy
  have hy'p : (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) ^ p = 1 := by
    rw [← map_pow, hyp, map_one]
  set y' := baseChangeGL (algebraMap K (AlgebraicClosure K)) y with hy'def
  have hBC : Subgroup.zpowers y' ≤ adjointGroup τ (AlgebraicClosure K) :=
    (Subgroup.zpowers_le).2 hy'
  haveI hBfin' : Finite (Subgroup.zpowers y') :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hy'p⟩)
  have hBfin : ((Subgroup.zpowers y' : Subgroup (ModGL τ (AlgebraicClosure K))) :
      Set (ModGL τ (AlgebraicClosure K))).Finite := Set.toFinite _
  have hBexp : ∀ x ∈ Subgroup.zpowers y', x ^ p = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy'p, one_zpow]
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_monomial_bar (L := AlgebraicClosure K) hℓp
    (isAlgebraic_zmod_algebraicClosure_of_finite K (ringChar K)) hBC hBfin hBexp
  have hn : c * y' * c⁻¹ ∈ monomialSubgroup τ (AlgebraicClosure K) :=
    hc y' (Subgroup.mem_zpowers y')
  have hnp : (c * y' * c⁻¹) ^ p = 1 := by rw [conj_pow, hy'p, mul_one, mul_inv_cancel]
  obtain ⟨g1, hg1C, hg1⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLchar hn hnp
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg1
  have hdp : rootDiagUnit τ a ^ p = 1 := by
    rw [← ha, conj_pow, hnp, mul_one, mul_inv_cancel]
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_one, ← hdp]
      exact (rootDiagUnitHom τ (AlgebraicClosure K)).map_pow a p
    have h2 := CFSG.LieType.Chevalley.rootDiagUnit_injective (K := AlgebraicClosure K)
      (τ := τ) h1
    exact fun i => by simpa using congrFun h2 i
  refine ⟨(g1 * c)⁻¹, inv_mem (mul_mem hg1C hcC), a, hap, ?_⟩
  rw [← ha]
  group

theorem exists_fixed_datum_gen {τ : Tag} {p n : ℕ} (hp : p.Prime) (hmon : MonomialToralAt τ p)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hq : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (hpq : ¬ p ∣ ℓ ^ f)
    (hcov : TypeCover τ p n (ℓ ^ f))
    {y : ModGL τ K} (hy : y ∈ adjointGroup τ K) (hyp : y ^ p = 1) :
    ∃ (g : ModGL τ (AlgebraicClosure K)) (w0 : WeylGroup τ)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (B : Subgroup (Fin τ.rank → (AlgebraicClosure K)ˣ)),
      g ∈ adjointGroup τ (AlgebraicClosure K) ∧ a ∈ B ∧ (∀ b ∈ B, ∀ i, b i ^ p = 1) ∧
      p ^ n ≤ Nat.card B ∧
      entrywiseFrobGL τ (AlgebraicClosure K) ℓ f g =
        g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w0 ∧
      (∀ b ∈ B, canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w0 *
          entrywiseFrobGL τ (AlgebraicClosure K) ℓ f (rootDiagUnit τ b) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w0)⁻¹ = rootDiagUnit τ b) ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y = g * rootDiagUnit τ a * g⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hpK : ¬ p ∣ Nat.card K := by rw [hq]; exact hpq
  have hpq' : Nat.Coprime p (ℓ ^ f) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
  obtain ⟨g0, hg0C, a, hap, hy0⟩ := exists_toral_conj_gen hp hmon K hpK hy hyp
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set Φ := entrywiseFrobGL τ L ℓ f with hΦ
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
  have hn : (g0⁻¹ * Φ g0) * Φ (rootDiagUnit τ a) * (g0⁻¹ * Φ g0)⁻¹ = rootDiagUnit τ a := by
    have h := hFix
    rw [hy0, map_mul, map_mul, map_inv] at h
    calc (g0⁻¹ * Φ g0) * Φ (rootDiagUnit τ a) * (g0⁻¹ * Φ g0)⁻¹
        = g0⁻¹ * (Φ g0 * Φ (rootDiagUnit τ a) * (Φ g0)⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * rootDiagUnit τ a * g0⁻¹) * g0 := by rw [h]
      _ = rootDiagUnit τ a := by group
  obtain ⟨w', z1, hz1, hlang⟩ := exists_lang_datum_of_plane ℓ f hf hpq' (fun _ : Unit => a)
    (fun _ i => hap i) hg0C (fun _ => hn)
  have hz1C := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz1)
  have hz1d : z1 * rootDiagUnit τ a = rootDiagUnit τ a * z1 := by
    have := hz1C.2 ()
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hg1C : g0 * z1 ∈ adjointGroup τ L := mul_mem hg0C hz1C.1
  have hg1fix : Φ (g0 * z1) = (g0 * z1) * canonicalRep (coxeterSystem τ) L w' :=
    inv_mul_eq_iff_eq_mul.1 hlang
  have hy1 : baseChangeGL ι y = (g0 * z1) * rootDiagUnit τ a * (g0 * z1)⁻¹ := by
    rw [hy0]
    calc g0 * rootDiagUnit τ a * g0⁻¹
        = g0 * (z1 * rootDiagUnit τ a) * z1⁻¹ * g0⁻¹ := by rw [hz1d]; group
      _ = (g0 * z1) * rootDiagUnit τ a * (g0 * z1)⁻¹ := by group
  have hfixd : canonicalRep (coxeterSystem τ) L w' * Φ (rootDiagUnit τ a) *
      (canonicalRep (coxeterSystem τ) L w')⁻¹ = rootDiagUnit τ a := by
    have h := hFix
    rw [hy1, map_mul, map_mul, map_inv, hg1fix] at h
    calc canonicalRep (coxeterSystem τ) L w' * Φ (rootDiagUnit τ a) *
          (canonicalRep (coxeterSystem τ) L w')⁻¹
        = (g0 * z1)⁻¹ * ((g0 * z1) * canonicalRep (coxeterSystem τ) L w' *
            Φ (rootDiagUnit τ a) *
            ((g0 * z1) * canonicalRep (coxeterSystem τ) L w')⁻¹) * (g0 * z1) := by group
      _ = (g0 * z1)⁻¹ * ((g0 * z1) * rootDiagUnit τ a * (g0 * z1)⁻¹) * (g0 * z1) := by
        rw [h]
      _ = rootDiagUnit τ a := by group
  have hchar : ∀ v, rootChar a (w' • v) = rootChar a v ^ ℓ ^ f := by
    intro v
    rw [hΦ, entrywiseFrobGL_rootDiagUnit_eq_pow] at hfixd
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (τ := τ) (K := L) a (a ^ ℓ ^ f) w').1
      hfixd.symm v
    rw [this, rootChar_pow']
  have hLchar : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ]
    intro h
    exact hpq (h ▸ dvd_pow_self ℓ (by omega))
  obtain ⟨w0, hw0a, B, haB, hBp, hBcard, hBw⟩ := hcov L hLchar a hap w' hchar
  have hrig : ∀ v, rootChar a ((w0⁻¹ * w') • v) = rootChar a v := by
    intro v
    rw [mul_smul]
    have h1 : rootChar a (w0⁻¹ • (w' • v)) ^ ℓ ^ f = rootChar a v ^ ℓ ^ f := by
      have h2 := hw0a (w0⁻¹ • (w' • v))
      rw [smul_inv_smul, hchar v] at h2
      exact h2.symm
    exact eq_of_pow_eq_of_coprime (rootChar_pow_eq_one a hap _) (rootChar_pow_eq_one a hap _)
      hpq' h1
  have hS : w0⁻¹ * w' ∈ Subgroup.closure
      ((fun α => rootReflection α) '' familyKernel (fun _ : Unit => a)) := by
    have hmem : w0⁻¹ * w' ∈ rootCharStabilizerSubgroup a := fun v => hrig v
    have h1 := hstab L a hap hmem
    rw [kernelReflectionGroup_eq_closure_rootReflection] at h1
    have hset : rootCharKernel a = familyKernel (fun _ : Unit => a) := by
      ext α
      simp only [rootCharKernel, familyKernel, Set.mem_setOf_eq, forall_const]
    rwa [hset] at h1
  have hy_mem := canonicalRep_mem_familyGroup_of_closure (L := L) (fun _ : Unit => a) hS
  have hw0img : (fun α => w0 • α) '' familyKernel (fun _ : Unit => a) =
      familyKernel (fun _ : Unit => a) :=
    image_familyKernel_of_pow ℓ hpq' (fun _ : Unit => a) (fun _ i => hap i)
      (fun _ v => hw0a v)
  obtain ⟨z2, hz2, hz2F⟩ := exists_datum_change ℓ f hf (fun _ : Unit => a) w' w0 (g0 * z1)
    hg1fix hw0img hy_mem
  have hz2C := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz2)
  have hz2d : z2 * rootDiagUnit τ a = rootDiagUnit τ a * z2 := by
    have := hz2C.2 ()
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  refine ⟨g0 * z1 * z2, w0, a, B, mul_mem hg1C hz2C.1, haB, hBp, hBcard, hz2F, ?_, ?_⟩
  · intro b hb
    rw [hΦ, entrywiseFrobGL_rootDiagUnit_eq_pow]
    refine ((rootDiagUnit_eq_conj_canonicalRep_iff (τ := τ) (K := L) b (b ^ ℓ ^ f) w0).2
      (fun v => ?_)).symm
    rw [rootChar_pow']
    exact hBw b hb v
  · rw [hy1]
    calc (g0 * z1) * rootDiagUnit τ a * (g0 * z1)⁻¹
        = (g0 * z1) * (z2 * rootDiagUnit τ a) * z2⁻¹ * (g0 * z1)⁻¹ := by
          rw [hz2d]; group
      _ = g0 * z1 * z2 * rootDiagUnit τ a * (g0 * z1 * z2)⁻¹ := by group

theorem centralizer_rank_of_cover {τ : Tag} {p n d : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hτ : (τ = Tag.E6 ∧ d = 3) ∨ (τ = Tag.E7 ∧ d = 2) ∨ (τ = Tag.E8 ∧ d = 1))
    (hmon : MonomialToralAt τ p)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (K : Type) [Field K] [Finite K] (hpK : ¬ p ∣ Nat.card K)
    (hcov : TypeCover τ p n (Nat.card K)) (y : adjointGroup τ K) (hy : y ^ p = 1) :
    n ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set (adjointGroup τ K))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact p.Prime := ⟨hp⟩
  have hq' : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  set L := AlgebraicClosure K with hL
  haveI : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective _
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hyp : (y : ModGL τ K) ^ p = 1 := by
    have := congrArg Subtype.val hy
    simpa using this
  obtain ⟨g, w0, a, B, hgC, haB, hBp, hBcard, hgfix, htw, hy0⟩ :=
    exists_fixed_datum_gen (K := K) (ℓ := ringChar K) (f := (f : ℕ)) hp hmon hstab hq' f.pos
      (hq' ▸ hpK) (hq' ▸ hcov) y.2 hyp
  let ι : K →+* L := algebraMap K L
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq']
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hrinj : Function.Injective (rootDiagUnitHom τ L) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (K := L) (τ := τ)
  let T : Subgroup (ModGL τ L) := B.map (rootDiagUnitHom τ L)
  let E : Subgroup (ModGL τ L) := T.map (MulAut.conj g).toMonoidHom
  have hEmem : ∀ x, x ∈ E ↔ ∃ b ∈ B, x = g * rootDiagUnit τ b * g⁻¹ := by
    intro x
    constructor
    · rintro ⟨t, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨rootDiagUnit τ b, ⟨b, hb, rfl⟩, rfl⟩
  have hEcard : Nat.card E = Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective hrinj]
  have hBpos : 0 < Nat.card B := lt_of_lt_of_le (pow_pos hp.pos n) hBcard
  have hEcomm : IsMulCommutative E := by
    refine IsMulCommutative.of_comm fun x y' => Subtype.ext ?_
    obtain ⟨b, -, hb⟩ := (hEmem x.1).1 x.2
    obtain ⟨c, -, hc⟩ := (hEmem y'.1).1 y'.2
    have hbc : rootDiagUnit τ b * rootDiagUnit τ c = rootDiagUnit τ c * rootDiagUnit τ b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    show (x : ModGL τ L) * y' = y' * x
    rw [hb, hc]
    calc g * rootDiagUnit τ b * g⁻¹ * (g * rootDiagUnit τ c * g⁻¹)
        = g * (rootDiagUnit τ b * rootDiagUnit τ c) * g⁻¹ := by group
      _ = g * (rootDiagUnit τ c * rootDiagUnit τ b) * g⁻¹ := by rw [hbc]
      _ = g * rootDiagUnit τ c * g⁻¹ * (g * rootDiagUnit τ b * g⁻¹) := by group
  have hEexp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hEmem x).1 hx
    have h1 : rootDiagUnit τ b ^ p = 1 := by
      have h2 : (rootDiagUnitHom τ L) (b ^ p) = (rootDiagUnitHom τ L) b ^ p := map_pow _ _ _
      rw [show b ^ p = 1 from funext (hBp b hb), map_one] at h2
      exact h2.symm
    rw [conj_pow, h1, mul_one, mul_inv_cancel]
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact hBpos.ne')
  have hEC : E ≤ adjointGroup τ L := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := (hEmem x).1 hx
    exact mul_mem (mul_mem hgC (CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
      (rootDiagUnit_mem_torusGroup b))) (inv_mem hgC)
  have hEF : ∀ x ∈ E, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hEmem x).1 hx
    have h1 := htw b hb
    change entrywiseFrobGL τ L (ringChar K) (f : ℕ) _ = _
    calc entrywiseFrobGL τ L (ringChar K) (f : ℕ) (g * rootDiagUnit τ b * g⁻¹)
        = (g * canonicalRep (coxeterSystem τ) L w0) *
            entrywiseFrobGL τ L (ringChar K) (f : ℕ) (rootDiagUnit τ b) *
            (g * canonicalRep (coxeterSystem τ) L w0)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgfix]
      _ = g * (canonicalRep (coxeterSystem τ) L w0 *
            entrywiseFrobGL τ L (ringChar K) (f : ℕ) (rootDiagUnit τ b) *
            (canonicalRep (coxeterSystem τ) L w0)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit τ b * g⁻¹ := by rw [h1]
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEexp x.1 x.2)⟩
  have hrat := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational (τ := τ) (K := K)
    (L := L) d hτ Fr hFr E hEC hEF).2 p hp hp3 E le_rfl hEp
  let φ' : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hφ' : Function.Injective φ' := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hErange : E ≤ φ'.range := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hrat hx
    exact ⟨⟨x', hx'⟩, rfl⟩
  let E₀ : Subgroup (adjointGroup τ K) := E.comap φ'
  have hmap : E₀.map φ' = E := Subgroup.map_comap_eq_self hErange
  have hE₀card : Nat.card E₀ = Nat.card B := by
    have h1 : Nat.card (E₀.map φ') = Nat.card E₀ := Subgroup.card_map_of_injective hφ'
    rw [← h1, hmap, hEcard]
  have hE₀ : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a' b' => Subtype.ext (hφ' ?_)⟩⟩, fun x hx => hφ' ?_⟩
    · have := congrArg Subtype.val (hEcomm.is_comm.comm ⟨φ' a', a'.2⟩ ⟨φ' b', b'.2⟩)
      simpa using this
    · rw [map_pow, map_one]
      exact hEexp _ hx
  have hyE : φ' y ∈ E := (hEmem _).2 ⟨a, haB, hy0⟩
  have hle : E₀ ≤ Subgroup.centralizer ({y} : Set (adjointGroup τ K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ'
    rw [map_mul, map_mul]
    have := congrArg Subtype.val (hEcomm.is_comm.comm ⟨φ' y, hyE⟩ ⟨φ' x, hx⟩)
    simpa using this.symm
  have hE₀fin : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hE₀card]; exact hBpos.ne')
  have hE₀p : IsPGroup p E₀ := fun x => ⟨1, Subtype.ext (by simpa using hE₀.2 x.1 x.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hE₀p
  have hnm : n ≤ m := by
    have h1 : p ^ n ≤ p ^ m := by rw [← hm, hE₀card]; exact hBcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  exact hnm.trans (CFSG.SectionRank.le_pRank hp.one_lt hle hE₀ hm)

end ExcRank

end CFSG.LocalAnalysis.RankFourTheoremC
