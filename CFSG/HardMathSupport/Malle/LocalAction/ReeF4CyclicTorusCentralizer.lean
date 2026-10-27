module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Open CFSG.RankThree.PartOne.K1214

section Abstract

theorem smul_det_eq_zero {G : Type*} [AddCommGroup G] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G) (h : ∀ k, ∑ l, A k l • x l = 0) (j : Fin 4) : A.det • x j = 0 := by
  have e : A.det • x j = ∑ l, (A.adjugate * A) j l • x l := by
    rw [Matrix.adjugate_mul]
    simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]
  rw [e]
  simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem pow_det_eq_one {G : Type*} [CommGroup G] (A : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin 4 → G)
    (h : ∀ k, ∏ l, b l ^ A k l = 1) (j : Fin 4) : b j ^ A.det = 1 := by
  have := smul_det_eq_zero A (fun l => Additive.ofMul (b l))
    (fun k => by
      have h' := congrArg Additive.ofMul (h k)
      simpa [ofMul_prod, ofMul_zpow] using h') j
  refine Additive.ofMul.injective (a₁ := b j ^ A.det) (a₂ := 1) ?_
  rw [ofMul_zpow]
  exact this

end Abstract

section Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128

section Exp

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] def relMatrix (a : ℕ) (Wm : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun k l => Wm l k -
    if l = (![3, 2, 1, 0] : Fin 4 → Fin 4) k then
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) l else 0

theorem relations_of_mem_twistedFixed (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag)
    (Wm : Matrix (Fin 4) (Fin 4) ℤ)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (k : Fin ReeTag.F4.tag.rank) :
    ∏ l : Fin ReeTag.F4.tag.rank, b l ^ Wm l k = b ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) ^
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
        ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) := by
  rw [rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF] at hb
  have h := hb (Pi.single k 1)
  rw [CTTorus.rootChar_single] at h
  have h1 : rootChar b (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      ∏ l : Fin ReeTag.F4.tag.rank, b l ^ Wm l k := by
    simp only [rootChar, hW]
  rw [h1] at h
  rw [h]
  show b (ReeTag.F4.perm k) ^ ((ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℕ) : ℤ) = _
  rw [relExp_vec, perm_vec]

theorem exponent_of_mem_twistedFixed (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag)
    (Wm : Matrix (Fin 4) (Fin 4) ℤ)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k) {M : ℕ}
    (hdet : (relMatrix a Wm).det.natAbs = M)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (j : Fin 4) :
    b j ^ M = 1 := by
  have hrel : ∀ k : Fin 4, ∏ l : Fin 4, b l ^ (relMatrix a Wm) k l = 1 := by
    intro k
    have h : ∏ l : Fin 4, b l ^ Wm l k = b ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) ^
        (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) :=
      relations_of_mem_twistedFixed hF w Wm hW hb k
    simp only [relMatrix, Matrix.of_apply, zpow_sub, ← div_eq_mul_inv, Finset.prod_div_distrib]
    have h2 : ∏ l : Fin 4, b l ^ (if l = (![3, 2, 1, 0] : Fin 4 → Fin 4) k then
        (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) l else 0) =
        b ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) ^
          (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
            ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) := by
      simp [apply_ite, Finset.prod_ite_eq']
    rw [h2, h, div_self']
  have h := pow_det_eq_one (relMatrix a Wm) (fun l : Fin 4 => b l) hrel j
  rcases Int.natAbs_eq (relMatrix a Wm).det with h' | h'
  · rw [h'] at h
    rw [← hdet]
    simpa using h
  · rw [h', zpow_neg, inv_eq_one] at h
    rw [← hdet]
    simpa using h

end Exp

section Twisted

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_hom_rank1_explicit (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (Wm : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ)
    (U : Fin ReeTag.F4.tag.rank → ℤ) (i : Fin ReeTag.F4.tag.rank)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hunit : IsCoprime (U i) (m : ℤ))
    (hfix : ∀ k : Fin ReeTag.F4.tag.rank, (∑ l, U l * Wm l k) ≡
      U (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple1 (z : Lˣ) U) := by
  classical
  let φ : (rootsOfUnity m L) →* (Fin ReeTag.F4.tag.rank → Lˣ) :=
    { toFun := fun z => expTuple1 (z : Lˣ) U
      map_one' := by
        funext l
        simp [expTuple1]
      map_mul' := fun z z' => by
        funext l
        simp [expTuple1, mul_zpow] }
  let Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L :=
    (rootDiagUnitHom ReeTag.F4.tag L).comp φ
  have hΦ : ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple1 (z : Lˣ) U) := fun z => rfl
  have hroot : ∀ z : rootsOfUnity m L, (z : Lˣ) ^ m = 1 := fun z => (mem_rootsOfUnity m _).1 z.2
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z : Lˣ) ^ U i = 1 := congrFun hb i
    exact Subtype.ext (zpow_eq_one_of_coprime (hroot z) hA hunit)
  refine ⟨Φ, hinj, ?_, hΦ⟩
  rintro _ ⟨z, rfl⟩
  rw [hΦ, rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF w]
  apply rootChar_smul_eq_of_forall_single
  intro k
  rw [rootChar_expTuple1, CTTorus.rootChar_single, reeTuple, expTuple1]
  have hpow : ∀ (n : ℕ) (x : Lˣ), x ^ n = x ^ (n : ℤ) := fun n x => (zpow_natCast x n).symm
  rw [hpow, ← zpow_mul]
  refine zpow_eq_zpow_of_modEq (hroot z) ?_
  have h0 := hfix k
  simp only [hW] at *
  exact h0

theorem exists_hom_rank1_explicit_vec (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 4 → ℤ) (i : Fin 4)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hunit : IsCoprime (U i) (m : ℤ))
    (hfix : ∀ k : Fin 4, (∑ l, U l * Wm l k) ≡
      U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
        (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple1 (z : Lˣ) U) := by
  refine exists_hom_rank1_explicit hF w Wm U i hW hunit (fun k => ?_)
  have h := hfix k
  have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
  have h1 := congrArg (fun j : Fin 4 => U j *
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j) e
  have h2 : U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) k)
        = U (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) := by
    rw [relExp_vec a (ReeTag.F4.perm k)]
    exact h1.symm
  rw [← h2]
  exact h

omit [CharP L 2] [IsAlgClosed L] in
theorem regular_famKernel_rank1 {ζ : Lˣ} {p : ℕ} (hζ : orderOf ζ = p)
    (U : Fin ReeTag.F4.tag.rank → ℤ)
    (hreg : ∀ β ∈ rootFinset ReeTag.F4.tag, ¬ (p : ℤ) ∣ ∑ i, U i * β i) :
    famKernel (τ := ReeTag.F4.tag)
      ({expTuple1 ζ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) = ∅ := by
  have hprim : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hζ
  refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
  obtain ⟨hroot, hall⟩ := hα
  have h1 := hall _ (Set.mem_singleton _)
  rw [rootChar_expTuple1, hprim.zpow_eq_one_iff_dvd] at h1
  exact hreg α (mem_rootFinset.2 hroot) h1

end Twisted

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]

theorem exists_regular_element_of_data (D : ReeFrameData K L 2) (w : WeylGroup ReeTag.F4.tag)
    (Wm : Matrix (Fin 4) (Fin 4) ℤ)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (U : Fin 4 → ℤ) (i : Fin 4) {p M : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hunit : IsCoprime (U i) (p : ℤ))
    (hfix : ∀ k : Fin 4, (∑ l, U l * Wm l k) ≡
      U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
        (![2 ^ 2, 2 ^ 2, 2 ^ (2 + 1), 2 ^ (2 + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD p])
    (hreg : ∀ β ∈ rootFinset ReeTag.F4.tag, ¬ (p : ℤ) ∣ ∑ i, U i * β i)
    (hdet : (relMatrix 2 Wm).det.natAbs = M) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = p ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ M = 1 := by
  classical
  have hpL : (p : L) ≠ 0 := fun h => by
    have h2 := (CharP.cast_eq_zero_iff L 2 p).1 h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_rank1_explicit_vec D.isFrob w Wm U i hW hunit hfix
  obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ := exists_hom_reeGamma_explicit D w Φ hΦinj hΦF
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  lift ζ₀ to Lˣ using hζ₀.isUnit hp.ne_zero
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  have hζord : orderOf ζ₀ = p := hζ₀.eq_orderOf.symm
  have hζp : ζ₀ ^ p = 1 := hζ₀.pow_eq_one
  let ζr : rootsOfUnity p L := ⟨ζ₀, (mem_rootsOfUnity p ζ₀).2 hζp⟩
  refine ⟨Ψ ζr, ?_, ?_⟩
  · rw [orderOf_injective Ψ hΨinj ζr, ← Subgroup.orderOf_coe ζr]
    exact hζord
  · intro γ hγ
    rw [Subgroup.mem_centralizer_iff] at hγ
    set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
    set u : ModGL ReeTag.F4.tag L := g₀⁻¹ * thetaGamma L 2 γ * g₀ with hu
    have hu_tw : u ∈ twistedFixed D.F n :=
      conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L γ) (D.fext_theta γ)
    have hcomm : u * Φ ζr = Φ ζr * u := by
      have h1 := hγ (Ψ ζr) (Set.mem_singleton _)
      have h2 := congrArg (thetaGamma L 2) h1
      rw [map_mul, map_mul, hΨ] at h2
      calc u * Φ ζr = g₀⁻¹ * (thetaGamma L 2 γ * (g₀ * Φ ζr * g₀⁻¹)) * g₀ := by rw [hu]; group
        _ = g₀⁻¹ * ((g₀ * Φ ζr * g₀⁻¹) * thetaGamma L 2 γ) * g₀ := by rw [h2]
        _ = Φ ζr * u := by rw [hu]; group
    have hΦ₁ : Φ ζr = rootDiagUnit ReeTag.F4.tag (expTuple1 ζ₀ U) := by
      rw [hΦ]
    have hFam : ∀ a ∈ ({expTuple1 ζ₀ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)),
        u * rootDiagUnit ReeTag.F4.tag a = rootDiagUnit ReeTag.F4.tag a * u := by
      intro a ha
      rw [Set.mem_singleton_iff.1 ha, ← hΦ₁]
      exact hcomm
    have hord : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) :=
      not_dvd_card_weylGroup_F4 hp hp3
    have hFp : ∀ a ∈ ({expTuple1 ζ₀ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)), ∀ i, a i ^ p = 1 := by
      intro a ha i
      rw [Set.mem_singleton_iff.1 ha]
      show (ζ₀ ^ U i) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
    have hstab := famStabilizer_subset_closure (τ := ReeTag.F4.tag) (L := L) hp hord
      hζord ({expTuple1 ζ₀ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) hFp
    have hker : famKernel (τ := ReeTag.F4.tag)
        ({expTuple1 ζ₀ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) ⊆
          (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
      rw [regular_famKernel_rank1 hζord U hreg]
    obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute_fam
      ({expTuple1 ζ₀ U} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) hstab (S := ∅) (fun α hα => hα.elim)
      (fun α hα => hα.elim) hker hu_tw.1 hFam
    have hbot : rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    have hq1 : q = 1 := by
      have : q ∈ rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := hq
      rw [hbot] at this
      exact this
    have htu : t = u := by
      subst hq1
      simpa using htq
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (htu ▸ ht)
    have hbM : ∀ j : Fin 4, b j ^ M = 1 := fun j =>
      exponent_of_mem_twistedFixed D.isFrob w Wm hW hdet (b := b) (by rw [← hb]; exact hu_tw) j
    have huM : u ^ M = 1 := by
      have h := (map_pow (rootDiagUnitHom ReeTag.F4.tag L) b M).symm
      have hb1 : b ^ M = 1 := funext fun k => by simpa using hbM k
      rw [hb1, map_one] at h
      rw [hb]
      exact h
    apply thetaGamma_injective L (K := K) (a := 2)
    rw [map_pow, map_one]
    have hθ : thetaGamma L 2 γ = g₀ * u * g₀⁻¹ := by rw [hu]; group
    have hc := map_pow (MulAut.conj g₀) u M
    simp only [MulAut.conj_apply] at hc
    rw [hθ, ← hc, huM]
    group

end Frame

section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_regular_element_of_data' (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (w : WeylGroup ReeTag.F4.tag) (Wm : Matrix (Fin 4) (Fin 4) ℤ)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (U : Fin 4 → ℤ) (i : Fin 4) {p M : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hunit : IsCoprime (U i) (p : ℤ))
    (hfix : ∀ k : Fin 4, (∑ l, U l * Wm l k) ≡
      U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
        (![2 ^ 2, 2 ^ 2, 2 ^ (2 + 1), 2 ^ (2 + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD p])
    (hreg : ∀ β ∈ rootFinset ReeTag.F4.tag, ¬ (p : ℤ) ∣ ∑ i, U i * β i)
    (hdet : (relMatrix 2 Wm).det.natAbs = M) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = p ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ M = 1 := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  exact exists_regular_element_of_data D w Wm hW U i hp hp3 hunit hfix hreg hdet

@[expose] noncomputable def w793 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1]

theorem w793_mat : wordMat ReeTag.F4.tag [0, 1] =
    toMat ReeTag.F4.tag.rank [[0, -1, 1, 0], [1, -1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
  wordMat_eq_toMat .F4 _ (by decide +kernel)

theorem det_w793 : (relMatrix 2 (toMat 4 [[0, -1, 1, 0], [1, -1, 1, 0], [0, 0, 1, 0],
    [0, 0, 0, 1]])).det.natAbs = 793 := by
  decide +kernel

theorem exists_regular_element_13 (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = 13 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ 793 = 1 :=
  exists_regular_element_of_data' hK w793
    (toMat 4 [[0, -1, 1, 0], [1, -1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    (fun k l => smul_single_eq_lget _ _ w793_mat k l)
    ![10, 8, 1, 1] 3 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) det_w793

theorem exists_regular_element_61 (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = 61 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ 793 = 1 :=
  exists_regular_element_of_data' hK w793
    (toMat 4 [[0, -1, 1, 0], [1, -1, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    (fun k l => smul_single_eq_lget _ _ w793_mat k l)
    ![46, 8, 39, 1] 3 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) det_w793

@[expose] noncomputable def w993 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 2, 1]

theorem w993_mat : wordMat ReeTag.F4.tag [0, 1, 2, 1] =
    toMat ReeTag.F4.tag.rank [[1, -1, 0, 1], [2, -1, 0, 1], [2, -2, 1, 1], [0, 0, 0, 1]] :=
  wordMat_eq_toMat .F4 _ (by decide +kernel)

theorem det_w993 : (relMatrix 2 (toMat 4 [[1, -1, 0, 1], [2, -1, 0, 1], [2, -2, 1, 1],
    [0, 0, 0, 1]])).det.natAbs = 993 := by
  decide +kernel

theorem exists_regular_element_331 (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = 331 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ 993 = 1 :=
  exists_regular_element_of_data' hK w993
    (toMat 4 [[1, -1, 0, 1], [2, -1, 0, 1], [2, -2, 1, 1], [0, 0, 0, 1]])
    (fun k l => smul_single_eq_lget _ _ w993_mat k l)
    ![96, 256, 31, 1] 3 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) det_w993

@[expose] noncomputable def w1321 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 0, 2, 1, 0, 3, 2, 1, 0]

theorem w1321_mat : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 3, 2, 1, 0] =
    toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-2, -1, 1, 1], [-2, -2, 2, 1], [-2, 0, 1, 0]] :=
  wordMat_eq_toMat .F4 _ (by decide +kernel)

theorem det_w1321 : (relMatrix 2 (toMat 4 [[-1, -1, 1, 0], [-2, -1, 1, 1], [-2, -2, 2, 1],
    [-2, 0, 1, 0]])).det.natAbs = 1321 := by
  decide +kernel

theorem exists_regular_element_1321 (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ x : ReeTag.F4.reeGamma K 2, orderOf x = 1321 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)), g ^ 1321 = 1 :=
  exists_regular_element_of_data' hK w1321
    (toMat 4 [[-1, -1, 1, 0], [-2, -1, 1, 1], [-2, -2, 2, 1], [-2, 0, 1, 0]])
    (fun k l => smul_single_eq_lget _ _ w1321_mat k l)
    ![586, 1055, 1289, 1] 3 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) det_w1321

end Main

end Lie

end CFSG.HardMathSupport.Malle.LocalAction
