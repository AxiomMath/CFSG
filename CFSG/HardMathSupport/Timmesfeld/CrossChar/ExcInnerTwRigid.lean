module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KGD.D4Twist
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

variable {τ : Tag} {L : Type} [Field L]

theorem rootSL2_mem_rootSpan_pair
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (B : SL2 L) :
    rootSL2 τ L β B ∈ rootSpan τ L {β, -β} := by
  have hB : rootSL2 τ L β B ∈ rootRankOneGroup τ L β := ⟨B, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L hβ).1] at hB
  exact sup_le (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ))) =>
    rootSubgroup τ L γ) β (Set.mem_insert _ _) le_rfl)
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ))) =>
      rootSubgroup τ L γ) (-β) (Set.mem_insert_of_mem _ rfl) le_rfl) hB

theorem eq_zero_of_dvd_pow_sub_one_or_add_one {p₀ f j m : ℕ} (hp₀ : p₀.Prime) (hj : j < f)
    (hm : m ∣ p₀ ^ f + 1) (hm2 : p₀ ^ f + 1 ≤ 2 * m)
    (h : m ∣ p₀ ^ j - 1 ∨ m ∣ p₀ ^ j + 1) : j = 0 := by
  by_contra hj0
  set x := p₀ ^ j with hxdef
  set q := p₀ ^ f with hqdef
  have hp2 := hp₀.two_le
  have hx : p₀ ≤ x := Nat.le_self_pow hj0 p₀
  have hq : p₀ * x ≤ q := by
    have h1 : q = p₀ ^ (f - j) * x := by rw [hqdef, hxdef, ← pow_add, Nat.sub_add_cancel hj.le]
    rw [h1]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) p₀)
  have hq2 : 2 * x ≤ q := le_trans (Nat.mul_le_mul_right _ hp2) hq
  obtain ⟨k, hk⟩ := hm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hk
      omega
    · exact h0
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have : m * 3 ≤ m * k := Nat.mul_le_mul_left _ (by omega)
    omega
  rcases h with h | h
  · have h1 : m ≤ x - 1 := Nat.le_of_dvd (by omega) h
    omega
  · have h1 : m ≤ x + 1 := Nat.le_of_dvd (by omega) h
    interval_cases k
    · omega
    · omega
    ·
      have hp3 : 3 ≤ p₀ := by
        rcases hp₀.eq_two_or_odd' with h2 | hodd
        · exfalso
          have hqe : Even q := by
            rw [hqdef, h2]
            exact (Nat.even_pow' (by omega)).2 even_two
          obtain ⟨r, hr⟩ := hqe
          omega
        · obtain ⟨r, hr⟩ := hodd
          omega
      have hq3 : 3 * x ≤ q := le_trans (Nat.mul_le_mul_right _ hp3) hq
      omega

theorem field_exponent_eq_zero {p₀ f j : ℕ} (hp₀ : p₀.Prime) (hj : j < f) {d m : ℕ}
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (hm : m ∣ p₀ ^ f + 1) (hm2 : p₀ ^ f + 1 ≤ 2 * m) (hm3 : 2 ≤ m)
    (hmd : ∀ x : ℤ, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ d * x → (m : ℤ) ∣ x)
    (i : Fin τ.rank)
    (hroot : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → (∀ l, l ≠ i → (m : ℤ) ∣ β l) →
      (m : ℤ) ∣ β i - 1 ∨ (m : ℤ) ∣ β i + 1)
    (b : Label τ)
    (hb : ∀ k : Fin τ.rank, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣
      (∑ l, τ.cartan k l * b.latticeWeight l) - (p₀ ^ j : ℕ) * τ.cartan k i) :
    j = 0 := by
  classical
  set N : ℤ := ((p₀ ^ f + 1 : ℕ) : ℤ) with hN
  set c : ℤ := ((p₀ ^ j : ℕ) : ℤ) with hc
  set w : Fin τ.rank → ℤ := b.latticeWeight - c • Pi.single i 1 with hw
  have hAw : ∀ k, N ∣ (τ.cartan *ᵥ w) k := by
    intro k
    have h1 : (τ.cartan *ᵥ w) k =
        (∑ l, τ.cartan k l * b.latticeWeight l) - c * τ.cartan k i := by
      simp only [Matrix.mulVec, dotProduct, hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single i (fun l _ hli => by simp [hli])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp
      ring
    rw [h1]
    exact hb k
  have hdw : ∀ l, N ∣ (d : ℤ) * w l := by
    intro l
    have h1 : (d : ℤ) * w l = (B *ᵥ (τ.cartan *ᵥ w)) l := by
      rw [Matrix.mulVec_mulVec, hB, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        smul_eq_mul]
    rw [h1]
    show N ∣ ∑ k, B l k * (τ.cartan *ᵥ w) k
    exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hAw k) _
  have hmw : ∀ l, (m : ℤ) ∣ w l := fun l => hmd _ (hdw l)
  have hcop : Nat.Coprime m p₀ := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp₀).2 fun hdvd => ?_)
    have h1 : p₀ ∣ p₀ ^ f + 1 := hdvd.trans hm
    have h2 : p₀ ∣ p₀ ^ f := dvd_pow_self p₀ (by omega)
    have h3 := (Nat.dvd_add_right h2).1 h1
    exact hp₀.one_lt.ne' (Nat.dvd_one.1 h3)
  have hx1 : 1 ≤ p₀ ^ j := Nat.one_le_pow _ _ hp₀.pos
  rcases b with l₀ | ⟨β, hβ⟩
  ·
    exfalso
    have h1 := hmw i
    simp only [hw, Label.latticeWeight, zero_sub, Pi.neg_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, dvd_neg, hc] at h1
    have h2 : m ∣ p₀ ^ j := Int.natCast_dvd_natCast.1 h1
    have h3 : m ∣ 1 := (Nat.Coprime.pow_right j hcop).eq_one_of_dvd h2 ▸ dvd_refl _
    exact absurd (Nat.le_of_dvd one_pos h3) (by omega)
  · have hβl : ∀ l, l ≠ i → (m : ℤ) ∣ β l := by
      intro l hli
      have h1 := hmw l
      simpa only [hw, Label.latticeWeight, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hli,
        smul_eq_mul, mul_zero, sub_zero] using h1
    have h1 := hmw i
    simp only [hw, Label.latticeWeight, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one] at h1
    refine eq_zero_of_dvd_pow_sub_one_or_add_one hp₀ hj hm hm2 ?_
    rcases hroot β hβ hβl with h | h
    · left
      have h2 : (m : ℤ) ∣ ((p₀ ^ j - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hx1, Nat.cast_one]
        have h3 := dvd_sub h h1
        rwa [show β i - 1 - (β i - c) = c - 1 by ring] at h3
      exact Int.natCast_dvd_natCast.1 h2
    · right
      have h2 : (m : ℤ) ∣ ((p₀ ^ j + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have h3 := dvd_sub h h1
        rwa [show β i + 1 - (β i - c) = c + 1 by ring] at h3
      exact Int.natCast_dvd_natCast.1 h2

theorem root_mod_simple_of_artifact {R : ℕ}
    (hb : ∀ l ∈ τ.artifactRoots, ∀ x ∈ l, |x| ≤ R)
    (hs : ∀ l ∈ τ.artifactRoots, ∀ i : Fin τ.rank, (∀ k : Fin τ.rank, k ≠ i → l.getD k 0 = 0) →
      l.getD i 0 = 1 ∨ l.getD i 0 = -1)
    (hsmall : ∀ m : ℕ, 3 ≤ m → m ≤ R → ∀ l ∈ τ.artifactRoots, ∀ i : Fin τ.rank,
      (∀ k : Fin τ.rank, k ≠ i → (m : ℤ) ∣ l.getD k 0) →
        (m : ℤ) ∣ l.getD i 0 - 1 ∨ (m : ℤ) ∣ l.getD i 0 + 1)
    {m : ℕ} (hm : 3 ≤ m) (i : Fin τ.rank) (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β)
    (hβl : ∀ l, l ≠ i → (m : ℤ) ∣ β l) : (m : ℤ) ∣ β i - 1 ∨ (m : ℤ) ∣ β i + 1 := by
  have hmem := isRoot_iff_mem_artifactRoots.1 hβ
  have hget : ∀ k : Fin τ.rank, (List.ofFn β).getD k 0 = β k := fun k => by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  by_cases hmR : m ≤ R
  · have h := hsmall m hm hmR _ hmem i (fun k hk => by rw [hget]; exact hβl k hk)
    rwa [hget] at h
  · have hzero : ∀ k, k ≠ i → β k = 0 := by
      intro k hk
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hβl k hk) ?_
      have h1 := hb _ hmem (β k) (List.mem_ofFn.2 ⟨k, rfl⟩)
      rw [Int.natAbs_natCast]
      have h2 : ((β k).natAbs : ℤ) ≤ R := by rw [Int.natCast_natAbs]; exact h1
      omega
    have h := hs _ hmem i fun k hk => by rw [hget]; exact hzero k hk
    rw [hget] at h
    rcases h with h | h
    · left
      rw [h, sub_self]
      exact dvd_zero _
    · right
      rw [h, neg_add_cancel]
      exact dvd_zero _

theorem exists_orderOf_eq_of_dvd_card_add_one (K : Type) [Field K] [Finite K] [Algebra K L]
    [IsAlgClosed L] {N : ℕ} (hN : N ∣ Nat.card K + 1) :
    ∃ ζ : Lˣ, orderOf ζ = N ∧ ζ ^ (Nat.card K + 1) = 1 := by
  classical
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero ((N : ℕ) : L) := ⟨by
    obtain ⟨m, hm⟩ := hN
    intro hN0
    have h1 : ((Nat.card K + 1 : ℕ) : L) = 0 := by rw [hm, Nat.cast_mul, hN0, zero_mul]
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1⟩
  have hNpos : N ≠ 0 := fun h0 => by
    rw [h0] at hN
    exact absurd (Nat.eq_zero_of_zero_dvd hN) (by omega)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  set ζu : Lˣ := (hζ.isUnit hNpos).unit with hζu
  have hζu' : IsPrimitiveRoot ζu N :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  refine ⟨ζu, hζu'.eq_orderOf.symm, ?_⟩
  obtain ⟨m, hm⟩ := hN
  rw [hm, pow_mul, hζu'.pow_eq_one, one_pow]

theorem exists_twisted_rootSL2 [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup τ}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hw : w • β = -β) :
    ∃ P : GL (Fin 2) L,
      (∀ B : SL2 L, canonicalRep (coxeterSystem τ) L w *
          Units.map (entrywiseHom Fr) (rootSL2 τ L β B) *
            (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) ∧
      ∀ ζ : Lˣ, ζ ^ (Nat.card K + 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) := by
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hnM : n ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L w
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hnM (mapsRootLines_canonicalRep w) hβ hw
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hβ
  set X : GL (Fin 2) L := RankThree.Classical.swapGL * diagUnitOne (a * s) with hX
  have hconj : ∀ A, n * rootSL2 τ L β A * n⁻¹ = rootSL2 τ L β (conjSL X A) := fun A => by
    rw [hs A, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]
  obtain ⟨P, hP⟩ := exists_twist_antidiag (K := K) Fr hFr 1 (a * s) X
    (by rw [hX, coe_swapGL_mul_diagUnitOne, Units.val_one])
  have hact : ∀ B : SL2 L, n * Units.map (entrywiseHom Fr) (rootSL2 τ L β B) * n⁻¹ =
      rootSL2 τ L β (conjSL (P * Matrix.GeneralLinearGroup.map Fr P⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B)) := fun B => by
    rw [entrywise_rootSL2_of_field, hconj, hP]
  refine ⟨P, fun B => a1_hS1_of_action Fr hFr P hact B, fun ζ hζ => ?_⟩
  rw [← sl2_twistedFixed_iff Fr (frobenius_fixed_iff Fr hFr) P, hP]
  have hζq' : ζ ^ Nat.card K = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hζ])
  have hq1 : ((ζ : Lˣ) : L) ^ Nat.card K = ((ζ : Lˣ) : L)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, hζq', Units.val_inv_eq_inv_val]
  have hq2 : (((ζ : Lˣ) : L)⁻¹) ^ Nat.card K = ((ζ : Lˣ) : L) := by
    rw [inv_pow, hq1, inv_inv]
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have ha0 : ((a : Lˣ) : L) ≠ 0 := a.ne_zero
  have hs0 : ((s : Lˣ) : L) ≠ 0 := s.ne_zero
  refine Subtype.ext ?_
  rw [coe_conjSL, hX, mul_inv_rev, swapGL_inv, Units.val_mul, Units.val_mul, coe_swapGL,
    coe_diagUnitOne, coe_diagUnitOne_inv, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HSL, RingHom.mapMatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, hFr, hq1, hq2,
      Matrix.map_apply, Matrix.vecMul, dotProduct, hK0]
  field_simp

theorem eq_one_of_model_aut_twisted [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f) [CharP L p₀]
    {Γ : Subgroup (ModGL τ L)} {g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (e : adjointGroup τ K ≃* Γ)
    (he : ∀ h, (e h : ModGL τ L) = g0⁻¹ * baseChangeGL (algebraMap K L) h * g0)
    (P : Fin τ.rank → GL (Fin 2) L)
    (hPΓ : ∀ (i : Fin τ.rank) (A : SL2 K), rootSL2 τ L (Pi.single i 1)
      (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈ Γ)
    (hPH : ∀ (i : Fin τ.rank) (ζ : Lˣ), ζ ^ (Nat.card K + 1) = 1 →
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL (P i)))
    (hfield : ∀ j < f, (∀ i : Fin τ.rank, ∃ b : Label τ, ∀ k : Fin τ.rank,
      ((Nat.card K + 1 : ℕ) : ℤ) ∣
        (∑ l, τ.cartan k l * b.latticeWeight l) - (p₀ ^ j : ℕ) * τ.cartan k i) → j = 0)
    (hcard : entryDegreeBound τ < Nat.card K) (δ : MulAut Γ)
    (hδ : ∀ (i : Fin τ.rank) (A : SL2 K), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩)
    {y : ModGL τ K} {σ : K ≃+* K} (hyC : baseChangeGL (algebraMap K L) y ∈ adjointGroup τ L)
    (hy : ∀ h : adjointGroup τ K, (((e.trans δ).trans e.symm) h : ModGL τ K) =
      y * Units.map (entrywiseHom σ.toRingHom) h * y⁻¹) :
    δ = 1 := by
  classical
  have : ExpChar L p₀ := ExpChar.prime hp₀
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') g0 := ⟨_, rfl⟩
  have hδx : ∀ x : Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) = g0 * (e h : ModGL τ L) * g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K (L := L) (dvd_refl _)
  have hfixT : ∀ k : Fin τ.rank,
      z * torusElt τ L k (ζ ^ (p₀ ^ j)) * z⁻¹ = torusElt τ L k ζ := by
    intro k
    obtain ⟨_, ⟨A, rfl⟩, hA⟩ := hPH k ζ hζq
    have hval : torusElt τ L k ζ = rootSL2 τ L (Pi.single k 1)
        (conjSL (P k) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) := by
      rw [← simpleRootSL2_HSL, ← rootSL2_single, ← hA]
    have h1 := hδx ⟨_, hPΓ k A⟩
    rw [hδ k A] at h1
    change rootSL2 τ L (Pi.single k 1)
        (conjSL (P k) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) =
      z * Units.map (entrywiseHom σ') (rootSL2 τ L (Pi.single k 1)
        (conjSL (P k) (Matrix.SpecialLinearGroup.map (algebraMap K L) A))) * z⁻¹ at h1
    rw [← hval, units_map_entrywiseHom_torusElt] at h1
    have hζσ : Units.map σ'.toMonoidHom ζ = ζ ^ (p₀ ^ j) :=
      Units.ext (by rw [Units.coe_map, hσ', RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        iterateFrobenius_def, Units.val_pow_eq_pow_val])
    rw [hζσ] at h1
    exact h1.symm
  have hj0 : j = 0 := by
    refine hfield j hj fun i => ?_
    obtain ⟨b, hb⟩ := exists_label_of_conj_torusElt z ζ (ζ ^ (p₀ ^ j)) hfixT
      (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩)
    refine ⟨b, fun k => ?_⟩
    have h1 := hb k
    have hsum : ∑ l, τ.cartan k l *
        (Label.latticeWeight (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩ : Label τ)) l =
        τ.cartan k i := sum_cartan_single k i
    rw [hsum, ← zpow_natCast, ← zpow_mul] at h1
    have h2 := (zpow_eq_zpow_iff_modEq.1 h1).symm.dvd
    rw [hζord] at h2
    exact_mod_cast h2
  have hF : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzC : z ∈ adjointGroup τ L := by
    rw [hz, hF]
    exact mul_mem (mul_mem (inv_mem hg0C) hyC) hg0C
  have hz1 : z = 1 := by
    refine eq_one_of_commute_rootRankOneGroup_simple hzC fun i => ?_
    have : Fintype K := Fintype.ofFinite K
    refine commute_rootRankOneGroup_of_twisted (algebraMap K L)
      (by rwa [← Nat.card_eq_fintype_card]) _ (P i) fun A => ?_
    have h1 := hδx ⟨_, hPΓ i A⟩
    rw [hδ i A, hF] at h1
    show z * _ = _ * z
    calc z * rootSL2 τ L (Pi.single i 1)
          (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) =
        z * rootSL2 τ L (Pi.single i 1)
          (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) * z⁻¹ * z := by
          group
      _ = _ * z := by rw [← h1]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hF, hz1, one_mul, inv_one, mul_one]
  rfl

end CFSG.HardMathSupport.Timmesfeld.CrossChar
