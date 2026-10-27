module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

section RootData

theorem e6_root_bound : ∀ l ∈ Tag.E6.artifactRoots, ∀ x ∈ l, |x| ≤ 3 := by decide +kernel

theorem e6_root_simple : ∀ l ∈ Tag.E6.artifactRoots, ∀ i : Fin Tag.E6.rank,
    (∀ k : Fin Tag.E6.rank, k ≠ i → l.getD k 0 = 0) → l.getD i 0 = 1 ∨ l.getD i 0 = -1 := by
  decide +kernel

theorem e6_root_small : ∀ m : ℕ, 3 ≤ m → m ≤ 3 → ∀ l ∈ Tag.E6.artifactRoots,
    ∀ i : Fin Tag.E6.rank, (∀ k : Fin Tag.E6.rank, k ≠ i → (m : ℤ) ∣ l.getD k 0) →
      (m : ℤ) ∣ l.getD i 0 - 1 ∨ (m : ℤ) ∣ l.getD i 0 + 1 := by
  intro m h3 h3'
  obtain rfl : m = 3 := by omega
  decide +kernel

theorem exists_mul_cartan_E6 : ∃ B : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ,
    B * Tag.E6.cartan = ((3 : ℕ) : ℤ) • 1 :=
  ⟨!![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4], by decide +kernel⟩

end RootData

section Arith

theorem eq_zero_of_dvd_pow_sub_one_or_add_one_third {p₀ f j m : ℕ} (hp₀ : p₀.Prime)
    (hj : j < f) (hm : 3 * m = p₀ ^ f + 1) (hq8 : p₀ ^ f ≠ 8)
    (h : m ∣ p₀ ^ j - 1 ∨ m ∣ p₀ ^ j + 1) : j = 0 := by
  by_contra hj0
  set x := p₀ ^ j with hxdef
  set q := p₀ ^ f with hqdef
  have hp2 := hp₀.two_le
  have hx : p₀ ≤ x := Nat.le_self_pow hj0 p₀
  have hqx : q = p₀ ^ (f - j) * x := by
    rw [hqdef, hxdef, ← pow_add, Nat.sub_add_cancel hj.le]
  have hq : p₀ * x ≤ q := by
    rw [hqx]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) p₀)
  have h2x : 2 * x ≤ q := le_trans (Nat.mul_le_mul_right _ hp2) hq
  have hpx : p₀ ∣ x := dvd_pow_self p₀ hj0
  have hpq : p₀ ∣ q := dvd_pow_self p₀ (by omega)
  have hp₀2 : p₀ ∣ 4 → p₀ = 2 := fun h4 => by
    have : p₀ ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).1 (hp₀.dvd_of_dvd_pow this)
  rcases h with h | h
  ·
    have hlt : x - 1 < 2 * m := by omega
    have hpos : 0 < x - 1 := by omega
    have hxm : x - 1 = m := by
      obtain ⟨k, hk⟩ := h
      rcases k with _ | _ | k
      · omega
      · omega
      · have : m * (k + 1 + 1) = m * k + 2 * m := by ring
        omega
    have h3x : 3 * x = q + 4 := by omega
    have h4 : x ∣ 4 := by
      have h1 : x ∣ q := by rw [hqx]; exact dvd_mul_left _ _
      have h2 : x ∣ q + 4 := by rw [← h3x]; exact dvd_mul_left _ _
      exact (Nat.dvd_add_right h1).1 h2
    have h2 : p₀ = 2 := hp₀2 (hpx.trans h4)
    have hx4 : x ≤ 4 := Nat.le_of_dvd (by norm_num) h4
    have hq' : q = 2 ∨ q = 8 := by omega
    rcases hq' with hq2 | hq8'
    ·
      omega
    · exact hq8 hq8'
  · obtain ⟨k, hk⟩ := h
    rcases k with _ | _ | k
    · omega
    ·
      have hq3 : q = 3 * x + 2 := by omega
      have h2 : p₀ ∣ 2 := by
        have h1 : p₀ ∣ 3 * x := Dvd.dvd.mul_left hpx 3
        rw [hq3] at hpq
        exact (Nat.dvd_add_right h1).1 hpq
      have hp₀2' : p₀ = 2 := (Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).1 h2
      subst hp₀2'
      have hj1 : j = 1 := by
        by_contra hj1
        have h4x : 4 ∣ x := by
          rw [hxdef, show j = 2 + (j - 2) by omega, pow_add]
          exact dvd_mul_right _ _
        have h4q : 4 ∣ q := by
          rw [hqdef, show f = 2 + (f - 2) by omega, pow_add]
          exact dvd_mul_right _ _
        omega
      have hx2 : x = 2 := by rw [hxdef, hj1]; norm_num
      exact hq8 (by omega)
    ·
      have : m * (k + 1 + 1) = m * k + 2 * m := by ring
      omega

variable {τ : Tag}

theorem field_exponent_eq_zero_of_arith {p₀ f j : ℕ} (hp₀ : p₀.Prime) {d m : ℕ}
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (hm : m ∣ p₀ ^ f + 1) (hm3 : 2 ≤ m) (hf : 1 ≤ f)
    (hmd : ∀ x : ℤ, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ d * x → (m : ℤ) ∣ x)
    (harith : m ∣ p₀ ^ j - 1 ∨ m ∣ p₀ ^ j + 1 → j = 0)
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
    refine harith ?_
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

theorem field_exponent_eq_zero_E6 {p₀ f j : ℕ} (hp₀ : p₀.Prime)
    (hf : 1 ≤ f) (hj : j < f) (hq4 : 4 ≤ p₀ ^ f) (hq8 : p₀ ^ f ≠ 8) (i : Fin Tag.E6.rank)
    (b : Label Tag.E6)
    (hb : ∀ k : Fin Tag.E6.rank, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣
      (∑ l, Tag.E6.cartan k l * b.latticeWeight l) - (p₀ ^ j : ℕ) * Tag.E6.cartan k i) :
    j = 0 := by
  obtain ⟨B, hB⟩ := exists_mul_cartan_E6
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · omega
  have hq5 : p₀ ^ f ≠ 5 := fun h5 => by
    have h1 : p₀ ∣ 5 := h5 ▸ dvd_pow_self p₀ (by omega)
    have h2 : p₀ = 5 := (Nat.prime_dvd_prime_iff_eq hp₀ (by norm_num)).1 h1
    rw [h2] at h5
    have h3 : (5 : ℕ) ^ f = 5 ^ 1 := by rw [h5, pow_one]
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 5) h3
    omega
  by_cases h3 : 3 ∣ p₀ ^ f + 1
  · obtain ⟨m, hm⟩ := h3
    have hm4 : 3 ≤ m := by omega
    have hm2 : 2 ≤ m := by omega
    have hm' : 3 * m = p₀ ^ f + 1 := by omega
    have hmdvd : m ∣ p₀ ^ f + 1 := ⟨3, by rw [hm]; ring⟩
    have hmd : ∀ x : ℤ, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ ((3 : ℕ) : ℤ) * x → (m : ℤ) ∣ x := by
      intro x hx
      rw [hm] at hx
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, ?_⟩
      have h1 : (3 : ℤ) * x = 3 * (m * c) := by
        push_cast at hc
        rw [hc]
        ring
      exact mul_left_cancel₀ (by norm_num) h1
    exact field_exponent_eq_zero_of_arith hp₀ (d := 3) (m := m) hB hmdvd hm2 hf hmd
      (eq_zero_of_dvd_pow_sub_one_or_add_one_third hp₀ hj hm' hq8) i
      (fun β hβ hβl => root_mod_simple_of_artifact e6_root_bound e6_root_simple e6_root_small
        hm4 i β hβ hβl) b hb
  · have hm2 : p₀ ^ f + 1 ≤ 2 * (p₀ ^ f + 1) := by omega
    have hm3 : 2 ≤ p₀ ^ f + 1 := by omega
    have hm4 : 3 ≤ p₀ ^ f + 1 := by omega
    have hmd : ∀ x : ℤ, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ ((3 : ℕ) : ℤ) * x →
        ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ x := by
      intro x hx
      have hcop : IsCoprime ((p₀ ^ f + 1 : ℕ) : ℤ) ((3 : ℕ) : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
      exact hcop.dvd_of_dvd_mul_left hx
    exact field_exponent_eq_zero hp₀ hj (d := 3) (m := p₀ ^ f + 1) hB (dvd_refl _) hm2 hm3 hmd i
      (fun β hβ hβl => root_mod_simple_of_artifact e6_root_bound e6_root_simple e6_root_small
        hm4 i β hβ hβl) b hb

end Arith

section TwistedSL2

variable {L : Type} [Field L]


theorem exists_twisted_rootSL2_twist [IsAlgClosed L] {t : TwistTag} {K₀ : Type} [Field K₀]
    [Finite K₀] [Algebra K₀ L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K₀)
    {w : WeylGroup t.tag} {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β)
    (hw : w • permLattice t.perm β = -β) :
    ∃ P : GL (Fin 2) L,
      (∀ B : SL2 L, canonicalRep (coxeterSystem t.tag) L w *
          twistHom t L Fr (rootSL2 t.tag L β B) *
            (canonicalRep (coxeterSystem t.tag) L w)⁻¹ = rootSL2 t.tag L β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P)) ∧
      ∀ ζ : Lˣ, ζ ^ (Nat.card K₀ + 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P) := by
  set n := canonicalRep (coxeterSystem t.tag) L w with hn
  have hnM : n ∈ monomialSubgroup t.tag L := canonicalRep_mem_monomialSubgroup L w
  have hwq : weylQuotientHom t.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq_twist hnM hβ
  rw [hwq, hw] at hs
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hβ
  set X : GL (Fin 2) L := RankThree.Classical.swapGL * diagUnitOne (a * s) with hX
  have hconj : ∀ A, n * diagramMap t L * rootSL2 t.tag L β A * (n * diagramMap t L)⁻¹ =
      rootSL2 t.tag L β (conjSL X A) := fun A => by
    rw [hs A, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]
  obtain ⟨P, hP⟩ := exists_twist_antidiag (K := K₀) Fr hFr 1 (a * s) X
    (by rw [hX, coe_swapGL_mul_diagUnitOne, Units.val_one])
  have hact : ∀ B : SL2 L, n * twistHom t L Fr (rootSL2 t.tag L β B) * n⁻¹ =
      rootSL2 t.tag L β (conjSL (P * Matrix.GeneralLinearGroup.map Fr P⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B)) := fun B => by
    have h1 : twistHom t L Fr (rootSL2 t.tag L β B) = diagramMap t L *
        rootSL2 t.tag L β (Matrix.SpecialLinearGroup.map Fr B) * (diagramMap t L)⁻¹ := by
      simp only [twistHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [entrywise_rootSL2_of_field]
    rw [h1, hP, ← hconj]
    group
  refine ⟨P, fun B => a1_hS1_of_action Fr hFr P hact B, fun ζ hζ => ?_⟩
  rw [← sl2_twistedFixed_iff Fr (frobenius_fixed_iff Fr hFr) P, hP]
  have hζq' : ζ ^ Nat.card K₀ = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hζ])
  have hq1 : ((ζ : Lˣ) : L) ^ Nat.card K₀ = ((ζ : Lˣ) : L)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, hζq', Units.val_inv_eq_inv_val]
  have hq2 : (((ζ : Lˣ) : L)⁻¹) ^ Nat.card K₀ = ((ζ : Lˣ) : L) := by
    rw [inv_pow, hq1, inv_inv]
  have hK0 : Nat.card K₀ ≠ 0 := Nat.card_pos.ne'
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

end TwistedSL2

section Rigid

variable {τ : Tag} {L : Type} [Field L]


theorem eq_one_of_fix_twistedSL2 [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    {p₀ F : ℕ} (hp₀ : p₀.Prime) (hF : 1 ≤ F) (hK : Nat.card K = p₀ ^ F) [ExpChar L p₀]
    {K₀ : Type} [Field K₀] [Finite K₀] [Algebra K₀ L]
    (hK₀ : entryDegreeBound τ < Nat.card K₀)
    {C : Subgroup (ModGL τ K)} {Γ : Subgroup (ModGL τ L)} (hΓC : Γ ≤ adjointGroup τ L)
    {g0 : ModGL τ L} (e : C ≃* Γ)
    (he : ∀ h, (e h : ModGL τ L) = g0⁻¹ * baseChangeGL (algebraMap K L) h * g0)
    (hnf : ∀ α : MulAut C, ∃ (y : ModGL τ K) (σ : K ≃+* K), ∀ h : C,
      (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) h * y⁻¹)
    (P : Fin τ.rank → GL (Fin 2) L)
    (hPΓ : ∀ i (A : SL2 K₀), rootSL2 τ L (Pi.single i 1)
      (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) ∈ Γ)
    (hPH : ∀ i (ζ : Lˣ), ζ ^ (Nat.card K₀ + 1) = 1 →
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL (P i)))
    (hfield : ∀ j < F, (∀ i : Fin τ.rank, ∃ b : Label τ, ∀ k : Fin τ.rank,
      ((Nat.card K₀ + 1 : ℕ) : ℤ) ∣
        (∑ l, τ.cartan k l * b.latticeWeight l) - (p₀ ^ j : ℕ) * τ.cartan k i) →
      ∃ u : ModGL τ L, ∀ x ∈ Γ,
        Units.map (entrywiseHom (iterateFrobenius L p₀ j)) x = u * x * u⁻¹)
    (δ : MulAut Γ) (hδ : ∀ i (A : SL2 K₀), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩) : δ = 1 := by
  classical
  obtain ⟨y, σ, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hF hK σ
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
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K₀ (L := L) (dvd_refl _)
  have hfixT : ∀ k : Fin τ.rank,
      z * torusElt τ L k (ζ ^ (p₀ ^ j)) * z⁻¹ = torusElt τ L k ζ := by
    intro k
    obtain ⟨_, ⟨A, rfl⟩, hA⟩ := hPH k ζ hζq
    have hval : rootSL2 τ L (Pi.single k 1)
        (conjSL (P k) (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) =
          torusElt τ L k ζ := by
      rw [hA, rootSL2_single, simpleRootSL2_HSL]
    have hfix := congrArg Subtype.val (hδ k A)
    have h1 := hδx ⟨_, hPΓ k A⟩
    rw [hfix] at h1
    simp only at h1
    rw [hval, units_map_entrywiseHom_torusElt] at h1
    have hζσ : Units.map σ'.toMonoidHom ζ = ζ ^ (p₀ ^ j) :=
      Units.ext (by rw [Units.coe_map, hσ', RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        iterateFrobenius_def, Units.val_pow_eq_pow_val])
    rw [hζσ] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := hfield j hj fun i => by
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
  have hu' : ∀ x ∈ Γ, Units.map (entrywiseHom σ') x = u * x * u⁻¹ := by
    rw [hσ']
    exact hu
  have hδx' : ∀ x : Γ, (δ x : ModGL τ L) = (z * u) * x * (z * u)⁻¹ := by
    intro x
    rw [hδx, hu' x x.2]
    group
  have hcomm : ∀ i (A : SL2 K₀), Commute (z * u) (rootSL2 τ L (Pi.single i 1)
      (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A))) := by
    intro i A
    have h1 := hδx' ⟨_, hPΓ i A⟩
    rw [congrArg Subtype.val (hδ i A)] at h1
    show (z * u) * _ = _ * (z * u)
    calc (z * u) * rootSL2 τ L (Pi.single i 1)
          (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) =
        ((z * u) * rootSL2 τ L (Pi.single i 1)
          (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) * (z * u)⁻¹) *
          (z * u) := by group
      _ = _ := by rw [← h1]
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hQ : ∀ i, ∀ x ∈ rootRankOneGroup τ L (Pi.single i 1), Commute (z * u) x := fun i =>
    commute_rootRankOneGroup_of_twisted (algebraMap K₀ L)
      (by rwa [← Nat.card_eq_fintype_card]) _ (P i) (hcomm i)
  have hxy : ∀ (i : Fin τ.rank) (c : L),
      Commute (z * u) (xUnit τ L i c) ∧ Commute (z * u) (yUnit τ L i c) := fun i c =>
    ⟨hQ i _ ⟨uSL c, by rw [rootSL2_single, simpleRootSL2_uSL]⟩,
      hQ i _ ⟨vSL c, by rw [rootSL2_single, simpleRootSL2_vSL]⟩⟩
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z * u} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hgx : g = xUnit τ L i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hgx]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).1.symm.eq
    · have hgy : g = yUnit τ L i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hgy]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).2.symm.eq
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx', MulAut.one_apply]
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle (hΓC x.2))
  calc (z * u) * (x : ModGL τ L) * (z * u)⁻¹ = (x : ModGL τ L) * (z * u) * (z * u)⁻¹ := by
        rw [h1]
    _ = x := by group

end Rigid

theorem permLattice_E6_perm_perm (x : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x := by
  funext i
  fin_cases i <;> rfl

@[expose] def negLabel {τ : Tag} : Label τ → Label τ
  | .inl l => .inl l
  | .inr β => .inr ⟨-β.1, IsRoot.neg β.2⟩

theorem latticeWeight_negLabel {τ : Tag} (b : Label τ) :
    (negLabel b).latticeWeight = -b.latticeWeight := by
  rcases b with l | β
  · simp [negLabel, Label.latticeWeight]
  · simp [negLabel, Label.latticeWeight]


theorem twisted_field_exponent_E6 {ℓ f j : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hj : j < 2 * f)
    (hq4 : 4 ≤ ℓ ^ f) (hq8 : ℓ ^ f ≠ 8) (b : Label Tag.E6) (i : Fin Tag.E6.rank)
    (hb : ∀ k : Fin Tag.E6.rank, ((ℓ ^ f + 1 : ℕ) : ℤ) ∣
      (∑ l, Tag.E6.cartan k l * b.latticeWeight l) - (ℓ ^ j : ℕ) * Tag.E6.cartan k i) :
    j = 0 ∨ j = f := by
  rcases Nat.lt_or_ge j f with hjf | hjf
  · exact Or.inl (field_exponent_eq_zero_E6 hℓ hf hjf hq4 hq8 i b hb)
  · right
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hjf
    have hj' : j' < f := by omega
    suffices j' = 0 by omega
    refine field_exponent_eq_zero_E6 hℓ hf hj' hq4 hq8 i (negLabel b) fun k => ?_
    have h1 := hb k
    rw [latticeWeight_negLabel]
    have h2 : ((ℓ ^ f + 1 : ℕ) : ℤ) ∣
        ((ℓ ^ f + 1 : ℕ) : ℤ) * ((ℓ ^ j' : ℕ) * Tag.E6.cartan k i) :=
      dvd_mul_right _ _
    have h3 := dvd_add h1 h2
    have h4 := dvd_neg.2 h3
    convert h4 using 1
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, pow_add]
    push_cast
    ring

section TwistedE6Neg

open CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exists_twistedSL2_rigid_twistedE6_neg {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ x, v • x = -permLattice TwistTag.E6.perm x)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hq4 : 4 ≤ ℓ ^ f) (hq8 : ℓ ^ f ≠ 8) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : Algebra K₀ (AlgebraicClosure K)),
      Nat.card K₀ = ℓ ^ f ∧
      ∃ P : Fin TwistTag.E6.tag.rank → GL (Fin 2) (AlgebraicClosure K),
      ∃ hPΓ : ∀ i (A : SL2 K₀), rootSL2 TwistTag.E6.tag (AlgebraicClosure K) (Pi.single i 1)
          (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K₀ (AlgebraicClosure K)) A)) ∈
          (LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0).Γ,
        (∀ i (ζ : (AlgebraicClosure K)ˣ), ζ ^ (Nat.card K₀ + 1) = 1 →
          HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ (AlgebraicClosure K))).range.map
            (conjSL (P i))) ∧
        ∀ δ : MulAut (LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0).Γ,
          (∀ i (A : SL2 K₀), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩) → δ = 1 := by
  classical
  set L := AlgebraicClosure K with hLdef
  set D := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 with hDdef
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : ExpChar L ℓ := ExpChar.prime hℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨-, -, -, -, -, k, -, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K (by rw [hK]; rfl)
  let _ : Algebra k L := ((algebraMap K L).comp k.subtype).toAlgebra
  have : Finite k := Subtype.finite
  have hFrk : ∀ c, Fr c = c ^ Nat.card k := fun c => by rw [hkcard]; exact hFr c
  have hk4 : 4 ≤ Nat.card k := by rw [hkcard]; exact hq4
  have htw : ∀ i : Fin TwistTag.E6.tag.rank, ∃ P : GL (Fin 2) L,
      (∀ B : SL2 L, canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          twistHom TwistTag.E6 L Fr (rootSL2 TwistTag.E6.tag L (Pi.single i 1) B) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ =
              rootSL2 TwistTag.E6.tag L (Pi.single i 1) B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL P)) ∧
      ∀ ζ : Lˣ, ζ ^ (Nat.card k + 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL P) := by
    intro i
    refine exists_twisted_rootSL2_twist (K₀ := k) hFrk (isRoot_single TwistTag.E6.tag i) ?_
    rw [hv, permLattice_E6_perm_perm]
  choose P hPiff hPH using htw
  have hPΓ : ∀ i (A : SL2 k), rootSL2 TwistTag.E6.tag L (Pi.single i 1)
      (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap k L) A)) ∈ D.Γ := by
    intro i A
    obtain ⟨hfin, hqs⟩ := sl2_conj_range_quasisimple (K := k) (L := L) hk4 (P i)
    set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL (P i)) with hS₀
    set S := S₀.map (rootSL2 TwistTag.E6.tag L (Pi.single i 1)) with hS
    have hSp : ⁅S, S⁆ = S := by
      rw [hS, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
    have hSM : S ≤ D.model := by
      rintro _ ⟨B, hB, rfl⟩
      exact ⟨rootSL2_mem_adjointGroup _ B, (hPiff i B).2 hB⟩
    have hmem : rootSL2 TwistTag.E6.tag L (Pi.single i 1)
        (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap k L) A)) ∈ S :=
      ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    rw [← hSp] at hmem
    exact Subgroup.commutator_mono hSM hSM hmem
  refine ⟨k, inferInstance, inferInstance, inferInstance, hkcard, P, hPΓ, hPH, fun δ hδ => ?_⟩
  have hΦ : D.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hΓM : D.Γ ≤ D.model := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact D.model.mul_mem (D.model.mul_mem (D.model.mul_mem ha hb) (D.model.inv_mem ha))
      (D.model.inv_mem hb)
  have hΓC : D.Γ ≤ adjointGroup TwistTag.E6.tag L := fun x hx => (hΓM hx).1
  have hKF : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, hfa, hnf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hdeg : entryDegreeBound TwistTag.E6.tag < Nat.card k := by
    have h2 : entryDegreeBound TwistTag.E6.tag = 2 := rfl
    rw [h2, hkcard]
    omega
  refine eq_one_of_fix_twistedSL2 hℓ (by omega) hKF (K₀ := k) hdeg hΓC
    (twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ) (coe_twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ)
    (fun α => ?_) P hPΓ hPH (fun j hj h => ?_) δ hδ
  ·
    obtain ⟨g, u, δ', hα⟩ := hnf α
    obtain ⟨-, -, -, -, -, hcoe, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
    refine ⟨(g : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u), δ', fun h => ?_⟩
    rw [hα]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, hfa]
    group
  ·
    obtain ⟨b, hb⟩ := h ⟨0, by decide⟩
    rw [hkcard] at hb
    rcases twisted_field_exponent_E6 hℓ hf hj hq4 hq8 b _ hb with hj0 | hjf
    · refine ⟨1, fun x _ => ?_⟩
      rw [hj0, iterateFrobenius_zero, one_mul, inv_one, mul_one]
      exact Units.ext (entrywise_id _)
    ·
      have hFrf : iterateFrobenius L ℓ j = Fr := RingHom.ext fun c => by
        rw [iterateFrobenius_def, hFr, hjf]
      refine ⟨(D.n * diagramMap TwistTag.E6 L)⁻¹, fun x hx => ?_⟩
      rw [hFrf]
      have hxM := (D.mem_model.1 (hΓM hx)).2
      rw [hΦ] at hxM
      simp only [twistHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] at hxM
      calc Units.map (entrywiseHom Fr) x =
          (D.n * diagramMap TwistTag.E6 L)⁻¹ *
            (D.n * (diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) x *
              (diagramMap TwistTag.E6 L)⁻¹) * D.n⁻¹) * (D.n * diagramMap TwistTag.E6 L) := by
            group
        _ = _ := by rw [hxM, inv_inv]

end TwistedE6Neg

end CFSG.HardMathSupport.Timmesfeld.CrossChar
