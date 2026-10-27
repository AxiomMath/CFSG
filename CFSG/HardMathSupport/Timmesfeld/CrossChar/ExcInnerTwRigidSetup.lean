module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidF4Even
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

section Descent

variable (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]

theorem le_langModel_of_perfect {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {n g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) {P : Subgroup (ModGL τ L)} [Finite P]
    (hPM : P ≤ twModel n Fr) (hPp : ⁅P, P⁆ = P) : P ≤ langModel τ K L g0 := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set X := P.map (MulAut.conj g0).toMonoidHom with hX
  have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap P)
    ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective P)
  have hXF : X ≤ adjointGroup τ L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono hPM
  have hXC : X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rcases hτ with rfl | rfl | rfl
    · rw [← (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1]
      exact hXF
    · have hdesc := finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr
        hFr X (fun x hx => (hXF hx).1) (fun x hx => (hXF hx).2)
      exact hdesc.2.2 X le_rfl (by rw [hX, ← Subgroup.map_commutator, hPp])
    · have hdesc := finite_fixed_subgroup_rational_perfect 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr
        hFr X (fun x hx => (hXF hx).1) (fun x hx => (hXF hx).2)
      exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 hdesc.1)
  intro x hx
  refine ⟨(MulAut.conj g0).toMonoidHom x, hXC ⟨x, hx, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Descent

section Field

theorem field_exponent_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {p₀ f : ℕ}
    (hp₀ : p₀.Prime) (hf : 1 ≤ f) {q : ℕ} (hq : q = p₀ ^ f) (hq4 : 4 ≤ q) :
    ∀ j < f, (∀ i : Fin τ.rank, ∃ b : Label τ, ∀ k : Fin τ.rank,
      ((q + 1 : ℕ) : ℤ) ∣
        (∑ l, τ.cartan k l * b.latticeWeight l) - (p₀ ^ j : ℕ) * τ.cartan k i) → j = 0 := by
  intro j hj h
  have hq1 := Nat.one_lt_pow (n := f) (by omega) hp₀.one_lt
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨B, hB⟩ := exists_mul_cartan_F4
    obtain ⟨b, hb⟩ := h ⟨0, by decide⟩
    rw [hq] at hb
    exact field_exponent_eq_zero hp₀ hj (d := 1) (m := p₀ ^ f + 1) (B := B)
      (by rw [hB, Nat.cast_one, one_smul]) (dvd_refl _) (by omega) (by omega)
      (fun x hx => by rwa [Nat.cast_one, one_mul] at hx) ⟨0, by decide⟩
      (fun β hβ hβl => root_mod_simple_of_artifact f4_root_bound f4_root_simple f4_root_small
        (by omega) _ β hβ hβl) b hb
  · obtain ⟨B, hB⟩ := exists_mul_cartan_E7
    obtain ⟨b, hb⟩ := h ⟨0, by decide⟩
    rw [hq] at hb
    obtain ⟨m, hm, hm2, hmd, hm3⟩ : ∃ m : ℕ, m ∣ p₀ ^ f + 1 ∧ p₀ ^ f + 1 ≤ 2 * m ∧
        (∀ x : ℤ, ((p₀ ^ f + 1 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * x → (m : ℤ) ∣ x) ∧ 3 ≤ m := by
      rcases Nat.even_or_odd (p₀ ^ f + 1) with ⟨r, hr⟩ | hodd
      · refine ⟨r, ⟨2, by omega⟩, by omega, fun x hx => ?_, by omega⟩
        have h2 : ((p₀ ^ f + 1 : ℕ) : ℤ) = 2 * r := by rw [hr]; push_cast; ring
        rw [h2, Nat.cast_ofNat] at hx
        exact (mul_dvd_mul_iff_left two_ne_zero).1 hx
      · refine ⟨p₀ ^ f + 1, dvd_refl _, by omega, fun x hx => ?_, by omega⟩
        have hcop : IsCoprime ((p₀ ^ f + 1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) :=
          Nat.isCoprime_iff_coprime.2 (Nat.coprime_two_right.2 hodd)
        exact hcop.dvd_of_dvd_mul_left hx
    exact field_exponent_eq_zero hp₀ hj (d := 2) (m := m) (B := B) hB hm hm2 (by omega) hmd
      ⟨0, by decide⟩ (fun β hβ hβl => root_mod_simple_of_artifact e7_root_bound e7_root_simple
        e7_root_small hm3 _ β hβ hβl) b hb
  · obtain ⟨B, hB⟩ := exists_mul_cartan_E8
    obtain ⟨b, hb⟩ := h ⟨0, by decide⟩
    rw [hq] at hb
    exact field_exponent_eq_zero hp₀ hj (d := 1) (m := p₀ ^ f + 1) (B := B)
      (by rw [hB, Nat.cast_one, one_smul]) (dvd_refl _) (by omega) (by omega)
      (fun x hx => by rwa [Nat.cast_one, one_mul] at hx) ⟨0, by decide⟩
      (fun β hβ hβl => root_mod_simple_of_artifact e8_root_bound e8_root_simple e8_root_small
        (by omega) _ β hβ hβl) b hb

end Field

section Rigid

theorem exists_twistedSL2_rigid_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) (K : Type) [Field K] [Finite K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hK4 : 4 ≤ Nat.card K) {g0 : ModGL τ L}
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    {Γ : Subgroup (ModGL τ L)} (hΓ : Γ = langModel τ K L g0) :
    ∃ (P : Fin τ.rank → GL (Fin 2) L) (hPΓ : ∀ (i : Fin τ.rank) (A : SL2 K),
      rootSL2 τ L (Pi.single i 1)
        (conjSL (P i) (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈ Γ),
      (∀ (i : Fin τ.rank) (ζ : Lˣ), ζ ^ (Nat.card K + 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL (P i))) ∧
      ∀ δ : MulAut Γ, (∀ (i : Fin τ.rank) (A : SL2 K), δ ⟨_, hPΓ i A⟩ = ⟨_, hPΓ i A⟩) →
        δ = 1 := by
  classical
  subst hΓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  have hsl : ∀ i : Fin τ.rank, ∃ P : GL (Fin 2) L,
      (∀ A : SL2 K, rootSL2 τ L (Pi.single i 1)
          (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈
            langModel τ K L g0) ∧
        ∀ ζ : Lˣ, ζ ^ (Nat.card K + 1) = 1 →
          HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) := by
    intro i
    obtain ⟨P, hiff, hHSL⟩ := exists_twisted_rootSL2 (K := K) hFr (isRoot_single τ i) (hw _)
    refine ⟨P, fun A => ?_, hHSL⟩
    obtain ⟨hfin, hqs⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 P
    set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)
    set S := S₀.map (rootSL2 τ L (Pi.single i 1)) with hS
    have : Finite S := Finite.of_surjective ((rootSL2 τ L (Pi.single i 1)).subgroupMap S₀)
      ((rootSL2 τ L (Pi.single i 1)).subgroupMap_surjective S₀)
    have hSp : ⁅S, S⁆ = S := by
      rw [hS, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
    have hSM : S ≤ twModel (canonicalRep (coxeterSystem τ) L w) Fr := by
      rintro _ ⟨B, hB, rfl⟩
      exact ⟨rootSL2_mem_adjointGroup _ B, (hiff B).2 hB⟩
    exact le_langModel_of_perfect K L hτ hFr hg0C hg0 hSM hSp ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
  choose P hPΓ hPH using hsl
  refine ⟨P, hPΓ, hPH, fun δ hδ => ?_⟩
  set e := langModelMulEquiv τ K L g0 with he_def
  have he : ∀ h, (e h : ModGL τ L) = g0⁻¹ * baseChangeGL (algebraMap K L) h * g0 :=
    fun h => by rw [coe_langModelMulEquiv, inv_inv]
  have hfield := field_exponent_neg hτ hp₀ hf hK hK4
  have hcard : entryDegreeBound τ < Nat.card K := by
    rcases hτ with rfl | rfl | rfl <;> simp [entryDegreeBound] <;> omega
  rcases hτ with rfl | rfl | rfl
  ·
    rcases Nat.even_or_odd (Nat.card K) with hev | hodd
    · exact eq_one_of_fix_twistedSL2_F4_even K L hFr hev hK4 hg0C P hPΓ hPH δ hδ
    · have hp2 : p₀ ≠ 2 := by
        rintro rfl
        rw [hK] at hodd
        exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' (by omega)).2 even_two)
      obtain ⟨⟨g, σ⟩, hα, -⟩ :=
        (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp₀ hp2 hf K hK Tag.F4
          (Or.inl rfl)).1 ((e.trans δ).trans e.symm)
      exact eq_one_of_model_aut_twisted hp₀ hf hK hg0C e he P hPΓ hPH hfield hcard δ hδ
        (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2) hα
  ·
    obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form Tag.E7
      (Or.inr (Or.inl rfl)) K).2.2 ((e.trans δ).trans e.symm)
    refine eq_one_of_model_aut_twisted hp₀ hf hK hg0C e he P hPΓ hPH hfield hcard δ hδ
      (y := (g : ModGL Tag.E7 K) * rootDiagUnit Tag.E7 a) (σ := σ) ?_ fun h => ?_
    · rw [map_mul, baseChangeGL_rootDiagUnit]
      exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
        (CFSG.RankThree.PartOne.K133H.torusGroup_le_adjointGroup'
          (rootDiagUnit_mem_torusGroup_E7 _))
    · rw [hα h]
      have hQ : exactQ Tag.E7 K ε = 1 := rfl
      rw [hQ, mul_one, inv_one, mul_one, mul_inv_rev]
      group
  ·
    obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form Tag.E8
      (Or.inr (Or.inr rfl)) K).2.2 ((e.trans δ).trans e.symm)
    refine eq_one_of_model_aut_twisted hp₀ hf hK hg0C e he P hPΓ hPH hfield hcard δ hδ
      (y := (g : ModGL Tag.E8 K) * rootDiagUnit Tag.E8 a) (σ := σ) ?_ fun h => ?_
    · rw [map_mul, baseChangeGL_rootDiagUnit]
      exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
        (CFSG.RankThree.PartOne.K133H.torusGroup_le_adjointGroup'
          (rootDiagUnit_mem_torusGroup_E8 _))
    · rw [hα h]
      have hQ : exactQ Tag.E8 K ε = 1 := rfl
      rw [hQ, mul_one, inv_one, mul_one, mul_inv_rev]
      group

end Rigid

section Setup

theorem commutator_adjointGroup_neg_eq_top {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] : commutator ↥(adjointGroup τ K) = ⊤ := by
  rcases hτ with rfl | rfl | rfl
  · exact commutator_adjointGroup_F4_eq_top K
  · exact commutator_adjointGroup_E7_eq_top K
  · exact commutator_adjointGroup_E8_eq_top K

theorem Γ_ofFrobenius_eq_langModel {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ)
    (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ =
      langModel τ K (AlgebraicClosure K) g0 := by
  set D := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 with hD
  have hperf := commutator_adjointGroup_neg_eq_top hτ K
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype) := by
    rcases hτ with h | h | h
    · exact langDescent_exact (Or.inr h) hFr D rfl hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) hperf
  rw [hd.Γ_eq, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem setupRigid_ofFrobenius_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp2 : p ≠ 2) (hpq1 : p ∣ Nat.card K + 1)
    [IsAlgClosed (AlgebraicClosure K)] (S : LangSetup τ (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) : SetupRigid S := by
  obtain ⟨D, ρ, frob, E, hp, hq, hqpow, hpq, hfin, hEle, hEexp, hEall⟩ := S
  simp only at hSD
  subst hSD
  intro D₁ hD₁E hD₁c δ _ _ hfixX
  obtain ⟨P, hPΓ, hPH, hrig⟩ := exists_twistedSL2_rigid_neg hτ hw K (AlgebraicClosure K) hFr hK4
    hg0C hg0 (Γ_ofFrobenius_eq_langModel hτ w K hFr hg0C hg0)
  refine hrig δ fun i A => hfixX _ ?_
  exact mem_bigComponentSet_of_twistedSL2 _ hp2 hD₁E hD₁c hK4 hpq1 i (P i) (hPΓ i) (hPH i) A

theorem langTorusPlaneBalance_neg_of_components {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q : ℕ → Prop}
    (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ p ∣ q + 1 ∧ 4 ≤ q)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) : LangTorusPlaneBalance τ w p Q := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
  refine langTorusPlaneBalance_of_setupRigidAt hτ' (fun K _ _ => commutator_adjointGroup_neg_eq_top
    hτ K) w hp (fun q hq2 hQq => ⟨(hQ q hq2 hQq).1, Or.inr (hQ q hq2 hQq).2.2⟩)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => ?_) hsub hin hsu htw hex
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨-, hpq1, hK4⟩ := hQ _ Finite.one_lt_card hQK
  exact setupRigid_ofFrobenius_neg hτ hw hFr hg0C hg0 hK4 hp2 hpq1 S hSD

end Setup

end CFSG.HardMathSupport.Timmesfeld.CrossChar
