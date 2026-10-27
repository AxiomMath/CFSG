module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Lattice CFSG.RankThree.Classical CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

private theorem sl2_map_HSL {K₀ L : Type} [Field K₀] [Field L] (ι : K₀ →+* L) (t : K₀ˣ) :
    Matrix.SpecialLinearGroup.map ι (HSL t) = HSL (Units.map ι.toMonoidHom t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, RingHom.mapMatrix_apply]

section Big

theorem mem_bigComponentSet_of_sl2 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hp2 : p ≠ 2) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) {K₀ : Type} [Field K₀] [Finite K₀] [Algebra K₀ L]
    (hK₀ : 4 ≤ Nat.card K₀) (i : Fin τ.rank) (P : GL (Fin 2) L)
    (hPΓ : ∀ A : SL2 K₀, rootSL2 τ L (Pi.single i 1)
      (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) ∈ S.Γ)
    (hζ : ∃ ζ : Lˣ, orderOf ζ = p ∧
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P))
    (A : SL2 K₀) :
    rootSL2 τ L (Pi.single i 1) (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) ∈
      bigComponentSet S D₁ := by
  classical
  have hp := S.hp
  have := S.finite_Γ
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  have hD₁p : ∀ x ∈ D₁, x ^ p = 1 := fun x hx => S.E_exp x (hD₁E hx)
  have hcard : p < Nat.card D₁ := by
    rw [hD₁c]
    have := hp.one_lt
    nlinarith
  obtain ⟨a, haD, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite hp hD₁T hD₁p hcard (Pi.single i 1)
  have hαk : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single τ i, hχ⟩
  set i₀ : KernelComponent (rootCharHom a) := ⟦⟨_, hαk⟩⟧ with hi₀
  have hαi : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i₀ := ⟨hαk, rfl⟩
  have hnegi := (isRootComponent_componentRoots (χ := rootCharHom a) i₀).neg_mem _ hαi
  obtain ⟨hfin, hqs⟩ := sl2_conj_range_quasisimple (K := K₀) (L := L) hK₀ P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P) with hS₀
  set X := S₀.map (rootSL2 τ L (Pi.single i 1)) with hX
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hXΓ : X ≤ S.Γ := by
    rintro _ ⟨B, ⟨_, ⟨A', rfl⟩, rfl⟩, rfl⟩
    exact hPΓ A'
  have hXspan : X ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i₀) := by
    rintro _ ⟨B, -, rfl⟩
    refine (?_ : rootSpan τ L {Pi.single i 1, -Pi.single i 1} ≤ _)
      (rootSL2_mem_rootSpan_pair (isRoot_single τ i) B)
    refine iSup₂_le fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ rationalRoots S.ρ
      (rootCharHom a) i₀) => rootSubgroup τ L δ) γ ?_ le_rfl
    rcases hγ with rfl | hγ
    · exact ⟨0, _, hαi, rfl⟩
    · rw [Set.mem_singleton_iff.1 hγ]
      exact ⟨0, _, hnegi, rfl⟩
  have hXR : X ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i₀ := by
    rw [← hXp]
    exact Subgroup.commutator_mono (le_inf hXspan hXΓ) (le_inf hXspan hXΓ)
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i₀ ≤ S.Γ :=
    (commutator_self_le_self _).trans inf_le_right
  have : Finite (rationalComponent S.ρ S.Γ (rootCharHom a) i₀) :=
    Finite.of_injective (Subgroup.inclusion hRΓ) (Subgroup.inclusion_injective hRΓ)
  obtain ⟨ζ, hζord, _, ⟨A', rfl⟩, hA'⟩ := hζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hζord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hp.two_le
    exact hp2 (by omega)
  have hζX : torusElt τ L i ζ ∈ X := ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, by
    rw [hA', rootSL2_single, simpleRootSL2_HSL]⟩
  have hord : orderOf (torusElt τ L i ζ) = p := by
    have h1 := orderOf_canonicalRep_conj_torusElt (K := L) hp (1 : WeylGroup τ) i hζord hζ2
    rwa [canonicalRep_one, one_mul, inv_one, mul_one] at h1
  have hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i₀)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    have h1 := orderOf_dvd_natCard (⟨_, hXR hζX⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₀))
    rwa [Subgroup.orderOf_mk, hord] at h1
  exact ⟨a, haD, ha1, i₀, hbig, hXR ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩⟩

end Big

section Gamma

theorem commutator_adjointGroup_exc_eq_top {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] :
    commutator ↥(adjointGroup τ K) = ⊤ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact commutator_adjointGroup_F4_eq_top K
  · exact commutator_adjointGroup_E6_eq_top K
  · exact commutator_adjointGroup_E7_eq_top K
  · exact commutator_adjointGroup_E8_eq_top K

theorem langDescent_ofFrobenius {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (w : WeylGroup τ) (K : Type) [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    LangDescent (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype) := by
  have hperf := commutator_adjointGroup_exc_eq_top hτ K
  rcases hτ with h | h | h | h
  · exact langDescent_exact (Or.inr h) hFr _ rfl hperf
  · exact langDescent_untw 3 (Or.inl ⟨h, rfl⟩) hFr _ rfl Nat.prime_seven (by norm_num) hperf
  · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr _ rfl Nat.prime_seven (by norm_num)
      hperf
  · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr _ rfl Nat.prime_seven (by norm_num)
      hperf

theorem Γ_ofFrobenius_one_eq {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) 1) :
    (LangDatum.ofFrobenius Fr (Nat.card K) hFr 1 hg0C hg0).Γ =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  set D := LangDatum.ofFrobenius Fr (Nat.card K) hFr 1 hg0C hg0 with hD
  have hd := langDescent_ofFrobenius hτ 1 K hFr hg0C hg0
  have hmodel : D.model = D.fix := by
    ext y
    rw [LangDatum.mem_model, LangDatum.mem_fix]
    have hn : D.n = 1 := canonicalRep_one (coxeterSystem τ) (AlgebraicClosure K)
    rw [hn, one_mul, inv_one, mul_one]
  rw [LangDatum.Γ, hmodel, hd.derived, MonoidHom.range_comp, Subgroup.range_subtype]

end Gamma

section Split

theorem setupRigid_ofFrobenius_one {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) 1)
    {p : ℕ} (hp2 : p ≠ 2) (hpq1 : p ∣ Nat.card K - 1) [IsAlgClosed (AlgebraicClosure K)]
    (S : LangSetup τ (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr 1 hg0C hg0) : SetupRigid S := by
  classical
  set L := AlgebraicClosure K
  have hp := S.hp
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpq1
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    omega
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : Kˣ, orderOf ζ₀ = p := exists_prime_orderOf_dvd_card p (by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
    exact hpq1)
  have hζ : ∃ ζ : Lˣ, orderOf ζ = p ∧
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL 1) := by
    refine ⟨Units.map (algebraMap K L).toMonoidHom ζ₀, ?_, ?_⟩
    · rw [orderOf_injective _ (Units.map_injective (algebraMap K L).injective) ζ₀, hζ₀]
    · exact ⟨Matrix.SpecialLinearGroup.map (algebraMap K L) (HSL ζ₀), ⟨HSL ζ₀, rfl⟩, by
        rw [conjSL_one, sl2_map_HSL]⟩
  have hΓ : S.Γ = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [show S.Γ = S.D.Γ from rfl, hSD]
    exact Γ_ofFrobenius_one_eq hτ K hFr hg0C hg0
  have hPΓ : ∀ (i : Fin τ.rank) (A : SL2 K), rootSL2 τ L (Pi.single i 1)
      (conjSL 1 (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈ S.Γ := by
    intro i A
    rw [conjSL_one, rootSL2_single, hΓ, map_baseChangeGL_adjointGroup]
    have hA : A ∈ Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top A
    induction hA using Subgroup.closure_induction with
    | mem B hB =>
      rcases hB with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · change simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) (uSL t)) ∈ _
        rw [sl2_map_uSL, simpleRootSL2_uSL]
        exact Subgroup.subset_closure ⟨i, t, Or.inl rfl⟩
      · change simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) (vSL t)) ∈ _
        rw [sl2_map_vSL, simpleRootSL2_vSL]
        exact Subgroup.subset_closure ⟨i, t, Or.inr rfl⟩
    | one => rw [map_one, map_one]; exact one_mem _
    | mul B C _ _ hB hC => rw [map_mul, map_mul]; exact mul_mem hB hC
    | inv B _ hB => rw [map_inv, map_inv]; exact inv_mem hB
  intro D₁ hD₁E hD₁c δ _ _ hfix
  have hbig : ∀ (i : Fin τ.rank) (A : SL2 K), rootSL2 τ L (Pi.single i 1)
      (conjSL 1 (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) ∈ bigComponentSet S D₁ :=
    fun i A => mem_bigComponentSet_of_sl2 S hp2 hD₁E hD₁c hK4 i 1 (hPΓ i) hζ A
  have hgen : S.Γ ≤ Subgroup.closure (bigComponentSet S D₁) := by
    rw [hΓ, map_baseChangeGL_adjointGroup]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · have h := hbig i (uSL c)
      rwa [conjSL_one, sl2_map_uSL, rootSL2_single, simpleRootSL2_uSL] at h
    · have h := hbig i (vSL c)
      rwa [conjSL_one, sl2_map_vSL, rootSL2_single, simpleRootSL2_vSL] at h
  have hX : bigComponentSet S D₁ ⊆ S.Γ := by
    rintro x ⟨a, -, -, i, -, hx⟩
    exact (inf_le_right : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.Γ)
      (commutator_self_le_self _ hx)
  have hcl := closure_eq_top_of_le_closure hX hgen
  rw [← fixSub_eq_top_iff, eq_top_iff, ← hcl, Subgroup.closure_le]
  intro x hx
  exact hfix x hx

end Split

section Vacuous

theorem langTorusPlaneBalance_one_of_not_dvd {τ : Tag} {p : ℕ} (hp : p.Prime) {Q : ℕ → Prop}
    (hQ : ∀ q, Q q → ¬ p ∣ q - 1) : LangTorusPlaneBalance τ 1 p Q := by
  classical
  intro K _ _ hQK Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  exfalso
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 (hQ _ hQK)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hbot : ∀ x ∈ D₀, x = 1 := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := htor x hx
    obtain ⟨htT, htF⟩ := mem_twistedTorusOf.1 ht
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom htT
    have htp : rootDiagUnitHom τ (AlgebraicClosure K) a ^ p = 1 := by
      have h1 : (MulAut.conj g0).toMonoidHom (rootDiagUnitHom τ (AlgebraicClosure K) a ^ p) =
          (MulAut.conj g0).toMonoidHom 1 := by
        rw [map_pow, hte, map_one, ← map_pow, ← Subgroup.coe_pow, hpow x hx, Subgroup.coe_one,
          map_one]
      exact (MulAut.conj g0).injective h1
    have htF' : rootDiagUnit τ (fun i => Units.map Fr.toMonoidHom (a i)) = rootDiagUnit τ a := by
      have h := htF
      change canonicalRep (coxeterSystem τ) (AlgebraicClosure K) 1 *
        Units.map (entrywiseHom Fr) (rootDiagUnit τ a) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) 1)⁻¹ = rootDiagUnit τ a at h
      rwa [canonicalRep_one, one_mul, inv_one, mul_one, units_map_entrywiseHom_rootDiagUnit] at h
    have hpa : a ^ p = 1 := rootDiagUnit_injective (by
      change rootDiagUnitHom τ (AlgebraicClosure K) (a ^ p) = rootDiagUnitHom τ _ 1
      rw [map_pow, htp, map_one])
    have hFa := rootDiagUnit_injective htF'
    have ha1 : a = 1 := by
      funext i
      have hpi : a i ^ p = 1 := by simpa using congrFun hpa i
      have hFi : Units.map Fr.toMonoidHom (a i) = a i := congrFun hFa i
      have hqi : a i ^ (Nat.card K - 1) = 1 := by
        have h1 : a i ^ (Nat.card K - 1) * a i = 1 * a i := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
          refine Units.ext ?_
          rw [Units.val_pow_eq_pow_val, ← hFr]
          exact congrArg Units.val hFi
        exact mul_right_cancel h1
      have := pow_gcd_eq_one.2 ⟨hpi, hqi⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    rw [ha1, map_one, map_one] at hte
    have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) 1 := by
      rw [map_one, ← hte]
    exact Subtype.ext (baseChangeGL_injective _ h2)
  have hD₀ : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hbot
  rw [hD₀, Subgroup.card_bot] at hcard
  exact absurd hcard (by have := hp.one_lt; omega)

end Vacuous

section Balance

theorem langTorusPlaneBalance_one {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : ℕ → Prop) (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    LangTorusPlaneBalance τ 1 p Q := by
  have hdvd : LangTorusPlaneBalance τ 1 p fun q => Q q ∧ p ∣ q - 1 :=
    langTorusPlaneBalance_of_setupRigidAt hτ (fun K _ _ => commutator_adjointGroup_exc_eq_top hτ K)
      1 hp (fun q hq2 hQq => by
        have h1 := Nat.le_of_dvd (by omega) hQq.2
        have h3 : 3 ≤ p := by have := hp.two_le; omega
        refine ⟨fun h => ?_, Or.inr (by omega)⟩
        have h2 := Nat.dvd_sub h hQq.2
        rw [Nat.sub_sub_self (by omega)] at h2
        exact hp.one_lt.ne' (Nat.dvd_one.1 h2))
      (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => by
        have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
        exact setupRigid_ofFrobenius_one hτ hFr hg0C hg0 hp2 hQK.2 S hSD)
      hsub hin hsu htw hex
  have hnd : LangTorusPlaneBalance τ 1 p fun q => Q q ∧ ¬ p ∣ q - 1 :=
    langTorusPlaneBalance_one_of_not_dvd hp fun _ h => h.2
  intro K _ _ hQK
  by_cases h : p ∣ Nat.card K - 1
  · exact hdvd K ⟨hQK, h⟩
  · exact hnd K ⟨hQK, h⟩

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
