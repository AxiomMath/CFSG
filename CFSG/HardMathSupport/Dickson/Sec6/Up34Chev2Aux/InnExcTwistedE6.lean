module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedKinds
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Lane

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)


namespace Up34Chev2

section Arith

theorem not_dvd_fixed {f : ℕ} (hf : 1 ≤ f) :
    ¬ (2 ^ f * ((2 ^ f) ^ 2 - 1) * (2 ^ f * ((2 ^ f) ^ 2 - 1)) *
      (2 ^ f * ((2 ^ f) ^ 2 - 1)) ∣ 20160) := by
  intro h
  rcases Nat.lt_or_ge f 2 with h1 | h1
  · obtain rfl : f = 1 := by omega
    revert h
    decide
  · have hQ : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h1
    generalize 2 ^ f = Q at hQ h
    have hle := Nat.le_of_dvd (by norm_num) h
    have hb : 60 ≤ Q * (Q ^ 2 - 1) := by
      have h15 : 15 ≤ Q ^ 2 - 1 := by
        have : 16 ≤ Q ^ 2 := by nlinarith
        omega
      calc 60 = 4 * 15 := by norm_num
        _ ≤ Q * (Q ^ 2 - 1) := Nat.mul_le_mul hQ h15
    have := Nat.mul_le_mul (Nat.mul_le_mul hb hb) hb
    omega

end Arith

section Fixed

variable {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem bad3_fixed_in (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {βa βb βk : Fin τ.rank → ℤ} (ha : IsRoot τ βa) (hb : IsRoot τ βb) (hk : IsRoot τ βk)
    (hab : iform βa βb = 0) (hak : iform βa βk = 0) (hbk : iform βb βk = 0)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (C : Subgroup (ModGL τ L))
    (hCa : (slHom βa (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C)
    (hCb : (slHom βb (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C)
    (hCk : (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    Bad3 (C ⊓ fixSub F₁) := by
  classical
  have hfix : ∀ {β : Fin τ.rank → ℤ}, (∀ A : SL2 L, F₁ (rootSL2 τ L β A) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) →
      ∀ A, F₁ (slHom β (RingHom.id L) (frobeniusFixedField L 2 f) A) =
        slHom β (RingHom.id L) (frobeniusFixedField L 2 f) A := by
    intro β hF A
    rw [F_slHom _ hF, RingHom.comp_id, slHom_frob_one]
  have hinj : ∀ β : Fin τ.rank → ℤ,
      Function.Injective (slHom (τ := τ) β (RingHom.id L) (frobeniusFixedField L 2 f)) :=
    fun β => slHom_injective _ _ _
  have hcl : ∀ β : Fin τ.rank → ℤ,
      ∀ a ∈ (slHom (τ := τ) β (RingHom.id L) (frobeniusFixedField L 2 f)).range,
        (∀ b ∈ (slHom (τ := τ) β (RingHom.id L) (frobeniusFixedField L 2 f)).range,
          a * b = b * a) → a = 1 :=
    fun β => centerless_range _ (hinj β) fun A hA => sl2_eq_one_of_forall_comm hA
  refine ⟨(slHom βa (RingHom.id L) (frobeniusFixedField L 2 f)).range,
    (slHom βb (RingHom.id L) (frobeniusFixedField L 2 f)).range,
    (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)).range, ?_, ?_, ?_, ?_, ?_, ?_,
    hcl βa, hcl βb, hcl βk, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCa ⟨A, rfl⟩, mem_fixSub.2 (hfix hFa A)⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCb ⟨A, rfl⟩, mem_fixSub.2 (hfix hFb A)⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCk ⟨A, rfl⟩, mem_fixSub.2 (hfix hFk A)⟩
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact (slHom_commute_gen hτ ha hb hab _ _ _ _ A B).eq
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact (slHom_commute_gen hτ ha hk hak _ _ _ _ A B).eq
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact (slHom_commute_gen hτ hb hk hbk _ _ _ _ A B).eq
  · rw [card_range_of_injective _ (hinj βa), card_range_of_injective _ (hinj βb),
      card_range_of_injective _ (hinj βk), card_sl2_frobFixed (by omega : 0 < f)]
    exact not_dvd_fixed hf

end Fixed

section Std6

variable
  {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem subsystemGroup_mono {K : Type} [Field K] {A B : Set (Fin τ.rank)} (h : A ⊆ B) :
    subsystemGroup τ K A ≤ subsystemGroup τ K B :=
  Subgroup.closure_mono fun _ ⟨i, hi, c, hc⟩ => ⟨i, h hi, c, hc⟩

theorem d4Set_subset_e6Set : d4Set τ ⊆ e6Set τ := fun i hi => by
  have h := hi.2
  have : Tag.E6.rank = 6 := rfl
  change i.val < Tag.E6.rank
  omega

theorem slHom_single_range_le {j : Fin τ.rank} {J : Set (Fin τ.rank)} (hj : j ∈ J)
    (φ : L →+* L) (K : Subfield L) :
    (slHom (Pi.single j 1 : Fin τ.rank → ℤ) φ K).range ≤ subsystemGroup τ L J := by
  have hle : (slHom (Pi.single j 1 : Fin τ.rank → ℤ) φ K).range ≤
      (rootSL2 τ L (Pi.single j 1 : Fin τ.rank → ℤ)).range := by
    rintro _ ⟨A, rfl⟩
    exact ⟨_, rfl⟩
  refine hle.trans ?_
  have h : rootSL2 τ L (Pi.single j 1 : Fin τ.rank → ℤ) = simpleRootSL2 τ L j :=
    MonoidHom.ext (rootSL2_single_apply' j)
  rw [h, range_simpleRootSL2, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_subsystemGroup hj c
  · exact yUnit_mem_subsystemGroup hj c

theorem bad3_layer_fixed (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {n₁ : ModGL τ L}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L,
      n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L ((1 : Equiv.Perm (Fin τ.rank)) j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L ((1 : Equiv.Perm (Fin τ.rank)) j) c)
    {a b k : Fin τ.rank} (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ) (hk : k ∈ d4Set τ)
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0) :
    Bad3 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hB := bad3_fixed_in hτ hf (isRoot_single τ a) (isRoot_single τ b) (isRoot_single τ k)
    (by rw [iform_single_cartan hτ, hab]) (by rw [iform_single_cartan hτ, hak])
    (by rw [iform_single_cartan hτ, hbk]) (F₁ := stdF n₁ f)
    (stdF_a (π := 1) hgen ha rfl) (stdF_a (π := 1) hgen hb rfl) (stdF_a (π := 1) hgen hk rfl)
    (subsystemGroup τ L (d4Set τ)) (slHom_single_range_le ha _ _) (slHom_single_range_le hb _ _)
    (slHom_single_range_le hk _ _)
  exact hB.mono (inf_le_inf_left _ (fixSub_stdF n₁ f).le)

variable [M27Ok τ] [E6Sub τ]

theorem bad3_stdLayer6 {f : ℕ} (hf : 1 ≤ f) {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hstd : StdTwist6 n₁ π) :
    Bad3 (subsystemGroup τ L (e6Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    Or.inr (Or.inr (M27Ok.isE7E8 (τ := τ)))
  have m1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have m2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have m3 : e6Idx (τ := τ) 3 ∈ d4Set τ := e6Idx_mem_d4Set' 3 (by decide) (by decide)
  have m4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  have c12 : τ.cartan (e6Idx 1) (e6Idx 2) = 0 := by rw [cartan_e6Idx]; decide
  have c21 : τ.cartan (e6Idx 2) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c14 : τ.cartan (e6Idx 1) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c41 : τ.cartan (e6Idx 4) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c24 : τ.cartan (e6Idx 2) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c31 : τ.cartan (e6Idx 3) (e6Idx 1) = -1 := by rw [cartan_e6Idx]; decide
  have c32 : τ.cartan (e6Idx 3) (e6Idx 2) = -1 := by rw [cartan_e6Idx]; decide
  have c34 : τ.cartan (e6Idx 3) (e6Idx 4) = -1 := by rw [cartan_e6Idx]; decide
  have hgen : ∀ j ∈ d4Set τ, ∀ c : L,
      n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c :=
    fun j hj => hstd.hgen j (d4Set_subset_e6Set hj)
  refine Bad3.mono (inf_le_inf_right _ (subsystemGroup_mono d4Set_subset_e6Set)) ?_
  rcases hstd.hπ with rfl | rfl
  · exact bad3_layer_fixed hτ' hf hgen m1 m2 m4 c12 c14 c24
  · refine bad3_layer_swap hτ' hf hgen m2 m4 m1 m3 c24 c21 c41 c32 c34 c31 ?_ ?_ ?_ ?_
    · rw [rhoτ_e6Idx]
      exact congrArg e6Idx (show rho6 2 = 4 by decide)
    · rw [rhoτ_e6Idx]
      exact congrArg e6Idx (show rho6 4 = 2 by decide)
    · rw [rhoτ_e6Idx]
      exact congrArg e6Idx (show rho6 1 = 1 by decide)
    · rw [rhoτ_e6Idx]
      exact congrArg e6Idx (show rho6 3 = 3 by decide)

end Std6

section Layer6

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L]
  [IsAlgClosed L] [CharP L 2]

theorem bad3_e6_layer {f : ℕ} (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ)) :
    Bad3 (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hw : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨n, hn⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    CFSG.RankThree.PartOne.KE6.exists_conj_twistedFixed (ℓ := 2) hf hn hπJ hπJ' hu hact
  have hP' : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  rw [hP']
  exact bad3_of_lang hh hlang (bad3_stdLayer6 hf ⟨hπ, hgen⟩)

end Layer6

section Lane6


theorem bad3_lane_e6 {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p0 : ℕ} (S : LangSetup τ L p0) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    Bad3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hq⟩ := ssTw_exists_f S (ℓ := 2)
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ := ssTw_rho_stable_e6 S haT i v hΨ
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hlayer : QB3 (rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hΨ]
    rw [hΨ] at hw
    refine ssTw_layer_untw S hq hFr hΦ hn v (e6Nodes τ) QB3 (fun P g h => h.map_conj g) ?_
    intro n hn' hw'
    have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
        weylQuotientHom τ L ⟨n, hn'⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
      intro α hα
      rw [hw']
      obtain ⟨β, hβ, hβe⟩ := hw (v • α) ⟨α, hα, rfl⟩
      rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
      exact hβ
    exact ⟨(e6Layer_finite_quasisimple τ (ℓ := 2) hf hn' hmaps).2, bad3_e6_layer hf hn' hmaps⟩
  have heq := ssTw_rationalComponent_eq_layer S i hρ hlayer.1
  rw [heq]
  exact hlayer.2

theorem bad3_e6class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ 3 = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72) :
    Bad3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have : (3 : ℕ) = 2 + 1 := rfl
      rw [this, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | D4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hr hc
    exact bad3_lane_e6 S hT i v hv
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hr hc
    exact bad3_lane_e6 S hT i v hv

end Lane6

end Up34Chev2

namespace Up34Exc

set_option linter.unusedSectionVars false

section ExcFinal


theorem char2HratRank_exc_e6 (τ : Tag) : Char2HratRank τ .exc fun r n => r = 6 ∧ n = 72 := by
  intro L _ _ _ p₀ S a hT hap h1 i hk h6 hq hL34
  exfalso
  haveI := ssTw_finite_rationalComponent S i
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  exact Up34Chev2.not_isLThreeFour_of_bad3
    (Up34Chev2.bad3_e6class S hT hTp h1 i h6.1 h6.2) hL34

theorem char2Hrat_exc (τ : Tag) : Char2Hrat τ .exc :=
  char2Hrat_exc_of_e6class (char2HratRank_exc_e6 τ)

end ExcFinal

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
