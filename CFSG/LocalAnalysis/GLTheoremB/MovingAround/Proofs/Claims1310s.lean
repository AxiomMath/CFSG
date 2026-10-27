module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310r2
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFieldCube
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.HoldsTw
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310s

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree (TwLangData twPlanePre mem_twPlanePre_iff card_twPlanePre
  diagG diagG_apply twistedTorus_le ringChar_eq_of_card_pow)
open CFSG.LieType.SeitzGeneration.ExcHighThree (rootCharHom exists_rootDiagUnit_of_mem_torusGroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (twistedE6InndiagGL twistedE6InndiagConj
  twistedE6InndiagConj_apply twistedE6InndiagConj_injective range_twistedE6InndiagConj)

set_option linter.unusedSectionVars false

section Transport

theorem noPlaneTwoSub_mono {S : Type} [Group S] {A A₁ : Subgroup (MulAut S)}
    (hno : Claims1310r.NoPlaneTwoSub A) (h : A₁ ≤ A) : Claims1310r.NoPlaneTwoSub A₁ :=
  fun F hF h9 V hV hinv => hno F (hF.trans h) h9 V hV hinv

theorem not_noPlaneTwoSub_of_congr {S C : Type} [Group S] [Group C] (e : S ≃* C)
    {A : Subgroup (MulAut S)} (hno : Claims1310r.NoPlaneTwoSub A) {F : Subgroup (MulAut C)}
    (hFA : F ≤ A.map (MulAut.congr e).toMonoidHom) (hF9 : 9 ≤ Nat.card F) {V : Subgroup C}
    (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 ↥V) (hVinv : ∀ φ ∈ F, ∀ v ∈ V, φ v ∈ V) : False := by
  set c := MulAut.congr e with hc
  have hF₀A : F.map c.symm.toMonoidHom ≤ A := by
    rintro _ ⟨ψ', hψ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hFA hψ'
    simpa using hψ
  have hF₀card : Nat.card (F.map c.symm.toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective c.symm.injective
  have hV₀ := hno _ hF₀A (by omega) (V.map e.symm.toMonoidHom) (hV2.map _) (by
    rintro _ ⟨ψ', hψ', rfl⟩ _ ⟨v', hv', rfl⟩
    refine ⟨ψ' v', hVinv ψ' hψ' v' hv', ?_⟩
    simp [hc, MulAut.congr_apply])
  exact hV1 ((Subgroup.map_eq_bot_iff_of_injective V (f := e.symm.toMonoidHom) e.symm.injective).1 hV₀)

end Transport

section Toral

@[expose] def IsToralTwE6 {S : Type} [Group S] (A : Subgroup (MulAut S)) (Q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
    (e : S ≃* twistedE6RootGroup K σ), (∀ c, σ c = c ^ Q) ∧ Nat.card K = Q ^ 2 ∧
      A.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ ∧
      Nonempty (TwLangData K σ Q (twPlanePre K σ (A.map (MulAut.congr e).toMonoidHom)))

theorem not_isToralTwE6 {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) (hno : Claims1310r.NoPlaneTwoSub A)
    {f : ℕ} (hf : 1 ≤ f) : ¬ IsToralTwE6 A (2 ^ f) := by
  rintro ⟨K, _, _, σ, e, hσ, hK, hle, ⟨D⟩⟩
  classical
  have h2K : ringChar K = 2 :=
    ringChar_eq_of_card_pow Nat.prime_two hf K (by rw [hK, ← pow_mul, mul_comm])
  have h3K : ringChar K ≠ 3 := by rw [h2K]; norm_num
  set c := MulAut.congr e with hc
  set A' := A.map c.toMonoidHom with hA'
  have hA'el : IsElemAbelian 3 A' := hA.map _
  have hA'card : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective c.injective
  have hinj := twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ
  set P := twPlanePre K σ A' with hP
  have hPcard : Nat.card P = Nat.card A' := card_twPlanePre 2 f Nat.prime_two hf K hK σ hσ A' hle
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ A' x).1 hx
    have h3 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by
      rw [map_pow]
      exact hA'el.2 _ hg
    have hg3 : g ^ 3 = 1 := hinj (h3.trans (map_one _).symm)
    rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one]
  have hPG : P ≤ twistedE6InndiagGL K σ := fun x hx => by
    obtain ⟨g, rfl, -⟩ := (mem_twPlanePre_iff K σ A' x).1 hx
    exact g.2
  set T₀ := (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).range with hT₀
  have hdiagT : ∀ x ∈ P, diagG D.g0 D.c x ∈ T₀ := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hte' : D.g0 * t * D.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹) := hte
    have hdt : diagG D.g0 D.c x = t := by
      change D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 = t
      rw [← hte']
      group
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (twistedTorus_le _ _ ht)
    exact ⟨a, by rw [hdt, ← ha]; rfl⟩
  let φ : ↥P →* ↥T₀ := ((diagG D.g0 D.c).comp P.subtype).codRestrict T₀ fun x => hdiagT x x.2
  have hrinj : Function.Injective (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) :=
    fun a b h => CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h
  let ι : (Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) ≃* ↥T₀ := MonoidHom.ofInjective hrinj
  set α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single 0 1 with hα
  have hαr : IsRoot TwistTag.E6.tag α := isRoot_single _ _
  let χ : ↥P →* (AlgebraicClosure K)ˣ :=
    (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).comp (ι.symm.toMonoidHom.comp φ)
  have hχ3 : ∀ x : ↥P, χ x ^ 3 = 1 := fun x => by
    have hx3 : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hP3 x x.2, Subgroup.coe_one])
    rw [← map_pow, hx3, map_one]
  have hidx : χ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    refine (Subgroup.card_le_of_le (show χ.range ≤ rootsOfUnity 3 (AlgebraicClosure K) from ?_)).trans
      (card_rootsOfUnity (AlgebraicClosure K) 3)
    rintro _ ⟨x, rfl⟩
    exact (mem_rootsOfUnity 3 _).2 (hχ3 x)
  set Pα : Subgroup (ModGL TwistTag.E6.tag K) := χ.ker.map P.subtype with hPα
  have hPαP : Pα ≤ P := Subgroup.map_subtype_le _
  have hPαcard : 9 ≤ Nat.card Pα := by
    have h1 := Subgroup.card_mul_index χ.ker
    have h2 : Nat.card Pα = Nat.card χ.ker := Subgroup.card_map_of_injective P.subtype_injective
    have h3 : 27 ≤ Nat.card χ.ker * χ.ker.index := by rw [h1, hPcard, hA'card]; exact h27
    have h4 : Nat.card χ.ker * χ.ker.index ≤ Nat.card χ.ker * 3 := Nat.mul_le_mul_left _ hidx
    omega
  have hkill : ∀ x ∈ Pα, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨ι.symm (φ y), ?_, hy⟩
    have e1 := congrArg Subtype.val (ι.apply_symm_apply (φ y))
    have e2 : ((ι (ι.symm (φ y)) : ↥T₀) : ModGL Tag.E6 (AlgebraicClosure K)) =
        rootDiagUnit Tag.E6 (ι.symm (φ y)) := rfl
    rw [e2] at e1
    exact e1.trans (diagG_apply D.g0 D.c y.1)
  let Dα : TwLangData K σ (2 ^ f) Pα :=
    { D with hc := fun x hx => D.hc x (hPαP hx) }
  obtain ⟨u, huC, hu1, ⟨n, hun⟩, huc⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ (2 ^ f) h3K hσ hK Pα Dα α hαr hkill
  set F : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    (Pα.subgroupOf (twistedE6InndiagGL K σ)).map (twistedE6InndiagConj K σ) with hF
  have hFA' : F ≤ A' := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg'eq, hg'A⟩ := (mem_twPlanePre_iff K σ A' _).1 (hPαP (Subgroup.mem_subgroupOf.1 hg))
    have hgg : g' = g := Subtype.ext hg'eq
    rw [← hgg]
    exact hg'A
  have hFcard : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPαP.trans hPG)).toEquiv]
    exact hPαcard
  set uC : ↥(twistedE6RootGroup K σ) := ⟨u, huC⟩ with huCdef
  have hFfix : ∀ ψ ∈ F, ψ uC = uC := by
    rintro _ ⟨g, hg, rfl⟩
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    have hcomm := huc _ (Subgroup.mem_subgroupOf.1 hg)
    change (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
    rw [← hcomm.eq, mul_inv_cancel_right]
  set V : Subgroup ↥(twistedE6RootGroup K σ) := Subgroup.zpowers uC with hV
  have hV2 : IsPGroup 2 ↥V := by
    intro v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 v.2
    refine ⟨n, Subtype.ext ?_⟩
    have huCn : uC ^ (2 ^ n) = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, huCdef, Subgroup.coe_one, ← h2K]
      exact hun)
    rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huCn, one_zpow]
  have hV1 : V ≠ ⊥ := by
    intro hbot
    apply hu1
    have hmem : uC ∈ V := Subgroup.mem_zpowers uC
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hVinv : ∀ ψ ∈ F, ∀ v ∈ V, ψ v ∈ V := by
    intro ψ hψ v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [map_zpow, hFfix ψ hψ]
    exact Subgroup.zpow_mem_zpowers uC k
  exact not_noPlaneTwoSub_of_congr e hno hFA' hFcard hV1 hV2 hVinv

end Toral

section TwoElem

open CFSG.LieType.SeitzGeneration.ExcHighThree (e6_regular_threeA rootChar_eq_one_of_dvd
  three_dvd_sum_of_mod rootDot_ofFn rootDot)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (map_twistedE6InndiagGL_le_twistedFixedGroup
  exists_lang_torus_of_conj_torus_twisted' monomialToralAt_E6_three)

theorem exists_root_kills_e6 (k : Fin Tag.E6.rank → ℕ) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ (3 : ℤ) ∣ ∑ i, α i * (k i : ℤ) := by
  classical
  by_cases hk : ∃ i, ¬ 3 ∣ k i
  · obtain ⟨i, hi⟩ := hk
    set v : List ℕ := List.ofFn fun i => k i % 3 with hv
    set u : List ℕ := List.ofFn fun _ : Fin Tag.E6.rank => 0 with hu
    have hvl : v.length = 6 := by simp [hv]; rfl
    have hul : u.length = 6 := by simp [hu]; rfl
    have hv3 : ∀ x ∈ v, x < 3 := fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.mod_lt _ (by norm_num)
    have hu3 : ∀ x ∈ u, x < 3 := fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      norm_num
    have hv0 : ∃ x ∈ v, x ≠ 0 := ⟨k i % 3, List.mem_ofFn.2 ⟨i, rfl⟩, by omega⟩
    have hex : ∃ a ∈ CFSG.Blueprint.Chevalley.e6ArtifactRoots, rootDot a v % 3 = 0 := by
      by_contra hcon
      push Not at hcon
      have hreg : ∀ a ∈ CFSG.Blueprint.Chevalley.e6ArtifactRoots,
          ¬ (rootDot a v % 3 = 0 ∧ rootDot a u % 3 = 0) := fun a ha h => hcon a ha h.1
      have h18 := e6_regular_threeA hvl hul hv3 hu3 hv0 hreg
      rw [List.filter_eq_nil_iff.2 (fun a ha => by simpa using hcon a ha)] at h18
      simp at h18
    obtain ⟨a, ha, h1⟩ := hex
    have hal : a.length = Tag.E6.rank := length_of_mem_artifactRoots (τ := .E6) ha
    set α : Fin Tag.E6.rank → ℤ := fun i => a.getD i 0 with hαdef
    have hα : List.ofFn α = a := by
      refine List.ext_getElem (by simp [hal]) fun m hm hm' => ?_
      simp [hαdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']
    refine ⟨α, isRoot_iff_mem_artifactRoots.2 (by rw [hα]; exact ha), ?_⟩
    rw [← hα, hv, rootDot_ofFn] at h1
    exact three_dvd_sum_of_mod α k h1
  · push Not at hk
    refine ⟨Pi.single 0 1, isRoot_single _ _, Finset.dvd_sum fun i _ => ?_⟩
    obtain ⟨m, hm⟩ := hk i
    rw [hm]
    push_cast
    exact Dvd.dvd.mul_left (dvd_mul_right 3 _) _

theorem mem_inndiag_of_two {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ (2 ^ 1)) {β : MulAut ↥(twistedE6RootGroup K₀ σ₀)}
    (hβ : β ^ 3 = 1) : β ∈ twistedE6Inn K₀ σ₀ ⊔ twistedE6Diag K₀ σ₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K₀ hK₀ σ₀ hσ₀
  rw [← hker, MonoidHom.mem_ker]
  have hcard : Nat.card (RingAut K₀) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K₀
      (by rw [hK₀]; norm_num)).1
  haveI : Finite (RingAut K₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h2 : Θ β ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K₀) (x := Θ β)
    rwa [hcard] at this
  have h3 : Θ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  calc Θ β = Θ β ^ 3 * (Θ β ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, one_mul, inv_one]

theorem exists_fixed_two_elem_of_two {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ (2 ^ 1)) (β : MulAut ↥(twistedE6RootGroup K₀ σ₀))
    (hβ : β ^ 3 = 1) :
    ∃ u : ↥(twistedE6RootGroup K₀ σ₀), u ≠ 1 ∧ (∃ n : ℕ, u ^ (2 ^ n) = 1) ∧ β u = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2K : ringChar K₀ = 2 :=
    ringChar_eq_of_card_pow Nat.prime_two le_rfl K₀ (by rw [hK₀]; norm_num)
  haveI : CharP K₀ 2 := h2K ▸ ringChar.charP K₀
  haveI : CharP (AlgebraicClosure K₀) 2 :=
    charP_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective 2
  have hβD := mem_inndiag_of_two hK₀ σ₀ hσ₀ hβ
  rw [← range_twistedE6InndiagConj] at hβD
  obtain ⟨g, hg⟩ := hβD
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK₀ σ₀ hσ₀
  have hg3 : g ^ 3 = 1 := hinj (by rw [map_pow, hg, hβ, map_one])
  set gm : ModGL TwistTag.E6.tag K₀ := (g : ModGL TwistTag.E6.tag K₀) with hgm
  have hgm3 : gm ^ 3 = 1 := by rw [hgm, ← Subgroup.coe_pow, hg3, Subgroup.coe_one]
  set L := AlgebraicClosure K₀ with hL
  set ι := algebraMap K₀ L with hι
  set Fr : L →+* L := iterateFrobenius L 2 1 with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ 1) := fun c => rfl
  have hgF := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two le_rfl hK₀ σ₀ hσ₀ Fr hFr
    (Subgroup.mem_map_of_mem (baseChangeGL ι) g.2)
  obtain ⟨hgad, hgfix⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hgF
  have h3K : ¬ 3 ∣ Nat.card K₀ := by rw [hK₀]; norm_num
  obtain ⟨C, hC, hCt⟩ := CFSG.StandardType.ExcElemToral.exists_conj_mem_torusGroup_of_pow_eq_one
    (τ := TwistTag.E6.tag) monomialToralAt_E6_three h3K hgad (by rw [← map_pow, hgm3, map_one])
  set AL : Subgroup (ModGL TwistTag.E6.tag L) := Subgroup.zpowers (baseChangeGL ι gm) with hAL
  have hFix : ∀ x ∈ AL, twistHom TwistTag.E6 L (iterateFrobenius L 2 1) x = x := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow]
    exact congrArg (· ^ k) hgfix
  have hCA : ∀ x ∈ AL, C * x * C⁻¹ ∈ torusGroup TwistTag.E6.tag L := by
    rintro _ ⟨k, rfl⟩
    rw [← conj_zpow]
    exact zpow_mem hCt k
  obtain ⟨v, g0, hg0C, hg0, hin⟩ :=
    exists_lang_torus_of_conj_torus_twisted' 2 TwistTag.E6 1 le_rfl hFix hC hCA
  let D : TwLangData K₀ σ₀ 2 (Subgroup.zpowers gm) :=
    { v := v, Fr := iterateFrobenius L 2 1, hFr := fun c => by rw [iterateFrobenius_def, pow_one],
      g0 := g0, hg0C := hg0C, hg0 := hg0, c := 1,
      hcI := one_mem _,
      hc := fun x hx => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [one_mul, inv_one, mul_one, map_zpow]
        exact hin _ (Subgroup.zpow_mem_zpowers _ k) }
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hin _ (Subgroup.mem_zpowers (baseChangeGL ι gm)))
  have hte' : g0 * t * g0⁻¹ = baseChangeGL ι gm := hte
  have htd : g0⁻¹ * baseChangeGL ι gm * g0 = t := by rw [← hte']; group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (twistedTorus_le _ _ ht)
  have ha3 : a ^ 3 = 1 := by
    have h1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) = rootDiagUnit TwistTag.E6.tag 1 := by
      have e1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) = (rootDiagUnit TwistTag.E6.tag a) ^ 3 :=
        map_pow (rootDiagUnitHom TwistTag.E6.tag L) a 3
      have e2 : rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank → Lˣ) = 1 :=
        map_one (rootDiagUnitHom TwistTag.E6.tag L)
      rw [e1, e2, ha, ← htd]
      calc (g0⁻¹ * baseChangeGL ι gm * g0) ^ 3 = g0⁻¹ * (baseChangeGL ι gm) ^ 3 * g0⁻¹⁻¹ := by
            rw [← conj_pow, inv_inv]
        _ = 1 := by rw [← map_pow, hgm3, map_one, mul_one, inv_inv, inv_mul_cancel]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1
  have hne3 : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.natCast_three_ne_zero_of_not_dvd (K := K₀) h3K
  haveI : NeZero ((3 : ℕ) : L) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  obtain ⟨ω, hωζ⟩ : ∃ ω : Lˣ, (ω : L) = ζ := ⟨hζu.unit, hζu.unit_spec⟩
  have hω3 : ω ^ 3 = 1 := Units.ext (by simp [hωζ, hζ.pow_eq_one])
  have hpow : ∀ b : Lˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : L) ^ 3 = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by simp [hωζ, hk])⟩
  choose k hk using fun i => hpow (a i) (by simpa using congrFun ha3 i)
  obtain ⟨α, hα, hαk⟩ := exists_root_kills_e6 k
  have hαa : rootChar a α = 1 := rootChar_eq_one_of_dvd hω3 hk hαk
  have hkill : ∀ x ∈ Subgroup.zpowers gm, ∃ a' : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag a' = D.g0⁻¹ *
        baseChangeGL ι (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K₀) * D.g0 ∧ rootChar a' α = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨a ^ m, ?_, ?_⟩
    · change rootDiagUnit TwistTag.E6.tag (a ^ m) = g0⁻¹ * baseChangeGL ι (1 * gm ^ m * 1⁻¹) * g0
      rw [one_mul, inv_one, mul_one, map_zpow]
      have e1 : rootDiagUnit TwistTag.E6.tag (a ^ m) = (rootDiagUnit TwistTag.E6.tag a) ^ m :=
        map_zpow (rootDiagUnitHom TwistTag.E6.tag L) a m
      rw [e1, ha, ← htd]
      calc (g0⁻¹ * baseChangeGL ι gm * g0) ^ m = g0⁻¹ * (baseChangeGL ι gm) ^ m * g0⁻¹⁻¹ := by
            rw [← conj_zpow, inv_inv]
        _ = g0⁻¹ * (baseChangeGL ι gm) ^ m * g0 := by rw [inv_inv]
    · have e2 : rootChar (a ^ m) α = (rootChar a α) ^ m :=
        map_zpow (rootCharHom (τ := TwistTag.E6.tag) (L := L) α) a m
      rw [e2, hαa, one_zpow]
  obtain ⟨u, huC, hu1, ⟨n, hun⟩, huc⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K₀ σ₀ 2 (by rw [h2K]; norm_num)
      (fun c => by rw [hσ₀, pow_one]) (by rw [hK₀]; norm_num) (Subgroup.zpowers gm) D α hα hkill
  refine ⟨⟨u, huC⟩, fun h1 => hu1 (congrArg Subtype.val h1), ⟨n, Subtype.ext ?_⟩, ?_⟩
  · rw [Subgroup.coe_pow, Subgroup.coe_one, ← h2K]
    exact hun
  · rw [← hg]
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    have hcomm := huc gm (Subgroup.mem_zpowers gm)
    change gm * u * gm⁻¹ = u
    rw [← hcomm.eq, mul_inv_cancel_right]

end TwoElem

section FieldCube

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (twFJ twFJ_le_twR mem_twFJ_of_commute
  subfieldRootGroupImage_le_twistedE6)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc (exists_primePower_fixSubfield_twisted
  fixSubfieldRestrict_eq_pow_twE6)

theorem exists_plane_two_of_not_le_inndiag {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ 3))
    {E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E) (h9 : 9 ≤ Nat.card E)
    (hnd : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ F : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), F ≤ E ∧ 9 ≤ Nat.card F ∧
      ∃ V : Subgroup ↥(twistedE6RootGroup K σ), V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧
        ∀ φ ∈ F, ∀ v ∈ V, φ v ∈ V := by
  classical
  have hK2f : Nat.card K = 2 ^ (2 * 3) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two (by norm_num) K hK σ hσ
  obtain ⟨x, hxE, hxD⟩ := Set.not_subset.1 hnd
  obtain ⟨hηo, -, ψ, hψ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_fieldActor_of_not_mem_twistedE6Inndiag
      Nat.prime_two (by norm_num) K hK2f σ hσ Θ hΘ Nat.prime_three (by norm_num) (hE.2 x hxE) hxD
  set η := Θ x with hη
  have hR := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK2f
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hR.1]; norm_num)
  let ΘE : ↥E →* RingAut K := Θ.comp E.subtype
  have hr3 : Nat.card ΘE.range ≤ 3 := by
    have hpg : IsPGroup 3 ΘE.range := by
      rintro ⟨_, ⟨y, rfl⟩⟩
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (by simpa using hE.2 y y.2)
      rw [this, map_one]
    obtain ⟨m, hm⟩ := hpg.exists_card_eq
    have hdvd : Nat.card ΘE.range ∣ 2 * 3 := hR.1 ▸ Subgroup.card_subgroup_dvd_card _
    rw [hm] at hdvd ⊢
    have hm1 : m ≤ 1 := by
      by_contra hm2
      push Not at hm2
      have : 3 ^ 2 ∣ 2 * 3 := (pow_dvd_pow 3 hm2).trans hdvd
      norm_num at this
    interval_cases m <;> norm_num
  have hk3 : 3 ≤ Nat.card ΘE.ker := by
    have h1 := Subgroup.card_mul_index ΘE.ker
    rw [Subgroup.index_ker] at h1
    by_contra h
    push Not at h
    have : Nat.card ΘE.ker * Nat.card ΘE.range ≤ 2 * 3 := Nat.mul_le_mul (by omega) hr3
    omega
  obtain ⟨⟨a, haE⟩, haK, ha1⟩ : ∃ a ∈ ΘE.ker, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ΘE.ker = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hk3
    omega
  have hΘa : Θ a = 1 := haK
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hx1 : x ≠ 1 := fun h => hxD (h ▸ one_mem _)
  have hxa : x * a = a * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxE⟩ ⟨a, haE⟩)
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  set a'' := ψ * a * ψ⁻¹ with ha''
  have hcomm : Commute a'' (fieldActor (t := TwistTag.E6) σ η) := by
    rw [hη, ← hψ]
    show ψ * a * ψ⁻¹ * (ψ * x * ψ⁻¹) = ψ * x * ψ⁻¹ * (ψ * a * ψ⁻¹)
    calc ψ * a * ψ⁻¹ * (ψ * x * ψ⁻¹) = ψ * (a * x) * ψ⁻¹ := by group
      _ = ψ * (x * a) * ψ⁻¹ := by rw [hxa]
      _ = ψ * x * ψ⁻¹ * (ψ * a * ψ⁻¹) := by group
  have ha''3 : a'' ^ 3 = 1 := by rw [ha'', conj_pow, ha3, mul_one, mul_inv_cancel]
  have hJ : ∀ b : MulAut ↥(twistedE6RootGroup K σ), Commute b (fieldActor (t := TwistTag.E6) σ η) →
      ∀ y ∈ twFJ σ η, b y ∈ twFJ σ η := fun b hb y hy =>
    mem_twFJ_of_commute Nat.prime_two (by norm_num) hK σ hσ Nat.prime_three (by norm_num) hηo hb hy
  let βJ : MulAut ↥(twFJ σ η) :=
    { toFun := fun y => ⟨a'' y, hJ a'' hcomm y y.2⟩
      invFun := fun y => ⟨a''⁻¹ y, hJ a''⁻¹ hcomm.inv_left y y.2⟩
      left_inv := fun y => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun y => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun y z => Subtype.ext (map_mul a'' (y : ↥(twistedE6RootGroup K σ)) z) }
  have hβJ : ∀ (n : ℕ) (y : ↥(twFJ σ η)),
      (((βJ ^ n) y : ↥(twFJ σ η)) : ↥(twistedE6RootGroup K σ)) = (a'' ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hβJ3 : βJ ^ 3 = 1 := MulEquiv.ext fun y => Subtype.ext (by rw [hβJ, ha''3]; rfl)
  set q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩ with hqdef
  have hqc : q.card = 2 ^ 3 := by rw [TauCeti.PrimePower.card_def]
  obtain ⟨q₀, -, hqq, hF⟩ := exists_primePower_fixSubfield_twisted (q := q) (m := 2) (by norm_num)
    (by rw [hqc]; exact hK) η Nat.prime_three (by norm_num) hηo
  have hq₀ : q₀.card = 2 := by
    have hc : q₀.card ^ 3 = 2 ^ 3 := by rw [← hqq, hqc]
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hc
  have hK₀ : Nat.card ↥(fixSubfield η) = (2 ^ 1) ^ 2 := by rw [hF, hq₀, pow_one]
  have hσq : ∀ c, σ c = c ^ q.card := fun c => by rw [hσ c, hqc]
  have hσ₀ : ∀ c, fixSubfieldRestrict σ η c = c ^ (2 ^ 1) := fun c => by
    rw [fixSubfieldRestrict_eq_pow_twE6 hqq (by decide) σ hσq η hF c, hq₀, pow_one]
  let eJ : ↥(twFJ σ η) ≃* ↥(twistedE6RootGroup ↥(fixSubfield η) (fixSubfieldRestrict σ η)) :=
    (Subgroup.subgroupOfEquivOfLe (subfieldRootGroupImage_le_twistedE6 σ η)).trans
      (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (τ := TwistTag.E6.tag) _)).symm
  obtain ⟨u', hu'1, ⟨n, hun⟩, hu'fix⟩ := exists_fixed_two_elem_of_two hK₀ (fixSubfieldRestrict σ η) hσ₀
    (MulAut.congr eJ βJ) (by rw [← map_pow, hβJ3, map_one])
  set uJ := eJ.symm u' with huJ
  have huJfix : βJ uJ = uJ := by
    apply eJ.injective
    have h1 : (MulAut.congr eJ βJ) u' = eJ (βJ (eJ.symm u')) := rfl
    rw [← h1, hu'fix, huJ, MulEquiv.apply_symm_apply]
  set u : ↥(twistedE6RootGroup K σ) := (uJ : ↥(twistedE6RootGroup K σ)) with hu
  have hua : a'' u = u := congrArg Subtype.val huJfix
  have huη : fieldActor (t := TwistTag.E6) σ η u = u := twFJ_le_twR σ η uJ.2
  have hu1 : u ≠ 1 := by
    intro h1
    apply hu'1
    have huJ1 : uJ = 1 := Subtype.ext h1
    rw [← eJ.apply_symm_apply u', ← huJ, huJ1, map_one]
  have hun' : u ^ (2 ^ n) = 1 := by
    have : uJ ^ (2 ^ n) = 1 := by rw [huJ, ← map_pow, hun, map_one]
    rw [hu, ← Subgroup.coe_pow, this, Subgroup.coe_one]
  set w : ↥(twistedE6RootGroup K σ) := ψ⁻¹ u with hw
  have hwx : x w = w := by
    have hxψ : x = ψ⁻¹ * fieldActor (t := TwistTag.E6) σ η * ψ := by rw [hη, ← hψ]; group
    rw [hxψ, hw, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, huη]
  have hwa : a w = w := by
    have haψ : a = ψ⁻¹ * a'' * ψ := by rw [ha'']; group
    rw [haψ, hw, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hua]
  have hax : a ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hηk : η ^ k = 1 := by
      have : Θ (x ^ k) = Θ a := by rw [hk]
      rw [map_zpow, hΘa] at this
      exact this
    have h3k : ((orderOf η : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hηk
    rw [hηo] at h3k
    obtain ⟨m, hm⟩ := h3k
    apply ha1'
    rw [← hk, hm, zpow_mul]
    norm_num [hE.2 x hxE]
  set F : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) := Subgroup.closure ({x, a} : Set _) with hFdef
  have hFE : F ≤ E := by
    rw [hFdef, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hxE
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact haE
  have hFcard : Nat.card F = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hE hxE haE hx1 hax
  have hFfix : ∀ φ ∈ F, φ w = w := by
    have hle : F ≤ MulAction.stabilizer (MulAut ↥(twistedE6RootGroup K σ)) w := by
      rw [hFdef, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact hwx
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hwa
    exact fun φ hφ => hle hφ
  refine ⟨F, hFE, by rw [hFcard]; norm_num, Subgroup.zpowers w, ?_, ?_, ?_⟩
  · intro hbot
    apply hu1
    have hmem : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
    rw [hbot, Subgroup.mem_bot] at hmem
    calc u = ψ w := by rw [hw, MulAut.apply_inv_self]
      _ = 1 := by rw [hmem, map_one]
  · intro v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 v.2
    refine ⟨n, Subtype.ext ?_⟩
    have hwn : w ^ (2 ^ n) = 1 := by rw [hw, ← map_pow, hun', map_one]
    rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hwn, one_zpow]
  · intro φ hφ v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [map_zpow, hFfix φ hφ]
    exact Subgroup.zpow_mem_zpowers w k

end FieldCube

section OuterPlanes

open CFSG.LieType.SeitzGeneration.ExcWideThree (TwE6NormalizesR exists_twLangData
  twE6HeisenbergParabolic_of_frame twE6HeisFrameNormalizesR_of_fixedElt twE6HeisFrameFixedElt_holds)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (TwistedE6DiagIsotropic)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_cubeExt twistedE6PlaneToralLang_proved)

theorem isElementaryAbelian_of_isElemAbelian' {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : CFSG.IsElementaryAbelian 3 ↥E :=
  { toIsMulCommutative := hE.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      Subtype.ext (by rw [Subgroup.coe_pow, hE.2 g g.2, Subgroup.coe_one]) }

theorem outerPlane_regular {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    (hno : Claims1310r.NoPlaneTwoSub A) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : S ≃* twistedE6RootGroup K σ) {E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hEA : E ≤ A.map (MulAut.congr e).toMonoidHom)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hEel : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (hEout : ¬ E ≤ twistedE6Inn K σ) :
    Nonempty (TwLangData K σ (2 ^ f) (twPlanePre K σ E)) ∧
      ∀ D : TwLangData K σ (2 ^ f) (twPlanePre K σ E), D.IsRegular := by
  classical
  have h2K : ringChar K = 2 :=
    ringChar_eq_of_card_pow Nat.prime_two hf K (by rw [hK, ← pow_mul, mul_comm])
  have h3K : ringChar K ≠ 3 := by rw [h2K]; norm_num
  haveI hEi : CFSG.IsElementaryAbelian 3 ↥E := isElementaryAbelian_of_isElemAbelian' hEel
  have hE9' : 9 ≤ Nat.card E := by rw [hE9]; norm_num
  have hinj := twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ
  refine ⟨?_, ?_⟩
  · obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
    haveI := hK₁
    by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
    · exact exists_twLangData twistedE6PlaneToralLang_proved 2 f Nat.prime_two (by norm_num) hf hK σ hσ
        K₁ hroot E hEi hE9 hED hiso
    · exfalso
      obtain ⟨R, hR1, hRp, hRE⟩ := twE6HeisenbergParabolic_of_frame
        (twE6HeisFrameNormalizesR_of_fixedElt twE6HeisFrameFixedElt_holds) K σ (2 ^ f) h3K hσ hK K₁ hroot
        E hED hEi hE9 hEout hiso
      refine not_noPlaneTwoSub_of_congr e hno hEA hE9' hR1 (h2K ▸ hRp) fun φ hφ v hv => ?_
      rw [← hRE φ hφ]
      exact ⟨v, hv, rfl⟩
  · rintro D ⟨α, hα, hkill⟩
    obtain ⟨u, huC, hu1, ⟨n, hun⟩, huc⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ (2 ^ f) h3K hσ hK
        (twPlanePre K σ E) D α hα hkill
    set uC : ↥(twistedE6RootGroup K σ) := ⟨u, huC⟩ with huCdef
    have hEfix : ∀ φ ∈ E, φ uC = uC := by
      intro φ hφ
      have hφr : φ ∈ (twistedE6InndiagConj K σ).range := by
        rw [range_twistedE6InndiagConj]
        exact hED hφ
      obtain ⟨g, rfl⟩ := hφr
      have hgP : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
        (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hφ⟩
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      have hcomm := huc _ hgP
      change (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
      rw [← hcomm.eq, mul_inv_cancel_right]
    refine not_noPlaneTwoSub_of_congr e hno hEA hE9' (V := Subgroup.zpowers uC) ?_ ?_ ?_
    · intro hbot
      apply hu1
      have hmem : uC ∈ Subgroup.zpowers uC := Subgroup.mem_zpowers uC
      rw [hbot, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · intro v
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 v.2
      refine ⟨n, Subtype.ext ?_⟩
      have huCn : uC ^ (2 ^ n) = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, huCdef, Subgroup.coe_one, ← h2K]
        exact hun)
      rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, huCn, one_zpow]
    · intro φ hφ v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, hEfix φ hφ]
      exact Subgroup.zpow_mem_zpowers uC k

end OuterPlanes

section High

@[expose] def IsHighTwE6 {S : Type} [Group S] (A : Subgroup (MulAut S)) (Q : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (e : S ≃* twistedE6RootGroup K σ),
    (∀ c, σ c = c ^ Q) → Nat.card K = Q ^ 2 →
      A.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ ∧
      (∀ A₁ : Subgroup (MulAut S), A₁ ≤ A → 27 ≤ Nat.card A₁ →
        IsEmpty (TwLangData K σ Q (twPlanePre K σ (A₁.map (MulAut.congr e).toMonoidHom)))) ∧
      ∀ E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), E ≤ A.map (MulAut.congr e).toMonoidHom →
        Nat.card E = 3 ^ 2 → ¬ E ≤ twistedE6Inn K σ →
          Nonempty (TwLangData K σ Q (twPlanePre K σ E)) ∧
            ∀ D : TwLangData K σ Q (twPlanePre K σ E), D.IsRegular

theorem isHighTwE6_of_noPlaneTwoSub {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) (hno : Claims1310r.NoPlaneTwoSub A) {f : ℕ}
    (hf : f = 1 ∨ f = 3) : IsHighTwE6 A (2 ^ f) := by
  intro K _ _ σ e hσ hK
  have hle : A.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rcases hf with rfl | rfl
    · rintro _ ⟨φ, hφ, rfl⟩
      exact mem_inndiag_of_two hK σ hσ (by rw [← map_pow, hA.2 φ hφ, map_one])
    · by_contra hnd
      have hA'el : IsElemAbelian 3 (A.map (MulAut.congr e).toMonoidHom) := hA.map _
      have h9 : 9 ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
        omega
      obtain ⟨F, hFE, hF9, V, hV1, hV2, hVinv⟩ :=
        exists_plane_two_of_not_le_inndiag σ hK hσ hA'el h9 hnd
      exact not_noPlaneTwoSub_of_congr e hno hFE hF9 hV1 hV2 hVinv
  have hf1 : 1 ≤ f := by rcases hf with rfl | rfl <;> norm_num
  refine ⟨hle, fun A₁ hA₁ h27₁ => ⟨fun D => ?_⟩, fun E hEA hE9 hEout =>
    outerPlane_regular hno hf1 σ hσ hK e hEA (hEA.trans hle) ((hA.map _).mono hEA) hE9 hEout⟩
  exact not_isToralTwE6 (hA.mono hA₁) h27₁ (noPlaneTwoSub_mono hno hA₁) hf1
    ⟨K, inferInstance, inferInstance, σ, e, hσ, hK, (Subgroup.map_mono hA₁).trans hle, ⟨D⟩⟩

end High

section Six

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)
open CFSG.HardMathSupport.Dickson.I271 (autImage)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def Rank3CuResExcSix : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          Subgroup.center (barOf 3 Kc) ≠ ⊥ →
          (∃ i : TauCeti.ValidLieTypeIndex,
            Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
            ((∃ q, IsTwoPow q 1 ∧ i.1 = .twistedE6 q ∧
                Claims1310r.NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ∧
                IsHighTwE6 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) (q.p ^ q.exponent)) ∨
              (∃ q, IsTwoPow q 3 ∧ i.1 = .twistedE6 q ∧
                Claims1310r.NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ∧
                ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                  (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range ∧
                IsHighTwE6 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) (q.p ^ q.exponent)))) →
          Kc ≤ M

theorem rank3CuResExcFive_of_six (hX : Rank3CuResExcSix) : Claims1310r.Rank3CuResExcFive := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal hZ htype
  obtain ⟨i, he, hcase⟩ := htype
  have hp3 : p = 3 := h139b.1
  obtain ⟨hcard, hB4⟩ := Claims1310r.card_autImage_eq h h139b hU hu hu1 hKc hN hcen
  have hBel : IsElemAbelian 3 B := hp3 ▸ h.bOne.1.1
  have hAel : IsElemAbelian 3 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage (isElemAbelian_barX hBel)
  have h27 : 27 ≤ Nat.card (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (CFSG.Open.pRank 3 B - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine hX h h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal hZ ⟨i, he, ?_⟩
  rcases hcase with ⟨q, hq, hiq, hno⟩ | ⟨q, hq, hiq, hno, hni⟩
  · refine Or.inl ⟨q, hq, hiq, hno, ?_⟩
    rw [hq.1, hq.2]
    exact isHighTwE6_of_noPlaneTwoSub hAel h27 hno (Or.inl rfl)
  · refine Or.inr ⟨q, hq, hiq, hno, hni, ?_⟩
    rw [hq.1, hq.2]
    exact isHighTwE6_of_noPlaneTwoSub hAel h27 hno (Or.inr rfl)

theorem rank3CuRes_of_six (h2 : KFactSeitzRankTwo)
    (hQ : InputsSeitz6.SeitzQuasiAt 3) (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcSix) :
    Claims1310.Rank3CuRes :=
  Claims1310r.rank3CuRes_of_five h2 hQ hGA (rank3CuResExcFive_of_six hX)

end Six

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310s

end
