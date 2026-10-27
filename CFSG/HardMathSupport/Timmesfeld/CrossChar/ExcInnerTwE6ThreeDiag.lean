module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTest
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAutBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE


theorem e6Three_rigid_of_torus (hAK : AnyKindCommuteT) (hbig : ThreeBigComponents)
    {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup Tag.E6 L 3) (hd : S.Descends) (hq4 : 4 ≤ S.D.q)
    {D : Subgroup (ModGL Tag.E6 L)} [Finite D] (hDT : D ≤ S.D.torus)
    (hpow : ∀ x ∈ D, x ^ 3 = 1) (hcard : 3 < Nat.card D) (δ : MulAut S.Γ)
    (hfix : ∀ x : S.Γ, (x : ModGL Tag.E6 L) ∈ bigComponentSet S D → δ x = x) : δ = 1 := by
  have hΓC : ∀ x : S.Γ, (x : ModGL Tag.E6 L) ∈ adjointGroup Tag.E6 L := fun x =>
    (S.Γ_le_model x.2).1
  refine rigid_E6_of_testSet S hd (bigComponentSet S D) (bigComponentSet_subset_Γ S D)
    (fun r f j _ hr hqf hj0 hjf z => noFrobenius_testSet_of_torus hbig S (by decide) hq4
      (Or.inr (Or.inr (Or.inl rfl))) hDT hpow hcard r f j hr hqf hj0 hjf z)
    (fun z _ hzc x => commute_adjointGroup_of_torus hAK hbig S (by decide) hq4 hDT hpow hcard
      hzc _ (hΓC x))
    (fun w hw hcomm => not_forall_commute_mul_diagramMap_E6 (K := K) hw
      (commute_adjointGroup_of_torus hAK hbig S (by decide) hq4 hDT hpow hcard hcomm)) δ hfix

theorem e6Three_langTorusPlaneBalanceInndiag (hsub : LangSubnormalT)
    (hin : LangComponentsQuasisimpleT .inner) (hsu : LangComponentsQuasisimpleT .suN)
    (htw : LangComponentsQuasisimpleT .twoD) (hex : LangComponentsQuasisimpleT .exc)
    (hAK : AnyKindCommuteT) (hbig : ThreeBigComponents) (w : WeylGroup Tag.E6) :
    LangTorusPlaneBalanceInndiag w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 := by
  classical
  intro K _ _ hQK Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hq4 : 4 ≤ Nat.card K := four_le_of_not_three_dvd Finite.one_lt_card hQK.1 hQK.2
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hιdef
  let D : LangDatum Tag.E6 L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hd : LangDescent D 7 ((baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype) :=
    langDescent_ofFrobenius (Or.inr (Or.inl rfl)) w K hFr hg0C hg0
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L D
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast ι, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K, map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨by
      rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card K, hK0⟩
  let S : LangSetup Tag.E6 L 3 :=
    D.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow hQK.1 hd.finite_model
  have hSq : S.D.q = Nat.card K := rfl
  have hι : Function.Injective ((baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  set φ : adjointGroup Tag.E6 K ≃* S.Γ := hd.mulEquiv' hι with hφdef
  have hφ : ∀ h : adjointGroup Tag.E6 K,
      ((φ h : S.Γ) : ModGL Tag.E6 L) = g0⁻¹ * baseChangeGL ι (h : ModGL Tag.E6 K) * g0 :=
    fun h => hd.coe_mulEquiv' hι h
  have hdesc : S.Descends := ⟨K, inferInstance, inferInstance, inferInstance, φ, rfl, hφ⟩
  set θ : ↥(e6InndiagGL K) →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL ι).comp (e6InndiagGL K).subtype) with hθdef
  have hθ : ∀ x : ↥(e6InndiagGL K), θ x = g0⁻¹ * baseChangeGL ι (x : ModGL Tag.E6 K) * g0 :=
    fun x => by
      change (MulAut.conj g0⁻¹) (baseChangeGL ι (x : ModGL Tag.E6 K)) = _
      rw [MulAut.conj_apply, inv_inv]
  have hθinj : Function.Injective θ :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective ι).comp Subtype.val_injective)
  set D' : Subgroup (ModGL Tag.E6 L) := D₀.map θ with hD'def
  have hD₀fin : Finite D₀ := Nat.finite_of_card_ne_zero (by omega)
  have hD'fin : Finite D' := Finite.of_surjective (fun x : D₀ => (⟨θ x, x, x.2, rfl⟩ : D'))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hD'T : D' ≤ S.D.torus := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := htor x hx
    rw [hθ, ← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
    exact hy
  have hD'pow : ∀ x ∈ D', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hD'card : 3 < Nat.card D' := by
    rw [hD'def, Subgroup.card_map_of_injective hθinj]
    exact hcard
  set ψ : MulAut (adjointGroup Tag.E6 K) ≃* MulAut S.Γ := MulAut.congr φ with hψdef
  have hψc : ∀ (x : ↥(e6InndiagGL K)) (y : S.Γ),
      ((ψ (e6InndiagConj K x) y : S.Γ) : ModGL Tag.E6 L) = θ x * y * (θ x)⁻¹ := by
    intro x y
    obtain ⟨h, rfl⟩ := φ.surjective y
    change ((φ (e6InndiagConj K x (φ.symm (φ h))) : S.Γ) : ModGL Tag.E6 L) = _
    rw [MulEquiv.symm_apply_apply, hφ, hφ, e6InndiagConj_apply, map_mul, map_mul, map_inv, hθ]
    group
  have hψconj : ∀ g : adjointGroup Tag.E6 K, ψ (MulAut.conj g) = MulAut.conj (φ g) := fun g => by
    ext z
    simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have hinj : Function.Injective (MulAut.conj : S.Γ →* MulAut S.Γ) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv φ.symm
      (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
  have := S.finite_Γ
  have hcinj := e6InndiagConj_injective K hq4
  have hH' : innerAut S.Γ ≤ H.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (φ.symm y), hH ⟨φ.symm y, rfl⟩, ?_⟩
    change ψ (MulAut.conj (φ.symm y)) = MulAut.conj y
    rw [hψconj, MulEquiv.apply_symm_apply]
  have hE' : (D₀.map (e6InndiagConj K)).map ψ.toMonoidHom ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ D₀, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hcon
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    intro hbot
    have hmem : ψ (e6InndiagConj K x) ∈ (D₀.map (e6InndiagConj K)).map ψ.toMonoidHom :=
      ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one ψ] at hmem
    exact hx1 (hcinj (ψ.injective hmem |>.trans (map_one _).symm))
  have key : localDeltaIn 3 (H.map ψ.toMonoidHom) ((D₀.map (e6InndiagConj K)).map ψ.toMonoidHom) =
      ⊥ := by
    refine localDeltaIn_eq_bot_of_aut_components_rigid Nat.prime_three hinj hH' hE'
      (S := {s : S.Γ | (s : ModGL Tag.E6 L) ∈ bigComponentSet S D'})
      (fun δ _ _ hδ => e6Three_rigid_of_torus (K := K) hAK hbig S hdesc (by rw [hSq]; exact hq4)
        hD'T hD'pow hD'card δ hδ) ?_
    rintro s ⟨a, haD, ha1, i, hbig', hsR⟩
    obtain ⟨x, hx, hxa⟩ := haD
    have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := hD'T ⟨x, hx, hxa⟩
    have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := hD'pow _ ⟨x, hx, hxa⟩
    obtain ⟨hRC, hRsn⟩ := hsub Tag.E6 L 3 S a hT hTp ha1 i
    set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
    have hRΓ : R ≤ S.Γ := hRC.trans inf_le_left
    have hfixe : fixSub (ψ (e6InndiagConj K x)) =
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}).subgroupOf S.Γ := by
      ext y
      rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hy
        refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h1 := congrArg Subtype.val hy
        rw [hψc, hxa] at h1
        calc (y : ModGL Tag.E6 L) * rootDiagUnit Tag.E6 a =
            (rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹) * rootDiagUnit Tag.E6 a := by
              rw [h1]
          _ = rootDiagUnit Tag.E6 a * y := by group
      · rintro ⟨-, hy⟩
        apply Subtype.ext
        rw [hψc, hxa]
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy
        calc rootDiagUnit Tag.E6 a * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 a)⁻¹ =
            y * rootDiagUnit Tag.E6 a * (rootDiagUnit Tag.E6 a)⁻¹ := by rw [h1]
          _ = y := by group
    refine ⟨ψ (e6InndiagConj K x), ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_, R.subgroupOf S.Γ, hsR, ?_, ?_,
      ?_, ?_⟩
    · intro h1
      apply ha1
      rw [← hxa, ← map_one θ]
      congr 1
      exact hcinj ((ψ.injective (h1.trans (map_one ψ).symm)).trans (map_one _).symm)
    · intro y hy
      rw [hfixe, Subgroup.mem_subgroupOf]
      exact hRC hy
    · have hq : CFSG.IsQuasisimple R := by
        cases hkind : twistKind S.ρ (rootCharHom a) i
        · exact hin Tag.E6 L 3 S a hT hTp ha1 i hkind hbig'
        · exact hsu Tag.E6 L 3 S a hT hTp ha1 i hkind hbig'
        · exact htw Tag.E6 L 3 S a hT hTp ha1 i hkind hbig'
        · exact hex Tag.E6 L 3 S a hT hTp ha1 i hkind hbig'
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm hq
    · rw [hfixe]
      exact isSubnormal_subgroupOf_subgroupOf inf_le_left hRsn
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv]
  have hle := Coordinator.map_localDeltaIn_le 3 ψ.toMonoidHom ψ.injective H
    (D₀.map (e6InndiagConj K))
  rw [key, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective] at hle
  exact hle

end CFSG.HardMathSupport.Timmesfeld.CrossChar
