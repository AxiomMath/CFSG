module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Rigid
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Abstract
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDProved
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SubnormalTorus

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem balance_of_setup {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup .E6 L 3)
    (hq4 : 4 ≤ S.D.q) (hnf : NormalFormAt S) (hfaith : FaithfulAt S)
    {C : Type} [Group C] (φ : C ≃* S.Γ)
    (hCc : Function.Injective (MulAut.conj : C →* MulAut C))
    {Ĉ : Type} [Group Ĉ] (cj : Ĉ →* MulAut C) (hcj : Function.Injective cj)
    (θ : Ĉ →* ModGL Tag.E6 L)
    (hθ : ∀ (x : Ĉ) (y : S.Γ),
      ((MulAut.congr φ (cj x) y : S.Γ) : ModGL Tag.E6 L) = θ x * y * (θ x)⁻¹)
    (a b : Fin Tag.E6.rank → Lˣ) {w : WeylGroup Tag.E6}
    (ha3 : ∀ i, a i ^ 3 = 1) (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    {u : ModGL Tag.E6 L} (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (g₁ g₂ : Ĉ) (hg₁ : θ g₁ = rootDiagUnit Tag.E6 a)
    (hg₂ : θ g₂ = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (D : Subgroup (MulAut C)) (hD₁ : cj g₁ ∈ D) (hD₂ : cj g₂ ∈ D)
    (H : Subgroup (MulAut C)) (hH : innerAut C ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  set ψ : MulAut C ≃* MulAut S.Γ := MulAut.congr φ with hψdef
  have hψconj : ∀ g : C, ψ (MulAut.conj g) = MulAut.conj (φ g) := fun g =>
    MulEquiv.ext fun y => by
      simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have hinjΓ : Function.Injective (MulAut.conj : S.Γ →* MulAut S.Γ) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv φ.symm hCc
  have := S.finite_Γ
  have hH' : innerAut S.Γ ≤ H.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (φ.symm y), hH ⟨φ.symm y, rfl⟩, ?_⟩
    change ψ (MulAut.conj (φ.symm y)) = MulAut.conj y
    rw [hψconj, MulEquiv.apply_symm_apply]
  have ha1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro h1
    apply hsh
    have : a = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    subst this
    simp [rootChar]
  have hd3 : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun i => by simpa using ha3 i
    rw [this, rootDiagUnit_one]
  have hE' : D.map ψ.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hmem : ψ (cj g₁) ∈ D.map ψ.toMonoidHom := ⟨_, hD₁, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one ψ] at hmem
    apply ha1
    rw [← hg₁, ← map_one θ]
    congr 1
    exact hcj ((ψ.injective hmem).trans (map_one _).symm)
  have key : localDeltaIn 3 (H.map ψ.toMonoidHom) (D.map ψ.toMonoidHom) = ⊥ := by
    refine localDeltaIn_eq_bot_of_aut_components_rigid_comm Nat.prime_three hinjΓ hH' hE'
      (S := {s : S.Γ | (s : ModGL Tag.E6 L) ∈
        bigComponentSet S (Subgroup.zpowers (rootDiagUnit Tag.E6 a))}) ?_ ?_
    · intro δ _ hδp hδE hδfix
      exact rigid_single_gen anyKindCommuteT_holds threeBigComponents_holds S hnf hfaith hq4 a b
        ha3 hw hsh hT hu (θ g₂) hg₂ (ψ (cj g₁)) (ψ (cj g₂)) (fun y => by rw [hθ, hg₁])
        (fun y => hθ g₂ y) δ hδp (hδE _ ⟨_, hD₁, rfl⟩) (hδE _ ⟨_, hD₂, rfl⟩) hδfix
    · rintro s ⟨a', haD, ha1', i, hbig', hsR⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 haD
      set x : Ĉ := g₁ ^ k with hxdef
      have hxD : cj x ∈ D := by
        rw [hxdef, map_zpow]
        exact zpow_mem hD₁ k
      have hxa : θ x = rootDiagUnit Tag.E6 a' := by
        rw [hxdef, map_zpow, hg₁, hk]
      have hT' : rootDiagUnit Tag.E6 a' ∈ S.D.torus := by
        rw [← hk]
        exact zpow_mem hT k
      have hTp : rootDiagUnit Tag.E6 a' ^ 3 = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
      obtain ⟨hRC, hRsn⟩ := langSubnormal_provedT Tag.E6 L 3 S a' hT' hTp ha1' i
      set R := rationalComponent S.ρ S.Γ (rootCharHom a') i with hRdef
      have hRΓ : R ≤ S.Γ := hRC.trans inf_le_left
      have hfixe : fixSub (ψ (cj x)) =
          (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a'}).subgroupOf S.Γ := by
        ext y
        rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · intro hy
          refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          have h1 := congrArg Subtype.val hy
          rw [hθ, hxa] at h1
          calc (y : ModGL Tag.E6 L) * rootDiagUnit Tag.E6 a' =
              (rootDiagUnit Tag.E6 a' * y * (rootDiagUnit Tag.E6 a')⁻¹) *
                rootDiagUnit Tag.E6 a' := by rw [h1]
            _ = rootDiagUnit Tag.E6 a' * y := by group
        · rintro ⟨-, hy⟩
          apply Subtype.ext
          rw [hθ, hxa]
          have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy
          calc rootDiagUnit Tag.E6 a' * (y : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 a')⁻¹ =
              y * rootDiagUnit Tag.E6 a' * (rootDiagUnit Tag.E6 a')⁻¹ := by rw [h1]
            _ = y := by group
      refine ⟨ψ (cj x), ⟨_, hxD, rfl⟩, ?_, R.subgroupOf S.Γ, hsR, ?_, ?_, ?_, ?_⟩
      · intro h1
        apply ha1'
        rw [← hxa, ← map_one θ]
        congr 1
        exact hcj ((ψ.injective (h1.trans (map_one ψ).symm)).trans (map_one _).symm)
      · intro y hy
        rw [hfixe, Subgroup.mem_subgroupOf]
        exact hRC hy
      · have hq : CFSG.IsQuasisimple R := by
          cases hkind : twistKind S.ρ (rootCharHom a') i
          · exact langComponentsQuasisimple_inner_holdsT Tag.E6 L 3 S a' hT' hTp ha1' i hkind hbig'
          · exact langComponentsQuasisimpleT_suN_proved Tag.E6 L 3 S a' hT' hTp ha1' i hkind hbig'
          · exact langComponentsQuasisimpleT_twoD_proved Tag.E6 L 3 S a' hT' hTp ha1' i hkind hbig'
          · exact langComponentsQuasisimple_exc_provedT Tag.E6 L 3 S a' hT' hTp ha1' i hkind hbig'
        exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm hq
      · rw [hfixe]
        exact isSubnormal_subgroupOf_subgroupOf inf_le_left hRsn
      · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv]
  have hle := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le 3 ψ.toMonoidHom
    ψ.injective H D
  rw [key, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective] at hle
  exact hle

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
