module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.TwoDKind
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcKind
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB

section TwE6


theorem noL34Layer_one_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    NoL34Layer (1 : MulAut ↥(twistedE6RootGroup K σ)) := by
  have hM : ChevalleyExceptionalModel ↥(twistedE6RootGroup K σ) .twistedE6 ℓ f :=
    I923.chevalleyExceptionalModel_twistedE6_of_equiv hℓ hf hK σ hσ (MulEquiv.refl _)
  obtain ⟨hnt, hs⟩ := CFSG.LieType.Simplicity.fam_2e6_simplicity _ ℓ f hM
  have hfix : fixSubgroup (1 : MulAut ↥(twistedE6RootGroup K σ)) = ⊤ := by
    ext y
    exact ⟨fun _ => trivial, fun _ => mem_fixSubgroup.2 rfl⟩
  let e : ↥(fixSubgroup (1 : MulAut ↥(twistedE6RootGroup K σ))) ≃* ↥(twistedE6RootGroup K σ) :=
    (MulEquiv.subgroupCongr hfix).trans Subgroup.topEquiv
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hnab : ∃ a b : ↥(twistedE6RootGroup K σ), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => hcon b a
    rw [hZ] at hc
    obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(twistedE6RootGroup K σ)
    have hx : x ∈ (⊥ : Subgroup ↥(twistedE6RootGroup K σ)) := hc ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup ↥(twistedE6RootGroup K σ)) := hc ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  exact noL34Layer_of_fixed_equiv _ e hs hnab
    (not_isLThreeFour_of_lieModel_odd hO hℓ2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))

theorem ssTw_not_L34_rational {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] (S : LangSetup τ L 3) (h2 : (2 : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact ssexc_not_L34_inner S h2 hT i hk
  | suN => exact ssexc_not_L34_suN S h2 hT hTp h1 i hk hq
  | twoD => exact ssexc_not_L34_twoD S h2 hT hTp h1 i hk hq
  | exc => exact ssexc_not_L34_exc S h2 hT hTp h1 i hk hq

theorem noL34Layer_inndiag_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut ↥(twistedE6RootGroup K σ))
    (hβ : β ∈ (twistedE6InndiagConj K σ).range) (hβ3 : β ^ 3 = 1) : NoL34Layer β := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ3 : ℓ ≠ 3 := by omega
  by_cases hβ1 : β = 1
  · subst hβ1
    exact noL34Layer_one_twE6 hO hℓ hℓ2 hf hK σ hσ
  obtain ⟨g, rfl⟩ := hβ
  set h : ModGL TwistTag.E6.tag K := (g : ModGL TwistTag.E6.tag K) with hh
  have hp1 : h ^ 3 = 1 := by
    have h3 : g ^ 3 = 1 :=
      twistedE6InndiagConj_injective hℓ hf hK σ hσ (by rw [map_pow, hβ3, map_one])
    have := congrArg Subtype.val h3
    simpa using this
  have hh1 : h ≠ 1 := fun h' => hβ1 (by
    have : g = 1 := Subtype.ext h'
    rw [this, map_one])
  haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f * 2) (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hq4 : 5 ≤ 3 ∨ 4 ≤ ℓ ^ f :=
    Or.inr (le_trans (by omega : 4 ≤ ℓ) (Nat.le_self_pow (by omega) ℓ))
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ Nat.prime_three (Ne.symm hℓ3)
      Nat.prime_three (Ne.symm hℓ3) hq4 monomialToralAt_E6_three (twistedE6InndiagConj K σ g) h
      g.2 (twistedE6InndiagConj_apply g) hp1 hh1
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hℓ Nat.prime_three hK (Ne.symm hℓ3)
  have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : AlgebraicClosure K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) ℓ] at this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL (fun h => absurd h (by decide)) hT
    hap h1
  haveI : Finite ↥(twistedE6RootGroup K σ) :=
    Finite.of_injective (fun x => (x : ModGL TwistTag.E6.tag K)) Subtype.val_injective
  exact noL34Layer_of_langSetup S Nat.prime_three ι hinj hrange _ hconj hT hap h1 hTame
    (fun i hq => ssTw_not_L34_rational S h2 hT hTp h1 i hq)

end TwE6

end CFSG.HardMathSupport.Dickson.Sec6
