module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open Module QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two
  CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

private theorem glaPLayer_ne_bot_of_factor {a : ↥(orthDerived Q)} {J₀ : Subgroup (V ≃ₗ[F] V)}
    (hJΩ : J₀ ≤ orthDerived Q) (hJc : J₀ ≤ isometryCentralizer Q (a : V ≃ₗ[F] V))
    (hJn : ∀ g ∈ isometryCentralizer Q (a : V ≃ₗ[F] V), ∀ f ∈ J₀, g * f * g⁻¹ ∈ J₀)
    (hq : CFSG.IsQuasisimple ↥J₀) (hN : NoNormalPPrime 3 J₀) :
    GLAPLayer 3 (Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) ≠ ⊥ := by
  set C := Subgroup.centralizer ({a} : Set ↥(orthDerived Q))
  set J : Subgroup ↥(orthDerived Q) := J₀.subgroupOf (orthDerived Q)
  have hne : J₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨u, w, huw⟩ := hq.2.2
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : ∀ z : ↥J₀, z = 1 := fun z =>
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot _ z.2)
    exact huw (by rw [h1 u, h1 w])
  have h3 : 3 ∣ Nat.card ↥J₀ := by
    by_contra hnd
    exact hne (hN J₀ le_rfl (fun y hy x hx => J₀.mul_mem (J₀.mul_mem hy hx) (J₀.inv_mem hy))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd))
  have hCiso : ∀ g ∈ C, (g : V ≃ₗ[F] V) ∈ isometryCentralizer Q (a : V ≃ₗ[F] V) := fun g hg =>
    Subgroup.mem_inf.mpr ⟨KCOrthogonal.orthDerived_le_orthogonalGroup g.2,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))⟩
  have hJC : J ≤ C := fun j hj => Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hJc (Subgroup.mem_subgroupOf.mp hj))).2))
  have hJn' : (J.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
    exact hJn _ (hCiso _ g.2) _ hn⟩
  let e : ↥J ≃* ↥J₀ := Subgroup.subgroupOfEquivOfLe hJΩ
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq))
  have hcomp : GLAPComponent 3 C J :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hJq
      (by rwa [Nat.card_congr e.toEquiv]) hJC hJn'
  intro hL
  have hle : J ≤ GLAPLayer 3 C := le_sSup hcomp
  rw [hL, le_bot_iff] at hle
  refine hne ((Subgroup.eq_bot_iff_forall _).2 fun f hf => ?_)
  have h1 := (Subgroup.eq_bot_iff_forall _).1 hle ⟨f, hJΩ hf⟩ (Subgroup.mem_subgroupOf.2 hf)
  exact congrArg Subtype.val h1

theorem glaPLayer_ne_bot_of_orth_three (hF : Nat.card F = 2) (hQ : (polarBilin Q).Nondegenerate)
    {a : ↥(orthDerived Q)} (ha : a ^ 3 = 1)
    (hdim : 6 ≤ finrank F ↥(fixedSpace (a : V ≃ₗ[F] V)) ∨
      finrank F ↥(fixedSpace (a : V ≃ₗ[F] V)) + 8 ≤ finrank F V) :
    GLAPLayer 3 (Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) ≠ ⊥ := by
  haveI := charP_two hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    rw [show ((3 : ℕ) : F) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  have hx : OddOrderIsometry Q 3 (a : V ≃ₗ[F] V) :=
    ⟨KCOrthogonal.orthDerived_le_orthogonalGroup a.2, by simpa using congrArg Subtype.val ha, h3,
      fun v hv => hQ.1 v hv⟩
  rcases hdim with h6 | h8
  · exact glaPLayer_ne_bot_of_factor hx.supportedFixedDerived_le_orthDerived
      supportedFixedDerived_le_isometryCentralizer
      (fun g hg f hf => hx.conj_mem_supportedFixedDerived hg hf)
      (isQuasisimple_supportedFixedDerived_of_six_le hx h2 h6)
      (noNormalPPrime_supportedFixedDerived hF hx hQ h6)
  · haveI : Fact (Irreducible (cyc3 F)) := ⟨irreducible_cyc3 hF⟩
    have hc := Submodule.finrank_add_eq_of_isCompl (isCompl_fixedSpace_cyc3 hF hx)
    have hm := finrank_cyc3 (x := (a : V ≃ₗ[F] V)) hF
    have hm4 : 4 ≤ primaryMultiplicity (a : V ≃ₗ[F] V).toLinearMap (cyc3 F) := by omega
    have hh := cyc3_mem_primaryFactors (x := (a : V ≃ₗ[F] V)) hF (by omega)
    obtain ⟨k, hk⟩ := hx.even_finrank_fixed
    have hT := exists_threeSingular_of_dim Q hQ
      (m := k + primaryMultiplicity (a : V ≃ₗ[F] V).toLinearMap (cyc3 F)) (by omega) (by omega)
    exact glaPLayer_ne_bot_of_factor (specialBlock_le_orthDerived hF hx hQ hT hh)
      (specialBlock_le_isometryCentralizer _) (fun g hg f hf => conj_mem_specialBlock hg hf)
      (orth2_isQuasisimple_specialBlock_selfDual hx (by decide) hh (cyc3_ne_X_sub_one F)
        (reciprocal_cyc3 F).symm hm4)
      (noNormalPPrime_specialBlock_cyc3 hF hx hh)

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
