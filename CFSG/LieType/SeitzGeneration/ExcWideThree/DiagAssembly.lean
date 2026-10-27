module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagKill
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Assembly


@[expose] def e6PlanePre (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Subgroup (ModGL Tag.E6 K) :=
  (E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype

@[expose] def E6NormalizesR (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
    ∀ ε ∈ E, R.map ε.toMonoidHom = R

@[expose] def E6InndiagTorality : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K →
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (adjointGroup Tag.E6 K) →
      (∃ D : LangGLData Tag.E6 K (e6PlanePre K E), ∃ x ∈ e6PlanePre K E,
          x ∉ adjointGroup Tag.E6 K) ∨ E6NormalizesR K E

@[expose] def E6DiagRegularOuter : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K →
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∀ D : LangGLData Tag.E6 K (e6PlanePre K E),
        (¬ ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ D.Kills α) →
        (∃ x ∈ e6PlanePre K E, x ∉ adjointGroup Tag.E6 K) → E6NormalizesR K E

@[expose] def E6InndiagParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K →
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (adjointGroup Tag.E6 K) →
      E6NormalizesR K E → Subgroup.closure (fixUnion E) = ⊤

theorem not_three_dvd_card_of_ringChar (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3) :
    ¬ 3 ∣ Nat.card K := by
  obtain ⟨e, -, hcard⟩ := card_eq_pow_ringChar K
  intro h
  rw [hcard] at h
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem four_le_card_of_not_innerAut (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (hnin : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) : 4 ≤ Nat.card K := by
  by_contra h
  push Not at h
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hp2 := hp.two_le
  have he1 : e = 1 := by
    by_contra hne
    have he2 : 2 ≤ e := by omega
    have h4 : ringChar K ^ 2 ≤ ringChar K ^ e := Nat.pow_le_pow_right (by omega) he2
    have h5 : 4 ≤ ringChar K ^ 2 := by nlinarith
    omega
  subst he1
  rw [pow_one] at hcard
  have h23 : ringChar K = 2 := by
    have hle : ringChar K ≤ 3 := by omega
    rcases (show ringChar K = 2 ∨ ringChar K = 3 by omega) with h2 | h3
    · exact h2
    · exact absurd h3 hK3
  have hK2 : Nat.card K = 2 := by rw [hcard, h23]
  have hinn := e6Inndiag_eq_innerAut_of_not_dvd K (by rw [hK2]; norm_num)
  rw [hinn] at hE
  exact hnin hE

theorem exists_primCubeRoot (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3) :
    ∃ ω : (AlgebraicClosure K)ˣ, IsPrimitiveRoot (ω : AlgebraicClosure K) 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_three_ne_zero_of_not_dvd (K := K) (not_three_dvd_card_of_ringChar K hK3)
  haveI : NeZero ((3 : ℕ) : AlgebraicClosure K) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  exact ⟨hζu.unit, by rw [IsUnit.unit_spec]; exact hζ⟩

theorem mem_e6PlanePre_iff (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (x : ModGL Tag.E6 K) :
    x ∈ e6PlanePre K E ↔
      ∃ g : ↥(e6InndiagGL K), (g : ModGL Tag.E6 K) = x ∧ e6InndiagConj K g ∈ E := by
  unfold e6PlanePre
  constructor
  · intro h
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 h
    exact ⟨g, hgx, Subgroup.mem_comap.1 hg⟩
  · rintro ⟨g, rfl, hg⟩
    exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_comap.2 hg, rfl⟩

theorem card_e6PlanePre (K : Type) [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K) :
    Nat.card (e6PlanePre K E) = Nat.card E := by
  have hinj := e6InndiagConj_injective K hK4
  have hEle : E ≤ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hE
  have h1 := Nat.card_congr
    (Subgroup.equivMapOfInjective (E.comap (e6InndiagConj K)) (e6InndiagConj K) hinj).toEquiv
  rw [Subgroup.map_comap_eq, inf_eq_right.2 hEle] at h1
  unfold e6PlanePre
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact h1

theorem pow_three_eq_one_of_mem_e6PlanePre (K : Type) [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) [CFSG.IsElementaryAbelian 3 E]
    {x : ModGL Tag.E6 K} (hx : x ∈ e6PlanePre K E) : x ^ 3 = 1 := by
  obtain ⟨g, rfl, hg⟩ := (mem_e6PlanePre_iff K E x).1 hx
  have hinj := e6InndiagConj_injective K hK4
  have h3 : e6InndiagConj K (g ^ 3) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := E) (e6InndiagConj K g) hg
  have hg3 : g ^ 3 = 1 := hinj (h3.trans (map_one _).symm)
  have := congrArg Subtype.val hg3
  simpa using this

theorem e6ThreeDiagPlanes_of_open (hT : E6InndiagTorality) (hO : E6DiagRegularOuter)
    (hP : E6InndiagParabolic) : E6ThreeDiagPlanes := by
  intro K _ _ hK3 E hEab hcard hE hnin
  rcases hT K hK3 E hE hEab hcard hnin with ⟨D, x, hxA, hxout⟩ | hnorm
  · by_cases hkillex : ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ D.Kills α
    · obtain ⟨α, hα, hkill⟩ := hkillex
      obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
        kill_root_gl_E6 K hK3 (e6PlanePre K E) D α hα hkill
      set U : adjointGroup Tag.E6 K := ⟨u, hu⟩ with hUdef
      have hU1 : U ≠ 1 := by
        intro h
        apply hu1
        have := congrArg Subtype.val h
        simpa [hUdef] using this
      have hUn : U ^ (ringChar K ^ n) = 1 := by
        apply Subtype.ext
        simpa [hUdef] using hn
      have hRp : IsPGroup (ringChar K) (Subgroup.zpowers U) := by
        intro g
        refine ⟨n, Subtype.ext ?_⟩
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hUn, one_zpow]
      refine hP K hK3 E hE hEab hcard hnin ⟨Subgroup.zpowers U, ?_, hRp, ?_⟩
      · exact fun h => hU1 (Subgroup.zpowers_eq_bot.1 h)
      · intro ε hεE
        have hεr : ε ∈ (e6InndiagConj K).range := by
          rw [range_e6InndiagConj]
          exact hE hεE
        obtain ⟨g, rfl⟩ := hεr
        have hgA : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E :=
          (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hεE⟩
        have hfix : e6InndiagConj K g U = U := by
          apply Subtype.ext
          rw [e6InndiagConj_apply]
          show (g : ModGL Tag.E6 K) * u * (g : ModGL Tag.E6 K)⁻¹ = u
          rw [mul_inv_eq_iff_eq_mul]
          exact (hcomm _ hgA).symm
        have hfix' : (e6InndiagConj K g).toMonoidHom U = U := hfix
        rw [MonoidHom.map_zpowers, hfix']
    · exact hP K hK3 E hE hEab hcard hnin (hO K hK3 E hE hEab hcard D hkillex ⟨x, hxA, hxout⟩)
  · exact hP K hK3 E hE hEab hcard hnin hnorm

end Assembly

end CFSG.LieType.SeitzGeneration.ExcWideThree
