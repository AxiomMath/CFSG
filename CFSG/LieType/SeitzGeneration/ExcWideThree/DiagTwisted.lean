module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Twisted


@[expose] def twPlanePre (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype

@[expose] def TwE6NormalizesR (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) : Prop :=
  ∃ R : Subgroup (twistedE6RootGroup K σ), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
    ∀ ε ∈ E, R.map ε.toMonoidHom = R

structure TwLangData (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (A : Subgroup (ModGL TwistTag.E6.tag K)) where
  v : WeylGroup TwistTag.E6.tag
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ q
  g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
  hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
    g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v
  c : ModGL TwistTag.E6.tag K
  hcI : c ∈ twistedE6InndiagGL K σ
  hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (c * x * c⁻¹ : ModGL TwistTag.E6.tag K) ∈
    (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom

@[expose] def TwE6InndiagTorality : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
      (∃ D : TwLangData K σ q (twPlanePre K σ E), ∃ x ∈ twPlanePre K σ E,
          x ∉ twistedE6RootGroup K σ) ∨ TwE6NormalizesR K σ E

@[expose] def TwE6DiagRegularGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ D : TwLangData K σ q (twPlanePre K σ E),
        (¬ ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧
          ∀ x ∈ twPlanePre K σ E, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
            rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
              baseChangeGL (algebraMap K (AlgebraicClosure K))
                (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1) →
        Subgroup.closure (fixUnion E) = ⊤

@[expose] def TwE6KillRoot : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ (A : Subgroup (ModGL TwistTag.E6.tag K)) (D : TwLangData K σ q A)
      (α : Fin TwistTag.E6.tag.rank → ℤ), IsRoot TwistTag.E6.tag α →
      (∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1) →
      ∃ u : ModGL TwistTag.E6.tag K, u ∈ twistedE6RootGroup K σ ∧ u ≠ 1 ∧
        (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ ∀ x ∈ A, Commute u x

@[expose] def TwE6InndiagParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ¬ E ≤ innerAut (twistedE6RootGroup K σ) → TwE6NormalizesR K σ E →
      Subgroup.closure (fixUnion E) = ⊤

theorem ringChar_eq_of_card_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * f)) : ringChar K = ℓ := by
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have h1 : ringChar K ∣ ℓ ^ (2 * f) := by
    rw [← hK, hcard]
    exact dvd_pow_self _ (by omega)
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h1)

theorem twistedTorus_le {τ : Tag} {L : Type} [Field L] (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) :
    twistedTorusOf n Φ ≤ torusGroup τ L :=
  fun _ h => (Subgroup.mem_inf.1 h).1

theorem mem_twPlanePre_iff (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (x : ModGL TwistTag.E6.tag K) :
    x ∈ twPlanePre K σ E ↔
      ∃ g : ↥(twistedE6InndiagGL K σ), (g : ModGL TwistTag.E6.tag K) = x ∧
        twistedE6InndiagConj K σ g ∈ E := by
  unfold twPlanePre
  constructor
  · intro h
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 h
    exact ⟨g, hgx, Subgroup.mem_comap.1 hg⟩
  · rintro ⟨g, rfl, hg⟩
    exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_comap.2 hg, rfl⟩

theorem card_twPlanePre (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Nat.card (twPlanePre K σ E) = Nat.card E := by
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hEle : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hE
  have h1 := Nat.card_congr
    (Subgroup.equivMapOfInjective (E.comap (twistedE6InndiagConj K σ)) (twistedE6InndiagConj K σ) hinj).toEquiv
  rw [Subgroup.map_comap_eq, inf_eq_right.2 hEle] at h1
  unfold twPlanePre
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact h1

theorem pow_three_eq_one_of_mem_twPlanePre (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) [CFSG.IsElementaryAbelian 3 E]
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twPlanePre K σ E) : x ^ 3 = 1 := by
  obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ E x).1 hx
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have h3 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := E) (twistedE6InndiagConj K σ g) hg
  have hg3 : g ^ 3 = 1 := hinj (h3.trans (map_one _).symm)
  have := congrArg Subtype.val hg3
  simpa using this

theorem twistedE6ThreeDiagPlanes_of_open (hT : TwE6InndiagTorality) (hO : TwE6DiagRegularGen)
    (hKR : TwE6KillRoot) (hP : TwE6InndiagParabolic) : TwistedE6ThreeDiagPlanes := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hEab hcard hE hnin
  have hp : ringChar K = ℓ := ringChar_eq_of_card_pow hℓ hf K hK
  have hK3 : ringChar K ≠ 3 := by
    rw [hp]
    exact hℓ3
  have hK' : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [hK, ← pow_mul, mul_comm]
  rcases hT K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin with ⟨D, x, hxA, hxout⟩ | hnorm
  · by_cases hkillex : ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧
        ∀ x ∈ twPlanePre K σ E, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1
    swap
    · exact hO K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin D hkillex
    obtain ⟨α, hα, hkill⟩ := hkillex
    obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
      hKR K σ (ℓ ^ f) hK3 hσ hK' (twPlanePre K σ E) D α hα hkill
    set U : twistedE6RootGroup K σ := ⟨u, hu⟩ with hUdef
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
    refine hP K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin ⟨Subgroup.zpowers U, ?_, hRp, ?_⟩
    · exact fun h => hU1 (Subgroup.zpowers_eq_bot.1 h)
    · intro ε hεE
      have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
        rw [range_twistedE6InndiagConj]
        exact hE hεE
      obtain ⟨g, rfl⟩ := hεr
      have hgA : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
        (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hεE⟩
      have hfix : twistedE6InndiagConj K σ g U = U := by
        apply Subtype.ext
        rw [twistedE6InndiagConj_apply]
        show (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
        rw [mul_inv_eq_iff_eq_mul]
        exact (hcomm _ hgA).symm
      have hfix' : (twistedE6InndiagConj K σ g).toMonoidHom U = U := hfix
      rw [MonoidHom.map_zpowers, hfix']
  · exact hP K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin hnorm

end Twisted

end CFSG.LieType.SeitzGeneration.ExcWideThree
