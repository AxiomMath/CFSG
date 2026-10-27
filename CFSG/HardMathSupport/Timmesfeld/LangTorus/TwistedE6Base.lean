module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.RankThree.PartOne.KE.A1Weyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical2

namespace LangDatum

variable {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)

@[expose] noncomputable def torsion (p : ℕ) : Subgroup (ModGL τ L) where
  carrier := {x | x ∈ D.torus ⊓ D.Γ ∧ x ^ p = 1}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (torusGroup_comm ha.1.1.1 hb.1.1.1)), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_torsion {p : ℕ} {x : ModGL τ L} :
    x ∈ D.torsion p ↔ x ∈ D.torus ⊓ D.Γ ∧ x ^ p = 1 :=
  Iff.rfl

@[expose] noncomputable def toSetup [IsAlgClosed L] (p : ℕ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : FrobRootMap D ρ) (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q) (hfin : Finite D.model) :
    LangSetup τ L p where
  D := D
  ρ := ρ
  frob := hρ
  E := D.torsion p
  hp := hp
  hq := hq
  hqpow := hqpow
  hpq := hpq
  finite := hfin
  E_le := fun _ hx => hx.1
  E_exp := fun _ hx => hx.2
  E_all := fun _ hx hxp => ⟨hx, hxp⟩

theorem toSetup_D [IsAlgClosed L] (p : ℕ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : FrobRootMap D ρ) (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q) (hfin : Finite D.model) :
    (D.toSetup p ρ hρ hp hq hqpow hpq hfin).D = D :=
  rfl

theorem model_eq_fixModel : D.model = fixModel ((MulAut.conj D.n).toMonoidHom.comp D.Φ) :=
  rfl

theorem model_eq_map_fixModel :
    D.model = (fixModel D.Φ).map (MulAut.conj D.g0⁻¹).toMonoidHom := by
  rw [← map_conj_fixModel D.g0_mem D.lang, Subgroup.map_map, ← model_eq_fixModel]
  conv_lhs => rw [← Subgroup.map_id D.model]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end LangDatum

section TwistedE6

variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
  {Fr : L →+* L}

theorem model_eq_map_twistedFixedGroup (D : LangDatum TwistTag.E6.tag L)
    (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) :
    D.model = (twistedFixedGroup TwistTag.E6 L Fr).map (MulAut.conj D.g0⁻¹).toMonoidHom := by
  rw [D.model_eq_map_fixModel, hΦ]
  rfl

theorem Γ_eq_map_twistedE6RootGroup (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L] (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) :
    D.Γ = ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj D.g0⁻¹).toMonoidHom := by
  obtain ⟨-, -, hder, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  rw [LangDatum.Γ, model_eq_map_twistedFixedGroup D hΦ, ← Subgroup.map_commutator, hder]

theorem finite_model_twistedE6 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L] (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) :
    Finite D.model := by
  obtain ⟨hfin, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  have hsurj := (MulAut.conj D.g0⁻¹).toMonoidHom.subgroupMap_surjective
    (twistedFixedGroup TwistTag.E6 L Fr)
  have : Finite ((twistedFixedGroup TwistTag.E6 L Fr).map (MulAut.conj D.g0⁻¹).toMonoidHom) :=
    Finite.of_surjective _ hsurj
  rw [model_eq_map_twistedFixedGroup D hΦ]
  exact this

@[expose] noncomputable def twistedE6EquivΓ (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L]
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (D : LangDatum TwistTag.E6.tag L)
    (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) : twistedE6RootGroup K σ ≃* D.Γ :=
  (((twistedE6RootGroup K σ).equivMapOfInjective (baseChangeGL (algebraMap K L))
    (baseChangeGL_injective _)).trans
      (((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L))).equivMapOfInjective
        (MulAut.conj D.g0⁻¹).toMonoidHom (MulAut.conj D.g0⁻¹).injective)).trans
    (MulEquiv.subgroupCongr (Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ).symm)

theorem coe_twistedE6EquivΓ (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L] (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (x : twistedE6RootGroup K σ) :
    ((twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ x : D.Γ) : ModGL TwistTag.E6.tag L) =
      D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * D.g0 := by
  change MulAut.conj D.g0⁻¹ (baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)) = _
  rw [MulAut.conj_apply, inv_inv]

theorem exists_langDatum_twistedE6 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (w : WeylGroup TwistTag.E6.tag) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
      ∃ D : LangDatum TwistTag.E6.tag (AlgebraicClosure K),
        D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr ∧ D.q = ℓ ^ f ∧
          D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L w
  refine ⟨iterateFrobenius L ℓ f, fun c => iterateFrobenius_def ℓ f c,
    { Φ := twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)
      q := ℓ ^ f
      n := canonicalRep (coxeterSystem TwistTag.E6.tag) L w
      g0 := g0
      steinberg := ⟨iterateFrobenius L ℓ f, fun c => iterateFrobenius_def ℓ f c,
        diagramMap TwistTag.E6 L, Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun g => rfl⟩
      n_weyl := ⟨w, rfl⟩
      g0_mem := hg0C
      lang := hg0 }, rfl, rfl, rfl⟩

end TwistedE6

end CFSG.HardMathSupport.Timmesfeld.LangTorus
