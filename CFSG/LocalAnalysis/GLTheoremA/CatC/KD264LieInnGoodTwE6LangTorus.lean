module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.TwPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

set_option linter.unusedSectionVars false


theorem exists_perfect_le_centralizer_of_langTorus_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ ℓ ^ f)
    (hq : 5 ≤ p ∨ 4 ≤ ℓ ^ f) {A : Subgroup (twistedE6RootGroup K σ)}
    (hApow : ∀ x ∈ A, x ^ p = 1) (hAcard : Nat.card A = p ^ 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    (hbig : ∀ S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p,
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 →
      ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)), D₁ ≤ S.E →
        Nat.card D₁ = p ^ 2 → (bigComponentSet S D₁).Nonempty) :
    ∃ x ∈ A, x ≠ 1 ∧ ∃ P : Subgroup (twistedE6RootGroup K σ),
      P ≤ Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) ∧ ⁅P, P⁆ = P ∧
        p ∣ Nat.card P := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι : K →+* L := algebraMap K L with hι
  let DL : LangDatum TwistTag.E6.tag L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0
  have hΦ : DL.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr DL hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L DL
  have hqpow : IsPrimePow DL.q ∧ ((DL.q : ℕ) : L) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : L) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S : LangSetup TwistTag.E6.tag L p := DL.toSetup p ρ hρ hp hq hqpow hpq hfin
  let φ : twistedE6RootGroup K σ ≃* S.Γ := twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ
  have hφ : ∀ h : twistedE6RootGroup K σ, ((φ h : S.Γ) : ModGL TwistTag.E6.tag L) =
      g0⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * g0 :=
    fun h => coe_twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ h
  let ψ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype)
  have hψ : ∀ y : twistedE6RootGroup K σ,
      ψ y = g0⁻¹ * baseChangeGL ι (y : ModGL TwistTag.E6.tag K) * g0 := fun y => by
    change (MulAut.conj g0⁻¹) (baseChangeGL ι (y : ModGL TwistTag.E6.tag K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective ι).comp Subtype.val_injective)
  let D₁ : Subgroup (ModGL TwistTag.E6.tag L) := A.map ψ
  have hD₁card : Nat.card D₁ = p ^ 2 := by
    change Nat.card (A.map ψ) = p ^ 2
    rw [Subgroup.card_map_of_injective hψinj, hAcard]
  have hD₁T : D₁ ≤ S.D.torus := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hc x hx
    rw [hψ, ← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
    exact hy
  have hD₁Γ : D₁ ≤ S.Γ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hψ, ← hφ]
    exact (φ x).2
  have hD₁pow : ∀ x ∈ D₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hApow x hx, map_one]
  have hD₁E : D₁ ≤ S.E := fun x hx => S.E_all x ⟨hD₁T hx, hD₁Γ hx⟩ (hD₁pow x hx)
  obtain ⟨x, hxbig⟩ := hbig S rfl D₁ hD₁E hD₁card
  obtain ⟨d, hdD, hd1, R, hRle, hRq, hRnc⟩ :=
    exists_quasisimple_of_mem_bigComponentSet S hD₁E hxbig
  have hRΓ : R ≤ S.Γ := fun r hr => (Subgroup.mem_inf.1 (hRle hr)).1
  have hRcent : R ≤ Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag L)) :=
    fun r hr => (Subgroup.mem_inf.1 (hRle hr)).2
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hRq.1
    exact Subgroup.commutator_eq_self
  obtain ⟨a, haA, rfl⟩ := hdD
  have hRrange : R ≤ ψ.range := by
    intro r hr
    obtain ⟨y, hy⟩ := φ.surjective ⟨r, hRΓ hr⟩
    refine ⟨y, ?_⟩
    rw [hψ, ← hφ, hy]
  obtain ⟨P, hPcent, hPperf, hPcard⟩ :=
    exists_perfect_le_centralizer_of_injective ψ hψinj hRrange hRperf hRcent
  refine ⟨a, haA, ?_, P, hPcent, hPperf, ?_⟩
  · intro ha1
    exact hd1 (by rw [ha1, map_one])
  · rw [hPcard]
    exact (Nat.Prime.dvd_iff_not_coprime hp).2 hRnc

theorem perfectCentralizerPlanes_twistedE6_five {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : ¬ 5 ∣ ℓ ^ f) (hq5 : ℓ ^ f % 5 = 1 ∨ ℓ ^ f % 5 = 4) :
    PerfectCentralizerPlanes 5 (twistedE6RootGroup K σ) := by
  intro E hE hEcard
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hc⟩ := twistedE6_toral_five hℓ hf h5 K hK σ hσ E hE.2 hEcard
  exact exists_perfect_le_centralizer_of_langTorus_twistedE6 hℓ hf hK σ hσ Nat.prime_five h5
    (Or.inl le_rfl) hE.2 hEcard hFr hg0C hg0 hc
    (fun S hSD D₁ hD₁E hD₁c => bigComponentSet_nonempty_of_bigAnyPBig S
      (bigAnyPBig_five S (by rw [hSD]; exact hq5)) hD₁E hD₁c)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
