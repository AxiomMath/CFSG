module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Residual

@[expose] def ExcRationalLieTypesP (p : ℕ) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

end Residual

theorem lieCompsExport_of_langSetupP {p : ℕ} (hres : ExcRationalLieTypesP p) (hp : p.Prime)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type}
    [Group C] [Finite C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hlayer : PerfectInLayer β) {ℓ : ℕ} (hℓ : ringChar L = ℓ) : LieCompsExport ℓ β := by
  classical
  have hdata : ∀ {K : Subgroup C}, IsComponentOf K (fixSubgroup β) →
      ∃ (R : Subgroup (ModGL τ L)) (eK : ↥K ≃* ↥R), CFSG.IsQuasisimple ↥R ∧ LieCompData ℓ ↥R := by
    intro K hK
    obtain ⟨i, hq, hKR⟩ := components_of_langSetup S hp ι hι hrange β hβ hT hap h1 hTame hK
    refine ⟨rationalComponent S.ρ S.Γ (rootCharHom a) i,
      (K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKR), hq, ?_⟩
    have := hres τ L p₀ S a hT hap h1 i hq
    rwa [hℓ] at this
  refine ⟨hlayer, fun K hK => ?_⟩
  obtain ⟨R, eK, hq, hty⟩ := hdata hK
  haveI : Finite ↥K := Subtype.finite
  haveI : Finite ↥R := Finite.of_equiv _ eK.toEquiv
  refine ⟨↥R, inferInstance, inferInstance, ⟨hq.1.commutator_eq_top, hty.chev, hty.centre⟩,
    eK.symm.toMonoidHom, eK.symm.surjective, ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have : x = 1 := eK.symm.injective (by simpa using hx)
  rw [this]
  exact one_mem _

theorem lieCompsExport_inner_untwP {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : ExcRationalLieTypesP p) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) (hpK : ¬ p ∣ Nat.card K)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hlayer : PerfectInLayer β) {ℓ : ℕ} (hℓ : ringChar K = ℓ) : LieCompsExport ℓ β := by
  classical
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h | h
    · subst h
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (hG2 rfl)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h])
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp (by omega)
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by rw [ringChar_algebraicClosure, hℓ]
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK (Or.inl hp5) hmon hperf β h hhL hβ hp1 hh1
  exact lieCompsExport_of_langSetupP hres hp S ι hinj hrange β hconj hT hap h1
    (langSetup_hTame S hT hap h1) hlayer hAC

theorem lieCompsExport_inner_twE6P {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hres : ExcRationalLieTypesP p) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hpℓ : p ≠ ℓ) (hmon : MonomialToralAt Tag.E6 p)
    (h : ↥(twistedE6InndiagGL K σ)) (hp1 : h ^ p = 1) (hh1 : h ≠ 1)
    (hlayer : PerfectInLayer (twistedE6InndiagConj K σ h)) :
    LieCompsExport ℓ (twistedE6InndiagConj K σ h) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := f * 2) hℓ (by omega) (by rw [hK, ← pow_mul])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀
      hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  exact lieCompsExport_of_langSetupP hres hp S ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
      (fun h => absurd h (by decide)) hT hap h1) hlayer hAC

theorem lieCompsExport_inner_triD4P {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hres : ExcRationalLieTypesP p) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hpℓ : p ≠ ℓ) (hmon : MonomialToralAt Tag.D4 p)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hlayer : PerfectInLayer (MulAut.conj x)) : LieCompsExport ℓ (MulAut.conj x) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := f * 3) hℓ (by omega) (by rw [hK, ← pow_mul])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀
      hmon x hxp hx1
  exact lieCompsExport_of_langSetupP hres hp S ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
      (fun h => absurd h (by decide)) hT hap h1) hlayer hAC

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
