module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)

set_option linter.unusedSectionVars false

section LangSetup


theorem noA6_of_langSetup (hres : ExcRationalLieTypes) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ComponentsNoA6 β := by
  classical
  intro K hK
  obtain ⟨i, hq, hKR⟩ :=
    components_of_langSetup S Nat.prime_three ι hι hrange β hβ hT hap h1 hTame hK
  have hty := (hres τ L p₀ S a hT hap h1 i hq).2
  let eK : ↥K ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKR)
  let g : (↥K ⧸ Subgroup.center ↥K) ≃*
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
    QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  exact ⟨fun e => hty.false (g.symm.trans e)⟩

end LangSetup

section Untwisted


theorem noA6_inner_untw (hres : ExcRationalLieTypes) {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    ComponentsNoA6 β := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr (Or.inr hτ)
  have hτne : τ ≠ .G2 := by rcases hτ with h | h | h <;> simp [h]
  have hpK : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  have h5K : ¬ 5 ∣ Nat.card K := by rw [hK]; norm_num
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with h | h | h <;> simp [h])
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three hpK Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf β h hhL hβ hp1 hh1
  exact noA6_of_langSetup hres S ι hinj hrange β hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three
      (natCast_ne_zero_algebraicClosure Nat.prime_three hpK)
      (fun hG2 => absurd hG2 hτne) hT hap h1)

end Untwisted

section Twisted


theorem noA6_inner_twE6 (hres : ExcRationalLieTypes) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hpℓ : 3 ≠ ℓ) (hmon : MonomialToralAt Tag.E6 3)
    (h : ↥(twistedE6InndiagGL K σ)) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    ComponentsNoA6 (twistedE6InndiagConj K σ h) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf Nat.prime_three (by norm_num) hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  exact noA6_of_langSetup hres S ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three
      (natCast_ne_zero_algebraicClosure_of_ne hℓ Nat.prime_three hK hpℓ)
      (fun h => absurd h (by decide)) hT hap h1)

end Twisted

section FinalUntwisted


theorem noA6_untw_even (hres : ExcRationalLieTypes) {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {S : Type} [Group S] (e : S ≃* ↥(adjointGroup τ K)) {α : MulAut S}
    (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) : ComponentsNoA6 α := by
  refine ComponentsNoA6.of_congr e ?_
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E hτ
      Nat.prime_three _ ((mem_innAutDerived_congr e).2 hα) hβ3 hβ1
  exact noA6_inner_untw hres hτ hK _ h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1
    hh1

theorem noA6_of_bridge_even {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeEven τ c) (hres : ExcRationalLieTypes)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hp : q.p = 2) (hq : q.card = 2) {S : Type}
    [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) {α : MulAut S}
    (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) : ComponentsNoA6 α := by
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨eB⟩ := hB q hv hp (GaloisField 2 1) (by rw [hK, hq])
  have hZ : Subgroup.center ↥(adjointGroup τ (GaloisField 2 1)) = ⊥ :=
    center_adjointGroup_eq_bot
  let e' : S ≃* ↥(adjointGroup τ (GaloisField 2 1)) :=
    e.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  exact noA6_untw_even hres hτ hK e' hα hα3 hα1

theorem i1430InnNoE_proved (hL : LieSemisimpleCent) (hres : ExcRationalLieTypes) :
    I1430InnNoE := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨q, hq⟩ hc hf ⟨e⟩ α hα hα3 hα1
  have hlayer : PerfectInLayer α :=
    hL S hS hnc ⟨d, hv⟩ ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (by show (3 : ℕ) ≠ d.characteristic; rw [hc]; norm_num) α hα3 hα1
  refine not_compOfType_isA6 hlayer ?_
  rcases hq with rfl | rfl | rfl
  · exact noA6_of_bridge_even (Or.inl rfl) CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 hres q
      hv (by simpa using hc) hf e hα hα3 hα1
  · exact noA6_of_bridge_even (Or.inr (Or.inl rfl))
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 hres q hv (by simpa using hc) hf e hα hα3 hα1
  · exact noA6_of_bridge_even (Or.inr (Or.inr rfl))
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 hres q hv (by simpa using hc) hf e hα hα3 hα1

end FinalUntwisted

section FinalTwisted


theorem noA6_twE6 (hres : ExcRationalLieTypes) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : 3 ≠ q.p) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) {α : MulAut S}
    (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) : ComponentsNoA6 α := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  refine ComponentsNoA6.of_congr e' ?_
  have hβmem : MulAut.congr e' α ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    (mem_innAutDerived_congr e').2 hα
  have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
      hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hmem : MulAut.congr e' α ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβmem
  obtain ⟨h, hh⟩ := hmem
  have hp1 : h ^ 3 = 1 :=
    twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
      (by rw [map_pow, hh, hβ3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [← hh, h', map_one])
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_three (by norm_num)
  rw [← hh]
  exact noA6_inner_twE6 hres q.prime_p q.exponent_pos hK σ hσ hq3 hmon h hp1 hh1

theorem i1430InnNoTwistedE6_proved (hL : LieSemisimpleCent) (hres : ExcRationalLieTypes) :
    I1430InnNoTwistedE6 := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α hα hα3 hα1
  have hp : q.p = 2 := by simpa using hc
  have hlayer : PerfectInLayer α :=
    hL S hS hnc ⟨_, hv⟩ ⟨e⟩ 3 Nat.prime_three (by norm_num) (by simp [hp]) α hα3 hα1
  exact not_compOfType_isA6 hlayer (noA6_twE6 hres q hv (by omega) e hα hα3 hα1)

end FinalTwisted

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
