module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcPlumbAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.HardMathSupport.Dickson.Sec6 (FamF4 FamE6 FamTwE6 FamE7 FamE8)
open CFSG.StandardType.RecipeExcLang (inndiagGroup)

section Hom


theorem l3u3Plumb_mem_range_twistedE6InndiagConj {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβ : β ∈ innAutDerived ↥(twistedE6RootGroup K σ)) :
    β ∈ (twistedE6InndiagConj K σ).range := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  have hKf : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  rw [range_twistedE6InndiagConj, ← hker]
  exact hΘ hβ

end Hom

section Twisted


theorem not_l3u3Pumpup_twE6 (hres : ∀ k, Char2L3U3 Tag.E6 k) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq2 : q.p = 2) {S : Type} [Group S]
    [Finite S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) {β : MulAut S}
    (hβ : β ∈ innAutDerived S) : ¬ L3U3Pumpup S β := by
  intro hp
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  have hp' := hp.of_congr e'
  obtain ⟨hβ3, hβ1, hno⟩ := (l3u3Pumpup_iff _).1 hp'
  obtain ⟨h, hh⟩ := l3u3Plumb_mem_range_twistedE6InndiagConj q.prime_p q.exponent_pos hK σ hσ
    ((mem_innAutDerived_congr e').2 hβ)
  have hp1 : h ^ 3 = 1 :=
    twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
      (by rw [map_pow, hh, hβ3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [← hh, h', map_one])
  rw [hq2] at hK hσ
  refine hno ?_
  rw [← hh]
  exact noL3U3Layer_inndiag_twE6_two hres q.exponent_pos hK σ hσ _ (h : ModGL TwistTag.E6.tag K) h.2
    (fun c => twistedE6InndiagConj_apply h c) (by rw [← Subgroup.coe_pow, hp1]; rfl)
    (fun h' => hh1 (Subtype.ext h'))

end Twisted

section Untwisted


theorem not_l3u3Pumpup_of_equiv_adjoint {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hres : ∀ k, Char2L3U3 τ k) {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (θ : S ≃* ↥(adjointGroup τ F)) {β : MulAut S}
    (hβ : β ∈ innAutDerived S) : ¬ L3U3Pumpup S β := by
  intro hp
  have hp' := hp.of_congr θ
  obtain ⟨hy3, hy1, hno⟩ := (l3u3Pumpup_iff _).1 hp'
  have hmem : MulAut.congr θ β ∈ innAutDerived ↥(adjointGroup τ F) :=
    (mem_innAutDerived_congr θ).2 hβ
  obtain ⟨h, hh, hβh, hp1, hh1⟩ : ∃ h ∈ inndiagGroup τ F,
      (∀ c : adjointGroup τ F, ((MulAut.congr θ β) c : ModGL τ F) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧
        h ≠ 1 := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_F4
        _ hmem hy3 hy1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inl rfl) Nat.prime_three _ hmem hy3 hy1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inr (Or.inl rfl)) Nat.prime_three _ hmem hy3 hy1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inr (Or.inr rfl)) Nat.prime_three _ hmem hy3 hy1
  exact hno (noL3U3Layer_exc_inner_untw_two hτ hres hf hF _ h
    (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1)

theorem not_l3u3Pumpup_untw {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hres : ∀ k, Char2L3U3 τ k)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hq2 : q.p = 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) {β : MulAut S}
    (hβ : β ∈ innAutDerived S) : ¬ L3U3Pumpup S β := by
  obtain ⟨F, _, _, hF, -, ⟨θ⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  rw [TauCeti.PrimePower.card_def, hq2] at hF
  exact not_l3u3Pumpup_of_equiv_adjoint hτ hres q.exponent_pos hF (e.trans θ) hβ

theorem not_l3u3Pumpup_exc
    (hres : ∀ τ : Tag, (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ k, Char2L3U3 τ k)
    {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex)
    (hd : FamF4 d.1 ∨ FamE6 d.1 ∨ FamTwE6 d.1 ∨ FamE7 d.1 ∨ FamE8 d.1) (hc : IsCharTwoLieIndex d.1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (β : MulAut S) (hβ : β ∈ innAutDerived S) :
    ¬ L3U3Pumpup S β := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    have hq2 : q.p = 2 := hc
    exact not_l3u3Pumpup_untw (c := TauCeti.LieTypeIndex.F4) (Or.inl rfl)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (hres .F4 (Or.inl rfl)) q hv hq2 e hβ
  | E6 q =>
    have hq2 : q.p = 2 := hc
    exact not_l3u3Pumpup_untw (c := TauCeti.LieTypeIndex.E6) (Or.inr (Or.inl rfl))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (hres .E6 (Or.inr (Or.inl rfl))) q hv hq2 e hβ
  | E7 q =>
    have hq2 : q.p = 2 := hc
    exact not_l3u3Pumpup_untw (c := TauCeti.LieTypeIndex.E7) (Or.inr (Or.inr (Or.inl rfl)))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (hres .E7 (Or.inr (Or.inr (Or.inl rfl)))) q hv hq2 e hβ
  | E8 q =>
    have hq2 : q.p = 2 := hc
    exact not_l3u3Pumpup_untw (c := TauCeti.LieTypeIndex.E8) (Or.inr (Or.inr (Or.inr rfl)))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (hres .E8 (Or.inr (Or.inr (Or.inr rfl)))) q hv hq2 e hβ
  | twistedE6 q =>
    have hq2 : q.p = 2 := hc
    exact not_l3u3Pumpup_twE6 (hres .E6 (Or.inr (Or.inl rfl))) q hv hq2 e hβ
  | _ => rcases hd with h | h | h | h | h <;> exact h.elim

end Untwisted

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
