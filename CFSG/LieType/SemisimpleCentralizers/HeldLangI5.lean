module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5LinCover
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5UniCover

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.LocalAnalysis.ComponentInitial

theorem onCenterQuotient_congr {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') (β : MulAut L) :
    onCenterQuotient (MulAut.congr e β) =
      MulAut.congr (QuotientGroup.congr (Subgroup.center L) (Subgroup.center L') e
        (Subgroup.map_center_eq e)) (onCenterQuotient β) := by
  set ē : L ⧸ Subgroup.center L ≃* L' ⧸ Subgroup.center L' :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center L') e (Subgroup.map_center_eq e) with hē
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := e.surjective x'
  show onCenterQuotient (MulAut.congr e β) (QuotientGroup.mk (e x)) =
    ē (onCenterQuotient β (ē.symm (QuotientGroup.mk (e x))))
  have h1 : ē.symm (QuotientGroup.mk (e x)) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  have h2 : onCenterQuotient (MulAut.congr e β) (QuotientGroup.mk (e x)) =
      QuotientGroup.mk (MulAut.congr e β (e x)) := onCenterQuotient_apply_mk _ _
  have h3 : onCenterQuotient β (QuotientGroup.mk x) = QuotientGroup.mk (β x) := onCenterQuotient_apply_mk _ _
  rw [h2, h3]
  show QuotientGroup.mk (MulAut.congr e β (e x)) = ē (QuotientGroup.mk (β x))
  have h4 : MulAut.congr e β (e x) = e (β x) := by simp [MulAut.congr_apply]
  rw [h4]
  rfl

theorem transport_kd264 {L L' : Type} [Group L] [Group L'] (e : L ≃* L') {m : ℕ}
    (h : ∀ β' : MulAut L', β' ^ 3 = 1 →
      onCenterQuotient β' ∉ innAutDerived (L' ⧸ Subgroup.center L') →
      ∃ E : Subgroup L', E ≤ MonoidHom.eqLocus β'.toMonoidHom (MonoidHom.id _) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ m)
    (β : MulAut L) (hβ3 : β ^ 3 = 1) (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) :
    ∃ E : Subgroup L, E ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ m := by
  have h3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hout' : onCenterQuotient (MulAut.congr e β) ∉ innAutDerived (L' ⧸ Subgroup.center L') := by
    rw [onCenterQuotient_congr, mem_innAutDerived_congr]
    exact hout
  obtain ⟨E', hE'fix, hE'ab, hE'card⟩ := h (MulAut.congr e β) h3 hout'
  refine ⟨E'.map e.symm.toMonoidHom, ?_, isElemAbelian_map_of_injective e.symm.toMonoidHom hE'ab, ?_⟩
  · rintro _ ⟨x', hx', rfl⟩
    have h1 : MulAut.congr e β x' = x' := hE'fix hx'
    show β (e.symm x') = e.symm x'
    have h2 : e (β (e.symm x')) = x' := by simpa [MulAut.congr_apply] using h1
    exact e.injective (by rw [h2, MulEquiv.apply_symm_apply])
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE'card]

theorem le_pRank_of_card {L : Type} [Group L] [Finite L] (E : Subgroup L) {m : ℕ} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ m) : m ≤ CFSG.Open.pRank 3 E := by
  refine le_csSup ⟨Nat.card L, ?_⟩ ⟨E, le_rfl, hE, hcard⟩
  rintro k ⟨E', -, -, hE'card⟩
  have h1 : 3 ^ k ≤ Nat.card L := hE'card ▸ Subgroup.card_le_card_group E'
  exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1

theorem pRank_le_one_of_isCyclic {L : Type} [Group L] [Finite L] (Z : Subgroup L) [IsCyclic Z] :
    CFSG.Open.pRank 3 Z ≤ 1 := by
  classical
  refine csSup_le' ?_
  rintro k ⟨E, hEZ, ⟨hEc, hE3⟩, hEcard⟩
  haveI := Fintype.ofFinite Z
  have h1 := IsCyclic.card_pow_eq_one_le (α := Z) (n := 3) (by norm_num)
  have hinj : Function.Injective (fun x : E => (⟨⟨(x : L), hEZ x.2⟩, Subtype.ext (hE3 x.1 x.2)⟩ :
      {a : Z // a ^ 3 = 1})) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {a : Z // a ^ 3 = 1} => ((z.1 : Z) : L)) hab)
  have h2 : Nat.card E ≤ Nat.card {a : Z // a ^ 3 = 1} := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card {a : Z // a ^ 3 = 1} ≤ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1
  rw [hEcard] at h2
  have h4 : 3 ^ k ≤ 3 := h2.trans h3
  by_contra hk
  push Not at hk
  have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem kd264I5Universal_linear (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.A n q).Valid)
    (h3n : 3 ∣ n + 1) (h3q : 3 ∣ q.card - 1)
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.A n q, hd⟩ L)
    (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) :
    ∃ E : Subgroup L, E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ∧ IsElemAbelian 3 E ∧
      (n - 1) + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E := by
  haveI hcyc : IsCyclic ↥(Subgroup.center L) := hL.2.2.1
  by_cases hne : n = 2 ∧ q.card = 4
  · exact (false_of_outer_three_A_small n q hd h3n (by omega) L hL β hβ3 hout).elim
  · obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := i5CoverIsSL_of_ne n q hd h3n h3q hne L hL
    have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
    have h3K : 3 ∣ Nat.card K - 1 := hK ▸ h3q
    obtain ⟨E, hEfix, hEab, hEcard⟩ := transport_kd264 e' (m := n + 1 - 1)
      (fun β' hβ'3 hout' => kd264I5_SL hN h3K β' hβ'3 hout') β hβ3 hout
    refine ⟨E, hEfix, hEab, ?_⟩
    have h1 : n + 1 - 1 ≤ CFSG.Open.pRank 3 E := le_pRank_of_card E hEab hEcard
    have h2 : CFSG.Open.pRank 3 (Subgroup.center L) ≤ 1 := pRank_le_one_of_isCyclic _
    omega

theorem kd264I5Universal_unitary (hSU : I5SUClosed) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (h3n : 3 ∣ n + 1) (h3q : 3 ∣ q.card + 1)
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.twistedA n q, hd⟩ L)
    (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) :
    ∃ E : Subgroup L, E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ∧ IsElemAbelian 3 E ∧
      (n - 1) + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E := by
  haveI hcyc : IsCyclic ↥(Subgroup.center L) := hL.2.2.1
  have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
  by_cases hq8 : q.card < 8
  · exact (false_of_outer_three_twistedA_small n q hd hN hq8 L hL β hβ3 hout).elim
  · obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := i5CoverIsSU_of_closed hSU n q hd hN (by omega) L hL
    have hdat : UnitaryFieldData q.p q.exponent K :=
      ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
    have hNq := not_three_two_of_valid n q hd hN
    have h3q' : 3 ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact h3q
    obtain ⟨E, hEfix, hEab, hEcard⟩ := transport_kd264 e' (m := n + 1 - 1)
      (fun β' hβ'3 hout' => kd264I5_SU hdat hN hNq h3q' β' hβ'3 hout') β hβ3 hout
    refine ⟨E, hEfix, hEab, ?_⟩
    have h1 : n + 1 - 1 ≤ CFSG.Open.pRank 3 E := le_pRank_of_card E hEab hEcard
    have h2 : CFSG.Open.pRank 3 (Subgroup.center L) ≤ 1 := pRank_le_one_of_isCyclic _
    omega

@[expose] def KD264I5UniversalExc : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5FieldBound e.1 k →
    (∃ q : TauCeti.PrimePower, e.1 = .E6 q ∨ e.1 = .twistedE6 q) →
    ∀ (L : Type) [Group L] [Finite L], IsI5UniversalCover e L →
      ∀ β : MulAut L, β ^ 3 = 1 →
        onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L) →
        ∃ E : Subgroup L, E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ∧ IsElemAbelian 3 E ∧
          k + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E

theorem kd264I5Universal_of_inputs (hSU : I5SUClosed) (hE : KD264I5UniversalExc) :
    KD264I5Universal := by
  intro e k hk L _ _ hL β hβ3 hout
  obtain ⟨d, hd⟩ := e
  cases d with
  | A n q =>
    obtain ⟨h3n, h3q, rfl⟩ := hk
    exact kd264I5Universal_linear n q hd h3n h3q L hL β hβ3 hout
  | twistedA n q =>
    obtain ⟨h3n, h3q, rfl⟩ := hk
    exact kd264I5Universal_unitary hSU n q hd h3n h3q L hL β hβ3 hout
  | E6 q => exact hE ⟨_, hd⟩ k hk ⟨q, Or.inl rfl⟩ L hL β hβ3 hout
  | twistedE6 q => exact hE ⟨_, hd⟩ k hk ⟨q, Or.inr rfl⟩ L hL β hβ3 hout
  | _ => exact hk.elim

end CFSG.LieType.SemisimpleCentralizers.HeldLang
