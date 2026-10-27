module

import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Field
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false

section Inndiag


theorem mem_adjointGroup_of_mem_inndiagGroup_pow_eq_one {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) {h : ModGL τ K}
    (hh : h ∈ inndiagGroup τ K) (hhp : h ^ p = 1) : h ∈ adjointGroup τ K := by
  classical
  obtain ⟨b, j, hj, rfl⟩ := hh
  have hN : ∀ u : Kˣ, u ^ (Nat.card K - 1) = 1 := fun u => by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hbN : b ^ (Nat.card K - 1) = 1 := funext fun i => by
    rw [Pi.pow_apply, hN, Pi.one_apply]
  haveI : ((adjointGroup τ K).subgroupOf (inndiagGroup τ K)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_adjointGroup_of_mem_inndiag g.2 hn⟩
  set π := QuotientGroup.mk' ((adjointGroup τ K).subgroupOf (inndiagGroup τ K)) with hπ
  let d : inndiagGroup τ K := ⟨rootDiagUnit τ b, rootDiagUnit_mem_inndiagGroup b⟩
  let j' : inndiagGroup τ K := ⟨j, adjointGroup_le_inndiagGroup hj⟩
  have hπj : π j' = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hj)
  have hdN : d ^ (Nat.card K - 1) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, rootDiagUnit_pow, hbN, rootDiagUnit_one]
    rfl)
  have h1 : π (d * j') ^ (Nat.card K - 1) = 1 := by
    rw [map_mul, hπj, mul_one, ← map_pow, hdN, map_one]
  have h2 : π (d * j') ^ p = 1 := by
    rw [← map_pow]
    have : (d * j') ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hhp)
    rw [this, map_one]
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
  have h3 : π (d * j') = 1 := by
    refine orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd ?_ ?_))
    · exact orderOf_dvd_of_pow_eq_one h2
    · exact orderOf_dvd_of_pow_eq_one h1
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)

end Inndiag

section Untw


theorem lieCompExport_char3_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hG2 : ∀ (q : TauCeti.PrimePower), (c q).Valid → τ = .G2 → 3 ≤ q.card)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hq3 : q.p = 3) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) (β : MulAut S) (hβ : β ^ 3 = 1)
    (hout : ∀ a : S, MulAut.conj a ≠ β) : LieCompExport 3 β := by
  classical
  obtain ⟨K, _, hKfin, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  have hℓ : ringChar K = 3 := (ringChar.eq K q.p).trans hq3
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1 : β ≠ 1 := fun h => hout 1 (by rw [map_one, h])
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hG2K : τ = .G2 → 3 ≤ Nat.card K := fun h => hK ▸ hG2 q hv h
  have hpK : ¬ 3 ∣ Nat.card K - 1 := by
    intro hd
    have h1 : 3 ∣ Nat.card K := by
      rw [hK, TauCeti.PrimePower.card_def, ← hq3]
      exact dvd_pow_self _ q.exponent_pos.ne'
    have h0 : 0 < Nat.card K := Nat.card_pos
    omega
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e' β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
        ((MulAut.congr e' β) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact exists_field_or_inndiag_FG (Or.inr h) hG2K Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_FG (Or.inl h) hG2K Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inl h) Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inl h)) Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inr h)) Nat.prime_three (by norm_num) _ hβ' hβ1'
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, -⟩
  · refine LieCompExport.of_congr e' (lieCompExport_of_conj ψ _ ?_)
    rw [hψ]
    exact lieCompExport_entrywiseAdjointAut_untw hB hchar hvalid hA6 hℓ σ
  · exfalso
    have hmem : h ∈ adjointGroup τ K :=
      mem_adjointGroup_of_mem_inndiagGroup_pow_eq_one Nat.prime_three hpK hh hp1
    refine hout (e'.symm ⟨h, hmem⟩) ?_
    apply (MulAut.congr e').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hβh c]
    simp [MulAut.conj_apply]

end Untw

section TwE6


theorem lieCompExport_char3_twE6
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : q.p = 3)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (β : MulAut S) (hβ : β ^ 3 = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    LieCompExport 3 β := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  rw [hq3] at hK hσ
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num)))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  refine LieCompExport.of_congr e' ?_
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_three
      q.exponent_pos K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e' β) = 1
  · exfalso
    have hmem : MulAut.congr e' β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact hΘβ
    have hpg : ¬ 3 ∣ Nat.gcd 3 (3 ^ q.exponent + 1) := fun h => by
      have h1 : 3 ∣ 3 ^ q.exponent + 1 := h.trans (Nat.gcd_dvd_right 3 _)
      have h2 : 3 ∣ 3 ^ q.exponent := dvd_pow_self 3 q.exponent_pos.ne'
      exact absurd ((Nat.dvd_add_right h2).1 h1) (by norm_num)
    obtain ⟨a, ha⟩ := CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag
      Nat.prime_three hK hσ hpg hcube hβ' hmem
    refine hout (e'.symm a) ?_
    apply (MulAut.congr e').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ha
  · exact lieCompExport_twE6_field hA6 Nat.prime_three q.exponent_pos
      (by rw [hK, ← pow_mul, mul_comm]) σ hσ Nat.prime_three (by norm_num) Θ hΘ _ hβ' hΘβ

end TwE6

section Main


theorem lieCompExport_char3_outer_of_ne_trialityD4 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .exceptional →
        (∀ q, idx.1 ≠ .trialityD4 q) → lieIndexChar idx.1 = 3 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ β : MulAut S, β ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ β) → LieCompExport 3 β := by
  intro S _ _ _ _ idx hF hntri h3 he β hβ hout
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | E6 q =>
    exact lieCompExport_char3_untw (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | E7 q =>
    exact lieCompExport_char3_untw (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | E8 q =>
    exact lieCompExport_char3_untw (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | F4 q =>
    exact lieCompExport_char3_untw (τ := .F4) (Or.inr (Or.inl rfl))
      (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | G2 q =>
    exact lieCompExport_char3_untw (τ := .G2) (Or.inl rfl)
      (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
      (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
      (fun q hv => isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | twistedE6 q =>
    exact lieCompExport_char3_twE6
      (fun q hv => isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩ (Or.inl rfl)) q hv h3 e β hβ hout
  | trialityD4 q => exact absurd rfl (hntri q)
  | _ => simp [lieFamily] at hF

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
