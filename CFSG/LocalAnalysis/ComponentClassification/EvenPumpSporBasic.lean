module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant transportAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.SolMax (card_of_mulEquiv_alt dvd_card_of_alt
  factorial_div_two_ne_of_lt exact_component_of_oddCore card_fixedSubgroup_congr
  fixedSubgroup_conj_eq)

@[expose] def NoEvenAltBelow (N : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ m : ℕ, Even m → 10 ≤ m → m.factorial / 2 ≤ N → IsEmpty (Y ≃* alternatingGroup (Fin m))

@[expose] def EvenPumpSporClauseFor (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P → ∀ m : ℕ, Even m → 10 ≤ m →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) → False

theorem factorial_div_two_ne_even {c : ℕ} (K : ℕ) (hK : c < K.factorial / 2)
    (hsmall : ∀ m < K, Even m → 10 ≤ m → m.factorial / 2 ≠ c) :
    ∀ m : ℕ, Even m → 10 ≤ m → m.factorial / 2 ≠ c := by
  intro m hm hm10
  by_cases hmK : m < K
  · exact hsmall m hmK hm hm10
  · exact factorial_div_two_ne_of_lt hK (by omega)

theorem noEvenAltBelow_of_card_quotient_center {N : ℕ} {Y : Type} [Group Y]
    (h : ∀ m : ℕ, Even m → 10 ≤ m → m.factorial / 2 ≤ N →
      Nat.card (Y ⧸ center Y) ≠ m.factorial / 2) : NoEvenAltBelow N Y := by
  intro m hm hm10 hmN
  refine ⟨fun f => h m hm hm10 hmN ?_⟩
  have hZ : center Y = ⊥ := by
    have h1 := Subgroup.map_center_eq f
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp h1
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot : Y ⧸ (⊥ : Subgroup Y) ≃* Y).toEquiv,
    card_of_mulEquiv_alt (by omega) f]

theorem noEvenAltBelow_of_card_quotient_center_eq {N c : ℕ} {Y : Type} [Group Y]
    (hc : ∀ m : ℕ, Even m → 10 ≤ m → m.factorial / 2 ≠ c) (h : Nat.card (Y ⧸ center Y) = c) :
    NoEvenAltBelow N Y :=
  noEvenAltBelow_of_card_quotient_center fun m hm hm10 _ => h ▸ (hc m hm hm10).symm

theorem compsSatisfy_noEvenAltBelow_of_quasisimple {N : ℕ} {X : Type} [Group X]
    (hX : IsQuasisimple X) (hZ : center X ≠ ⊥) : CompsSatisfy X (NoEvenAltBelow N) := by
  intro B hB m hm hm10 _
  refine ⟨fun f => hZ ?_⟩
  have hBt := RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hX hB
  let g : X ≃* alternatingGroup (Fin m) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hBt.symm)).trans f
  have h1 := Subgroup.map_center_eq g
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ g.injective).mp h1

theorem false_of_noEvenAlt_comps {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ σ : MulAut S, orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hin : ∀ t : S, orderOf t = 2 →
      CompsSatisfy (centralizer ({t} : Set S)) (NoEvenAltBelow (Nat.card S)))
    (hout : ∀ α : MulAut S, α * α = 1 → α ∉ inner S →
      CompsSatisfy (Sporadic.Schreier.fixSub α) (NoEvenAltBelow (Nat.card S)))
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P) {m : ℕ} (hm : Even m) (hm10 : 10 ≤ m)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) : False := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hmN : m.factorial / 2 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
    ((dvd_card_of_alt (by omega) eP).1.trans (Subgroup.card_subgroup_dvd_card P))
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h (hcore σ hσ2) hex
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    exact (hin t ht2 _ (isComponent_map_mulEquiv φ hcomp) m hm hm10 hmN).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))
  · have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    exact (hout σ hσσ hout' _ (isComponent_map_mulEquiv φ hcomp) m hm hm10 hmN).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))

theorem evenPumpSporClauseFor_of_comps {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) (NoEvenAltBelow (Nat.card G)))
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) (NoEvenAltBelow (Nat.card G))) :
    EvenPumpSporClauseFor s := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex m hm hm10 ⟨eP⟩
  exact false_of_noEvenAlt_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ)
    (hin S inferInstance hna ⟨e⟩) (hout S inferInstance hna ⟨e⟩) h hex hm hm10 eP

theorem outer_noEvenAlt_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ α : MulAut (NativeSporadic.Carrier s), α ∈ inner (NativeSporadic.Carrier s))
    (G : Type) [Group G] [Finite G] (_ : IsSimpleGroup G) (_ : ∃ x y : G, x * y ≠ y * x)
    (hG : Nonempty (G ≃* NativeSporadic.Carrier s)) (α : MulAut G) (_ : α * α = 1)
    (hα : α ∉ inner G) :
    CompsSatisfy (Sporadic.Schreier.fixSub α) (NoEvenAltBelow (Nat.card G)) := by
  obtain ⟨e⟩ := hG
  exact absurd (hinner (transportAut e α))
    (RestrictedStd.Spor.transportAut_not_mem_inner e hα)

theorem evenPumpSporClauseFor_of_card {s : TauCeti.SporadicName}
    (hs : ¬ 2520 ∣ Nat.card (NativeSporadic.Carrier s)) : EvenPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P _ _ m _ hm10 ⟨eP⟩
  apply hs
  rw [← Nat.card_congr e.toEquiv]
  exact (dvd_card_of_alt (by omega) eP).2.trans (Subgroup.card_subgroup_dvd_card P)

theorem evenPumpSporClauseFor_of_fixed_card {s : TauCeti.SporadicName} {K : Type} [Group K]
    (eK : NativeSporadic.Carrier s ≃* K)
    (hs : ∀ α : MulAut K, α * α = 1 → α ≠ 1 → ¬ 2520 ∣ Nat.card {y : K // α y = y}) :
    EvenPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P h _ m _ hm10 ⟨eP⟩
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ1 := h.ne_one
  apply hs (MulAut.congr (e.trans eK) σ) (by rw [← map_mul, hσσ, map_one])
    (fun h1 => hσ1 ((MulAut.congr (e.trans eK)).injective (by rw [h1, map_one])))
  rw [← card_fixedSubgroup_congr]
  exact (dvd_card_of_alt (by omega) eP).2.trans (Subgroup.card_dvd_of_le h.2.1)

theorem evenPumpSporClauseFor_of_fixedSubgroup_card {s : TauCeti.SporadicName}
    (hs : ∀ (S : Type) [Group S] [Finite S], (S ≃* NativeSporadic.Carrier s) →
      ∀ σ : MulAut S, σ * σ = 1 → σ ≠ 1 → ¬ 2520 ∣ Nat.card (fixedSubgroup σ)) :
    EvenPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P h _ m _ hm10 ⟨eP⟩
  exact hs S e σ (MulEquiv.ext fun y => h.1 y) h.ne_one
    ((dvd_card_of_alt (by omega) eP).2.trans (Subgroup.card_dvd_of_le h.2.1))

end CFSG.ComponentClassification.EvenPump
