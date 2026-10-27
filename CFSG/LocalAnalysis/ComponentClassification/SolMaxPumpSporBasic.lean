module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant transportAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def NoOddAltBelow (N : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ m : ℕ, Odd m → 7 ≤ m → m.factorial / 2 ≤ N → IsEmpty (Y ≃* alternatingGroup (Fin m))

@[expose] def AltPumpSporClauseFor (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P → ∀ m : ℕ, Odd m → 7 ≤ m →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) → False

theorem isoInvariant_noOddAltBelow (N : ℕ) : IsoInvariant (NoOddAltBelow N) := by
  intro Y Y' _ _ e h m hm hm7 hmN
  exact ⟨fun f => (h m hm hm7 hmN).false (e.symm.trans f)⟩

theorem dvd_factorial_div_two {m : ℕ} (hm : 7 ≤ m) : 2520 ∣ m.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hm
  rw [hk, show (7 : ℕ).factorial = 2 * 2520 by decide, mul_assoc,
    Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right _ _

theorem factorial_div_two_ne_of_lt {c K m : ℕ} (hK : c < K.factorial / 2) (hm : K ≤ m) :
    m.factorial / 2 ≠ c := by
  have h1 : K.factorial / 2 ≤ m.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le hm)
  omega

theorem factorial_div_two_ne {c : ℕ} (K : ℕ) (hK : c < K.factorial / 2)
    (hsmall : ∀ m < K, Odd m → 7 ≤ m → m.factorial / 2 ≠ c) :
    ∀ m : ℕ, Odd m → 7 ≤ m → m.factorial / 2 ≠ c := by
  intro m hm hm7
  by_cases hmK : m < K
  · exact hsmall m hmK hm hm7
  · exact factorial_div_two_ne_of_lt hK (by omega)

theorem noOddAltBelow_of_card_quotient_center {N : ℕ} {Y : Type} [Group Y]
    (h : ∀ m : ℕ, Odd m → 7 ≤ m → m.factorial / 2 ≤ N →
      Nat.card (Y ⧸ center Y) ≠ m.factorial / 2) : NoOddAltBelow N Y := by
  intro m hm hm7 hmN
  refine ⟨fun f => h m hm hm7 hmN ?_⟩
  have hZ : center Y = ⊥ := by
    have h1 := Subgroup.map_center_eq f
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp h1
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot : Y ⧸ (⊥ : Subgroup Y) ≃* Y).toEquiv,
    card_of_mulEquiv_alt (by omega) f]

theorem noOddAltBelow_of_card_quotient_center_eq {N c : ℕ} {Y : Type} [Group Y]
    (hc : ∀ m : ℕ, Odd m → 7 ≤ m → m.factorial / 2 ≠ c) (h : Nat.card (Y ⧸ center Y) = c) :
    NoOddAltBelow N Y :=
  noOddAltBelow_of_card_quotient_center fun m hm hm7 _ => h ▸ (hc m hm hm7).symm

theorem compsSatisfy_noOddAltBelow_of_quasisimple {N : ℕ} {X : Type} [Group X]
    (hX : IsQuasisimple X) (hZ : center X ≠ ⊥) : CompsSatisfy X (NoOddAltBelow N) := by
  intro B hB m hm hm7 _
  refine ⟨fun f => hZ ?_⟩
  have hBt := RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hX hB
  let g : X ≃* alternatingGroup (Fin m) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hBt.symm)).trans f
  have h1 := Subgroup.map_center_eq g
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ g.injective).mp h1

theorem dvd_card_of_alt {S : Type} [Group S] [Finite S] {P : Subgroup S} {m : ℕ} (hm7 : 7 ≤ m)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) :
    m.factorial / 2 ∣ Nat.card P ∧ 2520 ∣ Nat.card P := by
  have h1 : m.factorial / 2 ∣ Nat.card P := by
    rw [← card_of_mulEquiv_alt (by omega) eP]
    exact Subgroup.card_quotient_dvd_card _
  exact ⟨h1, (dvd_factorial_div_two hm7).trans h1⟩

theorem exact_component_of_oddCore {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P) :
    IsComponent (P.subgroupOf (fixedSubgroup σ)) ∧
      Nonempty (↥(P.subgroupOf (fixedSubgroup σ)) ≃* ↥P ⧸ Open.fusionZStar ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomp, -⟩ := h.isComponent_of_oddCore hcore
  refine ⟨hcomp, ?_⟩
  set L := P.subgroupOf (fixedSubgroup σ) with hL
  have hL0 : pPrimeCore 2 L = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hcomp.2,
      ← Sporadic.HeldB.oddCore_eq_pPrimeCore_two', hcore, bot_subgroupOf]
  let eLP : L ≃* P := subgroupOfEquivOfLe h.2.1
  have hP0 : pPrimeCore 2 P = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eLP, hL0, Subgroup.map_bot]
  have hZ : Open.fusionZStar ↥P = ⊥ := hex.trans hP0
  exact ⟨eLP.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))⟩

theorem false_of_noOddAlt_comps {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ σ : MulAut S, orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hin : ∀ t : S, orderOf t = 2 →
      CompsSatisfy (centralizer ({t} : Set S)) (NoOddAltBelow (Nat.card S)))
    (hout : ∀ α : MulAut S, α * α = 1 → α ∉ inner S →
      CompsSatisfy (Sporadic.Schreier.fixSub α) (NoOddAltBelow (Nat.card S)))
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P) {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) : False := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hmN : m.factorial / 2 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
    ((dvd_card_of_alt hm7 eP).1.trans (Subgroup.card_subgroup_dvd_card P))
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h (hcore σ hσ2) hex
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    exact (hin t ht2 _ (isComponent_map_mulEquiv φ hcomp) m hm hm7 hmN).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))
  · have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    exact (hout σ hσσ hout' _ (isComponent_map_mulEquiv φ hcomp) m hm hm7 hmN).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))

theorem altPumpSporClauseFor_of_comps {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) (NoOddAltBelow (Nat.card G)))
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) (NoOddAltBelow (Nat.card G))) :
    AltPumpSporClauseFor s := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex m hm hm7 ⟨eP⟩
  exact false_of_noOddAlt_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ)
    (hin S inferInstance hna ⟨e⟩) (hout S inferInstance hna ⟨e⟩) h hex hm hm7 eP

theorem outer_noOddAlt_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ α : MulAut (NativeSporadic.Carrier s), α ∈ inner (NativeSporadic.Carrier s))
    (G : Type) [Group G] [Finite G] (_ : IsSimpleGroup G) (_ : ∃ x y : G, x * y ≠ y * x)
    (hG : Nonempty (G ≃* NativeSporadic.Carrier s)) (α : MulAut G) (_ : α * α = 1)
    (hα : α ∉ inner G) :
    CompsSatisfy (Sporadic.Schreier.fixSub α) (NoOddAltBelow (Nat.card G)) := by
  obtain ⟨e⟩ := hG
  exact absurd (hinner (transportAut e α))
    (RestrictedStd.Spor.transportAut_not_mem_inner e hα)

theorem altPumpSporClauseFor_of_card {s : TauCeti.SporadicName}
    (hs : ¬ 2520 ∣ Nat.card (NativeSporadic.Carrier s)) : AltPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P _ _ m _ hm7 ⟨eP⟩
  apply hs
  rw [← Nat.card_congr e.toEquiv]
  exact (dvd_card_of_alt hm7 eP).2.trans (Subgroup.card_subgroup_dvd_card P)

theorem card_fixedSubgroup_congr {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (σ : MulAut S) :
    Nat.card (fixedSubgroup σ) = Nat.card {y : T // MulAut.congr e σ y = y} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  change σ x = x ↔ (MulAut.congr e σ) (e x) = e x
  rw [MulAut.congr_apply]
  simp

theorem altPumpSporClauseFor_of_fixed_card {s : TauCeti.SporadicName} {K : Type} [Group K]
    (eK : NativeSporadic.Carrier s ≃* K)
    (hs : ∀ α : MulAut K, α * α = 1 → α ≠ 1 → ¬ 2520 ∣ Nat.card {y : K // α y = y}) :
    AltPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P h _ m _ hm7 ⟨eP⟩
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ1 := h.ne_one
  apply hs (MulAut.congr (e.trans eK) σ) (by rw [← map_mul, hσσ, map_one])
    (fun h1 => hσ1 ((MulAut.congr (e.trans eK)).injective (by rw [h1, map_one])))
  rw [← card_fixedSubgroup_congr]
  exact (dvd_card_of_alt hm7 eP).2.trans (Subgroup.card_dvd_of_le h.2.1)

theorem altPumpSporClauseFor_of_fixedSubgroup_card {s : TauCeti.SporadicName}
    (hs : ∀ (S : Type) [Group S] [Finite S], (S ≃* NativeSporadic.Carrier s) →
      ∀ σ : MulAut S, σ * σ = 1 → σ ≠ 1 → ¬ 2520 ∣ Nat.card (fixedSubgroup σ)) :
    AltPumpSporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P h _ m _ hm7 ⟨eP⟩
  exact hs S e σ (MulEquiv.ext fun y => h.1 y) h.ne_one
    ((dvd_card_of_alt hm7 eP).2.trans (Subgroup.card_dvd_of_le h.2.1))

end CFSG.ComponentClassification.SolMax
