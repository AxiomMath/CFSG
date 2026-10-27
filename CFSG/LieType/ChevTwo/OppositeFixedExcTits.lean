module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTitsGlue
public import CFSG.LieType.ChevTwo.OppositeFixedExcInner
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem pCoreOf_autCentralizer_eq_bot_of_oppInner {K : Type} [Group K] [Finite K]
    (hBT : Holds K 2) (hopp : OppositeFixedInner K) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Subgroup (MulAut K)) (hR : IsPGroup p R)
    (hRinn : R ≤ (MulAut.conj : K →* MulAut K).range) :
    pCoreOf 2 (autCentralizer R) = ⊥ := by
  by_contra hne
  set U := pCoreOf 2 (autCentralizer R) with hU
  have hUp : IsPGroup 2 U := pCoreOf_isPGroup 2 _
  obtain ⟨hle, hQp, hnorm, hnetop, hcore, -⟩ := canonical_parabolic hBT hne hUp
  set Q := radInf 2 U with hQ
  have hUC : U ≤ autCentralizer R := by
    rw [hU]
    exact Subgroup.map_subtype_le _
  have hmap : ∀ α ∈ R, U.map α.toMonoidHom = U := by
    intro α hα
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : α y = y := hUC hy α hα
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, hUC hx α hα⟩
  have hinv : ∀ α ∈ R, Q.map α.toMonoidHom = Q := fun α hα =>
    radInf_map_eq (α : K ≃* K) (hmap α hα)
  have hCN : autCentralizer R ≤ Subgroup.normalizer (Q : Set K) := fun c hc =>
    hnorm (le_normalizer_pCoreOf 2 (autCentralizer R) hc)
  have hQne : Q ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ hle))
  have h0 := hopp p hp hp2 R hR hRinn Q hQne hQp hcore hnetop hinv hCN
  exact hne (le_bot_iff.1 (h0 ▸ le_inf hUC hle))

theorem inner_of_odd_orderOf_of_outer {G : Type} [Group G]
    (hO : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) (α : MulAut G)
    (hα : Odd (orderOf α)) : α ∈ (MulAut.conj : G →* MulAut G).range := by
  haveI := CFSG.ComponentClassification.OuterAutomorphisms.innerNormal G
  set q : CFSG.ComponentClassification.OuterAutomorphisms.Outer G :=
    (QuotientGroup.mk α : MulAut G ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    with hq
  obtain ⟨k, hk⟩ := hO q
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf q ∣ orderOf α := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hq, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hodd : Odd (orderOf q) := hα.of_dvd_nat h2
  have hq1 : orderOf q = 1 := by
    rcases i with _ | i
    · simpa using hi
    · exfalso
      have h2d : 2 ∣ orderOf q := hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)
      have := Nat.odd_iff.1 hodd
      omega
  have hq0 : q = 1 := orderOf_eq_one_iff.1 hq1
  exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner G) α).1 hq0

section Cert


theorem oppositeFixed_of_titsModel {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1)
    (hΓ : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
      OppositeFixedInner ↥(reeFixed ReeTag.F4 K 0)) : OppositeFixed S := by
  have hS := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 h
  obtain ⟨-, a, hf, hmodel⟩ := h
  have ha : a = 0 := by omega
  subst ha
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  let e1 : S ≃* ↥(commutator ↥(reeFixed ReeTag.F4 K 0)) :=
    e'.trans ((QuotientGroup.quotientMulEquivOfEq (CFSG.Sporadic.Schreier.Tits.center_commutator_reeFixed hK2)).trans
      QuotientGroup.quotientBot)
  have hT : OppositeFixed ↥(commutator ↥(reeFixed ReeTag.F4 K 0)) := by
    refine oppositeFixed_of_normal (commutator ↥(reeFixed ReeTag.F4 K 0))
      (CFSG.Sporadic.Schreier.Tits.center_commutator_reeFixed hK2) ?_ ?_
    · intro α hα
      have hα' : Odd (orderOf (MulAut.congr e1.symm α)) := by
        rwa [MulEquiv.orderOf_eq]
      obtain ⟨s, hs⟩ := inner_of_odd_orderOf_of_outer hS.1 _ hα'
      refine ⟨e1 s, ?_⟩
      have h1 : MulAut.conj (e1 s) = MulAut.congr e1 (MulAut.conj s) :=
        (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e1 s).symm
      rw [h1]
      change MulAut.congr e1 (MulAut.conj s) = α
      rw [show (MulAut.conj s : MulAut S) = MulAut.congr e1.symm α from hs]
      ext x
      simp [MulAut.congr_apply]
    · intro p hp hp2 S₀ hS₀
      have hR : IsPGroup p (S₀.map (MulAut.conj : ↥(reeFixed ReeTag.F4 K 0) →*
          MulAut ↥(reeFixed ReeTag.F4 K 0))) := hS₀.map _
      have hRinn : S₀.map (MulAut.conj : ↥(reeFixed ReeTag.F4 K 0) →*
          MulAut ↥(reeFixed ReeTag.F4 K 0)) ≤
          (MulAut.conj : ↥(reeFixed ReeTag.F4 K 0) →* MulAut ↥(reeFixed ReeTag.F4 K 0)).range := by
        rintro _ ⟨s, -, rfl⟩
        exact ⟨s, rfl⟩
      have h0 := pCoreOf_autCentralizer_eq_bot_of_oppInner
        (holds_reeFixed ReeTag.F4 K 0 : Holds ↥(reeFixed ReeTag.F4 K 0) 2) (hΓ K hK2) p hp hp2 _
        hR hRinn
      have hceq : autCentralizer (S₀.map (MulAut.conj : ↥(reeFixed ReeTag.F4 K 0) →*
          MulAut ↥(reeFixed ReeTag.F4 K 0))) = Subgroup.centralizer (S₀ : Set _) := by
        ext x
        rw [Subgroup.mem_centralizer_iff]
        constructor
        · intro hx r hr
          have h1 : r * x * r⁻¹ = x := hx (MulAut.conj r) ⟨r, hr, rfl⟩
          calc r * x = (r * x * r⁻¹) * r := by group
            _ = x * r := by rw [h1]
        · rintro hx _ ⟨r, hr, rfl⟩
          have h1 : r * x = x * r := hx r hr
          change r * x * r⁻¹ = x
          calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [h1]
            _ = x := by group
      rwa [hceq] at h0
  exact oppositeFixed_of_mulEquiv e1 hT

end Cert

end CFSG.LieType.ChevTwo
