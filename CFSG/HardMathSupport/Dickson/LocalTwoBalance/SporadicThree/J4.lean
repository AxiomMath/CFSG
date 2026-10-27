module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestJ4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGammaPairs
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Nine
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Blueprint CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Sporadic.J4

private theorem fixGen_map_mulEquiv {M X : Type*} [Group M] [Group X] (e : M ≃* X)
    {P : Subgroup M} (h : Item434SporGen.FixGen P) : Item434SporGen.FixGen (P.map e.toMonoidHom) := by
  obtain ⟨S, hS, hgen⟩ := h
  refine ⟨e '' S, ?_, ?_⟩
  · intro x _
    have hx : e.symm x ∈ Subgroup.closure S := hS (Subgroup.mem_top _)
    have h1 : e (e.symm x) ∈ (Subgroup.closure S).map e.toMonoidHom := ⟨_, hx, rfl⟩
    rw [MonoidHom.map_closure] at h1
    simpa using h1
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ3, p, hp, hp1, hpσ⟩ := hgen σ hσ
    refine ⟨by rw [MulEquiv.orderOf_eq]; exact hσ3, e p, ⟨p, hp, rfl⟩, ?_, ?_⟩
    · intro h1
      apply hp1
      apply e.injective
      rw [h1, map_one]
    · rw [← map_mul, ← map_mul, hpσ]

private theorem center_eq_bot_of_simple {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem localDeltaIn_top_eq_bot_of_fixGen {S : Type*} [Group S]
    (hcen : Subgroup.center S = ⊥) {E : Subgroup S} (hgen : Item434SporGen.FixGen E)
    (hres : ∀ d ∈ E, d ≠ 1 → ∀ o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set S)),
      ∀ c ∈ Subgroup.centralizer ({d} : Set S), o * c = c * o) :
    localDeltaIn 3 (⊤ : Subgroup S) E = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨T, hT, hTgen⟩ := hgen
  have hle : Subgroup.closure T ≤ Subgroup.centralizer ({w} : Set S) := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨-, p, hp, hp1, hpx⟩ := hTgen x hx
    have h3 := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hw p) hp) hp1
    rw [top_inf_eq] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hres p hp hp1 w h3 x (Subgroup.mem_centralizer_singleton_iff.mpr hpx.symm)).symm
  have hwZ : w ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hT (Subgroup.mem_top x)))
  rw [hcen] at hwZ
  exact hwZ

private theorem orderThree_centralizer_residual
    {S : Type} [Group S] [Finite S]
    (φ : S ≃* NativeSporadic.Carrier .J4) {s : S} (hs : orderOf s = 3) :
    ∀ o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)),
      ∀ d ∈ Subgroup.centralizer ({s} : Set S), o * d = d * o := by
  refine commute_of_mem_gLAPPrimeCoreOf_of_conj (H := J) Nat.prime_three
    (φ.trans (seedEquiv j4Facts.mat))
    (fun y hy => exists_conj_cE_of_orderThree y (hy ▸ pow_orderOf_eq_one y) ?_)
    (centralizer_cE_quasisimple j4Facts).1 hs
  intro h1
  rw [h1, orderOf_one] at hy
  exact absurd hy (by norm_num)

private theorem fixGen_of_equiv
    {S : Type} [Group S] (φ : S ≃* NativeSporadic.Carrier .J4) {E : Subgroup S}
    (hEc : Nat.card E = 9) :
    Item434SporGen.FixGen E := by
  have hcardJ : Nat.card NativeSporadic.J4 = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
  have : Finite NativeSporadic.J4 := Nat.finite_of_card_ne_zero (by rw [hcardJ]; norm_num)
  have hL : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
    rw [hcardJ, show (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have h9 : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hEc]
  have h1 := fixGen_map_mulEquiv φ.symm (ONanJ4Nine.fixGen_j4 hL _ h9)
  have h2 : (E.map φ.toMonoidHom).map φ.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id E
    ext x
    simp
  rwa [h2] at h1

private theorem innerAut_eq_top_of_equiv
    {S : Type} [Group S] (φ : S ≃* NativeSporadic.Carrier .J4) :
    innerAut S = ⊤ :=
  innerAut_eq_top_of_mulEquiv (K' := NativeSporadic.Carrier .J4) φ
    (Subgroup.index_eq_one.mp CFSG.AGLEmbedding.card_outer_J4)

theorem sporadicTwoBalanceThree_J4 :
    SporadicTwoBalanceThree .J4 := by
  intro S _ _ hS hnab ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  have b' : NativeSporadic.Carrier .J4 ≃* (TauCeti.CFSGIndex.sporadic .J4).Group := b
  have φ : S ≃* NativeSporadic.Carrier .J4 := e.trans b'.symm
  refine isLocallyBalancedAbs_of_inner_eq_top hcen (innerAut_eq_top_of_equiv φ) fun E hE hEc => ?_
  refine localDeltaIn_top_eq_bot_of_fixGen hcen
    (fixGen_of_equiv φ (by rw [hEc]; norm_num)) fun d hd hd1 => ?_
  exact orderThree_centralizer_residual φ (orderOf_eq_prime (hE.2 d hd) hd1)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
