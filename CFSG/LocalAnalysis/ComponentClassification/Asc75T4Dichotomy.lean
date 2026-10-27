module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Local
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveApply

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.Open (aschbacherThm5Core aschbacherThm5OddCore)
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem map_layer_le_centralizer {N W : Subgroup Y} (hWN : W ≤ normalizer (N : Set Y))
    (hNW : N ≤ normalizer (W : Set Y)) (hW : Group.IsSolvable W) :
    (CFSG.layer N).map N.subtype ≤ centralizer (W : Set Y) := by
  set V := N ⊔ W with hV
  have hNV : N ≤ V := le_sup_left
  have hWV : W ≤ V := le_sup_right
  have hNn : (N.subgroupOf V).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNV).mpr (sup_le le_normalizer hWN)
  have hWn : (W.subgroupOf V).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWV).mpr (sup_le hNW le_normalizer)
  have hWs : Group.IsSolvable (W.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hWV).toMonoidHom)
      (subgroupOfEquivOfLe hWV).injective
  have hcent := (CFSG.LocalCores.component_solvable_centralizer hWs hWn.isSubnormal).1
  rw [map_le_iff_le_comap]
  refine sSup_le fun C hC => ?_
  rw [← map_le_iff_le_comap]
  set C' : Subgroup V := (C.map N.subtype).subgroupOf V with hC'
  have hCN : C.map N.subtype ≤ N := map_subtype_le C
  have hC'q : CFSG.IsQuasisimple C' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((C.equivMapOfInjective N.subtype N.subtype_injective).trans
        (subgroupOfEquivOfLe (hCN.trans hNV)).symm) hC.1
  have hC'N : C' ≤ N.subgroupOf V := subgroupOf_mono V hCN
  have hC'sub : (C'.subgroupOf (N.subgroupOf V)).IsSubnormal := by
    have heq : C'.subgroupOf (N.subgroupOf V) = C.comap (subgroupOfEquivOfLe hNV).toMonoidHom := by
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, hcx⟩ := hx
        have : c = (subgroupOfEquivOfLe hNV) x := Subtype.ext hcx
        rw [mem_comap, MulEquiv.coe_toMonoidHom, ← this]
        exact hc
      · intro hx
        exact ⟨_, hx, rfl⟩
    rw [heq]
    exact hC.2.comap _
  have hC'c : CFSG.IsComponent C' := ⟨hC'q, hC'sub.trans hC'N hNn.isSubnormal⟩
  have hcomm := hcent C' hC'c
  intro x hx
  rw [mem_centralizer_iff]
  intro w hw
  have hxC : (⟨x, hNV (hCN hx)⟩ : V) ∈ C' := hx
  have h1 := commutator_eq_bot_iff_le_centralizer.mp hcomm hxC
  have h2 := mem_centralizer_iff.mp h1 ⟨w, hWV hw⟩ (show (⟨w, hWV hw⟩ : V) ∈ W.subgroupOf V from hw)
  exact congrArg Subtype.val h2

omit [Finite Y] in
theorem not_isCyclic_of_fourGroup {T E : Subgroup Y} (hET : E ≤ T) (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hE4 : Nat.card E = 4) : ¬ IsCyclic T := by
  intro hc
  have hexp : Monoid.exponent (E.subgroupOf T) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (Subtype.ext (by simpa using hE _ x.2))
  rw [IsCyclic.exponent_eq_card, Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv, hE4] at hexp
  norm_num at hexp

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem toBar_mem_map_layer {Q : Subgroup G} {k : normalizer (Q : Set G)}
    (hk : (k : G) ∈ twoPrimeLayerIn Q) :
    toBar Q k ∈ (CFSG.layer (bar Q Q)).map (bar Q Q).subtype := by
  obtain ⟨hkQ, hlay⟩ := mem_twoPrimeLayerIn_iff.mp hk
  let e₀ : Q ⧸ CFSG.Assembly.oddCore Q ≃* Q ⧸ aschbacherThm5OddCore Q :=
    QuotientGroup.quotientMulEquivOfEq rfl
  let e : Q ⧸ CFSG.Assembly.oddCore Q ≃* bar Q Q :=
    e₀.trans ((MonoidHom.ofInjective (quotientEmbedding_injective Q)).trans
      (MulEquiv.subgroupCongr (bar_D_eq_range Q).symm))
  have h1 : e (QuotientGroup.mk' _ ⟨k, hkQ⟩) ∈ CFSG.layer (bar Q Q) := by
    rw [← layer_map_mulEquiv e]
    exact ⟨_, hlay, rfl⟩
  exact ⟨_, h1, rfl⟩

theorem commutator_mem_oddCoreIn_of_solvable {Q T : Subgroup G}
    (hTQ : T ≤ normalizer (Q : Set G)) {W : Subgroup (Bar Q)} (hWs : Group.IsSolvable W)
    (hTW : bar Q T ≤ W) (hWN : W ≤ normalizer (bar Q Q : Set (Bar Q)))
    (hNW : bar Q Q ≤ normalizer (W : Set (Bar Q))) :
    ∀ t ∈ T, ∀ k ∈ twoPrimeLayerIn Q, t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn Q := by
  intro t ht k hk
  have hkQ : k ∈ Q := twoPrimeLayerIn_le Q hk
  let k' : normalizer (Q : Set G) := ⟨k, le_normalizer hkQ⟩
  let t' : normalizer (Q : Set G) := ⟨t, hTQ ht⟩
  have hc := map_layer_le_centralizer hWN hNW hWs (toBar_mem_map_layer (k := k') hk)
  have htW : toBar Q t' ∈ W := hTW (toBar_mem_bar Q (h := t') ht)
  have hcomm : toBar Q t' * toBar Q k' = toBar Q k' * toBar Q t' :=
    mem_centralizer_iff.mp hc _ htW
  have h1 : toBar Q (t' * k' * t'⁻¹ * k'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [toBar_eq_one_iff] at h1
  exact h1

theorem exists_hyp3_bar {Q : Subgroup G} (htight : TightlyEmbedded Q) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hT1 : T ≠ ⊥) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Q ⊔ T) ∧ T ≤ S ∧ T ⊓ Q = ⊥ ∧
      AschbacherTheorem3.Hyp3 (bar Q Q) (bar Q T) (bar Q (rightConjugate Q g ⊓ (Q ⊔ T)))
        (bar Q S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have hTQg : T ≤ rightConjugate Q g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hKH : Q ⊔ T ≤ normalizer (Q : Set G) := sup_le le_normalizer hTH
  obtain ⟨S, hS, hTS, hSN⟩ := exists_sylow_normalizer (le_sup_right : T ≤ Q ⊔ T) hT2
  obtain ⟨hbot, -, hcardN⟩ := part_one_of_isSylowOf Q htight g hg hT hS hTS hT1
  have hTSN : T ≤ S ⊓ normalizer (T : Set G) := le_inf hTS le_normalizer
  have hidx : T.relIndex (S ⊓ normalizer (T : Set G)) ≤ Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T (S ⊓ normalizer (T : Set G))
    rw [inf_eq_left.mpr hTSN, hcardN] at h1
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h1]
  set P := rightConjugate Q g ⊓ (Q ⊔ T) with hP
  have hTP : IsSylowOf 2 T P :=
    hT.of_le (le_inf hTQg le_sup_right) (inf_le_inf_left _ hKH)
  have heven : Even (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hT2)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have htightP : ∀ y ∈ Q ⊔ T, y ∉ normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    have hQgt := rightConjugate_tightlyEmbedded Q htight g
    have hyQg : y ∉ normalizer (rightConjugate Q g : Set G) := by
      intro hyn
      apply hyN
      rw [← rightConjugate_eq_self_iff] at hyn ⊢
      rw [hP, AschbacherTheorem3.rightConjugate_inf, hyn,
        (rightConjugate_eq_self_iff _ y).mpr (le_normalizer hy)]
    exact (hQgt.2 y hyQg).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)))
  exact ⟨S, hS, hTS, hbot, hyp3_bar le_rfl (core_le Q) le_normalizer hTH hTH hT2 hT1 hbot
    inf_le_right hTP heven htightP hS hTS hSN hidx⟩

theorem exists_thm3Conclusion (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G}
    (htight : TightlyEmbedded Q) {g : G} (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hT1 : T ≠ ⊥) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Q ⊔ T) ∧ T ≤ S ∧ T ⊓ Q = ⊥ ∧
      AschbacherTheorem3.Thm3Conclusion (bar Q Q) (bar Q T) (bar Q S) := by
  obtain ⟨S, hS, hTS, hbot, h⟩ := exists_hyp3_bar htight hg hT hT1
  exact ⟨S, hS, hTS, hbot, h3 _ _ _ _ _ h⟩

@[expose] def Thm3Alt3 {X : Type} [Group X] (Q T : Subgroup X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧
    AschbacherTheorem3.oTwoPrime (Q ⊔ T) =
      CFSG.Open.pCoreOf 2 (Q ⊔ T) ⊔ AschbacherTheorem3.oTwoPrime Q ∧
    CFSG.Open.pCoreOf 2 (Q ⊔ T) ⊓ AschbacherTheorem3.oTwoPrime Q = ⊥ ∧
    ⁅CFSG.Open.pCoreOf 2 (Q ⊔ T), AschbacherTheorem3.oTwoPrime Q⁆ = ⊥ ∧
    CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 (Q ⊔ T)) ∧
    Nat.card (CFSG.Open.pCoreOf 2 (Q ⊔ T)) = 2 ^ n ∧
    Nonempty (AschbacherTheorem3.oTwoPrime Q ≃* PSL(2, GaloisField 2 n))

theorem commutator_mem_or_thm3Alt3 (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G}
    (htight : TightlyEmbedded Q) {g : G} (hg : g ∉ normalizer (Q : Set G)) {T E : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hET : E ≤ T)
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) :
    (∀ t ∈ T, ∀ k ∈ twoPrimeLayerIn Q, t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn Q) ∨
      Thm3Alt3 (bar Q Q) (bar Q T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have hE2 : IsPGroup 2 E := isPGroup_of_sq_eq_one hE
  have hT1 : T ≠ ⊥ := by
    intro h
    have : Nat.card E = 1 := by
      rw [card_eq_one, eq_bot_iff]
      exact h ▸ hET
    rw [hE4] at this
    norm_num at this
  obtain ⟨S, hS, hTS, -, hconc⟩ := exists_thm3Conclusion h3 htight hg hT hT1
  have hQn : bar Q Q ≤ normalizer (bar Q Q : Set (Bar Q)) := le_normalizer
  have hTn : bar Q T ≤ normalizer (bar Q Q : Set (Bar Q)) :=
    bar_le_normalizer hTH le_normalizer
  have hSn : bar Q S ≤ normalizer (bar Q Q : Set (Bar Q)) := by
    refine (bar_mono Q hS.le).trans ?_
    rw [bar_sup le_normalizer hTH]
    exact sup_le hQn hTn
  have hS2 : IsPGroup 2 (bar Q S) := isPGroup_bar hS.isPGroup
  have hTSb : bar Q T ≤ bar Q S := bar_mono Q hTS
  suffices hW : (∃ W : Subgroup (Bar Q), IsPGroup 2 W ∧ bar Q T ≤ W ∧
      W ≤ normalizer (bar Q Q : Set (Bar Q)) ∧ bar Q Q ≤ normalizer (W : Set (Bar Q))) ∨
      Thm3Alt3 (bar Q Q) (bar Q T) by
    rcases hW with ⟨W, hW2, hTW, hWN, hNW⟩ | h
    · left
      have hWs : Group.IsSolvable W := by
        have := hW2.isNilpotent
        infer_instance
      exact commutator_mem_oddCoreIn_of_solvable hTH hWs hTW hWN hNW
    · exact Or.inr h
  rcases hconc with ⟨hcyc, -, -⟩ | h2 | h3' | ⟨x, hx, -, -, -, -, hN4, -, -⟩ |
      ⟨hN5, -, -, -, -, -, -⟩
  ·
    exfalso
    refine not_isCyclic_of_fourGroup (bar_mono Q hET) ?_ ?_ hcyc
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (mem_bar_iff Q E x).mp hx
      rw [← map_pow, toBar_eq_one_iff]
      have : ((y ^ 2 : normalizer (Q : Set G)) : G) = 1 := by simpa using hE _ hy
      rw [this]
      exact one_mem _
    · rw [card_bar_of_isPGroup hE2 (hET.trans hTH), hE4]
  ·
    exact Or.inl ⟨bar Q T, isPGroup_bar hT.isPGroup, le_rfl, hTn, le_sup_left.trans h2⟩
  · exact Or.inr h3'
  ·
    exact Or.inl ⟨_, hS2.to_le (relative_weak_closure_le _ _ _),
      subgroup_le_relative_weak_closure _ _ _ hTSb, (relative_weak_closure_le _ _ _).trans hSn,
      le_sup_left.trans hN4⟩
  ·
    exact Or.inl ⟨_, hS2.to_le (relative_weak_closure_le _ _ _),
      subgroup_le_relative_weak_closure _ _ _ hTSb, (relative_weak_closure_le _ _ _).trans hSn,
      le_sup_left.trans hN5⟩

theorem le_normalizer_or_thm3Alt3 (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G}
    (htight : TightlyEmbedded Q) {g : G} (hg : g ∉ normalizer (Q : Set G)) {T E : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hET : E ≤ T)
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) :
    twoPrimeLayerIn Q ≤ normalizer (rightConjugate Q g : Set G) ∨ Thm3Alt3 (bar Q Q) (bar Q T) := by
  rcases commutator_mem_or_thm3Alt3 h3 htight hg hT hET hE hE4 with hc | h
  · left
    have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
    have hTQg : T ≤ rightConjugate Q g := hT.le.trans inf_le_left
    have hcov := le_inf_centralizer_sup (isPGroup_of_sq_eq_one hE) (odd_card_oddCoreIn Q)
      (by rw [← oddCoreIn_twoPrimeLayerIn Q]; exact oddCoreIn_le _)
      ((twoPrimeLayerIn_le Q).trans (normalIn_le_normalizer (oddCoreIn_normalIn Q)))
      ((hET.trans hTH).trans (normalizer_le_normalizer_oddCoreIn Q))
      fun t ht k hk => hc t (hET ht) k hk
    have hQgt := rightConjugate_tightlyEmbedded Q htight g
    have hne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
    obtain ⟨⟨e, heE⟩, he1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have hCe : centralizer (E : Set G) ≤ normalizer (rightConjugate Q g : Set G) :=
      (centralizer_le (Set.singleton_subset_iff.mpr heE)).trans
        (centralizer_le_of_involution hQgt (hTQg (hET heE)) (orderOf_eq_prime (hE e heE) he1'))
    have hO : oddCoreIn Q ≤ normalizer (rightConjugate Q g : Set G) :=
      le_normalizer_of_fourGroup hQgt (hET.trans hTQg) hE hE4 (odd_card_oddCoreIn Q)
        ((hET.trans hTH).trans (normalizer_le_normalizer_oddCoreIn Q))
    exact hcov.trans (sup_le (inf_le_right.trans hCe) hO)
  · exact Or.inr h

end CFSG.ComponentClassification.Asc75T4
