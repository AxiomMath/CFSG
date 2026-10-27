module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.Monster.B.Fischer


theorem card_ge_of_isU62 {X : Type} [Group X] [Finite X] (h : IsU62 (X ⧸ center X)) :
    9196830720 ≤ Nat.card X := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card (X ⧸ center X) = 9196830720 := by
    rw [Nat.card_congr e.toEquiv, fi22D_card_quotient]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
  have h3 : 0 < Nat.card ↥(center X) := Nat.card_pos
  rw [h1] at h2
  omega

theorem fi22_equiv_of_inner {Y : Type} [Group Y] [Finite Y] {N' P : Subgroup Y}
    (hL : IsSporadic ↥N' .Fi22) {t : Y} (htN : t ∈ N') (ht2 : orderOf t = 2) (hPN : P ≤ N')
    (hPt : P ≤ centralizer ({t} : Set Y)) (hPcard : 9196830720 ≤ Nat.card ↥P) :
    Nonempty (↥P ≃* Fi22D) := by
  have hle : Nat.card ↥P ≤ Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) :=
    Subgroup.card_le_of_le (le_inf hPN hPt)
  have hC18 : Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) = 18393661440 := by
    rcases fi22_card_inf_centralizer hL htN ht2 with h | h | h <;> omega
  obtain ⟨f⟩ := fi22_pair_equiv (K := N' ⊓ centralizer ({t} : Set Y)) hL htN ht2 inf_le_left
    (fun k hk => mem_centralizer_singleton_iff.1 hk.2) hC18.ge
  set C : Subgroup Y := N' ⊓ centralizer ({t} : Set Y) with hCdef
  have hPC : P ≤ C := le_inf hPN hPt
  have : Group.IsPerfect Fi22D := fi22D_isQuasisimple.1
  have : Group.IsPerfect ↥C :=
    Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup ↥C, Q = P.subgroupOf C := ⟨_, rfl⟩
  have hQcard : Nat.card ↥Q = Nat.card ↥P := by
    rw [hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hQidx : Q.index * Nat.card ↥Q = Nat.card ↥C := Subgroup.index_mul_card Q
  have hidx : Q.index ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ Q.index := by omega
    have := Nat.mul_le_mul_right (Nat.card ↥Q) h3
    omega
  have hQn : Q.Normal := by
    have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases (by omega : Q.index = 1 ∨ Q.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have hCQ : (⊤ : Subgroup ↥C) ≤ Q := Hyp.le_of_perfect_of_index_le_two hidx inferInstance
  have hCP : C ≤ P := fun c hc => by
    have h := hCQ (Subgroup.mem_top (⟨c, hc⟩ : ↥C))
    rw [hQ, Subgroup.mem_subgroupOf] at h
    exact h
  exact ⟨(MulEquiv.subgroupCongr (le_antisymm hPC hCP)).trans f⟩

theorem fi22_card_inf_centralizer_outer {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    [N'.Normal] (hC : centralizer (N' : Set Y) ≤ N') (hL : IsSporadic ↥N' .Fi22) {t : Y}
    (htN : t ∉ N') (ht2 : orderOf t = 2) :
    Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) = 3317760 ∨
      Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) = 1045094400 ∨
      Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) = 2903040 := by
  obtain ⟨e⟩ := hL
  obtain ⟨θ⟩ : Nonempty (↥N' ≃* ↥fi22P) := ⟨e.trans fi22PermEquiv⟩
  have hcenter : center ↥N' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : θ z ∈ center ↥fi22P := by
      rw [mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := θ.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz x]
    rw [HypOne.Fi22.center_fi22P, mem_bot] at h1
    rw [mem_bot]
    exact θ.injective (h1.trans (map_one θ).symm)
  have hC1 : centralizer (N' : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzN : (⟨z, hC hz⟩ : ↥N') ∈ center ↥N' := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hz g g.2)
    rw [hcenter, mem_bot] at hzN
    exact mem_bot.2 (congrArg Subtype.val hzN)
  have hA := HypOne.Fi22.fi22_autModel
  have hinj := hA.embed_injective N' θ hC1
  have hwP : hA.embed N' θ t ∉ fi22P := fun h => htN (by
    have h1 : hA.embed N' θ ↑(θ.symm ⟨hA.embed N' θ t, h⟩) = hA.embed N' θ t := by
      rw [hA.embed_coe N' θ (θ.symm ⟨hA.embed N' θ t, h⟩), MulEquiv.apply_symm_apply]
    have h2 := hinj h1
    rw [← h2]
    exact (θ.symm ⟨hA.embed N' θ t, h⟩).2)
  have hw2 : orderOf (hA.embed N' θ t) = 2 := by rw [orderOf_injective _ hinj, ht2]
  have hout := card_centralizerIn_fi22_outer (hA.embed_mem N' θ t) hwP hw2
  rw [Nat.card_congr (hA.centralizerEquiv N' θ hC1 t).toEquiv]
  exact hout

theorem fi22U62Sub_proved : Fi22U62Sub := by
  intro Y _ _ N' P hNn hC hL hPN ⟨t, ht2, hPt⟩ _ hU
  have : N'.Normal := hNn
  have hPcard : 9196830720 ≤ Nat.card ↥P := card_ge_of_isU62 hU
  by_cases htN : t ∈ N'
  · obtain ⟨e⟩ := fi22_equiv_of_inner hL htN ht2 hPN hPt hPcard
    obtain ⟨g⟩ := oddQuot_equiv_of_surj e.toMonoidHom e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, Subgroup.card_bot]
      exact odd_one)
    exact ⟨g.trans ((QuotientGroup.quotientMulEquivOfEq fi22D_oddCore).trans
      QuotientGroup.quotientBot)⟩
  · exfalso
    have hle : Nat.card ↥P ≤ Nat.card ↥(N' ⊓ centralizer ({t} : Set Y)) :=
      Subgroup.card_le_of_le (le_inf hPN hPt)
    have := fi22_card_inf_centralizer_outer hC hL htN ht2
    omega

end CFSG.EvenSporadicStandard.Induction.Fi
