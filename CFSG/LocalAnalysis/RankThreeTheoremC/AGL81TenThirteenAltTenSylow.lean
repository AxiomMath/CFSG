module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open Equiv Equiv.Perm
open scoped commutatorElement

theorem natCard_altTen : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_sylow_five (S : Sylow 5 (alternatingGroup (Fin 10))) :
    Nat.card (S : Subgroup (alternatingGroup (Fin 10))) = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hidx := S.not_dvd_index
  have hmul := (S : Subgroup (alternatingGroup (Fin 10))).card_mul_index
  rw [natCard_altTen, hk] at hmul
  have hk3 : k ≤ 2 := by
    by_contra h
    have h1 : 5 ^ 3 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
    have h2 : 5 ^ k ∣ 1814400 := ⟨_, hmul.symm⟩
    have := h1.trans h2
    norm_num at this
  interval_cases k
  · rw [pow_zero, one_mul] at hmul
    exact absurd (hmul ▸ (by norm_num : 5 ∣ 1814400)) hidx
  · have h1 : (S : Subgroup (alternatingGroup (Fin 10))).index = 362880 := by omega
    exact absurd (h1 ▸ (by norm_num : 5 ∣ 362880)) hidx
  · rw [hk]
    norm_num

@[expose] def restrictB {B : Finset (Fin 10)} (S : Subgroup (alternatingGroup (Fin 10)))
    (hS : ∀ s ∈ S, ∀ i ∈ B, (s : Perm (Fin 10)) i ∈ B) :
    ↥S →* Perm {x // x ∈ B} where
  toFun s := (s : Perm (Fin 10)).subtypePerm fun x => by
    refine ⟨fun hx => ?_, hS s s.2 x⟩
    by_contra hxB
    have himg : B.image (s : Perm (Fin 10)) = B := Finset.eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact hS s s.2 z hz)
      (by rw [Finset.card_image_of_injective _ (s : Perm (Fin 10)).injective])
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp (himg.symm ▸ hx :
      (s : Perm (Fin 10)) x ∈ B.image (s : Perm (Fin 10)))
    exact hxB ((s : Perm (Fin 10)).injective hzx ▸ hz)
  map_one' := Equiv.ext fun x => rfl
  map_mul' a b := Equiv.ext fun x => rfl

theorem exists_fix_of_sylow {B : Finset (Fin 10)} (hB : B.card = 5)
    (S : Sylow 5 (alternatingGroup (Fin 10)))
    (hS : ∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), ∀ i ∈ B,
      (s : Perm (Fin 10)) i ∈ B) :
    ∃ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), s ≠ 1 ∧
      ∀ i ∈ B, (s : Perm (Fin 10)) i = i := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set r := restrictB (S : Subgroup (alternatingGroup (Fin 10))) hS with hr
  have hcard := Subgroup.card_ker_mul_card_range r
  rw [card_sylow_five] at hcard
  have hrange5 : Nat.card r.range ≤ 5 := by
    have hp : IsPGroup 5 r.range :=
      IsPGroup.of_surjective S.isPGroup' r.rangeRestrict r.rangeRestrict_surjective
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp
    have hdvd : Nat.card r.range ∣ 120 := by
      have hBc : Nat.card {x // x ∈ B} = 5 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, hB]
      have h1 := Subgroup.card_subgroup_dvd_card r.range
      rw [Nat.card_perm, hBc, show Nat.factorial 5 = 120 by rfl] at h1
      exact h1
    rw [hj] at hdvd ⊢
    have hj1 : j ≤ 1 := by
      by_contra h
      have h1 : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 (by omega)
      have := h1.trans hdvd
      norm_num at this
    interval_cases j <;> norm_num
  have hker : r.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, one_mul] at hcard
    omega
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨s, s.2, fun h => hs1 (Subtype.ext (Subtype.ext h)), fun i hi => ?_⟩
  have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hs) ⟨i, hi⟩
  exact congrArg Subtype.val h1

theorem card_altB {B : Finset (Fin 10)} (hB : B.card = 5) :
    Nat.card (alternatingGroup.ofSubtype B).range = 60 := by
  have hc : Fintype.card {x // x ∈ B} = 5 := by rw [Fintype.card_coe, hB]
  have e : {x // x ∈ B} ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  rw [Nat.card_congr ((MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans
    e.altCongrHom).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem swap_iff {B : Finset (Fin 10)} (hB : B.card = 5) {g : Perm (Fin 10)}
    (hg : ∀ i ∈ B, g i ∉ B) : ∀ x, g x ∈ B ↔ x ∉ B := by
  have hc : Bᶜ.card = 5 := by rw [Finset.card_compl, hB]; rfl
  have himg : B.image g = Bᶜ := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_compl.mpr (hg z hz))
    (by rw [Finset.card_image_of_injective _ g.injective, hc, hB])
  intro x
  constructor
  · intro hgx hxB
    exact hg x hxB hgx
  · intro hxB
    by_contra hgx
    obtain ⟨z, hz, hzx⟩ :=
      Finset.mem_image.mp (himg.symm ▸ Finset.mem_compl.mpr hgx : g x ∈ B.image g)
    exact hxB (g.injective hzx ▸ hz)

theorem isQuasisimple_of_equiv_alt5 {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    CFSG.Open.IsQuasisimple X := by
  haveI hs : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  haveI : Nontrivial X := e.symm.injective.nontrivial
  haveI : IsSimpleGroup X :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have h3 : IsMulCommutative (alternatingGroup (Fin 5)) := ⟨⟨fun a b => by
      apply e.symm.injective
      rw [map_mul, map_mul, hc]⟩⟩
    have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 5)).mp h3
    rw [Nat.card_fin] at this
    omega
  have hcen : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      rw [← commutatorElement_eq_one_iff_mul_comm]
      have : ⁅a, b⁆ ∈ commutator X := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h] at this
      exact this
    · exact h
  · have f : X ≃* X ⧸ Subgroup.center X :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
    haveI : Nontrivial (X ⧸ Subgroup.center X) := f.injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective f.toMonoidHom f.surjective

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
