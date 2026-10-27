module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar1
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

@[expose] def dPart (p : ℕ) {P : Type*} [Group P] (C : Subgroup P) : Subgroup P :=
  ⁅C, C⁆ ⊔ Subgroup.closure {x | x ∈ C ∧ Nat.Coprime (orderOf x) p}

variable {Y : Type} [Group Y] [Finite Y]

abbrev proj (Y : Type) [Group Y] : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _

omit [Finite Y] in
theorem exists_central_of_fixed {S : Subgroup (MulAut Y)} {a : Y}
    (ha : proj Y a ∈ c25Fix (S.map (centerDescend Y))) {s : MulAut Y} (hs : s ∈ S) :
    ∃ z ∈ Subgroup.center Y, s a = a * z := by
  refine ⟨a⁻¹ * s a, ?_, by group⟩
  have h := ha (centerDescend Y s) ⟨s, hs, rfl⟩
  have h2 : ((s a : Y) : Y ⧸ Subgroup.center Y) = (a : Y ⧸ Subgroup.center Y) := h
  exact QuotientGroup.eq.1 h2.symm

theorem commutator_mem_map {S : Subgroup (MulAut Y)} {a b : Y}
    (ha : proj Y a ∈ c25Fix (S.map (centerDescend Y)))
    (hb : proj Y b ∈ c25Fix (S.map (centerDescend Y))) :
    ⁅proj Y a, proj Y b⁆ ∈ (c25Fix S).map (proj Y) := by
  refine ⟨⁅a, b⁆, ?_, map_commutatorElement (proj Y) a b⟩
  intro s hs
  obtain ⟨z₁, hz₁, h₁⟩ := exists_central_of_fixed ha hs
  obtain ⟨z₂, hz₂, h₂⟩ := exists_central_of_fixed hb hs
  rw [map_commutatorElement s a b, h₁, h₂]
  exact commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 hz₁ b))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ a))

theorem coprime_mem_map {p : ℕ} [Fact p.Prime] (hZ : IsPGroup p (Subgroup.center Y)) {S : Subgroup (MulAut Y)}
    {x : Y ⧸ Subgroup.center Y} (hx : x ∈ c25Fix (S.map (centerDescend Y)))
    (hxo : Nat.Coprime (orderOf x) p) : x ∈ (c25Fix S).map (proj Y) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  set e := Nat.card (Subgroup.center Y) with he
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hcop : Nat.Coprime (orderOf (a : Y ⧸ Subgroup.center Y)) e := by
    rw [he, hn]
    exact Nat.Coprime.pow_right n hxo
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  have hek : e ∣ k := (Nat.modEq_zero_iff_dvd.1 hk2)
  refine ⟨a ^ k, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz, hsz⟩ := exists_central_of_fixed hx hs
    rw [map_pow, hsz, (show Commute a z from Subgroup.mem_center_iff.1 hz a).mul_pow]
    have hz1 : z ^ k = 1 := by
      obtain ⟨t, rfl⟩ := hek
      have : z ^ e = 1 := by
        have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center Y))
        exact congrArg Subtype.val h
      rw [pow_mul, this, one_pow]
    rw [hz1, mul_one]
  · show (proj Y) (a ^ k) = (a : Y ⧸ Subgroup.center Y)
    rw [map_pow]
    show ((a : Y ⧸ Subgroup.center Y)) ^ k = (a : Y ⧸ Subgroup.center Y)
    conv_rhs => rw [← pow_one (a : Y ⧸ Subgroup.center Y)]
    exact (pow_eq_pow_iff_modEq).2 hk1

theorem dPart_le_map {p : ℕ} [Fact p.Prime] (hZ : IsPGroup p (Subgroup.center Y)) (S : Subgroup (MulAut Y)) :
    dPart p (c25Fix (S.map (centerDescend Y))) ≤ (c25Fix S).map (proj Y) := by
  refine sup_le (Subgroup.commutator_le.2 fun x hx y hy => ?_)
    ((Subgroup.closure_le _).2 fun x hx => coprime_mem_map hZ hx.1 hx.2)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact commutator_mem_map hx hy

theorem gen_of_dPart {p : ℕ} [Fact p.Prime] (hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤)
    (hZ : IsPGroup p (Subgroup.center Y)) (𝒮 : Set (Subgroup (MulAut Y)))
    (h : ⊤ ≤ ⨆ S ∈ 𝒮, dPart p (c25Fix (S.map (centerDescend Y)))) :
    ⊤ ≤ ⨆ S ∈ 𝒮, c25Fix S := by
  set H := ⨆ S ∈ 𝒮, c25Fix S with hH
  have hmap : ⊤ ≤ H.map (proj Y) := by
    refine h.trans (iSup₂_le fun S hS => (dPart_le_map hZ S).trans (Subgroup.map_mono ?_))
    exact le_iSup₂_of_le S hS le_rfl
  rw [top_le_iff] at hmap
  have hHZ : H ⊔ (proj Y).ker = ⊤ := by
    have h2 := Subgroup.comap_map_eq (proj Y) H
    rw [hmap, Subgroup.comap_top] at h2
    exact h2.symm
  have hker : (proj Y).ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  rw [hker] at hHZ
  refine hperf.symm.le.trans (Subgroup.commutator_le.2 ?_)
  intro k₁ _ k₂ _
  have hk₁ : k₁ ∈ H ⊔ Subgroup.center Y := by rw [hHZ]; trivial
  have hk₂ : k₂ ∈ H ⊔ Subgroup.center Y := by rw [hHZ]; trivial
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₂
  rw [commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 hz₁ m₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ m₁))]
  exact H.mul_mem (H.mul_mem (H.mul_mem hm₁ hm₂) (H.inv_mem hm₁)) (H.inv_mem hm₂)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
