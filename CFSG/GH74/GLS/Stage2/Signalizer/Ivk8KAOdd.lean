module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
  CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Fix

variable {Y : Type} [Group Y]

theorem map_fixSub_of_comm {α g : MulAut Y} (h : g * α = α * g) :
    (fixSub α).map g.toMonoidHom = fixSub α := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSub] at hx ⊢
    have h1 := congrArg (fun φ : MulAut Y => φ x) h
    simp only [MulAut.mul_apply] at h1
    change α (g x) = g x
    rw [← h1, hx]
  · intro hy
    refine ⟨g⁻¹ y, ?_, by simp⟩
    rw [mem_fixSub] at hy ⊢
    have h2 : g⁻¹ * α = α * g⁻¹ := by
      calc g⁻¹ * α = g⁻¹ * (α * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * α) * g⁻¹ := by rw [h]
        _ = α * g⁻¹ := by group
    have h3 := congrArg (fun φ : MulAut Y => φ y) h2
    simp only [MulAut.mul_apply] at h3
    change α (g⁻¹ y) = g⁻¹ y
    rw [← h3, hy]

end Fix

section Bridge

variable {Y : Type} [Group Y]

@[expose] def OddCoreAut (Y : Type) [Group Y] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], Nonempty (S ≃* Y) →
    centralizer (S : Set X) = ⊥ → ∀ t : X, orderOf t = 2 →
      CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥

theorem kaNoP_of_oddCore_aut [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (hY : OddCoreAut Y) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KANoP α := by
  classical
  have hc : Subgroup.center Y = ⊥ := center_eq_bot_of_simple hs hna
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot hc
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have hSn : ((MulAut.conj : Y →* MulAut Y).range).Normal := conj_range_normal
  have hC : centralizer (((MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) :
      Set (MulAut Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    refine Subgroup.mem_bot.mpr (eq_one_of_commute_conj hc fun g => ?_)
    exact (hφ (MulAut.conj g) ⟨g, rfl⟩).symm
  have hαo : orderOf α = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hodd := hY (MulAut Y) _ ⟨(MonoidHom.ofInjective hinj).symm⟩ hC α hαo
  intro p hp hp2 N hN hNn hNp
  have : Fact p.Prime := ⟨hp⟩
  have hNnorm : fixSub α ≤ normalizer (N : Set Y) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hNn c hc' n hn, fun hn => ?_⟩
    have := hNn c⁻¹ ((fixSub α).inv_mem hc') _ hn
    simpa [mul_assoc] using this
  have hNO : N ≤ Op p (fixSub α) := le_Op_of_normal hN hNnorm hNp
  set O : Subgroup Y := Op p (fixSub α) with hO
  have hOle : O ≤ fixSub α := Op_le p (fixSub α)
  have hOp : IsPGroup p ↥O := isPGroup_Op p hp (fixSub α)
  have hOodd : Odd (Nat.card ↥O) := odd_card_of_isPGroup_odd_prime hp2 hOp
  let C : Subgroup (MulAut Y) := centralizer ({α} : Set (MulAut Y))
  let OX : Subgroup (MulAut Y) := O.map (MulAut.conj : Y →* MulAut Y)
  have hOXC : OX ≤ C := by
    rintro _ ⟨o, ho, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : α * MulAut.conj o * α⁻¹ = MulAut.conj (α o) := conj_apply_aut α o
    rw [mem_fixSub.1 (hOle ho)] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hnorm : (OX.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hon⟩ := hn
    have hg : (g : MulAut Y) * α = α * (g : MulAut Y) :=
      Subgroup.mem_centralizer_singleton_iff.1 g.2
    have hgo : (g : MulAut Y) * MulAut.conj o * (g : MulAut Y)⁻¹ = MulAut.conj ((g : MulAut Y) o) :=
      conj_apply_aut (g : MulAut Y) o
    have hmem : (g : MulAut Y) o ∈ O := by
      have h1 := Op_map p (g : MulAut Y) (fixSub α)
      rw [map_fixSub_of_comm hg] at h1
      have h2 : (g : MulAut Y) o ∈ (Op p (fixSub α)).map (g : MulAut Y).toMonoidHom := ⟨o, ho, rfl⟩
      rw [← h1] at h2
      exact h2
    refine ⟨(g : MulAut Y) o, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hon, hgo]
  have hcard : Nat.card ↥(OX.subgroupOf C) = Nat.card ↥O := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOXC).toEquiv,
      Subgroup.card_map_of_injective hinj]
  have hle : OX.subgroupOf C ≤ CFSG.oddCore ↥C :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hnorm (hcard ▸ hOodd)
  have hbot : OX.subgroupOf C = ⊥ := by
    rw [hodd] at hle
    exact le_bot_iff.mp hle
  have hOb : O = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    have h1 : (⟨MulAut.conj o, hOXC ⟨o, ho, rfl⟩⟩ : ↥C) ∈ OX.subgroupOf C :=
      Subgroup.mem_subgroupOf.2 ⟨o, ho, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : MulAut.conj o = 1 := congrArg Subtype.val h1
    exact Subgroup.mem_bot.2 (hinj (h2.trans (map_one _).symm))
  exact eq_bot_iff.2 (hNO.trans hOb.le)

theorem exists_noncomm_of_simple_of_not_prime [Finite Y] (hs : IsSimpleGroup Y)
    (h : ¬ (Nat.card Y).Prime) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup Y := { ‹Group Y› with mul_comm := fun a b => hcon a b }
  exact h IsSimpleGroup.prime_card

theorem kaNoP_of_oddCore_inner [Finite Y] {t : Y}
    (h : CFSG.oddCore ↥(centralizer ({t} : Set Y)) = ⊥) : KANoP (MulAut.conj t) := by
  intro p hp hp2 N hN hNn hNp
  have : Fact p.Prime := ⟨hp⟩
  rw [kn_fixSub_conj] at hN hNn
  have hnorm : (N.subgroupOf (centralizer ({t} : Set Y))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g g.2 n hn⟩
  have hodd : Odd (Nat.card ↥(N.subgroupOf (centralizer ({t} : Set Y)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv]
    exact odd_card_of_isPGroup_odd_prime hp2 hNp
  have hle := CFSG.ABGLocalTools.le_oddCore_of_normal hnorm hodd
  rw [h] at hle
  have hbot := le_bot_iff.mp hle
  rw [eq_bot_iff]
  intro n hn
  have h1 : (⟨n, hN hn⟩ : ↥(centralizer ({t} : Set Y))) ∈
      N.subgroupOf (centralizer ({t} : Set Y)) := hn
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem kaAll_of_allInner [Finite Y] (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hinner : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g)
    (hNoP : ∀ t : Y, t * t = 1 → t ≠ 1 → KANoP (MulAut.conj t)) {α : MulAut Y}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨t, rfl⟩ := hinner α
  have ht2 : t * t = 1 := hinj (by rw [map_mul, hα2, map_one])
  have ht1 : t ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hOutCyc : KAOutCyc Y := by
    intro p hp hp2 P hPp hPinn
    have hP : P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨g, rfl⟩ := hinner x
      exact Subgroup.mem_bot.2 (hPinn _ hx ⟨g, rfl⟩)
    rw [hP]
    infer_instance
  refine ka_all_of_noP hinj (hNoP t ht2 ht1) hOutCyc ?_
  intro x
  obtain ⟨g, hg⟩ := hinner ⁅x, MulAut.conj t⁆
  exact ⟨g, hg.symm⟩

theorem hOut_of_outAbelian (h : OutAbelian Y) (α : MulAut Y) :
    ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y := fun x => by
  rw [commutatorElement_def]
  exact h x α

theorem kaAll_of_oddCore_aut [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (hY : OddCoreAut Y) (hOutCyc : KAOutCyc Y)
    (hOut : OutAbelian Y) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α :=
  ka_all_of_noP (conj_injective_of_center_eq_bot (center_eq_bot_of_simple hs hna))
    (kaNoP_of_oddCore_aut hs hna hY hα2 hα1) hOutCyc (hOut_of_outAbelian hOut α)

end Bridge

section OutCyc

theorem kaOutCyc_of_card_outer_le_four {Y : Type} [Group Y] [Finite Y]
    (h : Nat.card (Outer Y) ≤ 4) : KAOutCyc Y := by
  intro p hp hp2 P hPp hPinn
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have hOfin : Finite (Outer Y) := inferInstance
  let f : ↥P →* Outer Y := (QuotientGroup.mk' (inner Y)).comp P.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : MulAut Y) ∈ inner Y := (QuotientGroup.eq_one_iff _).1 hx
    exact Subtype.ext (hPinn x x.2 hx')
  have hcard : Nat.card ↥P ≤ 4 := (Nat.card_le_card_of_injective f hinj).trans h
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hn1 : n ≤ 1 := by
    by_contra hn2
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    omega
  interval_cases n
  · have h1 : Nat.card ↥P = 1 := by rw [hn]; simp
    have : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · exact isCyclic_of_prime_card (p := p) (by rw [hn]; simp)

theorem kaOutCyc_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : KAOutCyc Y) : KAOutCyc Y' := by
  intro p hp hp2 P' hP' hinn
  let f : MulAut Y →* MulAut Y' := (MulAut.congr e).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.congr e).injective
  have hfsurj : Function.Surjective f := (MulAut.congr e).surjective
  let P : Subgroup (MulAut Y) := P'.comap f
  have hPp : IsPGroup p ↥P := IsPGroup.comap_of_injective hP' f hfinj
  have hPinn : ∀ x ∈ P, x ∈ innSub Y → x = 1 := by
    intro x hx hxi
    obtain ⟨y, rfl⟩ := hxi
    have hfx : f (MulAut.conj y) ∈ P' := hx
    have hfi : f (MulAut.conj y) ∈ innSub Y' := ⟨e y, (ka_congr_conj e y).symm⟩
    exact hfinj ((hinn _ hfx hfi).trans (map_one f).symm)
  have hc := h p hp hp2 P hPp hPinn
  let g : ↥P →* ↥P' := (f.comp P.subtype).codRestrict P' (fun x => x.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hfsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact isCyclic_of_surjective g hg

end OutCyc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
