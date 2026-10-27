module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OutLocalQ

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.EvenSporadicStandard.Induction.TMemRu CFSG.Sporadic.RuSchreier

section Model

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem card_centralizer_ruA0 :
    Nat.card ↥(centralizer ({(⟨ruA0, tmA0_mem⟩ : ↥ruP)} : Set ↥ruP)) = 116480 := by
  obtain ⟨A, B, z, l, S, hAP, hBP, hAc, hBc, hA5, hB7, -⟩ := tmRu_facts
  have ha0 : orderOf (⟨ruA0, tmA0_mem⟩ : ↥ruP) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_tmA0
  have hBmem : (⟨B, hBP⟩ : ↥ruP) ∈ centralizer ({(⟨ruA0, tmA0_mem⟩ : ↥ruP)} : Set ↥ruP) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hBc
  have h7 : 7 ∣ Nat.card ↥(centralizer ({(⟨ruA0, tmA0_mem⟩ : ↥ruP)} : Set ↥ruP)) := by
    have := Subgroup.orderOf_dvd_natCard _ hBmem
    rwa [Subgroup.orderOf_mk, hB7] at this
  rcases (ruFacts_ruP.card_centralizer _ ha0) with h | h
  · rw [h] at h7
    exact absurd h7 (by norm_num)
  · exact h

theorem ru_model (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    ∃ Ψ : ↥L →* Equiv.Perm (Fin 4060), Function.Injective Ψ ∧ (∀ x, Ψ x ∈ ruP) ∧
      (∀ y ∈ ruP, ∃ x, Ψ x = y) ∧ Ψ ⟨u, hQ.1⟩ = ruA0 := by
  obtain ⟨f⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hL
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hQ.2.1
  have hcu := card_centralizer_of_ruPair hL hQ
  have hcu' : Nat.card (centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) = 116480 := by
    rw [FactsA.card_centralizer_subtype L ⟨u, hQ.1⟩]; exact hcu
  have hs : orderOf (f ⟨u, hQ.1⟩) = 2 := by rw [MulEquiv.orderOf_eq, hu2]
  have hcf : Nat.card (centralizer ({f ⟨u, hQ.1⟩} : Set ↥ruP)) = 116480 := by
    rw [← card_centralizer_eq_of_mulEquiv f]
    exact hcu'
  have ha0 : orderOf (⟨ruA0, tmA0_mem⟩ : ↥ruP) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_tmA0
  have hconj : IsConj (f ⟨u, hQ.1⟩) ⟨ruA0, tmA0_mem⟩ :=
    ruFacts_ruP.isConj_B _ _ hs ha0 hcf card_centralizer_ruA0
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  refine ⟨ruP.subtype.comp (f.trans (MulAut.conj c)).toMonoidHom,
    ruP.subtype_injective.comp (f.trans (MulAut.conj c)).injective, fun x => (_ : ↥ruP).2,
    fun y hy => ?_, congrArg Subtype.val hc⟩
  obtain ⟨x, hx⟩ := (f.trans (MulAut.conj c)).surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem map_centralizer_eq_tmE {Ψ : ↥L →* Equiv.Perm (Fin 4060)} (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ ruP) (hΨR : ∀ y ∈ ruP, ∃ x, Ψ x = y) {u' : ↥L} (hΨu : Ψ u' = ruA0) :
    (centralizer ({u'} : Set ↥L)).map Ψ = tmE := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hΨL x, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
  · rintro ⟨hyP, hyc⟩
    obtain ⟨x, rfl⟩ := hΨR y hyP
    refine ⟨x, mem_centralizer_singleton_iff.2 (hΨ ?_), rfl⟩
    rw [map_mul, map_mul, hΨu]
    exact mem_centralizer_singleton_iff.1 hyc

theorem ru_conj_mem (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u)
    {x : ↥L} (hx : x ∈ centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) {κ : ↥L}
    (hκ : κ ∈ K.subgroupOf L) : x * κ * x⁻¹ ∈ K.subgroupOf L := by
  have hn := hf.normal H L K u hL hQ
  have hxu : (x : H) * u = u * (x : H) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
  let c : ↥(L ⊓ centralizer ({u} : Set H)) := ⟨x, x.2, mem_centralizer_singleton_iff.2 hxu⟩
  have hκC : (κ : H) ∈ L ⊓ centralizer ({u} : Set H) :=
    ⟨κ.2, mem_centralizer_singleton_iff.2 (hQ.2.2.2.1 κ (mem_subgroupOf.1 hκ))⟩
  have h1 := hn.conj_mem ⟨κ, hκC⟩ (mem_subgroupOf.2 (mem_subgroupOf.1 hκ)) c
  exact mem_subgroupOf.2 (mem_subgroupOf.1 h1)

theorem ru_quot2Data (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u)
    {Ψ : ↥L →* Equiv.Perm (Fin 4060)} (hΨ : Function.Injective Ψ) (hΨL : ∀ x, Ψ x ∈ ruP)
    (hΨR : ∀ y ∈ ruP, ∃ x, Ψ x = y) (hΨu : Ψ ⟨u, hQ.1⟩ = ruA0) :
    Quot2Data tmE.subtype ((K.subgroupOf L).map Ψ) ∧
      Nat.card ↥((K.subgroupOf L).map Ψ) = 29120 := by
  have hKL := hQ.2.2.1
  have hE := map_centralizer_eq_tmE hΨ hΨL hΨR hΨu
  have hKLle : K.subgroupOf L ≤ centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hQ.2.2.2.1 k (mem_subgroupOf.1 hk))
  have hKPle : (K.subgroupOf L).map Ψ ≤ tmE := hE ▸ Subgroup.map_mono hKLle
  have hcardKP : Nat.card ↥((K.subgroupOf L).map Ψ) = 29120 := by
    rw [Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hQ.2.2.2.2
  have hcu : Nat.card (centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) = 116480 := by
    rw [FactsA.card_centralizer_subtype L ⟨u, hQ.1⟩]
    exact card_centralizer_of_ruPair hL hQ
  have hcardE : Nat.card ↥tmE = 116480 := by
    rw [← hE, Subgroup.card_map_of_injective hΨ]
    exact hcu
  let e : ↥K ≃* ↥((K.subgroupOf L).map Ψ) :=
    (Subgroup.subgroupOfEquivOfLe hKL).symm.trans (Subgroup.equivMapOfInjective _ Ψ hΨ)
  have hsimple : IsSimpleGroup ↥((K.subgroupOf L).map Ψ) :=
    (MulEquiv.isSimpleGroup_congr e).1 (hf.simple H L K u hL hQ)
  have hnc : ∃ a b : ↥((K.subgroupOf L).map Ψ), a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hcardKP]; norm_num)
  refine ⟨⟨?_, ?_, hsimple, hnc, ⟨2, ?_⟩, ⟨0, ?_⟩, ?_⟩, hcardKP⟩
  · rw [Subgroup.range_subtype]
    exact hKPle
  · rw [Subgroup.range_subtype]
    intro y hy
    rw [← hE] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      refine ⟨x * κ * x⁻¹, ru_conj_mem hf hL hQ hx hκ, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨κ, hκ, hκh⟩
      have hmem := ru_conj_mem hf hL hQ (Subgroup.inv_mem _ hx) hκ
      rw [inv_inv] at hmem
      refine ⟨x⁻¹ * κ * x, hmem, ?_⟩
      rw [map_mul, map_mul, map_inv, hκh]
      group
  · rw [Subgroup.range_subtype, hcardE, hcardKP]
    norm_num
  · rw [Subgroup.ker_subtype, Subgroup.card_bot]
    rfl
  · rw [Subgroup.ker_subtype, Subgroup.card_bot, hcardKP]
    norm_num

theorem sol78Local39Q_ru (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru) :
    Sol78Local39Q .Ru RuPair := by
  intro H _ _ N L K t u hcov hset hP
  have hL : IsSporadic ↥L .Ru := hcov.isSporadic_of_mult hmult
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := ru_model hL hP
  obtain ⟨hq, hKcard⟩ := ru_quot2Data hf hL hP hΨ hΨL hΨR hΨu
  obtain ⟨M⟩ := ruOutRowModel hq hKcard
  have hKperf : Group.IsPerfect ↥K := (ruPair_isQuasisimple hf hL hP).1
  exact M.local39_of_fields hP.1 hP.2.1 hP.2.2.1 (mem_centralizer_iff.2 hP.2.2.2.1)
    hset.hyp35 Ψ hΨ hΨL hΨR hΨu hKperf (hP.2.2.2.2.trans hKcard.symm)

end Model

end CFSG.EvenSporadicStandard.Induction
