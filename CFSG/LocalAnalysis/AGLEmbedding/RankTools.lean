module

public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

open scoped IsMulCommutative

namespace CFSG.AGLEmbedding

open CFSG.Open

section Barred

variable {G : Type} [Group G] [Finite G]

theorem pRank_barM_eq {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (M A : Subgroup G) (hAM : A ≤ M) :
    Open.pRank q (barM M A) = Open.pRank q A := by
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hO : q.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  rw [barM, pRank_map_mk_eq_pRank_map_subtype hq _ hO, Subgroup.map_subgroupOf_eq_of_le hAM]

end Barred

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem pRank_add_le_pRank_sup_of_coprime {q : ℕ} (hq : q.Prime) {A B : Subgroup X}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAB : Nat.Coprime q (Nat.card (A ⊓ B : Subgroup X))) :
    Open.pRank q A + Open.pRank q B ≤ Open.pRank q (A ⊔ B) := by
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hq1 A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hq1 B
  let f : E₁ × E₂ →* X := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x (hE₁A x.2) y (hE₂B y.2))
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : X) * y = 1 := hxy
    have hxB : (x : X) ∈ B := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact B.inv_mem (hE₂B y.2)
    have hx : (x : X) ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hE₁A x.2, hxB⟩
    have hx1 : (x : X) = 1 := by
      have h1 : orderOf (⟨x, hx⟩ : (A ⊓ B : Subgroup X)) ∣ Nat.card (A ⊓ B : Subgroup X) :=
        orderOf_dvd_natCard _
      have h2 : orderOf (⟨x, hx⟩ : (A ⊓ B : Subgroup X)) ∣ q := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext (by simpa using hE₁.2 x x.2)
      have h3 := Nat.eq_one_of_dvd_coprimes hAB h2 h1
      have := orderOf_eq_one_iff.mp h3
      simpa using congrArg Subtype.val this
    have hy : (y : X) = 1 := by rw [hx1, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx1, Subtype.ext hy⟩
  have hc₁' := hE₁.1
  have hc₂' := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hq1 (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, hc₁, hc₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (hE₁A a.2)) (Subgroup.mem_sup_right (hE₂B b.2))

theorem pRank_le_pRank_inf_centralizer_add_pRank {q : ℕ} (hq : q.Prime) {L E : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hEL : E ≤ L ⊔ Subgroup.centralizer (L : Set X))
    (hZ : ¬ q ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set X) : Subgroup X)) :
    Open.pRank q E ≤ Open.pRank q (E ⊓ Subgroup.centralizer (L : Set X)) + Open.pRank q L := by
  set N := Subgroup.normalizer (L : Set X) with hNdef
  set C := Subgroup.centralizer (L : Set X) with hCdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  set C' : Subgroup N := C.subgroupOf N
  have hC'n : C'.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer _
  set L' : Subgroup N := L.subgroupOf N
  set f := QuotientGroup.mk' C'
  set E' : Subgroup N := E.subgroupOf N
  have hmapE : E'.map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEN
  have hmapL : L'.map N.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLN
  have hE' : Open.pRank q E' = Open.pRank q E := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq N.subtype
      N.subtype_injective E', hmapE]
  have hL' : Open.pRank q L' = Open.pRank q L := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq N.subtype
      N.subtype_injective L', hmapL]
  have hEC' : Open.pRank q (E' ⊓ f.ker) ≤ Open.pRank q (E ⊓ C) := by
    rw [QuotientGroup.ker_mk']
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq N.subtype
      N.subtype_injective (E' ⊓ C')]
    refine CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq ?_
    rintro _ ⟨x, ⟨hxE, hxC⟩, rfl⟩
    exact ⟨hxE, hxC⟩
  have h1 := pRank_le_pRank_inf_ker_add_pRank_map hq f E'
  have hmap : E'.map f ≤ L'.map f := by
    rintro _ ⟨e, he, rfl⟩
    have heLC : (e : X) ∈ ((L ⊔ C : Subgroup X) : Set X) := hEL he
    have hNC : N ≤ Subgroup.normalizer (C : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hNC)] at heLC
    obtain ⟨l, hl, c, hc, hlc⟩ := heLC
    refine ⟨⟨l, hLN hl⟩, hl, ?_⟩
    have hcN : (⟨c, hCN hc⟩ : N) ∈ C' := hc
    have he' : e = ⟨l, hLN hl⟩ * ⟨c, hCN hc⟩ := Subtype.ext hlc.symm
    have hfc : f ⟨c, hCN hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
    rw [he', map_mul, hfc, mul_one]
  have h2 : Open.pRank q (L'.map f) ≤ Open.pRank q L' := by
    have hker : ¬ q ∣ Nat.card (f.comp L'.subtype).ker := by
      intro hdvd
      apply hZ
      set K := (f.comp L'.subtype).ker
      have hinj : Function.Injective (N.subtype.comp L'.subtype) :=
        N.subtype_injective.comp L'.subtype_injective
      have hcard : Nat.card (K.map (N.subtype.comp L'.subtype)) = Nat.card K :=
        Subgroup.card_map_of_injective hinj
      refine hdvd.trans (hcard ▸ Subgroup.card_dvd_of_le ?_)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have : ((x : N) : N) ∈ C' := (QuotientGroup.eq_one_iff _).mp hx
      exact this
    have := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hq (f.comp L'.subtype) hker ⊤
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    calc Open.pRank q (L'.map f) ≤ Open.pRank q (⊤ : Subgroup L') := this
      _ = Open.pRank q L' := by
        rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective q hq L'.subtype
          L'.subtype_injective ⊤, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h3 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq hmap
  omega

end Rank

end CFSG.AGLEmbedding
