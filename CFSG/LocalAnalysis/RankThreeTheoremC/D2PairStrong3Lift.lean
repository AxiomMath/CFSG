module

import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

theorem pRank_bot_eq_zero {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) :
    Open.pRank q (⊥ : Subgroup X) = 0 := by
  obtain ⟨E, hE, -, hEcard⟩ := pRank_attained q hq (⊥ : Subgroup X)
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hEcard
  by_contra hne
  have := Nat.one_lt_pow hne hq.one_lt
  omega

variable {X : Type*} [Group X] [Finite X]

theorem pRank_le_pRank_inf_sup_centralizer {q : ℕ} (hq : q.Prime) {L E : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hEL : E ≤ L ⊔ Subgroup.centralizer (L : Set X))
    (hZ : ¬ q ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set X) : Subgroup X))
    (hEC : E ⊓ Subgroup.centralizer (L : Set X) = ⊥) :
    Open.pRank q E ≤ Open.pRank q (L ⊓ (E ⊔ Subgroup.centralizer (L : Set X))) := by
  set N := Subgroup.normalizer (L : Set X) with hNdef
  set C := Subgroup.centralizer (L : Set X) with hCdef
  set D : Subgroup X := L ⊓ (E ⊔ C) with hDdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hDN : D ≤ N := inf_le_left.trans hLN
  set C' : Subgroup N := C.subgroupOf N
  have hC'n : C'.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer _
  set D' : Subgroup N := D.subgroupOf N
  set f := QuotientGroup.mk' C'
  set E' : Subgroup N := E.subgroupOf N
  have hmapE : E'.map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEN
  have hmapD : D'.map N.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDN
  have hE' : Open.pRank q E' = Open.pRank q E := by
    rw [← pRank_map_of_injective q hq N.subtype N.subtype_injective E', hmapE]
  have hD' : Open.pRank q D' = Open.pRank q D := by
    rw [← pRank_map_of_injective q hq N.subtype N.subtype_injective D', hmapD]
  have hker : E' ⊓ f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxE : (x : X) ∈ E := hx.1
    have hxC : (x : X) ∈ C := by
      have : x ∈ C' := (QuotientGroup.eq_one_iff _).mp hx.2
      exact this
    have : (x : X) ∈ E ⊓ C := ⟨hxE, hxC⟩
    rw [hEC, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have h1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hq f E'
  rw [hker, pRank_bot_eq_zero hq, zero_add] at h1
  have hmap : E'.map f ≤ D'.map f := by
    rintro _ ⟨e, he, rfl⟩
    have heLC : (e : X) ∈ ((L ⊔ C : Subgroup X) : Set X) := hEL he
    have hNC : N ≤ Subgroup.normalizer (C : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hNC)] at heLC
    obtain ⟨l, hl, c, hc, hlc⟩ := heLC
    have hlE : l ∈ E ⊔ C := by
      have : l = (e : X) * c⁻¹ := by rw [← hlc]; group
      rw [this]
      exact (E ⊔ C).mul_mem (Subgroup.mem_sup_left he) ((E ⊔ C).inv_mem
        (Subgroup.mem_sup_right hc))
    refine ⟨⟨l, hLN hl⟩, ⟨hl, hlE⟩, ?_⟩
    have hcN : (⟨c, hCN hc⟩ : N) ∈ C' := hc
    have he' : e = ⟨l, hLN hl⟩ * ⟨c, hCN hc⟩ := Subtype.ext hlc.symm
    have hfc : f ⟨c, hCN hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
    rw [he', map_mul, hfc, mul_one]
  have h2 : Open.pRank q (D'.map f) ≤ Open.pRank q D' := by
    have hkerD : ¬ q ∣ Nat.card (f.comp D'.subtype).ker := by
      intro hdvd
      apply hZ
      set K := (f.comp D'.subtype).ker
      have hinj : Function.Injective (N.subtype.comp D'.subtype) :=
        N.subtype_injective.comp D'.subtype_injective
      have hcard : Nat.card (K.map (N.subtype.comp D'.subtype)) = Nat.card K :=
        Subgroup.card_map_of_injective hinj
      refine hdvd.trans (hcard ▸ Subgroup.card_dvd_of_le ?_)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨(x.2 : (x : N) ∈ D').1, ?_⟩
      have : ((x : N) : N) ∈ C' := (QuotientGroup.eq_one_iff _).mp hx
      exact this
    have := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hq (f.comp D'.subtype) hkerD ⊤
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    calc Open.pRank q (D'.map f) ≤ Open.pRank q (⊤ : Subgroup D') := this
      _ = Open.pRank q D' := by
        rw [← pRank_map_of_injective q hq D'.subtype D'.subtype_injective ⊤,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h3 := pRank_mono q hq hmap
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
