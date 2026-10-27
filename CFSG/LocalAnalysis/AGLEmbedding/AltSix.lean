module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Equiv Equiv.Perm CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem conjNormal_swap_notMem_range :
    MulAut.conjNormal (H := alternatingGroup (Fin 6)) (swap 0 1) ∉
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  rintro ⟨a, ha⟩
  rw [← MulAut.conjNormal_val] at ha
  have h := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num) ha
  have hs := a.2
  rw [h, mem_alternatingGroup, sign_swap (by decide)] at hs
  exact absurd hs (by decide)

theorem card_outer_alternatingGroup_six_dvd_four :
    Nat.card (Outer (alternatingGroup (Fin 6))) ∣ 4 := by
  have hle := DegreeSix.outer_card_le_four
  have h1 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (MulAut.conjNormal (H := alternatingGroup (Fin 6)) (swap 0 1)) ≠ 1 := by
    rw [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact conjNormal_swap_notMem_range
  have h2 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (MulAut.conjNormal (H := alternatingGroup (Fin 6)) (swap 0 1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, sq, swap_mul_self, map_one, map_one]
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) :=
    orderOf_eq_prime h2 h1 ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  obtain ⟨c, hc⟩ := hdvd
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · exact ⟨2, by omega⟩
  · exact ⟨1, by omega⟩

theorem mem_range_conj_of_odd_orderOf (f : MulAut (alternatingGroup (Fin 6)))
    (hf : Odd (orderOf f)) : f ∈ (MulAut.conj : alternatingGroup (Fin 6) →* _).range := by
  set π := QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
  have h4 : orderOf (π f) ∣ 4 :=
    (orderOf_dvd_natCard _).trans card_outer_alternatingGroup_six_dvd_four
  have hodd := Nat.odd_iff.mp (hf.of_dvd_nat (orderOf_map_dvd π f))
  have hle := Nat.le_of_dvd (by norm_num) h4
  have h1 : orderOf (π f) = 1 := by
    interval_cases h : orderOf (π f) <;> omega
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mem_range_conj_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (alternatingGroup (Fin 6))} (hf : f ^ p = 1) :
    f ∈ (MulAut.conj : alternatingGroup (Fin 6) →* _).range :=
  mem_range_conj_of_odd_orderOf f
    ((hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hf))

theorem pRank_top_mulAut_alternatingGroup_six_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    pRank p (⊤ : Subgroup (MulAut (alternatingGroup (Fin 6)))) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  refine SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have := hE.1
  set c := (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6)))
  have hc : Function.Injective c := DegreeSix.inner_conjugation_injective
  have hEc : E ≤ c.range := fun x hx => mem_range_conj_of_pow_eq_one hp hp2 (hE.2 x hx)
  set E' : Subgroup (Perm (Fin 6)) := (E.comap c).map (alternatingGroup (Fin 6)).subtype
  have hcard : Nat.card E' = Nat.card E := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      ← Subgroup.card_map_of_injective hc, Subgroup.map_comap_eq_self hEc]
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := congrArg Subtype.val (mul_comm' (⟨c a, ha⟩ : E) ⟨c b, hb⟩)
    simp only [Subgroup.coe_mul, ← map_mul] at h
    simp only [Subgroup.coe_subtype, ← Subgroup.coe_mul, hc h]
  have hpE : IsPGroup p E' := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h : c (a ^ p) = c 1 := by rw [map_pow, map_one]; exact hE.2 _ ha
    simpa using congrArg Subtype.val (hc h)
  calc Nat.card E = Nat.card E' := hcard.symm
    _ ≤ p ^ (Fintype.card (Fin 6) / p) := card_le_pow_div_of_commute E' hcomm hpE
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (Nat.div_le_of_le_mul (by
        have := hp.two_le
        rw [Fintype.card_fin]
        omega))

theorem kFactBetaA6 : KFactBetaA6 := by
  intro K _ _ ⟨e⟩ p hp hp2 _ _ _
  left
  rw [SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)]
  exact pRank_top_mulAut_alternatingGroup_six_le hp hp2

end CFSG.AGLEmbedding
