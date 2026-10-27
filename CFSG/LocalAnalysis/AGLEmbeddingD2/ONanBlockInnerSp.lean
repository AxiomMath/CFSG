module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.InnerTypes

open CFSG.Open

theorem le_pRank_three_catSp (k : ℕ) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) :
    k ≤ Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨q, hq2, hd⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B k q := hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hqp hk
    (MulEquiv.refl _)
  rw [hqp] at hm
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hm
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨⟨A, hA, hAc⟩, -⟩ := CFSG.LieType.unique_even_symplectic_prime_field_three_rank
    (K := F) (n := k) (by omega)
  have hA' : IsElemAbelian 3 A := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).1 hA
  have hE : IsElemAbelian 3 (A.map e.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA' _
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE
    (by rw [Subgroup.card_map_of_injective e.symm.injective, hAc])

end CFSG.AGLEmbeddingD2.InnerTypes
