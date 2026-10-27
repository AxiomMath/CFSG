module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallFU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallFExist

open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallFU3 CFSG.ComponentClassification.LiteratureLocal.SmallRee
open TauCeti CFSG.LocalAnalysis.GLTheoremA CFSG.Open CFSG.LieType.Ree

section Ree


theorem exists_six_reeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    ∃ P : Subgroup (ReeTag.G2.reeGamma K 1), IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  let φ : Multiplicative (K × K) →* ReeTag.G2.reeGamma K 1 :=
    { toFun := fun x => uIn hK 0 (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
      map_one' := by
        simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero]
        exact uIn_zero hK
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        rw [uIn_mul]
        simp [smallReeSigma_zero] }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : uIn hK 0 (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 =
        uIn hK 0 0 0 := by
      rw [uIn_zero hK]
      exact hx
    obtain ⟨-, h1, h2⟩ := uIn_inj hK hx'
    exact toAdd_eq_zero.1 (Prod.ext h1 h2)
  have h3 : (3 : K) = 0 := three_eq_zero_of_charP
  have hexp : ∀ x : Multiplicative (K × K), x ^ 3 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    ext
    · simp [toAdd_pow, h3]
    · simp [toAdd_pow, h3]
  refine ⟨φ.range, KDRank3SmallL3.isElemAbelian_three_range φ hexp, ?_⟩
  rw [KDRank3SmallL3.card_range_eq φ hinj,
    (Nat.card_congr (Multiplicative.ofAdd : K × K ≃ Multiplicative (K × K))).symm, Nat.card_prod,
    hK]
  norm_num

theorem exists_six_of_reeG2 {S : Type} [Group S] (hv : (LieTypeIndex.reeG2 1).Valid)
    (e : S ≃* (ValidLieTypeIndex.Group ⟨LieTypeIndex.reeG2 1, hv⟩)) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge 1 hv (GaloisField 3 3) (by rw [hK])
  have hmodel : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 3 :=
    ⟨⟨Nat.prime_three, by norm_num, rfl, rfl, by decide, le_rfl⟩, 1, by norm_num,
      GaloisField 3 3, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
  obtain ⟨eG⟩ := (CFSG.LieType.Ree.small_Ree_model_Schreier S 3 3 hmodel).2.2.2.2 1
    (GaloisField 3 3) (by norm_num) hK ⟨e.trans b.symm⟩
  obtain ⟨P, hP, hcard⟩ := exists_six_reeGamma (K := GaloisField 3 3) (by rw [hK])
  refine ⟨P.map eG.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hP _, ?_⟩
  rw [Subgroup.card_map_of_injective eG.symm.injective, hcard]

theorem hExistRest_all :
    ∀ (S : Type) [Group S] [Finite S] (d : ValidLieTypeIndex),
      Nonempty (S ≃* (CFSGIndex.lie d).Group) → IsRank3Small d.1 →
      (∀ q : PrimePower, d.1 ≠ LieTypeIndex.A 2 q) →
      ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  intro S _ _ d hd hsmall hnotA2
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact hsmall.elim
    · exact hsmall.elim
    · exact absurd rfl (hnotA2 q)
    · exact hsmall.elim
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact hsmall.elim
    · exact hsmall.elim
    · exact exists_six_of_twistedA2 q hv hsmall hd.some
    · exact hsmall.elim
  | reeG2 m =>
    have hm : m = 1 := hsmall
    subst hm
    exact exists_six_of_reeG2 hv hd.some
  | _ => exact hsmall.elim

end Ree

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallFExist
