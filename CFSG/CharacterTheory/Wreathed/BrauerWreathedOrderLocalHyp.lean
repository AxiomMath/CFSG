module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderLocal
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderAdapted
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderDegree
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormalizerQuotient

public section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG.Wreathed.ConditionalFourier

theorem conditionalLocalHyp_of_linear {G : Type} [Group G] [Fintype G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {F : Type} [Field F] [Finite F]
    {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
    (φx : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) ≃*
      GL (Fin 2) F ⧸ Z)
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
    (h2 : (2 : F) ≠ 0) (hq : Nat.card F % 4 = 1) (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hno2 : ¬ ∃ H : Subgroup G, H.Normal ∧ H.index = 2) :
    ConditionalLocalHyp n hn S e p f := by
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have heven : Even (Nat.card F) := by
        rw [hcard, h]
        exact (Nat.even_pow' (by omega)).mpr even_two
      obtain ⟨k, hk⟩ := heven
      omega
    · exact h
  exact
    { modelData := exists_conditionalCompatibleModelData_of_linear hZ hZodd h2 hq hn φx p f hcard
      layerNoncyclic :=
        exists_sylow_not_isCyclic_of_linear hZ hZodd h2 hq hn φx p f hp hpodd hf hcard
      qTwoPart := two_pow_factorization_sq_sub_one hZ hZodd h2 hq hn φx p f hcard
      adaptedBase := exists_isAdaptedBase_of_sym3 S e hn hbase
      involutions_conj := hinv
      principal_degree := fun ideal _ _ basis principal hprincipal ψ hψ hψp =>
        two_le_basisDegree_of_principal n hn S e hno2 ideal basis principal hprincipal ψ hψ hψp }

end CFSG.Wreathed.BrauerWreathedOrder
