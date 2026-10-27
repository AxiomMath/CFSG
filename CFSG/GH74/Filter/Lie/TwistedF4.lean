module

public import CFSG.GH74.Filter.Lie.SepWitness
public import CFSG.GH74.Filter.Lie.FixedElemAbelian
public import CFSG.GH74.Filter.Statements
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Ree.SmallReeRank
public import CFSG.LocalAnalysis.SectionRank.Exceptional

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.SectionRank

@[expose] def quadF4 : SepWitness ReeTag.F4.tag 4 where
  word := ![([1] : List (Fin 4)), ([2] : List (Fin 4)), ([2, 3, 1] : List (Fin 4)),
    ([1, 2, 1] : List (Fin 4))]
  simple := ![(2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4)]
  sep := ![([2, 1] : List (Fin 4)), ([1, 2] : List (Fin 4)), ([2, 1, 2, 3, 2] : List (Fin 4)),
    ([1, 2, 0, 1, 0] : List (Fin 4))]

theorem quadF4_check : quadF4.check = true := by decide +kernel

theorem quadF4_dual : ∀ i : Fin 4,
    List.ofFn (ReeTag.F4.dualRoot (quadF4.vec i)) =
      List.ofFn (quadF4.vec (![1, 0, 3, 2] i)) := by
  decide +kernel

theorem dualRootOf_quadF4
    (i : Fin 4) :
    ReeTag.F4.dualRootOf (quadF4.root i) = quadF4.root (![1, 0, 3, 2] i) :=
  Subtype.ext (by
    change ReeTag.F4.dualRoot (quadF4.root i).1 = (quadF4.root (![1, 0, 3, 2] i)).1
    rw [RootWitness.root_val, RootWitness.root_val]
    exact List.ofFn_injective (quadF4_dual i))

theorem not_gen4_reeFixed_F4
    {K : Type} [Field K] [Finite K] [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ¬ Gen4 (reeFixed ReeTag.F4 K a) := by
  have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  let F : adjointGroup ReeTag.F4.tag K ≃* adjointGroup ReeTag.F4.tag K := ReeTag.F4.reeAut K a
  have hFF : ∀ g, F (F g) = g := ReeTag.F4.reeAut_reeAut a hK
  let f : Fin 4 → Multiplicative K →* adjointGroup ReeTag.F4.tag K := fun i =>
    rootHom (K := K) (quadF4.root i)
  obtain ⟨hcomm, hinj⟩ := SepWitness.pi_data quadF4_check (K := K)
  have hstab : ∀ i y, F (f i y) ∈ (MonoidHom.noncommPiCoprod f hcomm).range := by
    intro i y
    have h1 : f i y ∈ (rootOperatorFamily ReeTag.F4.tag).rootSubgroup K (quadF4.root i) :=
      (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _
    have h2 := ReeTag.reeAut_mem_X (t := ReeTag.F4) a h1
    rw [dualRootOf_quadF4] at h2
    obtain ⟨c, hc⟩ := ((rootOperatorFamily ReeTag.F4.tag).mem_rootSubgroup).1 h2
    refine ⟨Pi.mulSingle (![1, 0, 3, 2] i) (Multiplicative.ofAdd c), ?_⟩
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    exact hc
  obtain ⟨E, hEF, hEc, hEs, hEcard⟩ := exists_fixed_elemAbelian_of_pi F hFF
    (fun x => CharTwo.add_self_eq_zero x) f hcomm hinj hstab
  have hEΓ : E ≤ reeFixed ReeTag.F4 K a := fun x hx => (mem_reeFixed _ _ _).2 (hEF x hx)
  refine not_gen4_of_injective (Subgroup.inclusion hEΓ) (Subgroup.inclusion_injective hEΓ)
    (fun x y => Subtype.ext (hEc x.1 x.2 y.1 y.2))
    (fun x => Subtype.ext (by simpa [sq] using hEs x.1 x.2)) ?_
  rw [Fintype.card_fin] at hEcard
  have hK8 : 2 ^ 3 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  by_contra hcon
  have hcon' : Nat.card E ≤ 2 ^ 4 := not_lt.1 hcon
  have h1 : Nat.card E ^ 2 ≤ (2 ^ 4) ^ 2 := Nat.pow_le_pow_left hcon' 2
  have h2 : (2 ^ 3) ^ 4 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left hK8 4
  norm_num at h1 h2
  omega

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.SectionRank

theorem t_twistedF4 :
    S_twistedF4 := by
  intro G _ _ f h
  obtain ⟨-, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨⟨-, -, -, -, -, h3⟩, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_natCard_eq_pow hK
  have : CharP K ReeTag.F4.prime := hc
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨e'⟩ := hiso a K hfa hK ⟨e⟩
  have hΓ : ReeTag.F4.reeGamma K a =
      (reeFixed ReeTag.F4 K a).map (adjointGroup ReeTag.F4.tag K).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)
  let e2 : ReeTag.F4.reeGamma K a ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hΓ).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm
  exact not_gen4_of_mulEquiv (e'.trans e2).symm (not_gen4_reeFixed_F4 ha hK')

end CFSG.GH74.Filter
