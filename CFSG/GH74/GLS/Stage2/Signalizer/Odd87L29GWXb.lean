module

public import CFSG.GH74.GLS.IVK.Defs
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GorensteinWalter

theorem le_of_isPerfect_of_odd_index {M : Type} [Group M] [Finite M] (L : Subgroup M)
    [L.Normal] (hL : Odd L.index) (J : Subgroup M) (hJ : Group.IsPerfect ↥J) : J ≤ L := by
  have hsol : Group.IsSolvable (M ⧸ L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hL
  have hJc : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ
  have hK : ⁅J.map (QuotientGroup.mk' L), J.map (QuotientGroup.mk' L)⁆ =
      J.map (QuotientGroup.mk' L) := by
    rw [← Subgroup.map_commutator, hJc]
  have hKbot : J.map (QuotientGroup.mk' L) = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hK
  intro x hx
  have h1 : QuotientGroup.mk' L x ∈ J.map (QuotientGroup.mk' L) := Subgroup.mem_map_of_mem _ hx
  rw [hKbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem not_isSolvable_of_odd_index {M : Type} [Group M] [Finite M]
    (hns : ¬ Group.IsSolvable M) (L : Subgroup M) [L.Normal] (hL : Odd L.index) :
    ¬ Group.IsSolvable ↥L := by
  intro hsol
  have hq : Group.IsSolvable (M ⧸ L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hL
  exact hns (Group.isSolvable_of_subgroup_quotient L)

theorem three_le_card_of_isOddPrimePower {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : 3 ≤ Nat.card K := by
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hK
  have hpne2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rw [hcard]
  exact hp3.trans (Nat.le_self_pow (by omega) p)

theorem odd_card_of_isOddPrimePower {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hK
  rw [hcard]
  exact hpodd.pow

theorem isSolvable_psl2_of_card_three {K : Type} [Field K] [Finite K] (h : Nat.card K = 3) :
    Group.IsSolvable (PSL2 K) := by
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using h
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eP : PSL2 K ≃* alternatingGroup (Fin 4) :=
    (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
  have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := eP.toMonoidHom) eP.injective

theorem isSolvable_pgl2_of_card_three {K : Type} [Field K] [Finite K] (h : Nat.card K = 3) :
    Group.IsSolvable (PGL2 K) := by
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using h
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eP : PGL2 K ≃* Equiv.Perm (Fin 4) :=
    (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
  have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := eP.toMonoidHom) eP.injective

theorem dgroup_structure_of_psl2 {M : Type} [Group M] [Finite M] (hns : ¬ Group.IsSolvable M)
    (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup M) [L.Normal] (hL : Odd L.index) (e : ↥L ≃* PSL2 K) :
    ∃ L₀ : Subgroup M, L₀.Normal ∧ IsSimpleGroup ↥L₀ ∧ (∃ a b : ↥L₀, a * b ≠ b * a) ∧
      (∀ J : Subgroup M, Group.IsPerfect ↥J → J ≤ L₀) ∧ IVK.IsL2 ↥L₀ Odd := by
  have hnsL := not_isSolvable_of_odd_index hns L hL
  have h3 : 3 < Nat.card K := by
    have h := three_le_card_of_isOddPrimePower hK
    refine lt_of_le_of_ne h fun h3 => hnsL ?_
    have := isSolvable_psl2_of_card_three (K := K) h3.symm
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hsimp : IsSimpleGroup ↥L :=
    (MulEquiv.isSimpleGroup_congr e).mpr (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h3)
  refine ⟨L, inferInstance, hsimp, ?_, le_of_isPerfect_of_odd_index L hL,
    K, inferInstance, inferInstance, odd_card_of_isOddPrimePower hK,
    ⟨e.trans (IVK.L2.equivPSL K).symm⟩⟩
  by_contra hcon
  push Not at hcon
  exact hnsL (Group.isSolvable_of_comm fun a b => hcon a b)

theorem dgroup_structure_of_pgl2 {M : Type} [Group M] [Finite M] (hns : ¬ Group.IsSolvable M)
    (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup M) [L.Normal] (hL : Odd L.index) (e : ↥L ≃* PGL2 K) :
    ∃ L₀ : Subgroup M, L₀.Normal ∧ IsSimpleGroup ↥L₀ ∧ (∃ a b : ↥L₀, a * b ≠ b * a) ∧
      (∀ J : Subgroup M, Group.IsPerfect ↥J → J ≤ L₀) ∧ IVK.IsL2 ↥L₀ Odd := by
  have hnsL := not_isSolvable_of_odd_index hns L hL
  have h3 : 3 < Nat.card K := by
    have h := three_le_card_of_isOddPrimePower hK
    refine lt_of_le_of_ne h fun h3 => hnsL ?_
    have := isSolvable_pgl2_of_card_three (K := K) h3.symm
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  obtain ⟨eC⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK h3 e
  let eD : ↥((commutator ↥L).map L.subtype) ≃* commutator ↥L :=
    ((commutator ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm
  let eL₀ : ↥((commutator ↥L).map L.subtype) ≃* PSL2 K := eD.trans eC
  have hsimp : IsSimpleGroup ↥((commutator ↥L).map L.subtype) :=
    (MulEquiv.isSimpleGroup_congr eL₀).mpr (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h3)
  refine ⟨(commutator ↥L).map L.subtype, inferInstance, hsimp, ?_, ?_,
    K, inferInstance, inferInstance, odd_card_of_isOddPrimePower hK,
    ⟨eL₀.trans (IVK.L2.equivPSL K).symm⟩⟩
  · by_contra hcon
    push Not at hcon
    have h1 : Group.IsSolvable ↥((commutator ↥L).map L.subtype) :=
      Group.isSolvable_of_comm fun a b => hcon a b
    have h2 : Group.IsSolvable (commutator ↥L) :=
      Group.isSolvable_of_isSolvable_injective (f := eD.symm.toMonoidHom) eD.symm.injective
    exact hnsL (Group.isSolvable_commutator_iff.mp h2)
  · intro J hJ
    have hJL := le_of_isPerfect_of_odd_index L hL J hJ
    rw [Subgroup.map_subtype_commutator]
    calc J = ⁅J, J⁆ := (Subgroup.isPerfect_iff.mp hJ).symm
      _ ≤ ⁅L, L⁆ := Subgroup.commutator_mono hJL hJL

theorem dgroup_structure (hGW : gorensteinWalterStatement.{0}) {M : Type} [Group M] [Finite M]
    (hO : pPrimeCore 2 M = ⊥) (hns : ¬ Group.IsSolvable M) (hS : HasDihedralSylowTwo M) :
    ∃ L₀ : Subgroup M, L₀.Normal ∧ IsSimpleGroup ↥L₀ ∧ (∃ a b : ↥L₀, a * b ≠ b * a) ∧
      (∀ J : Subgroup M, Group.IsPerfect ↥J → J ≤ L₀) ∧
      (Nonempty (↥L₀ ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 ↥L₀ Odd) := by
  let Φ : M ≃* (M ⧸ pPrimeCore 2 M) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 M))
      ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO],
        QuotientGroup.mk'_surjective _⟩
  rcases hGW M hS with ⟨_, hq⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, K, hKp, L, hLn, hLi, hLm⟩
  · exfalso
    have hp : IsPGroup 2 M := hq.of_equiv Φ.symm
    have : Group.IsNilpotent M := hp.isNilpotent
    exact hns inferInstance
  · have e' : (⊤ : Subgroup M) ≃* alternatingGroup (Fin 7) :=
      Subgroup.topEquiv.trans (Φ.trans e)
    refine ⟨⊤, inferInstance, ?_, ?_, fun J _ => le_top, Or.inl ⟨e'⟩⟩
    · exact (MulEquiv.isSimpleGroup_congr e').mpr (alternatingGroup.isSimpleGroup (by simp))
    · by_contra hcon
      push Not at hcon
      have h1 : Group.IsSolvable ↥(⊤ : Subgroup M) :=
        Group.isSolvable_of_comm fun a b => hcon a b
      exact hns (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := M)).toMonoidHom)
        (Subgroup.topEquiv (G := M)).surjective)
  · let L' : Subgroup M := L.map (Φ.symm : (M ⧸ pPrimeCore 2 M) →* M)
    have hLn' : L'.Normal := hLn.map _ Φ.symm.surjective
    have hLi' : Odd L'.index := by
      have h := Subgroup.index_map_equiv (H := L) Φ.symm
      exact h ▸ hLi
    let eL' : ↥L ≃* ↥L' :=
      L.equivMapOfInjective (Φ.symm : (M ⧸ pPrimeCore 2 M) →* M) Φ.symm.injective
    rcases hLm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨L₀, h1, h2, h3, h4, h5⟩ :=
        dgroup_structure_of_psl2 hns K hKp L' hLi' (eL'.symm.trans e)
      exact ⟨L₀, h1, h2, h3, h4, Or.inr h5⟩
    · obtain ⟨L₀, h1, h2, h3, h4, h5⟩ :=
        dgroup_structure_of_pgl2 hns K hKp L' hLi' (eL'.symm.trans e)
      exact ⟨L₀, h1, h2, h3, h4, Or.inr h5⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW
