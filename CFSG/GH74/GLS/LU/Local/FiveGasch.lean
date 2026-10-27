module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

section Gasch

variable {G : Type} [Group G] [Finite G]

theorem exists_complement_of_lift (N E D : Subgroup G)
    (hEN : N ≤ normalizer (E : Set G)) (hEle : E ≤ N)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hD : D ≤ N) (hED : E ⊓ D = ⊥) (m : ℕ)
    (hm : Nat.card ↥N = m * Nat.card ↥(E ⊔ D)) (hcopm : Nat.Coprime m (Nat.card ↥E)) :
    ∃ K : Subgroup G, K ≤ N ∧ E ⊓ K = ⊥ ∧ E ⊔ K = N := by
  have hEnorm : (E.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEle).mpr hEN
  have hEcomm : IsMulCommutative (E.subgroupOf N) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩
  have hDE : E ⊔ D ≤ N := sup_le hEle hD
  have hidx : ((E ⊔ D).subgroupOf N).index = m := by
    have h1 := Subgroup.card_mul_index ((E ⊔ D).subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hm, mul_comm m] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcop : Nat.Coprime ((E ⊔ D).subgroupOf N).index (Nat.card ↥(E.subgroupOf N)) := by
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv]
    exact hcopm
  have hdisj : E.subgroupOf N ⊓ D.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ E ⊓ D := ⟨hx.1, hx.2⟩
    rw [hED, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  obtain ⟨K', -, hK'i, hK's⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting (E.subgroupOf N)
      ((E ⊔ D).subgroupOf N) (D.subgroupOf N) hcop hdisj (Subgroup.subgroupOf_sup hEle hD).symm
  refine ⟨K'.map N.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxK
    have hy1 : y ∈ E.subgroupOf N ⊓ K' := ⟨hxE, hy⟩
    rw [hK'i, Subgroup.mem_bot] at hy1
    rw [Subgroup.mem_bot, hy1]
    exact map_one _
  · calc E ⊔ K'.map N.subtype
        = (E.subgroupOf N).map N.subtype ⊔ K'.map N.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hEle]
      _ = (E.subgroupOf N ⊔ K').map N.subtype := (Subgroup.map_sup _ _ _).symm
      _ = N := by rw [hK's, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite G] in
theorem exists_mul_of_mem_sup {N E K : Subgroup G} (hEN : N ≤ normalizer (E : Set G))
    (hEle : E ≤ N) (hKN : K ≤ N) (hEK : E ⊔ K = N) {g : G} (hg : g ∈ N) :
    ∃ e ∈ E, ∃ k ∈ K, e * k = g := by
  have hEnorm : (E.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEle).mpr hEN
  have htop : E.subgroupOf N ⊔ K.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hEle hKN, hEK, Subgroup.subgroupOf_self]
  have hmem : (⟨g, hg⟩ : N) ∈ ((E.subgroupOf N ⊔ K.subgroupOf N : Subgroup N) : Set N) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨e, he, k, hk, hek⟩ := Set.mem_mul.mp hmem
  exact ⟨e, he, k, hk, congrArg Subtype.val hek⟩

theorem exists_conj_of_complements (N E U K : Subgroup G)
    (hEN : N ≤ normalizer (E : Set G)) (hEle : E ≤ N)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hU : U ≤ N) (hcopU : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U))
    (hKN : K ≤ N) (hEK : E ⊓ K = ⊥) (hEKN : E ⊔ K = N) :
    ∃ n ∈ E, ∀ u ∈ U, ∃ k ∈ K, n * k * n⁻¹ = u := by
  have hΓN : E ⊔ U ≤ N := sup_le hEle hU
  have hEΓ : E ≤ E ⊔ U := le_sup_left
  have hUΓ : U ≤ E ⊔ U := le_sup_right
  have hEnorm : (E.subgroupOf (E ⊔ U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEΓ).mpr (hΓN.trans hEN)
  have hEcomm : IsMulCommutative (E.subgroupOf (E ⊔ U)) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩
  have hA : Subgroup.IsComplement' (E.subgroupOf (E ⊔ U)) (U.subgroupOf (E ⊔ U)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ E ⊓ U := ⟨hx.1, hx.2⟩
      rw [disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopU), Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    · rw [← Subgroup.normal_mul (E.subgroupOf (E ⊔ U)) (U.subgroupOf (E ⊔ U))]
      have htop : E.subgroupOf (E ⊔ U) ⊔ U.subgroupOf (E ⊔ U) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hEΓ hUΓ, Subgroup.subgroupOf_self]
      rw [htop, Subgroup.coe_top]
  have hB : Subgroup.IsComplement' (E.subgroupOf (E ⊔ U)) (K.subgroupOf (E ⊔ U)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ E ⊓ K := ⟨hx.1, hx.2⟩
      rw [hEK, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    · refine Set.eq_univ_of_forall fun g => Set.mem_mul.mpr ?_
      obtain ⟨e, he, k, hk, hek⟩ := exists_mul_of_mem_sup hEN hEle hKN hEKN (hΓN g.2)
      have hkΓ : k ∈ E ⊔ U := by
        have hk' : k = e⁻¹ * (g : G) := by rw [← hek]; group
        rw [hk']
        exact mul_mem (inv_mem (hEΓ he)) g.2
      exact ⟨⟨e, hEΓ he⟩, he, ⟨k, hkΓ⟩, hk, Subtype.ext hek⟩
  have hcop' : Nat.Coprime (Nat.card ↥(E.subgroupOf (E ⊔ U))) (E.subgroupOf (E ⊔ U)).index := by
    rw [hA.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUΓ).toEquiv]
    exact hcopU
  obtain ⟨n, hn⟩ := Subgroup.exists_conj_eq_of_isComplement' hcop' hB hA
  refine ⟨((n : ↥(E ⊔ U)) : G), n.2, fun u hu => ?_⟩
  have hu' : (⟨u, hUΓ hu⟩ : ↥(E ⊔ U)) ∈ U.subgroupOf (E ⊔ U) := hu
  rw [hn] at hu'
  obtain ⟨k, hk, hku⟩ := Subgroup.mem_map.mp hu'
  refine ⟨(k : G), hk, ?_⟩
  have hku' := congrArg Subtype.val hku
  simpa [MulAut.conj_apply] using hku'

theorem exists_complement_containing_coprime (N E D U : Subgroup G)
    (hEN : N ≤ normalizer (E : Set G)) (hEle : E ≤ N)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hD : D ≤ N) (hED : E ⊓ D = ⊥) (m : ℕ)
    (hm : Nat.card ↥N = m * Nat.card ↥(E ⊔ D)) (hcopm : Nat.Coprime m (Nat.card ↥E))
    (hU : U ≤ N) (hcopU : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) :
    ∃ L : Subgroup G, L ≤ N ∧ E ⊓ L = ⊥ ∧ E ⊔ L = N ∧ U ≤ L := by
  obtain ⟨K, hKN, hEK, hEKN⟩ := exists_complement_of_lift N E D hEN hEle hcomm hD hED m hm hcopm
  obtain ⟨n, hnE, hn⟩ := exists_conj_of_complements N E U K hEN hEle hcomm hU hcopU hKN hEK hEKN
  have hnN : n ∈ N := hEle hnE
  have hmemL : ∀ x : G, x ∈ K.map (MulAut.conj n).toMonoidHom ↔ ∃ k ∈ K, n * k * n⁻¹ = x := by
    intro x
    rw [Subgroup.mem_map]
    simp [MulAut.conj_apply]
  have hconj : ∀ k : G, k = n⁻¹ * (n * k * n⁻¹) * n := fun k => by group
  have hLN : K.map (MulAut.conj n).toMonoidHom ≤ N := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (hmemL x).mp hx
    exact mul_mem (mul_mem hnN (hKN hk)) (inv_mem hnN)
  refine ⟨K.map (MulAut.conj n).toMonoidHom, hLN, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxL⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk, rfl⟩ := (hmemL x).mp hxL
    have hkE : k ∈ E := by
      rw [hconj k]
      exact mul_mem (mul_mem (inv_mem hnE) hxE) hnE
    have hk1 : k ∈ E ⊓ K := ⟨hkE, hk⟩
    rw [hEK, Subgroup.mem_bot] at hk1
    rw [Subgroup.mem_bot, hk1]
    group
  · refine le_antisymm (sup_le hEle hLN) ?_
    rw [← hEKN]
    refine sup_le le_sup_left fun k hk => ?_
    rw [hconj k]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hnE))
      (Subgroup.mem_sup_right ((hmemL _).mpr ⟨k, hk, rfl⟩))) (Subgroup.mem_sup_left hnE)
  · intro u hu
    obtain ⟨k, hk, hku⟩ := hn u hu
    exact (hmemL u).mpr ⟨k, hk, hku⟩

end Gasch

end CFSG.GH74.GLS.LU.Local.Five
