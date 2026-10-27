module

public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.RankThree.SteinbergR3ELargeReeOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

namespace Core3Ree

theorem exists_conj_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U Syl : Sylow p G) {P : Subgroup G} (hSN : Subgroup.normalizer (Syl : Subgroup G) ≤ P) :
    ∃ g : G, Subgroup.normalizer (U : Subgroup G) ≤ P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Syl U
  refine ⟨g, ?_⟩
  have h1 : (U : Subgroup G) = (Syl : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [h1, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hSN

theorem map_conj_ne_top {G : Type*} [Group G] {P : Subgroup G} (hP : P ≠ ⊤) (g : G) :
    P.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  intro h
  apply hP
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : (MulAut.conj g) x ∈ P.map (MulAut.conj g).toMonoidHom := h ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := (MulAut.conj g).injective hyx
  exact this ▸ hy

theorem map_subtype_ne {M : Type*} [Group M] {Γ : Subgroup M} {P : Subgroup Γ} (hP : P ≠ ⊤) :
    P.map Γ.subtype ≠ Γ := by
  intro h
  apply hP
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : (x : M) ∈ P.map Γ.subtype := by
    rw [h]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem fixedRelElt_one :
    ReeTag.F4.fixedRelElt ⟨1, by decide⟩ = ReeTag.F4.fixedOrbitElement ⟨0, by decide⟩ := by
  have hw : ReeTag.F4.fixedRelWord ⟨1, by decide⟩ = [⟨0, by decide⟩] := rfl
  rw [ReeTag.fixedRelElt, hw]
  simp

theorem fixedRelElt_two :
    ReeTag.F4.fixedRelElt ⟨2, by decide⟩ = ReeTag.F4.fixedOrbitElement ⟨1, by decide⟩ := by
  have hw : ReeTag.F4.fixedRelWord ⟨2, by decide⟩ = [⟨1, by decide⟩] := rfl
  rw [ReeTag.fixedRelElt, hw]
  simp

section ReeGroup

variable
  {K : Type} [Field K] [Finite K]

theorem reeParabolic_univ {t : ReeTag} [CharP K t.prime] (a : ℕ) :
    t.reeParabolic K a Set.univ = t.reeGamma K a := by
  rw [ReeTag.reeParabolic, Set.image_univ, ← ReeTag.reeGamma_eq_sup_closure]

theorem overgroup_cases [CharP K ReeTag.F4.prime] (a : ℕ)
    (A : Subgroup (ModGL ReeTag.F4.tag K)) (hB : ReeTag.F4.reeFixedBorel K a ≤ A)
    (hA : A ≤ ReeTag.F4.reeGamma K a) (hne : A ≠ ReeTag.F4.reeGamma K a) :
    A = ReeTag.F4.reeFixedBorel K a ∨ ∃ i : Fin ReeTag.F4.fixedOrbitCount,
      (A : Set (ModGL ReeTag.F4.tag K)) = (ReeTag.F4.reeFixedBorel K a : Set _) ∪
        ReeTag.F4.reeFixedBruhatCell K a (ReeTag.F4.fixedOrbitElement i) := by
  obtain ⟨hAJ, -⟩ := ReeTag.ree_Borel_overgroup_classification ReeTag.F4 a K A hB hA
  set J : Set (Fin ReeTag.F4.fixedOrbitCount) := {j | canonicalRep (coxeterSystem ReeTag.F4.tag) K
    (ReeTag.F4.fixedOrbitElement j) ∈ A} with hJ
  have hJne : J ≠ Set.univ := fun h => hne (by rw [hAJ, h, reeParabolic_univ])
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ J := by
    by_contra h
    push Not at h
    exact hJne (Set.eq_univ_of_forall h)
  rcases J.eq_empty_or_nonempty with hJ0 | ⟨i, hi⟩
  · left
    rw [hAJ, hJ0, ReeTag.reeParabolic_empty]
  · right
    refine ⟨i, ?_⟩
    have hJi : J ⊆ {i} := by
      intro j hj
      have hr : ReeTag.F4.fixedOrbitCount = 2 := rfl
      have hij : (i : ℕ) ≠ j₀ := fun h => hj₀ (Fin.ext h ▸ hi)
      have hjj : (j : ℕ) ≠ j₀ := fun h => hj₀ (Fin.ext h ▸ hj)
      have := i.2
      have := j.2
      have := j₀.2
      exact Fin.ext (by omega)
    have hle := ReeTag.reeParabolic_le_reeGamma_inf (K := K) (a := a) hJi
    rw [← hAJ] at hle
    refine Set.Subset.antisymm (fun g hg => ?_) (Set.union_subset hB fun g hg => ?_)
    · have hg' := hle hg
      rw [← SetLike.mem_coe, ReeTag.coe_reeGamma_inf_parabolicSubgroup] at hg'
      exact hg'
    · obtain ⟨b, hb, b', hb', rfl⟩ := ReeTag.mem_reeFixedBruhatCell.1 hg
      exact mul_mem (mul_mem (hB hb) hi) (hB hb')

theorem card_cell_orbit [CharP K ReeTag.F4.prime] (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (i : Fin ReeTag.F4.fixedOrbitCount) :
    Nat.card (ReeTag.F4.reeFixedBruhatCell K a (ReeTag.F4.fixedOrbitElement i)) =
      Nat.card (ReeTag.F4.reeFixedBorel K a) * Nat.card K ^ (i.1 + 1) := by
  have hw := ReeTag.fixedOrbitElement_mem (t := ReeTag.F4) i
  have hbij := ReeTag.bijOn_reeFixedBruhatCell (K := K) (a := a) hw
  have hU : Nat.card (ReeTag.F4.reeFixedCellUnipotent K a (ReeTag.F4.fixedOrbitElement i)) =
      Nat.card K ^ (i.1 + 1) := by
    obtain ⟨n, hn⟩ := i
    have hn' : n < 2 := hn
    interval_cases n
    · have h := CFSG.RankThree.LargeReeOrder.card_reeFixedCellUnipotent_fixedRelElt
        (K := K) (a := a) hK ⟨1, by decide⟩
      rw [fixedRelElt_one] at h
      rw [h]
      rfl
    · have h := CFSG.RankThree.LargeReeOrder.card_reeFixedCellUnipotent_fixedRelElt
        (K := K) (a := a) hK ⟨2, by decide⟩
      rw [fixedRelElt_two] at h
      rw [h]
      rfl
  rw [← hU, Nat.card_congr hbij.equiv.symm, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  rfl

theorem card_overgroup [CharP K ReeTag.F4.prime] (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (A : Subgroup (ModGL ReeTag.F4.tag K)) (hB : ReeTag.F4.reeFixedBorel K a ≤ A)
    (hA : A ≤ ReeTag.F4.reeGamma K a) (hne : A ≠ ReeTag.F4.reeGamma K a) :
    Nat.card A = Nat.card (ReeTag.F4.reeFixedBorel K a) ∨ ∃ i : Fin ReeTag.F4.fixedOrbitCount,
      Nat.card A = Nat.card (ReeTag.F4.reeFixedBorel K a) * (1 + Nat.card K ^ (i.1 + 1)) := by
  rcases overgroup_cases a A hB hA hne with h | ⟨i, hi⟩
  · exact Or.inl (h ▸ rfl)
  · refine Or.inr ⟨i, ?_⟩
    have hdisj := ReeTag.disjoint_reeFixedBorel_reeFixedBruhatCell (t := ReeTag.F4) (K := K)
      (a := a) i
    have h1 : Nat.card A = (A : Set (ModGL ReeTag.F4.tag K)).ncard :=
      Nat.card_coe_set_eq (A : Set (ModGL ReeTag.F4.tag K))
    have h2 : Nat.card (ReeTag.F4.reeFixedBorel K a) =
        (ReeTag.F4.reeFixedBorel K a : Set (ModGL ReeTag.F4.tag K)).ncard :=
      Nat.card_coe_set_eq (ReeTag.F4.reeFixedBorel K a : Set (ModGL ReeTag.F4.tag K))
    have h3 := card_cell_orbit (K := K) a hK i
    rw [Nat.card_coe_set_eq] at h3
    rw [h1, hi, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), h3, ← h2]
    ring

end ReeGroup

section ReeHoldsSection

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem holds_reeGamma (a : ℕ) :
    CFSG.LieType.BorelTits.Holds ↥(ReeTag.F4.reeGamma K a) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  exact (holds_reeFixed ReeTag.F4 K a).of_mulEquiv (ReeTag.reeFixedEquivReeGamma K a)

end ReeHoldsSection

@[expose] def reeParabolicOrders : List ℕ :=
  [8 ^ 12 * 49, 8 ^ 12 * 49 * 9, 8 ^ 12 * 49 * 65]

section ReeGroupSylow

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem card_normalizer_sylow_le (hK : Nat.card K = 8)
    {P : Subgroup ↥(ReeTag.F4.reeGamma K 1)} (hP : P ≠ ⊤)
    (Syl : Sylow 2 ↥(ReeTag.F4.reeGamma K 1))
    (hSN : Subgroup.normalizer (Syl : Subgroup ↥(ReeTag.F4.reeGamma K 1)) ≤ P) :
    Nat.card P ∈ reeParabolicOrders := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]; norm_num
  let U₀ : Sylow 2 ↥(ReeTag.F4.reeGamma K 1) :=
    (ReeTag.isPGroup_reeFixedPosUnipotent_subgroupOf (K := K) (a := 1)).toSylow
      ReeTag.not_dvd_index_reeFixedPosUnipotent
  obtain ⟨g, hg⟩ := exists_conj_normalizer_le U₀ Syl hSN
  have hBN : (ReeTag.F4.reeFixedBorel K 1).subgroupOf (ReeTag.F4.reeGamma K 1) ≤
      Subgroup.normalizer (U₀ : Subgroup ↥(ReeTag.F4.reeGamma K 1)) := by
    intro x hx
    have hxN : (x : ModGL ReeTag.F4.tag K) ∈
        Subgroup.normalizer (ReeTag.F4.reeFixedPosUnipotent K 1 : Set (ModGL ReeTag.F4.tag K)) :=
      ReeTag.reeFixedBorel_le_normalizer_reeFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hx)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 hxN (h : ModGL ReeTag.F4.tag K)
    exact this
  have hBP : (ReeTag.F4.reeFixedBorel K 1).subgroupOf (ReeTag.F4.reeGamma K 1) ≤
      P.map (MulAut.conj g).toMonoidHom := hBN.trans hg
  have hBA : ReeTag.F4.reeFixedBorel K 1 ≤
      (P.map (MulAut.conj g).toMonoidHom).map (ReeTag.F4.reeGamma K 1).subtype := fun b hb =>
    ⟨⟨b, ReeTag.reeFixedBorel_le_reeGamma hb⟩, hBP (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hcard : Nat.card ((P.map (MulAut.conj g).toMonoidHom).map
      (ReeTag.F4.reeGamma K 1).subtype) = Nat.card P := by
    rw [Subgroup.card_map_of_injective (ReeTag.F4.reeGamma K 1).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hB : Nat.card (ReeTag.F4.reeFixedBorel K 1) = 8 ^ 12 * 49 := by
    rw [CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hK']
    norm_num
  rw [← hcard]
  rcases card_overgroup 1 hK' _ hBA (Subgroup.map_subtype_le _)
    (map_subtype_ne (map_conj_ne_top hP g)) with h | ⟨⟨n, hn⟩, h⟩
  · rw [h, hB]
    simp [reeParabolicOrders]
  · have hn' : n < 2 := hn
    rw [h, hB, hK]
    interval_cases n <;> simp [reeParabolicOrders]

theorem exists_parabolic_card (hK : Nat.card K = 8) {T : Subgroup ↥(ReeTag.F4.reeGamma K 1)}
    (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    ∃ P : Subgroup ↥(ReeTag.F4.reeGamma K 1),
      Subgroup.normalizer (T : Set ↥(ReeTag.F4.reeGamma K 1)) ≤ P ∧
        Nat.card P ∈ reeParabolicOrders := by
  obtain ⟨Syl, P, hP, hN, -, -, hSN⟩ := holds_reeGamma (K := K) 1 T hT hT2
  exact ⟨P, hN, card_normalizer_sylow_le hK hP Syl hSN⟩

end ReeGroupSylow

end Core3Ree

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
