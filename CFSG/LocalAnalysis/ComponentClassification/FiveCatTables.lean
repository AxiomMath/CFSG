module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf Equiv

private theorem card_L2_16 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 2 2 4) :
    Nat.card S = 4080 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_L3_4 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 3 2 2) :
    Nat.card S = 20160 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_U3_4 {S : Type} [Group S] (h : Blueprint.LieModel S .PSU 3 2 2) :
    Nat.card S = 62400 :=
  ((CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.1 rfl).trans (by decide)

private theorem card_L2_25 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 2 5 2) :
    Nat.card S = 7800 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_L3_5 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 3 5 1) :
    Nat.card S = 372000 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_U3_5 {S : Type} [Group S] (h : Blueprint.LieModel S .PSU 3 5 1) :
    Nat.card S = 126000 :=
  (CFSG.GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) h).trans (by decide)

private theorem card_PSp4_5 {S : Type} [Group S] (h : Blueprint.LieModel S .PSp 2 5 1) :
    Nat.card S = 4680000 :=
  (CFSG.GH74.card_of_lieModel_PSp (by norm_num) (by norm_num) h).trans (by decide)

private theorem card_L4_5 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 4 5 1) :
    Nat.card S = 7254000000 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_J1_iso {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .J1) : Nat.card S = 175560 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J1.card_J1

private theorem card_J2_iso {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .J2) : Nat.card S = 604800 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2

private theorem card_M12_iso {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .M12) : Nat.card S = 95040 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM12

theorem FivePumpNonAlt.table
    {S : Type} [Group S] [Finite S] (h : FivePumpNonAlt S) :
    ExactResidueOutcome S ∨ ¬ 225 ∣ Nat.card S := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inr (by rw [card_L2_16 h]; decide)
  · exact Or.inr (by rw [card_L3_4 h]; decide)
  · exact Or.inr (by rw [card_U3_4 h]; decide)
  · exact Or.inr (by rw [card_L2_25 h]; decide)
  · exact Or.inr (by rw [card_L3_5 h]; decide)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (by rw [card_J1_iso (Classical.choice h)]; decide)
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr (by rw [card_M12_iso (Classical.choice h)]; decide)

theorem FivePumpNonAlt.not_dvd_a9 {S : Type} [Group S] [Finite S]
    (h : FivePumpNonAlt S) :
    ¬ 181440 ∣ Nat.card S := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · rw [card_L2_16 h]; decide
  · rw [card_L3_4 h]; decide
  · rw [card_U3_4 h]; decide
  · rw [card_L2_25 h]; decide
  · rw [card_L3_5 h]; decide
  · rw [card_U3_5 h]; decide
  · rw [card_PSp4_5 h]; decide
  · rw [card_J1_iso (Classical.choice h)]; decide
  · rw [card_J2_iso (Classical.choice h)]; decide
  · rw [card_M12_iso (Classical.choice h)]; decide

theorem FiveTwoLayerOutcome.table {S : Type} [Group S] [Finite S] (h : FiveTwoLayerOutcome S) :
    Blueprint.LieModel S .PSU 4 5 1 ∨ ¬ 181440 ∣ Nat.card S := by
  rcases h with h | h
  · exact Or.inr (by rw [card_L4_5 h]; decide)
  · exact Or.inl h

theorem FivePumpNonAlt.catalog {S : Type} [Group S] (h : FivePumpNonAlt S) :
    Blueprint.Catalog S := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J1, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J2, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M12, h⟩)))

theorem FiveTwoLayerOutcome.catalog {S : Type} [Group S] (h : FiveTwoLayerOutcome S) :
    Blueprint.Catalog S := by
  rcases h with h | h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h
  · exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ h

theorem literal_of_stable {X : Type} [Group X] [Finite X] {Y N T : Subgroup X} (hNY : N ≤ Y)
    (hN : IsPComponent 2 (N.subgroupOf Y)) (hTN : T ≤ N)
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5))
    (h : T ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) :
    Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : T.subgroupOf N ⊔ pPrimeCore 2 ↥N = ⊤ := by
    have h1 := congrArg (fun Z : Subgroup X => Z.subgroupOf N) h
    simp only [subgroupOf_self] at h1
    rw [subgroupOf_sup hTN (map_subtype_le _),
      show ((pPrimeCore 2 ↥N).map N.subtype).subgroupOf N = pPrimeCore 2 ↥N from
        comap_map_eq_self_of_injective N.subtype_injective _] at h1
    exact h1
  let ψ : ↥(T.subgroupOf N) →* ↥N ⧸ pPrimeCore 2 ↥N :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (T.subgroupOf N).subtype
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥N) q
    have hm : m ∈ T.subgroupOf N ⊔ pPrimeCore 2 ↥N := by
      rw [hsup]
      exact mem_top m
    obtain ⟨s, hs, o, ho, rfl⟩ := mem_sup_of_normal_right.mp hm
    refine ⟨⟨s, hs⟩, ?_⟩
    have ho1 : QuotientGroup.mk' (pPrimeCore 2 ↥N) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    change QuotientGroup.mk' (pPrimeCore 2 ↥N) s = QuotientGroup.mk' (pPrimeCore 2 ↥N) (s * o)
    rw [map_mul, ho1, mul_one]
  have hR_bot : (pPrimeCore 2 ↥(T.subgroupOf N)).map ψ = ⊥ := by
    have hnorm : ((pPrimeCore 2 ↥(T.subgroupOf N)).map ψ).Normal := by
      haveI : (pPrimeCore 2 ↥(T.subgroupOf N)).Normal := CFSG.pPrimeCore_normal
      exact Subgroup.Normal.map this ψ hψ
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥(T.subgroupOf N)).map ψ)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ψ) CFSG.pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥(T.subgroupOf N)).map ψ ≤ pPrimeCore 2 (↥N ⧸ pPrimeCore 2 ↥N) :=
      le_sSup ⟨hnorm, hcop⟩
    have hO : pPrimeCore 2 (↥N ⧸ pPrimeCore 2 ↥N) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥N) 2
    rw [hO] at hle
    exact le_bot_iff.mp hle
  have hO_le : pPrimeCore 2 ↥(T.subgroupOf N) ≤ ψ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    have h1 : ψ s ∈ (pPrimeCore 2 ↥(T.subgroupOf N)).map ψ := Subgroup.mem_map_of_mem ψ hs
    rw [hR_bot, Subgroup.mem_bot] at h1
    exact h1
  have hker_le : ψ.ker ≤ pPrimeCore 2 ↥(T.subgroupOf N) := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hsO : (s : ↥N) ∈ pPrimeCore 2 ↥N := (QuotientGroup.eq_one_iff _).mp hs
    have hnorm : ((pPrimeCore 2 ↥N).comap (T.subgroupOf N).subtype).Normal := by
      haveI : (pPrimeCore 2 ↥N).Normal := CFSG.pPrimeCore_normal
      exact Subgroup.Normal.comap this _
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥N).comap (T.subgroupOf N).subtype)) :=
      Nat.Coprime.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 ↥N) (T.subgroupOf N).subtype
          (T.subgroupOf N).subtype_injective)
        CFSG.pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥N).comap (T.subgroupOf N).subtype ≤ pPrimeCore 2 ↥(T.subgroupOf N) :=
      le_sSup ⟨hnorm, hcop⟩
    exact hle (Subgroup.mem_comap.mpr hsO)
  have hker : ψ.ker = pPrimeCore 2 ↥(T.subgroupOf N) := le_antisymm hker_le hO_le
  have e1 : ↥N ⧸ pPrimeCore 2 ↥N ≃* ↥(T.subgroupOf N) ⧸ pPrimeCore 2 ↥(T.subgroupOf N) :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have e2 : ↥(T.subgroupOf N) ⧸ pPrimeCore 2 ↥(T.subgroupOf N) ≃* ↥T ⧸ pPrimeCore 2 ↥T :=
    QuotientGroup.congr (pPrimeCore 2 ↥(T.subgroupOf N)) (pPrimeCore 2 ↥T)
      (Subgroup.subgroupOfEquivOfLe hTN)
      (CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hTN))
  exact ⟨e1.trans (e2.trans eT)⟩

end CFSG.ComponentClassification.SolMax.FiveCat
