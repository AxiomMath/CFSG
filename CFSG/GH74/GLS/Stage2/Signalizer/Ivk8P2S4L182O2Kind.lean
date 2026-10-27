module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182O2Cen
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182O2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_two_pow)

section Bar

variable {G : Type} [Group G] [Finite G]

@[expose] def barPCore (z : G) : Subgroup (CentralizerBar z) :=
  (pCore 2 ↥(Cen z)).map (toBar z)

omit [Finite G] in
theorem barPCore_normal (z : G) : (barPCore z).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Subgroup.Normal.map pCore_normal (toBar z) (toBar_surjective z)

omit [Finite G] in
theorem barPCore_isPGroup (z : G) : IsPGroup 2 ↥(barPCore z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCore_isPGroup (G := ↥(Cen z)) (p := 2)).map (toBar z)

theorem barPCore_le_generalizedFitting (z : G) :
    barPCore z ≤ generalizedFitting (CentralizerBar z) :=
  (CFSG.LocalCores.fitting_characteristic.2.2 _ (barPCore_normal z)
    (barPCore_isPGroup z).isNilpotent).trans le_sup_left

theorem pRank_Op2_le_one {z : G} {A : Subgroup (CentralizerBar z)} (hTA : barPCore z ≤ A)
    (hA : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → x = y) :
    pRank 2 ↥(Op 2 (Cen z)) ≤ 1 :=
  pRank_le_one_of_noCommuting (noCommuting_map_subtype (J := pCore 2 ↥(Cen z)) hTA hA)

end Bar

section Kinds

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

@[expose] def UniqueInvCover (z : G) : Prop :=
  ∃ A : Subgroup (CentralizerBar z), barPCore z ≤ A ∧
    ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → x = y

theorem exists_unique_inv_of_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) : UniqueInvCover z := by
  have hK₁ : IsComponent L₁ := (show L₁ ∈ {K | IsComponent K} by
    rw [hP.comps]; exact Set.mem_insert _ _)
  have hT : barPCore z ≤ L₁ ⊔ L₂ := by
    rw [hP.prod.1, ← hP.fitting]
    exact barPCore_le_generalizedFitting z
  exact ⟨L₂, le_of_centralizes_component hK₁ (barPCore_normal z) (barPCore_isPGroup z)
    hP.prod.2.1 (sl2_model_center_inv hP.odd hP.sl₁).1 hP.prod.2.2 hT,
    (sl2_model_center_inv hP.odd hP.sl₂).2⟩

theorem exists_unique_inv_of_g2 {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ r₂ L₁ L₂) : UniqueInvCover z := by
  obtain ⟨hr₁, hr₂, hgt₁, hprod, m₁, m₂, -, h3, h4, -, -, -⟩ := hsh
  have hr₂ge : 2 ≤ r₂ := by
    obtain ⟨F, _, _, hF', -⟩ := m₂
    rw [← hF']
    exact Finite.one_lt_card
  have hfacts := sl2_model_facts hr₁ (by omega) m₁
  have hK₁ : IsComponent L₁ :=
    ⟨hfacts.1, isSubnormal_of_commute (LBar_normal z) hprod.1 hprod.2.1⟩
  have hFL : generalizedFitting (CentralizerBar z) ≤ LBar z := by
    rcases Nat.lt_or_ge 3 r₂ with hgt | hle
    · exact ((h4 hgt).2).le
    · have hr₃ : r₂ = 3 := by
        obtain ⟨m, hm⟩ := hr₂
        omega
      rw [(h3 hr₃).2]
      exact Subgroup.map_subtype_le _
  have hT : barPCore z ≤ L₁ ⊔ L₂ := by
    rw [hprod.1]
    exact (barPCore_le_generalizedFitting z).trans hFL
  exact ⟨L₂, le_of_centralizes_component hK₁ (barPCore_normal z) (barPCore_isPGroup z)
    hprod.2.1 hfacts.2.1 hprod.2.2 hT, (sl2_model_center_inv hr₂ m₂).2⟩

theorem exists_unique_inv_of_cover {n : ℕ} (h : IsDoubleCoverOfAlt (CentralizerBar z) n) :
    UniqueInvCover z :=
  ⟨center (CentralizerBar z), le_center_of_quasisimple h.1 (barPCore_normal z)
    (barPCore_isPGroup z), unique_involution_of_card_two h.2.1⟩

theorem isSolvable_cen_of_m12 (h : Stage1M12 G z S) : Group.IsSolvable ↥(Cen z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWn, ⟨e⟩⟩ := h.quot
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have hWs : Group.IsSolvable ↥(WBar z) := by
    have : Group.IsNilpotent ↥(WBar z) := hWp.isNilpotent
    infer_instance
  have hP3 : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    CFSG.OrderReductions.PermutationReduction.permutation_solvable_of_card_le_four (Fin 3)
      (by simp)
  have hQs : Group.IsSolvable (CentralizerBar z ⧸ WBar z) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hC : Group.IsSolvable (CentralizerBar z) :=
    CFSG.isSolvable_of_normal_subgroup_and_quotient (WBar z)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hO : Group.IsSolvable ↥(pPrimeCore 2 ↥(Cen z)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact CFSG.isSolvable_of_normal_subgroup_and_quotient (pPrimeCore 2 ↥(Cen z))

theorem exists_unique_inv {k : Kind} (ctx : Stage2Ctx G z k S)
    (hns : ¬ Group.IsSolvable ↥(Cen z)) : UniqueInvCover z := by
  cases ctx.data with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := h.shape
    exact exists_unique_inv_of_g2 hsh
  | m12 h => exact (hns (isSolvable_cen_of_m12 h)).elim
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hP⟩ := h
    exact exists_unique_inv_of_pair hP.pair
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hL⟩ := h
    exact exists_unique_inv_of_pair hL.pair
  | mcl h =>
    obtain ⟨n, -, hS⟩ := h
    exact exists_unique_inv_of_cover hS.cover
  | ly h =>
    obtain ⟨n, -, hS⟩ := h
    exact exists_unique_inv_of_cover hS.cover

end Kinds

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182O2
