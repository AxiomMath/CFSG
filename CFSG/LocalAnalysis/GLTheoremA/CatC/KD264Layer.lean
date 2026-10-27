module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowData
public import CFSG.GH74.Uniqueness.SU.KI1r4EComp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.PerfectCore
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG CFSG.Open CFSG.RankThree.PartTwo.Sec21

theorem layer_quasisimple_normal {T : Type} [Group T] (C : Subgroup T)
    (hs : IsSimpleGroup (↥(inSubgroup CFSG.layer C) ⧸ Subgroup.center ↥(inSubgroup CFSG.layer C))) :
    CFSG.Open.IsQuasisimple ↥(inSubgroup CFSG.layer C) ∧ inSubgroup CFSG.layer C ≤ C ∧
      ((inSubgroup CFSG.layer C).subgroupOf C).Normal := by
  set E := inSubgroup CFSG.layer C
  have hsub : E.subgroupOf C = CFSG.layer ↥C := by
    simp only [E, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hEC : E ≤ C := Subgroup.map_subtype_le _
  have eE : ↥(CFSG.layer ↥C) ≃* ↥E :=
    (CFSG.layer ↥C).equivMapOfInjective C.subtype C.subtype_injective
  have hperf : Group.IsPerfect ↥(CFSG.layer ↥C) :=
    (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.isPerfect_iff_commutator_eq _).2
      CFSG.GH74.Uniqueness.SU.K.R4.layer_perfect
  have hperfE : commutator ↥E = ⊤ := by
    have h1 : commutator ↥(CFSG.layer ↥C) = ⊤ := hperf.commutator_eq_top
    rw [← Subgroup.map_top_of_surjective eE.toMonoidHom eE.surjective, ← h1, commutator_def,
      commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ eE.surjective]
  refine ⟨⟨hperfE, hs⟩, hEC, ?_⟩
  rw [hsub]
  exact CFSG.GH74.Uniqueness.SU.K.R4.layer_normal _

theorem kd264RowData_of_layer {T : Type} [Group T] [Finite T]
    (hfac : (Nat.card T).factorization 3 = 3)
    (hno : ∀ D : Subgroup T, IsElemAbelian 3 D → Nat.card D ≠ 27)
    (hlay : ∀ x : T, x ≠ 1 → IsCentral218 (⊤ : Subgroup T) x →
      IsSimpleGroup (↥(inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T))) ⧸
        Subgroup.center ↥(inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)))) ∧
      3 ∣ Nat.card ↥(inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)))) :
    KD264RowData 3 T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hno3 : ∀ S : Subgroup T, IsElemAbelian 3 S → Nat.card S < 3 ^ 3 := by
    intro S hS
    obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hS).exists_card_eq
    have hdvd : 3 ^ k ∣ Nat.card T := hk ▸ Subgroup.card_subgroup_dvd_card S
    have hk3 : k ≤ 3 := by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hT0).1 hdvd
      omega
    have hne := hno S hS
    rw [hk] at hne ⊢
    interval_cases k <;> simp_all
  set P₀ : Sylow 3 T := default
  have hP₀card : Nat.card (P₀ : Subgroup T) = 3 ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  haveI : Nontrivial ↥(P₀ : Subgroup T) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP₀card]; norm_num
  haveI : Nontrivial ↥(Subgroup.center ↥(P₀ : Subgroup T)) := P₀.isPGroup'.center_nontrivial
  obtain ⟨m, hm⟩ := (P₀.isPGroup'.to_subgroup (Subgroup.center _)).exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := ↥(Subgroup.center ↥(P₀ : Subgroup T)))
    rw [hm, pow_zero] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(P₀ : Subgroup T))) 3
    (by rw [hm]; exact dvd_pow_self 3 hm0)
  set z₀ : T := ((c : ↥(P₀ : Subgroup T)) : T)
  have hzo : orderOf z₀ = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hc
  have hzP : ∀ g ∈ (P₀ : Subgroup T), g * z₀ = z₀ * g := by
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨g, hg⟩)
  have hz1 : z₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have hcen : IsCentral218 (⊤ : Subgroup T) z₀ := by
    refine ⟨P₀, ⟨P₀.subtype le_top, ?_⟩, ⟨c, c.2, rfl⟩⟩
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq]
  obtain ⟨hs, h3⟩ := hlay z₀ hz1 hcen
  obtain ⟨hq, hEC, hEn⟩ := layer_quasisimple_normal _ hs
  have hJ := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hq h3
    hEC hEn
  exact kd264RowData_of_central Nat.prime_three hno3 z₀ hzo P₀ hzP hJ

theorem kd264RowData_of_tripleCover {T : Type} [Group T] [Finite T] {k : ℕ} (hk : 5 ≤ k)
    (hfac : (Nat.card T).factorization 3 = 3)
    (hno : ∀ D : Subgroup T, IsElemAbelian 3 D → Nat.card D ≠ 27)
    (hlay : ∀ x : T, x ≠ 1 → IsCentral218 (⊤ : Subgroup T) x →
      x ∈ inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)) ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover
        ↥(inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)))
        (alternatingGroup (Fin k))) :
    KD264RowData 3 T := by
  refine kd264RowData_of_layer hfac hno fun x hx1 hx => ?_
  obtain ⟨-, hc3, ⟨e⟩⟩ := hlay x hx1 hx
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hk)
  refine ⟨e.isSimpleGroup, ?_⟩
  rw [← hc3]
  exact Subgroup.card_subgroup_dvd_card _

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
