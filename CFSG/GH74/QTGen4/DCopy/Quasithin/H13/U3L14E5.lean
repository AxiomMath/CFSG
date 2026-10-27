module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.H13.A5RawNat
public import CFSG.Quasithin.H13.U3L14G2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_I_F4 (h1332 : Stmt13_3_2_F4) {K : Subgroup G} (hD : KData14 T L V V₂ Lp K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    ∃ I : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T I ∧
      I ⊓ centralizer (K : Set G) = ⊥ ∧ T ≤ normalizer (I : Set G) ∧ IsElemAbelian 2 I ∧
      normalizer (I : Set G) ≤ normalizer (K : Set G) ∧ Nonempty (A5.Frame T K I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, -, -, huniq⟩, ⟨⟨I, hI⟩, hall⟩, -⟩ := h1332 G T L S.h13 K hD.faithful
  obtain ⟨-, hTI, -, hIc, hmod⟩ := hall I hI
  have hKI : K ≤ normalizer (I : Set G) := hI.2.2.1
  have hIe : IsElemAbelian 2 I := ⟨hIc, fun v hv => (mem_reducedAggregate' (hI.1 hv)).2.2⟩

  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hO : pCoreOf 2 K ≤ centralizer (I : Set G) := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K _ le_sup_left hKn
    intro k hk
    rw [mem_centralizer_iff]
    intro v hv
    exact ((mem_reducedAggregate' (hI.1 hv)).2.1 k (h1 hk)).symm
  obtain ⟨e₀⟩ := hA5
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
    rw [Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hle := card_autOn_le_card_quot hKI hO
  rw [hcard] at hle
  rcases hmod with ⟨hnat, hZ⟩ | ⟨hnat, -⟩ | ⟨-, -, hreal⟩ | ⟨hlin, -, -⟩ | ⟨hu, -, -⟩
  ·
    have hNL : normalizer (I : Set G) ≤ normalizer (K : Set G) := by
      have hI2 : IsPGroup 2 I := fun v => ⟨1, Subtype.ext (by simpa using hIe.2 v v.2)⟩
      obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
        (⟨I, hI.2.1, hI2, rfl⟩ : IsTwoLocal (normalizer (I : Set G)))
      have := huniq M' hM' ((sup_le hKI hTI).trans hM'le)
      exact this ▸ hM'le
    have hsyl : IsSylowTwoOf (T ⊓ K) K :=
      isSylowTwoOf_inf_of_le_normalizer (S.syl (le_sup_right : T ≤ K ⊔ T)) le_sup_left
        (sup_le le_normalizer hD.T_K)
    obtain ⟨R⟩ := A5.exists_rawData5_of_nat hKI hnat
    obtain ⟨F⟩ := A5.exists_frame R hNL S.isP_T hTI hsyl
    exact ⟨I, hI, hZ, hTI, hIe, hNL, ⟨F⟩⟩
  ·
    obtain ⟨e6⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) hnat
    rw [Nat.card_congr e6.toEquiv] at hle
    change Nat.card ↥(alternatingGroup (Fin 6)) ≤ 60 at hle
    rw [nat_card_alternatingGroup, Nat.card_fin] at hle
    exact absurd hle (by decide)
  · obtain ⟨e6⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altCoreModel_faithful (by norm_num)) hreal
    rw [Nat.card_congr e6.toEquiv] at hle
    change Nat.card ↥(alternatingGroup (Fin 6)) ≤ 60 at hle
    rw [nat_card_alternatingGroup, Nat.card_fin] at hle
    exact absurd hle (by decide)
  · obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel hlin
    rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two] at hcard
    exact absurd hcard (by norm_num)
  · rw [card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hu)] at hcard
    exact absurd hcard (by norm_num)

end Set14

end CFSG.Quasithin.H13.U3
