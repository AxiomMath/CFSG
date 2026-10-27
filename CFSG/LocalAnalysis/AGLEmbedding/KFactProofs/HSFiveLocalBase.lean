
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import Certificates.Certificate19830
public import Certificates.Data.HSFiveLocalR
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.Native.HSMcLAut

@[expose] public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.RankThree.Native Certificates.MaxD2Heis
open CFSG.ComponentClassification.OuterAutomorphisms

theorem hs_tabs_eq :
    hs100Arr 0 = hsTabA ∧ hs100Arr 1 = hsTabB ∧ hs100Arr 15 = hsTabU ∧ hsTabA.size = 100 ∧
      hsTabB.size = 100 ∧ hsTabU.size = 100 :=
  Certificates.certificate19830

theorem hs_tab_a :
    TabRep hsTabA hs100A := by
  have h := rep_hs100A
  rw [hs_tabs_eq.1] at h
  exact ⟨hs_tabs_eq.2.2.2.1, fun i => h i⟩

theorem hs_tab_b :
    TabRep hsTabB hs100B := by
  have h := rep_hs100B
  rw [hs_tabs_eq.2.1] at h
  exact ⟨hs_tabs_eq.2.2.2.2.1, fun i => h i⟩

theorem hs_tab_u :
    TabRep hsTabU hs100U := by
  have h := rep_hs100U
  rw [hs_tabs_eq.2.2.1] at h
  exact ⟨hs_tabs_eq.2.2.2.2.2, fun i => h i⟩

theorem hsS_two {a b : Tab} {A B : Equiv.Perm (Fin 100)} (ha : TabRep a A) (hb : TabRep b B) :
    ∀ j, TabRep ((#[a, b] : Array Tab).getD j (idTab 100)) ([A, B].getD j 1) :=
  rep_getD_of_forall (L := [a, b]) (P := [A, B]) rfl (by
    intro i hi
    have hi' : i < 2 := hi
    interval_cases i
    · exact ha
    · exact hb)

theorem hsS_three {a b c : Tab} {A B C : Equiv.Perm (Fin 100)} (ha : TabRep a A)
    (hb : TabRep b B) (hc : TabRep c C) :
    ∀ j, TabRep ((#[a, b, c] : Array Tab).getD j (idTab 100)) ([A, B, C].getD j 1) :=
  rep_getD_of_forall (L := [a, b, c]) (P := [A, B, C]) rfl (by
    intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact ha
    · exact hb
    · exact hc)

theorem hsFiveDataP_hS :
    ∀ j, TabRep (hsFiveDataP.gT.getD j (idTab 100)) ([hs100A, hs100B].getD j 1) :=
  hsS_two hs_tab_a hs_tab_b

theorem hsFiveDataR_hS :
    ∀ j, TabRep (hsFiveDataR.gT.getD j (idTab 100)) ([hs100A, hs100B, hs100U].getD j 1) :=
  hsS_three hs_tab_a hs_tab_b hs_tab_u

theorem hsP_closure_eq :
    Subgroup.closure {g | g ∈ [hs100A, hs100B]} = hs100P := by
  unfold hs100P
  congr 1
  ext g
  simp

theorem hsR_closure_eq :
    Subgroup.closure {g | g ∈ [hs100A, hs100B, hs100U]} = hs100R := by
  unfold hs100R
  congr 1
  ext g
  simp

theorem orderOf_three_zmod_five_hs : orderOf ((3 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem eq_or_eq_of_index_two {G : Type*} [Group G] [Finite G] {P B R : Subgroup G}
    (hPB : P ≤ B) (hBR : B ≤ R) (hcard : Nat.card R = 2 * Nat.card P) : B = P ∨ B = R := by
  have h1 : Nat.card P ∣ Nat.card B := Subgroup.card_dvd_of_le hPB
  have h2 : Nat.card B ∣ Nat.card R := Subgroup.card_dvd_of_le hBR
  obtain ⟨k, hk⟩ := h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  rw [hk, hcard] at h2
  have hk2 : k ∣ 2 := by
    have : Nat.card P * k ∣ Nat.card P * 2 := by rwa [mul_comm 2] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hPB (by rw [hk, mul_one])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hBR (by rw [hcard, hk, mul_comm])

end CFSG.AGLEmbeddingD2
