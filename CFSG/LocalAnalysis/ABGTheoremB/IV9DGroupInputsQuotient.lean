module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputsLinear
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputsASeven
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.ABGDGroups.LinearSignalizers
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
public import Certificates.Certificate7
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44

public section

namespace CFSG.ABGTheoremB.IV9DGroups

open CFSG.QuasiDihedralFusion CFSG.ABGDGroups CFSG.ABGLocalTools

variable {Q : Type} [Group Q] [Finite Q]

theorem eq_bot_of_hasWreathedSylow (hQ : IsDGroup Q) (hO : CFSG.oddCore Q = ⊥) {n : ℕ}
    (hW : HasWreathedSylow Q n) {T X : Subgroup Q} (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set Q)) : X = ⊥ := by
  rcases hQ with ⟨hDih, -⟩ | ⟨K, hK⟩
  · exact (not_hasWreathedSylow_and_dihedral hW hDih).elim
  · rw [eq_bot_iff, ← hO]
    exact wreathed_dGroup_odd_four_invariant_le_oddCore hK hW hT hX hXT

theorem four_lt_card {T D : Subgroup Q} (hT : IsKleinFour T) (hTD : T ≤ D) (hDT : D ≠ T) :
    4 < Nat.card D := by
  have hle : Nat.card T ≤ Nat.card D := Subgroup.card_le_of_le hTD
  rw [hT.card_four] at hle
  rcases hle.lt_or_eq with h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hTD (by rw [← h, hT.card_four])).symm hDT

omit [Finite Q] in
theorem isPGroup_two_of_isKleinFour {T : Subgroup Q} (hT : IsKleinFour T) : IsPGroup 2 T :=
  IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)

theorem exists_odd_le_centralizer (hQ : IsDGroup Q) (hO : CFSG.oddCore Q = ⊥)
    {T D : Subgroup Q} (hT : IsKleinFour T) (hTD : T ≤ D) (hD : IsPGroup 2 D) (hDT : D ≠ T)
    (hDN : D ≤ Subgroup.normalizer (T : Set Q)) {x : Q} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hxD : D ≤ Subgroup.centralizer ({x} : Set Q)) {Z : Subgroup Q} (hZ : Odd (Nat.card Z))
    (hZD : D ≤ Subgroup.normalizer (Z : Set Q)) :
    ∃ W : Subgroup Q, Odd (Nat.card W) ∧ Z ≤ W ∧ W ≤ Subgroup.centralizer ({x} : Set Q) ∧
      Subgroup.centralizer ({x} : Set Q) ≤ Subgroup.normalizer (W : Set Q) := by
  by_cases hW : ∃ n, HasWreathedSylow Q n
  · obtain ⟨n, hn⟩ := hW
    have hZ1 := eq_bot_of_hasWreathedSylow hQ hO hn hT hZ (hTD.trans hZD)
    refine ⟨⊥, by rw [Subgroup.card_bot]; decide, hZ1.le, bot_le, ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  rcases aSeven_or_linearDecomposition hQ hO hW with he | hlin
  · obtain ⟨e⟩ := he
    exact exists_odd_le_centralizer_of_aSeven e hD (four_lt_card hT hTD hDT) (hTD hxT) hx1 hxD
      hZ hZD
  · have : IsKleinFour T := hT
    have hx : orderOf x = 2 := kleinFour_orderOf hxT hx1
    obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({x} : Set Q))) := inferInstance
    set x' : Subgroup.centralizer ({x} : Set Q) :=
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hx'P : x' ∈ (P : Subgroup (Subgroup.centralizer ({x} : Set Q))) := by
      have hcen : Subgroup.zpowers x' ≤
          Subgroup.center (Subgroup.centralizer ({x} : Set Q)) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
      have : (Subgroup.zpowers x').Normal := Subgroup.normal_of_le_center hcen
      have h2 : IsPGroup 2 (Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
      exact h2.le_sylow_of_normal P (Subgroup.mem_zpowers x')
    set PQ := (P : Subgroup (Subgroup.centralizer ({x} : Set Q))).map
      (Subgroup.centralizer ({x} : Set Q)).subtype
    have hxPQ : x ∈ PQ := ⟨x', hx'P, rfl⟩
    obtain ⟨S, hPS⟩ :=
      (P.isPGroup'.map (Subgroup.centralizer ({x} : Set Q)).subtype).exists_le_sylow
    obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
    have hEP : E ≤ Subgroup.centralizer (PQ : Set Q) :=
      hd.le_centralizer.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPS))
    have hEx : E ≤ Subgroup.centralizer ({x} : Set Q) :=
      hEP.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxPQ))
    have hZx : Z ≤ Subgroup.centralizer ({x} : Set Q) := by
      obtain ⟨t, htT, ht1, hZt⟩ := hd.exists_le_centralizer_of_kleinFour hT (hTD.trans hZD)
        (inf_eq_bot_of_odd_of_isPGroup hZ (isPGroup_two_of_isKleinFour hT))
      have hDT' : ¬ D ≤ Subgroup.centralizer (T : Set Q) := by
        intro hle
        apply hDT
        obtain ⟨P', hP'⟩ := hD.exists_le_sylow
        have hDL : D ≤ L := hP'.trans (hd.sylow_le P')
        exact le_antisymm ((le_inf hDL hle).trans (hd.inf_centralizer_kleinFour hT).le) hTD
      exact le_centralizer_of_kleinFour hDN hxT hx1 hxD hDT' hZD htT ht1 hZt
    obtain ⟨W, hWodd, hWC, hCW, hWZ⟩ :=
      LinearDecomposition.exists_odd_normal_of_le_centralizer hd hx le_rfl hEx P hEP
    exact ⟨W, hWodd, hWZ Z hZ hZx, hWC, hCW⟩

end CFSG.ABGTheoremB.IV9DGroups
