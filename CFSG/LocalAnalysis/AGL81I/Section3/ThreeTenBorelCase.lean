module

public import CFSG.LocalAnalysis.AGL81I.Section3.SL2AutStructure
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open scoped MatrixGroups

variable {H : Type} [Group H] [Finite H]

theorem normalizer_inter_le_Y_of_nontrivial_le {I D P Y A : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) (hAD : A ≤ D) (hAne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set H) ⊓ (I ⊔ D) ≤ Y := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact d.Prime := ⟨hd⟩
  have hApg : IsPGroup d A := hD.isPGroup.to_le hAD
  have hdvd : d ∣ Nat.card A := by
    rcases hApg.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hAne
    · exact h1
  have hpos : 1 ≤ CFSG.Open.pRank d (A.subgroupOf (I ⊔ D)) := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf d
      (hAD.trans le_sup_right)]
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.one_le_pRank_of_dvd_card hd hdvd
  intro x hx
  have hxT : x ∈ I ⊔ D := hx.2
  let y : ↥(I ⊔ D) := ⟨x, hxT⟩
  have hyN : y ∈ Subgroup.normalizer
      ((A.subgroupOf (I ⊔ D) : Subgroup ↥(I ⊔ D)) : Set ↥(I ⊔ D)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (hAD.trans le_sup_right)]
    rw [Subgroup.mem_subgroupOf]
    exact hx.1
  have hcore : y ∈ CFSG.Open.GLBCore d 1 (D.subgroupOf (I ⊔ D)) :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer
      (p := d) (k := 1) (Q := A.subgroupOf (I ⊔ D))
      (Subgroup.subgroupOf_mono (I ⊔ D) hAD) hpos le_rfl) hyN
  exact hγ (Subgroup.mem_map.mpr ⟨y, hcore, rfl⟩)

section PSLBorel

variable {F : Type} [Field F] [Finite F]

theorem not_normalizer_le_borel_PSL {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ≠ ringChar F) (A : Subgroup (PSL(2, F))) (hAne : A ≠ ⊥)
    (hA : IsPGroup d A) :
    ¬ Subgroup.normalizer (A : Set (PSL(2, F))) ≤ CFSG.PSL2Table.borel F := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  intro hN
  have hcardker : Nat.card (CFSG.PSL2Table.mk (F := F)).ker ≤ 2 := by
    rw [show (CFSG.PSL2Table.mk (F := F)).ker = Subgroup.center (SL(2, F)) by
      simp [CFSG.PSL2Table.mk, QuotientGroup.ker_mk']]
    exact card_center_SL_le_two
  have hker : ¬ d ∣ Nat.card (CFSG.PSL2Table.mk (F := F)).ker := by
    intro hdvd
    have hpos : 0 < Nat.card (CFSG.PSL2Table.mk (F := F)).ker := Nat.card_pos
    have hle : d ≤ Nat.card (CFSG.PSL2Table.mk (F := F)).ker := Nat.le_of_dvd hpos hdvd
    have hd3 : 3 ≤ d := by
      rcases hd.eq_two_or_odd' with h | ⟨k, hk⟩
      · exact absurd h hd2
      · have hdpos : 1 < d := hd.one_lt
        omega
    omega
  obtain ⟨Q, hQp, -, hQmap, -⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker
      (p := d) (f := CFSG.PSL2Table.mk (F := F)) CFSG.PSL2Table.mk_surjective hker hA
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [← hQmap, hbot, Subgroup.map_bot]
  have hQnontriv : 1 < Nat.card Q := (Subgroup.one_lt_card_iff_ne_bot Q).mpr hQne
  obtain ⟨w, hwN, hwb⟩ := exists_normalizer_not_mem_borel hd hd2 hdp Q hQnontriv hQp
  have hNw : CFSG.PSL2Table.mk w ∈ Subgroup.normalizer (A : Set (PSL(2, F))) := by
    rw [← hQmap]
    exact Subgroup.le_normalizer_map (H := Q) (f := CFSG.PSL2Table.mk (F := F))
      ⟨w, hwN, rfl⟩
  have hwb' : CFSG.PSL2Table.mk w ∉ CFSG.PSL2Table.borel F := by
    intro hmem
    exact hwb ((CFSG.PSL2Table.mk_mem_borel_iff w).mp hmem)
  exact hwb' (hN hNw)

end PSLBorel

section Transport

variable {X : Type} [Group X] [Finite X]

theorem not_normalizer_le_map_borelSL {d p : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (e : X ≃* SL(2, ZMod p)) (A : Subgroup X) (hAne : A ≠ ⊥) (hA : IsPGroup d A) :
    ¬ Subgroup.normalizer (A : Set X) ≤
      (CFSG.PSL2Table.borelSL (ZMod p)).map e.symm.toMonoidHom := by
  intro hN
  haveI : Fact d.Prime := ⟨hd⟩
  let A' : Subgroup (SL(2, ZMod p)) := A.map e.toMonoidHom
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    refine hAne ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) A
      e.injective).mp ?_)
    exact hbot
  have hA'pg : IsPGroup d A' := hA.map e.toMonoidHom
  have hA'nontriv : 1 < Nat.card A' := (Subgroup.one_lt_card_iff_ne_bot A').mpr hA'ne
  have hdp' : d ≠ ringChar (ZMod p) := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨w, hwN, hwb⟩ :=
    exists_normalizer_not_mem_borel hd hd2 hdp' A' hA'nontriv hA'pg
  have hmapN : Subgroup.normalizer (A' : Set (SL(2, ZMod p))) ≤
      CFSG.PSL2Table.borelSL (ZMod p) := by
    calc Subgroup.normalizer (A' : Set (SL(2, ZMod p)))
        = (Subgroup.normalizer (A : Set X)).map e.toMonoidHom := by
          rw [Subgroup.map_equiv_normalizer_eq A e]
      _ ≤ ((CFSG.PSL2Table.borelSL (ZMod p)).map e.symm.toMonoidHom).map e.toMonoidHom :=
          Subgroup.map_mono hN
      _ = CFSG.PSL2Table.borelSL (ZMod p) := by
          rw [Subgroup.map_map,
            show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from by
              ext x
              simp,
            Subgroup.map_id]
  exact hwb (hmapN hwN)

theorem not_normalizer_le_map_borel {d p : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (e : X ≃* PSL(2, ZMod p)) (A : Subgroup X) (hAne : A ≠ ⊥) (hA : IsPGroup d A) :
    ¬ Subgroup.normalizer (A : Set X) ≤
      (CFSG.PSL2Table.borel (ZMod p)).map e.symm.toMonoidHom := by
  intro hN
  haveI : Fact d.Prime := ⟨hd⟩
  let A' : Subgroup (PSL(2, ZMod p)) := A.map e.toMonoidHom
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    refine hAne ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) A
      e.injective).mp ?_)
    exact hbot
  have hA'pg : IsPGroup d A' := hA.map e.toMonoidHom
  have hdp' : d ≠ ringChar (ZMod p) := by rwa [ZMod.ringChar_zmod_n]
  have hb := not_normalizer_le_borel_PSL (F := ZMod p) hd hd2 hdp' A' hA'ne hA'pg
  apply hb
  calc Subgroup.normalizer (A' : Set (PSL(2, ZMod p)))
      = (Subgroup.normalizer (A : Set X)).map e.toMonoidHom := by
        rw [Subgroup.map_equiv_normalizer_eq A e]
    _ ≤ ((CFSG.PSL2Table.borel (ZMod p)).map e.symm.toMonoidHom).map e.toMonoidHom :=
        Subgroup.map_mono hN
    _ = CFSG.PSL2Table.borel (ZMod p) := by
        rw [Subgroup.map_map,
          show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from by
            ext x
            simp,
          Subgroup.map_id]

end Transport

theorem normalizer_subgroupOf_le_of_normalizer_inf_le {I E Y B : Subgroup H}
    {B' : Subgroup ↥I} (hEI : E ≤ I) (hB : Y ⊓ I = B) (hBorel : B = B'.map I.subtype)
    (hN : Subgroup.normalizer (E : Set H) ⊓ I ≤ B) :
    Subgroup.normalizer ((E.subgroupOf I) : Set ↥I) ≤ B' := by
  intro x hx
  have hxN : (x : H) ∈ Subgroup.normalizer (E : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hEI] at hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact hx
  have hxB : (x : H) ∈ B := hN ⟨hxN, x.2⟩
  rw [hBorel] at hxB
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxB
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

theorem D_inf_I_eq_bot_of_isSLType {I D P Y B : Subgroup H} {p d : ℕ} [Fact p.Prime]
    (hhyp : ThreeTenHyp I D P Y p d) (e : ↥I ≃* SL(2, ZMod p))
    (hB : Y ⊓ I = B)
    (hBorel : B = ((CFSG.PSL2Table.borelSL (ZMod p)).map e.symm.toMonoidHom).map I.subtype) :
    D ⊓ I = ⊥ := by
  by_contra hne
  have hEne : D ⊓ I ≠ ⊥ := hne
  have hNY : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ (I ⊔ D) ≤ Y :=
    normalizer_inter_le_Y_of_nontrivial_le hhyp inf_le_left hEne
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hNIY : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ Y := by
    intro x hx
    exact hNY ⟨hx.1, (le_sup_left : I ≤ I ⊔ D) hx.2⟩
  have hNIB : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ B := by
    have h : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ Y ⊓ I :=
      le_inf hNIY inf_le_right
    rwa [hB] at h
  have hsub : Subgroup.normalizer (((D ⊓ I).subgroupOf I) : Set ↥I) ≤
      (CFSG.PSL2Table.borelSL (ZMod p)).map e.symm.toMonoidHom :=
    normalizer_subgroupOf_le_of_normalizer_inf_le
      (inf_le_right : D ⊓ I ≤ I) hB hBorel hNIB
  have hE'ne : ((D ⊓ I).subgroupOf I) ≠ ⊥ := by
    intro hbot
    apply hEne
    have hmap := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D ⊓ I ≤ I)
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hE'pg : IsPGroup d ((D ⊓ I).subgroupOf I) :=
    (hD.isPGroup.to_le (inf_le_left : D ⊓ I ≤ D)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ I ≤ I)).symm
  exact not_normalizer_le_map_borelSL hd hd2 hdp e _ hE'ne hE'pg hsub

theorem D_inf_I_eq_bot_of_isPSLType {I D P Y B : Subgroup H} {p d : ℕ} [Fact p.Prime]
    (hhyp : ThreeTenHyp I D P Y p d) (e : ↥I ≃* PSL(2, ZMod p))
    (hB : Y ⊓ I = B)
    (hBorel : B = ((CFSG.PSL2Table.borel (ZMod p)).map e.symm.toMonoidHom).map I.subtype) :
    D ⊓ I = ⊥ := by
  by_contra hne
  have hEne : D ⊓ I ≠ ⊥ := hne
  have hNY : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ (I ⊔ D) ≤ Y :=
    normalizer_inter_le_Y_of_nontrivial_le hhyp inf_le_left hEne
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hNIY : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ Y := by
    intro x hx
    exact hNY ⟨hx.1, (le_sup_left : I ≤ I ⊔ D) hx.2⟩
  have hNIB : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ B := by
    have h : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ Y ⊓ I :=
      le_inf hNIY inf_le_right
    rwa [hB] at h
  have hsub : Subgroup.normalizer (((D ⊓ I).subgroupOf I) : Set ↥I) ≤
      (CFSG.PSL2Table.borel (ZMod p)).map e.symm.toMonoidHom :=
    normalizer_subgroupOf_le_of_normalizer_inf_le
      (inf_le_right : D ⊓ I ≤ I) hB hBorel hNIB
  have hE'ne : ((D ⊓ I).subgroupOf I) ≠ ⊥ := by
    intro hbot
    apply hEne
    have hmap := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D ⊓ I ≤ I)
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hE'pg : IsPGroup d ((D ⊓ I).subgroupOf I) :=
    (hD.isPGroup.to_le (inf_le_left : D ⊓ I ≤ D)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ I ≤ I)).symm
  exact not_normalizer_le_map_borel hd hd2 hdp e _ hE'ne hE'pg hsub

end CFSG.LocalAnalysis.AGL81I.Section3
