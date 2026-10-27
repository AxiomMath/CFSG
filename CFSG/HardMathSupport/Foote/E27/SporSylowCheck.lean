module

public import CFSG.HardMathSupport.Foote.E27.SporSylowCheckData
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sylowCentWitOK_spec {n : ℕ} (hn : n < 2 ^ 32) {cap m : ℕ} {gs : List Table}
    {ws : List Wit235} (h : sylowCentWitOK n cap m gs ws = true) :
    Nat.card ↥(genOf n gs) = m ∧
      ∀ s ∈ genOf n gs, s ^ 3 = 1 → s ≠ 1 →
        81 ∣ Nat.card ↥(genOf n gs ⊓ centralizer ({s} : Set (Equiv.Perm (Fin n)))) ∨
          ∃ w ∈ ws, ∃ P ∈ genOf n gs, s = P * tp n w.x * P⁻¹ ∧
            tp n w.a * tp n w.x = tp n w.x * tp n w.a ∧
            tp n w.b * tp n w.x = tp n w.x * tp n w.b ∧
            tp n w.a ^ 2 = 1 ∧ tp n w.b ^ 3 = 1 ∧ (tp n w.a * tp n w.b) ^ 5 = 1 ∧
            tp n w.b ≠ 1 := by
  classical
  simp only [sylowCentWitOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hperm, henum⟩, hws⟩, hall⟩ := h
  have hg : ∀ g ∈ gs, permOK n g = true := fun g hg => List.all_eq_true.1 hperm g hg
  obtain ⟨hcard, hrep, hcov, hdist⟩ := enumOK_spec hn hg henum
  set E := (mulClosureH n gs.toArray cap).1 with hE
  have hrepL := forall₂_tablePerm (fun k hk => (hrep k hk).1)
  have hnodup := nodup_of_hkeysDistinct hrepL hdist
  have hmemL : ∀ g, g ∈ E.toList.map (tablePerm n) ↔ g ∈ genOf n gs := by
    intro g
    constructor
    · intro hg'
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm (fun k hk => (hrep k hk).1) hg'
      exact (hrep k hk).2
    · intro hg'
      obtain ⟨k, hk, hkrep⟩ := hcov g hg'
      refine List.mem_map.mpr ⟨E[k]!, ?_, tablePerm_eq hkrep⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  refine ⟨hcard, fun s hs hs3 hs1 => ?_⟩
  obtain ⟨k, hk, hkrep⟩ := hcov s hs
  have hmem : E[k]! ∈ E.toList := by
    rw [getElem!_pos E k hk]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  have hsel : selOK n [3] E[k]! = true := (selOK_iff hn hkrep).2 ⟨hs1, 3, by simp, hs3⟩
  have hc := List.all_eq_true.1 hall _ hmem
  simp only [hsel, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · left
    have hcount := card_subtype_eq_countP (genOf n gs) (E.toList.map (tablePerm n)) hnodup hmemL
      (fun y => y * s = s * y)
    have hcongr : Nat.card {x : genOf n gs // (x : Equiv.Perm (Fin n)) * s = s * x} =
        Nat.card ↥(genOf n gs ⊓ centralizer ({s} : Set (Equiv.Perm (Fin n)))) :=
      Nat.card_congr ⟨fun x => ⟨x.1, mem_inf.mpr ⟨x.1.2, mem_centralizer_singleton_iff.2 x.2⟩⟩,
        fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, mem_centralizer_singleton_iff.1 (mem_inf.mp x.2).2⟩,
        fun _ => rfl, fun _ => rfl⟩
    have hcnt : Nat.card ↥(genOf n gs ⊓ centralizer ({s} : Set (Equiv.Perm (Fin n)))) =
        E.toList.countP fun y => commTT n y E[k]! := by
      rw [← hcongr, hcount, List.countP_map]
      apply List.countP_congr
      intro T hT
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
      have hj' := (hrep j hj).1
      rw [getElem!_pos E j hj] at hj'
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact (commTT_iff hj' hkrep).symm
    rw [hcnt]
    exact Nat.dvd_of_mod_eq_zero hc
  · right
    obtain ⟨w, hwm, hw⟩ := List.any_eq_true.1 hc
    obtain ⟨p, hpm, hp⟩ := List.any_eq_true.1 hw
    have hwok := List.all_eq_true.1 hws w hwm
    simp only [wit235OK, Bool.and_eq_true] at hwok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, ha⟩, hb⟩, hax⟩, hbx⟩, ha2⟩, hb3⟩, hab5⟩, ha1⟩, hb1⟩ := hwok
    have hxR := rep_tp hx
    have haR := rep_tp ha
    have hbR := rep_tp hb
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hpm)
    have hpR := (hrep j hj).1
    rw [getElem!_pos E j hj] at hpR
    have hPmem := (hrep j hj).2
    rw [getElem!_pos E j hj] at hPmem
    refine ⟨w, hwm, tablePerm n E[j], hPmem, ?_, (commTT_iff haR hxR).1 hax,
      (commTT_iff hbR hxR).1 hbx, (tblEq_iff_eq (Rep.powT hn haR 2) (Rep.idT hn)).1 ha2,
      (tblEq_iff_eq (Rep.powT hn hbR 3) (Rep.idT hn)).1 hb3,
      (tblEq_iff_eq (Rep.powT hn (Rep.compT haR hbR) 5) (Rep.idT hn)).1 hab5, ?_⟩
    · have hPX : tablePerm n E[j] * tp n w.x = s * tablePerm n E[j] :=
        (tblEq_iff_eq (Rep.compT hpR hxR) (Rep.compT hkrep hpR)).1 hp
      rw [hPX]; group
    · intro e'
      rw [Bool.not_eq_true'] at hb1
      exact absurd ((tblEq_idT_iff hn hbR).2 e') (by simp [hb1])

end CFSG.HardMathSupport.Foote.E27
