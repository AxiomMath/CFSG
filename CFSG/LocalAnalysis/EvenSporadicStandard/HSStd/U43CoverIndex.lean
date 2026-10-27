module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverGroup
public import Certificates.Certificate27272

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.M24Std.CU43
open scoped commutatorElement

section Tables

theorem tp_commTab {a b : Table} (ha : permOK 820 a = true)
    (hai : CFSG.Sporadic.Th.Native.invOK 820 a (invT 820 a) = true) (hb : permOK 820 b = true)
    (hbi : CFSG.Sporadic.Th.Native.invOK 820 b (invT 820 b) = true)
    (hc : permOK 820 (commTab a b) = true) : tp 820 (commTab a b) = ⁅tp 820 a, tp 820 b⁆ := by
  have hra : Rep 820 a (tp 820 a) := rep_tp ha
  have hrb : Rep 820 b (tp 820 b) := rep_tp hb
  have h : Rep 820 (commTab a b) (tp 820 a * tp 820 b * ((tp 820 a)⁻¹ * (tp 820 b)⁻¹)) :=
    Rep.compT (Rep.compT hra hrb) (Rep.compT (rep_invT hra hai) (rep_invT hrb hbi))
  rw [CFSG.Sporadic.Schreier.rep_unique (rep_tp hc) h, commutatorElement_def]
  group

theorem tp_cubeTab {p : Table} (hp : permOK 820 p = true) (hc : permOK 820 (cubeTab p) = true) :
    tp 820 (cubeTab p) = tp 820 p ^ 3 := by
  have hrp : Rep 820 p (tp 820 p) := rep_tp hp
  have h : Rep 820 (cubeTab p) (tp 820 p * (tp 820 p * tp 820 p)) :=
    Rep.compT hrp (Rep.compT hrp hrp)
  rw [CFSG.Sporadic.Schreier.rep_unique (rep_tp hc) h, pow_three]

theorem memCheck_spec {y a : Table} (hy : permOK 820 y = true)
    (h : memCheck y a = true) :
    tp 820 a ∈ P ⊓ centralizer ({tp 820 y} : Set (Equiv.Perm (Fin 820))) ∧
      permOK 820 a = true ∧ CFSG.Sporadic.Th.Native.invOK 820 a (invT 820 a) = true := by
  simp only [memCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hai⟩, hin⟩, hcomm⟩ := h
  refine ⟨mem_inf.2 ⟨(inP_iff (co2Rep_natArr_iff.2 (rep_tp ha))).1 hin, ?_⟩, ha, hai⟩
  rw [mem_centralizer_singleton_iff]
  exact (commTT_iff (rep_tp ha) (rep_tp hy)).1 hcomm

end Tables

theorem kRepCheck_spec {y : Table} {cs : List (Table × Table)}
    {ps : List Table} (h : kRepCheck y cs ps = true) :
    324 ∣ Nat.card ↥(cubeCore (P ⊓ centralizer ({tp 820 y} : Set (Equiv.Perm (Fin 820))))
      (tp 820 y)) := by
  simp only [kRepCheck, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hy, hcs⟩, hps⟩, hperm⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  obtain ⟨-, -, hcard⟩ := enum_spec (n := 820) (by norm_num) (A := kTabs y cs ps)
    (fun x hx => (hperm x hx).1) (fun x hx => (hperm x hx).2) (cap := kCap) htree hclosed hdist
  rw [hsize] at hcard
  have hle : closure (tp 820 '' {x | x ∈ kTabs y cs ps}) ≤
      cubeCore (P ⊓ centralizer ({tp 820 y} : Set (Equiv.Perm (Fin 820)))) (tp 820 y) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ kTabs y cs ps := hx
    have hxc := (hperm x hx').1
    simp only [kTabs, List.mem_toArray, List.mem_cons, List.mem_append, List.mem_map] at hx'
    rcases hx' with (hxy | ⟨c, hc, hcx⟩) | ⟨p, hp, hpx⟩
    · rw [hxy]
      exact self_mem_cubeCore
    · obtain ⟨h1, h1a, h1i⟩ := memCheck_spec hy (hcs c hc).1
      obtain ⟨h2, h2a, h2i⟩ := memCheck_spec hy (hcs c hc).2
      rw [← hcx] at hxc ⊢
      show tp 820 (commTab c.1 c.2) ∈ _
      rw [tp_commTab h1a h1i h2a h2i hxc]
      exact commutator_mem_cubeCore h1 h2
    · obtain ⟨h1, h1a, -⟩ := memCheck_spec hy (hps p hp)
      rw [← hpx] at hxc ⊢
      show tp 820 (cubeTab p) ∈ _
      rw [tp_cubeTab h1a hxc]
      exact cube_mem_cubeCore h1
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [hcard] at hdvd

theorem kCheck_facts :
    kRepCheck yBTab kBComm kBCube = true ∧ kRepCheck yCTab kCComm kCCube = true := by
  have h := Certificates.certificate27272
  simpa only [kCheck, Bool.and_eq_true] using h

theorem card_cubeCore_conj {y g : Equiv.Perm (Fin 820)} (hg : g ∈ P)
    (h : 324 ≤ Nat.card ↥(cubeCore (P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) y)) :
    324 ≤ Nat.card ↥(cubeCore (P ⊓ centralizer ({g * y * g⁻¹} : Set (Equiv.Perm (Fin 820))))
      (g * y * g⁻¹)) := by
  have e : cubeCore (P ⊓ centralizer ({g * y * g⁻¹} : Set (Equiv.Perm (Fin 820))))
      (g * y * g⁻¹) =
      (cubeCore (P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) y).map
        (MulAut.conj g).toMonoidHom := by
    rw [map_cubeCore, ← inf_centralizer_conj P hg y]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h

theorem card_cubeCore_ge
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P) (ho : orderOf β = 3)
    (hc : Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 972) :
    324 ≤ Nat.card ↥(cubeCore (P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) β) := by
  obtain ⟨g, hg, h | h⟩ := exists_conj_of_card_972 hβ ho hc
  · rw [h]
    refine card_cubeCore_conj hg ?_
    exact Nat.le_of_dvd Nat.card_pos (kRepCheck_spec kCheck_facts.1)
  · rw [h]
    refine card_cubeCore_conj hg ?_
    exact Nat.le_of_dvd Nat.card_pos (kRepCheck_spec kCheck_facts.2)

end CFSG.EvenSporadicStandard.HSStd.U43
