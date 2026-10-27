module

public import Certificates.Data.P43Twin
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallGood
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43

open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.P43Twin
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

theorem mem_iff_of_setEqB {l m : List P45} (h : setEqB l m = true) (x : P45) : x ∈ l ↔ x ∈ m := by
  unfold setEqB at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun hx => memB_iff.1 (h.1 x hx), fun hx => memB_iff.1 (h.2 x hx)⟩

theorem q8List_conj {Y : Type} [Group Y] {t a b c : Y} (hct : c * t * c⁻¹ = t) :
    (q8List t a b).map (MulAut.conj c) = q8List t (c * a * c⁻¹) (c * b * c⁻¹) := by
  have ht : MulAut.conj c t = t := by rw [MulAut.conj_apply, hct]
  simp only [q8List, List.map_cons, List.map_nil, map_mul, map_one, ht, MulAut.conj_apply]

theorem mem_map_conj_iff {Y : Type} [Group Y] {l : List Y} {c y : Y} :
    y ∈ l.map (MulAut.conj c) ↔ c⁻¹ * y * c ∈ l := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact List.mem_map.2 ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_of_mem_centQ {L Q : List P45} {x : P45} (hx : x ∈ centQ L Q) : x ∈ L :=
  List.mem_of_mem_filter hx

section Sound

variable {Y : Type} [Group Y] {ι : Y →* P45} (hι : Function.Injective ι) {L : List P45}
  (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι in
theorem mem_q8List_iff (t a b y : Y) : y ∈ q8List t a b ↔ ι y ∈ q8B (ι t) (ι a) (ι b) := by
  rw [q8B_eq (ι := ι)]
  exact (List.mem_map_of_injective hι).symm

include hι hL in
theorem pairOK_of_pairChk {t : Y} (h : pairChk (ι t) (centB L (ι t)) = true) {a b : Y}
    (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b) :
    pairOK (ι t) (ι a) (ι b) = true := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨b, htb, rfl⟩
  unfold pairChk at h
  rw [List.all_eq_true] at h
  have h1 := h (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
  rw [decide_eq_true hrel] at h2
  simpa using h2

include hι hL in
theorem mem_centralizer_iff_centQ {H : Subgroup Y} {Q : List P45} (hH : ∀ y, y ∈ H ↔ ι y ∈ Q)
    (hQ : ∀ q ∈ Q, q ∈ L) (y : Y) :
    y ∈ Subgroup.centralizer (H : Set Y) ↔ ι y ∈ centQ L Q := by
  rw [Subgroup.mem_centralizer_iff, centQ, List.mem_filter, List.all_eq_true]
  constructor
  · intro hy
    refine ⟨(hL _).2 ⟨y, rfl⟩, fun q hq => ?_⟩
    obtain ⟨k, rfl⟩ := (hL q).1 (hQ q hq)
    have hk : k ∈ H := (hH k).2 hq
    apply decide_eq_true
    rw [← map_mul, ← map_mul, hy k hk]
  · rintro ⟨-, hy⟩ k hk
    have h1 := of_decide_eq_true (hy (ι k) ((hH k).1 hk))
    exact hι (by rw [map_mul, map_mul]; exact h1)

include hι hL in
theorem card_centralizer_eq (hnd : L.Nodup) {H : Subgroup Y} {Q : List P45}
    (hH : ∀ y, y ∈ H ↔ ι y ∈ Q) (hQ : ∀ q ∈ Q, q ∈ L) :
    Nat.card ↥(Subgroup.centralizer (H : Set Y)) = (centQ L Q).length := by
  refine CFSG.Sporadic.Schreier.card_eq_length
    (fun y => y ∈ Subgroup.centralizer (H : Set Y)) ι hι (centQ L Q) (hnd.filter _) ?_
  intro m
  constructor
  · intro hm
    obtain ⟨y, rfl⟩ := (hL m).1 (List.mem_of_mem_filter hm)
    exact ⟨y, (mem_centralizer_iff_centQ hι hL hH hQ y).2 hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mem_centralizer_iff_centQ hι hL hH hQ y).1 hy

end Sound

theorem check_parts (h : check () = true) :
    coverB [tA, tB] (elemsT QP45) = true ∧ (∀ τ ∈ [tA, tB], localChk (elemsT QP45) τ = true) ∧
      coverB [tA, tB, t36, t540] (elemsT QA45) = true ∧
      (∀ τ ∈ [tA, tB, t36, t540], localChk (elemsT QA45) τ = true) ∧
      sigmaChk (elemsT QP45) = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  exact h

theorem sigma_parts {L : List P45} (h : sigmaChk L = true) :
    (∀ q ∈ Q1 ++ Q2, q ∈ L) ∧ (centQ L Q1).length = 24 ∧ (centQ L Q2).length = 24 ∧
      x1 ∈ centQ L Q1 ∧ a2 ∈ centQ L Q1 ∧ x2 ∈ centQ L Q2 ∧ a1 ∈ centQ L Q2 ∧
      x1 ^ 3 = 1 ∧ x2 ^ 3 = 1 ∧ orderOf (x1 * a2 * x1⁻¹ * a2⁻¹) = 4 ∧
      orderOf (x2 * a1 * x2⁻¹ * a1⁻¹) = 4 ∧
      ∀ u ∈ centQ L Q1, ∀ v ∈ centQ L Q2, u * v = v * u := by
  simp only [sigmaChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨hQ, h1, h2, hx1, ha2, hx2, ha1, hx13, hx23, ho1, ho2, hc⟩ := h
  refine ⟨fun q hq => memB_iff.1 (hQ q hq), h1, h2, memB_iff.1 hx1, memB_iff.1 ha2,
    memB_iff.1 hx2, memB_iff.1 ha1, hx13, hx23, ?_, ?_, hc⟩
  · rw [orderOf_eq_of_ordB (by rw [ho1]; norm_num), ho1]
  · rw [orderOf_eq_of_ordB (by rw [ho2]; norm_num), ho2]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43
