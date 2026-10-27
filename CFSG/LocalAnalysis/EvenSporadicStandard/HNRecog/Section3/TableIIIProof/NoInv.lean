module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.FixedCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

variable {G : Type} [Group G]

private theorem t3_orderOf_eq_of_isConj {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g) x).symm

theorem tableIII_barOf_eq_one_4A (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (hSGz : StructGzFacts a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a')
    (hc : c ∈ tab3Set a z a' 2) (t : ↥(Gx z)) (ht : (t : G) ∈ Gxyz a' z c)
    (ht2 : barOf z t ^ 2 = 1) : barOf z t = 1 := by
  classical
  by_contra hne
  have hc' : c ∈ tab3Base a z a' ∧ (a' * c) ^ 2 = z := by
    simpa [tab3Set] using hc
  obtain ⟨hcB, hcsq⟩ := hc'
  have hcQ : c ∈ Qz z := hcB.1
  have hcA : IsConj a c := hcB.2.1
  obtain ⟨ha'2, ha'1, ha'z, ha'zcomm, hz2, hz1, -, -⟩ := tableIII_basic hI h ha'Q ha'
  have hc2 : c ^ 2 = 1 := by
    have hordc : orderOf c = 2 := (t3_orderOf_eq_of_isConj hcA).symm.trans h.orderOf_a
    rw [← hordc]
    exact pow_orderOf_eq_one c
  have htGa' : (t : G) ∈ Gx a' := (mem_Gxyz.mp ht).1
  have htGz : (t : G) ∈ Gx z := t.2
  have htGc : (t : G) ∈ Gx c := (mem_Gxyz.mp ht).2.2
  let W : Subgroup G := Qz z ⊓ Gx a'
  let K : Set G := {w | w ∈ W ∧ ⁅w, (t : G)⁆ ∈ Subgroup.zpowers z}
  have hWcard : Nat.card W = 2 ^ 8 := by
    show Nat.card ↥(Qz z ⊓ Gx a') = 2 ^ 8
    exact tableIII_card_Qz_inf_Gx h ha'Q ha'1 ha'z
  have hzW : z ∈ W := ⟨self_mem_Qz hz2, mem_Gx.mpr ha'zcomm⟩
  have hzc : ∀ w ∈ W, w * z = z * w := by
    intro w hw
    exact (mem_Gx.mp (tableIII_Qz_le z hw.1)).symm
  have hsq : ∀ w ∈ W, w ^ 2 ∈ Subgroup.zpowers z :=
    fun w hw => tableIII_sq_mem_zpowers h hw.1
  have hcomm : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ Subgroup.zpowers z :=
    fun w hw w' hw' => commutatorElement_mem_zpowers_of_mem_Qz h hw.1 hw'.1
  have htW : ∀ w ∈ W, (t : G) * w * (t : G)⁻¹ ∈ W := by
    intro w hw
    exact ⟨tableIII_conj_mem_Qz htGz hw.1,
      mul_mem (mul_mem htGa' hw.2) ((Gx a').inv_mem htGa')⟩
  have htW' : ∀ w ∈ W, (t : G)⁻¹ * w * (t : G) ∈ W := by
    intro w hw
    have h1 : (t : G)⁻¹ * w * (t : G) ∈ Qz z := by
      simpa only [inv_inv] using
        tableIII_conj_mem_Qz (g := (t : G)⁻¹) ((Gx z).inv_mem htGz) hw.1
    exact ⟨h1, mul_mem (mul_mem ((Gx a').inv_mem htGa') hw.2) htGa'⟩
  have htz : (t : G) * z = z * (t : G) := (mem_Gx.mp htGz).symm
  have ht2W : (t : G) ^ 2 ∈ W := by
    have hbar : barOf z (t ^ 2) = 1 := by
      simpa only [QuotientGroup.mk_pow] using ht2
    have hQ : (t : G) ^ 2 ∈ Qz z := by
      have hmem := (barOf_eq_one_iff (z := z) (t ^ 2)).mp hbar
      simpa only [Subgroup.coe_pow] using hmem
    exact ⟨hQ, pow_mem htGa' 2⟩
  have hfixed := tableIII_two_mul_card_le_sq (W := W) (z := z) (t := (t : G))
    hz1 hz2 hzW hzc hsq hcomm htW htW' htz ht2W
  rw [hWcard] at hfixed
  have hcz : c * z * c⁻¹ = z := by
    have hczc : c * z = z * c := (mem_Gx.mp (tableIII_Qz_le z hcQ)).symm
    rw [hczc, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_zp : ∀ x ∈ Subgroup.zpowers z, c * x * c⁻¹ ∈ Subgroup.zpowers z := by
    intro x hx
    rcases (tableIII_mem_zpowers_iff h).mp hx with hx1 | hxz
    · rw [hx1]
      simpa using Subgroup.one_mem (Subgroup.zpowers z)
    · rw [hxz, hcz]
      exact Subgroup.mem_zpowers z
  have hmem_cw : ∀ k : ↥K, ⁅c * k.1, (t : G)⁆ ∈ Subgroup.zpowers z := by
    intro k
    have hct : ⁅c, (t : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_Gx.mp htGc)
    have hcw : ⁅c * k.1, (t : G)⁆ = c * ⁅k.1, (t : G)⁆ * c⁻¹ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hct, mul_one]
    rw [hcw]
    exact hconj_zp _ k.2.2
  let F : ↥K ⊕ ↥K → ↥(centQtilde z (t : G)) := fun s =>
    match s with
    | Sum.inl k => ⟨k.1, by exact ⟨k.2.1.1, k.2.2⟩⟩
    | Sum.inr k => ⟨c * k.1, by exact ⟨mul_mem hcQ k.2.1.1, hmem_cw k⟩⟩
  have hFinj : Function.Injective F := by
    intro s s' hss'
    rcases s with k | k <;> rcases s' with k' | k' <;> dsimp only [F] at hss'
    · have h : k.1 = k'.1 :=
        congrArg (fun x : ↥(centQtilde z (t : G)) => (x : G)) hss'
      exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h : k.1 = c * k'.1 :=
        congrArg (fun x : ↥(centQtilde z (t : G)) => (x : G)) hss'
      have hcGa' : c ∈ Gx a' := by
        have hmem : c = k.1 * k'.1⁻¹ := by
          rw [h]
          group
        rw [hmem]
        exact mul_mem k.2.1.2 ((Gx a').inv_mem k'.2.1.2)
      have hca' : a' * c = c * a' := mem_Gx.mp hcGa'
      have hone : (a' * c) ^ 2 = 1 := by
        calc (a' * c) ^ 2 = (a' * c) * (a' * c) := pow_two _
          _ = a' * (c * a') * c := by group
          _ = a' * (a' * c) * c := by rw [← hca']
          _ = (a' * a') * (c * c) := by group
          _ = 1 := by rw [← pow_two, ha'2, ← pow_two, hc2, mul_one]
      exact hz1 (hcsq.symm.trans hone)
    · exfalso
      have h : c * k.1 = k'.1 :=
        congrArg (fun x : ↥(centQtilde z (t : G)) => (x : G)) hss'
      have hcGa' : c ∈ Gx a' := by
        have hmem : c = k'.1 * k.1⁻¹ := by
          rw [← h]
          group
        rw [hmem]
        exact mul_mem k'.2.1.2 ((Gx a').inv_mem k.2.1.2)
      have hca' : a' * c = c * a' := mem_Gx.mp hcGa'
      have hone : (a' * c) ^ 2 = 1 := by
        calc (a' * c) ^ 2 = (a' * c) * (a' * c) := pow_two _
          _ = a' * (c * a') * c := by group
          _ = a' * (a' * c) * c := by rw [← hca']
          _ = (a' * a') * (c * c) := by group
          _ = 1 := by rw [← pow_two, ha'2, ← pow_two, hc2, mul_one]
      exact hz1 (hcsq.symm.trans hone)
    · have h : c * k.1 = c * k'.1 :=
        congrArg (fun x : ↥(centQtilde z (t : G)) => (x : G)) hss'
      have h' : k.1 = k'.1 := mul_left_cancel h
      exact congrArg Sum.inr (Subtype.ext h')
  have hinj : Nat.card (↥K ⊕ ↥K) ≤ Nat.card ↥(centQtilde z (t : G)) :=
    Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_sum] at hinj
  have hcent : Nat.card ↥(centQtilde z (t : G)) = 2 ^ 5 := hSGz.centQ_inv t ht2 hne
  rw [hcent] at hinj
  have hK16 : Nat.card ↥K ≤ 16 := by omega
  have hpow : Nat.card ↥K ^ 2 ≤ 16 ^ 2 := Nat.pow_le_pow_left hK16 2
  rw [show (16 : ℕ) ^ 2 = 256 by norm_num] at hpow
  have hfixed' : 2 * 2 ^ 8 ≤ Nat.card ↥K ^ 2 := hfixed
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
