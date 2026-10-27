module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Fusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BAab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5b_comm_of_mem_centerIn {K : Subgroup G} {a : G} (h : a ∈ centerIn K) :
    ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm

theorem sec5b_mem_tclass [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5) {t : G} {L S : Subgroup G}
    {z : G} (hC : Sec5Ctx G t L S z) {A : Subgroup G} (h : Case59Two t z A) {x : G}
    (hxA : x ∈ A) (hx1 : x ≠ 1) (hx : x ∈ conjClassIn L (t * z)) :
    x ∈ conjClassIn (normalizer (A : Set G)) t := by
  obtain ⟨c1, c2, -, -⟩ := h
  have hnot := sec5_tz_not_conj_z h36 h37 h52b h53 tab hC
  have hxz : x ∉ conjClassIn (normalizer (A : Set G)) z := by
    rintro ⟨m, -, hxm⟩
    obtain ⟨g, -, hxg⟩ := hx
    apply hnot (m⁻¹ * g)
    calc (m⁻¹ * g)⁻¹ * z * (m⁻¹ * g) = g⁻¹ * (m * z * m⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [← hxm]
      _ = t * z := by rw [hxg]; group
  have hmem : x ∈ conjClassIn ⊤ t ∩ (A : Set G) := by
    rw [c1]
    exact ⟨⟨hxA, hx1⟩, hxz⟩
  rwa [c2] at hmem

theorem sec5b_exists_p [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5) (fact : Asc82Fact512H)
    {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G}
    (hK : Sec5KCtx G t L S z r B A K₁ K₂) (h2 : Case59Two t z A) (hzA : z ∈ A) :
    ∃ p ∈ A, p ∈ K₁ ⊔ K₂ ∧ p ≠ t ∧ p ∈ conjClassIn (normalizer (A : Set G)) t ∧
      p * z ∈ conjClassIn (normalizer (A : Set G)) t ∧
      t * z ∈ conjClassIn (normalizer (A : Set G)) t := by
  have hR : Sec5RCtx G t L S z r B A := hK.toSec5RCtx
  have hC : Sec5Ctx G t L S z := hR.toSec5Ctx
  have hΩ : IsOm6Z2 L := hC.toSec5Setting.isOm6Z2
  obtain ⟨-, hsq⟩ := sec5b_A_elemAb hR
  obtain ⟨-, htA⟩ := sec5b_card_t_mem hR
  have hzr : z ∈ zpowers r ⊔ B := hR.A_eq ▸ hzA
  obtain ⟨p, hpr, hpTwo, hp1, hpz⟩ := fact.meet G L hΩ t hC.involution hK.centre r
    (sec5b_orderOf_r hR) hR.type_r B hR.B_le hR.B_E32 hR.B_split.1 hR.B_split.2.1
    hR.B_split.2.2 z hR.pocket hzr
  have hpA : p ∈ A := hR.A_eq ▸ hpr
  have hz2 : orderOf z = 2 := hR.pocket.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hsq z hzA)
  have hpK : p ∈ K₁ ⊔ K₂ := hK.prod ▸ hpTwo
  have hord : ∀ u ∈ A, u ≠ 1 → orderOf u = 2 := fun u hu hu1 =>
    orderOf_eq_prime (by rw [sq]; exact hsq u hu) hu1
  have hpz' : p * z ≠ 1 := fun h => hpz (by rw [eq_inv_of_mul_eq_one_left h, hzz])
  have hpzA : p * z ∈ A := A.mul_mem hpA hzA
  have hpzTwo : p * z ∈ twoRes (L ⊓ centralizer ({z} : Set G)) := by
    rw [← hK.prod]
    exact (K₁ ⊔ K₂).mul_mem hpK (le_sup_left (a := K₁) (b := K₂) hK.pocket₁.1)
  have hpzne : p * z ≠ z := fun h => hp1 (by simpa using h)
  have hpTz : p ∈ conjClassIn L (t * z) :=
    fact.inv_class G L hΩ t hC.involution hK.centre z hR.pocket p hpTwo (hord p hpA hp1) hpz
  have hpzTz : p * z ∈ conjClassIn L (t * z) :=
    fact.inv_class G L hΩ t hC.involution hK.centre z hR.pocket (p * z) hpzTwo
      (hord _ hpzA hpz') hpzne
  have htzTz : t * z ∈ conjClassIn L (t * z) := ⟨1, L.one_mem, by simp⟩
  have htz1 : t * z ≠ 1 := by
    intro h
    refine sec5_t_not_conj_z h37 hC 1 ?_
    rw [eq_inv_of_mul_eq_one_left h, hzz]
    simp
  have hpt : p ≠ t := by
    intro hpt
    rw [hpt] at hpTz
    obtain ⟨g, hgL, hg⟩ := hpTz
    have htc : t ∈ centerIn L := hK.centre ▸ Subgroup.mem_zpowers t
    have hgt : t * g = g * t := sec5b_comm_of_mem_centerIn htc g hgL
    have h1 : t = t * (g * z * g⁻¹) :=
      calc t = g * (t * z) * g⁻¹ := hg
        _ = (g * t) * z * g⁻¹ := by group
        _ = (t * g) * z * g⁻¹ := by rw [← hgt]
        _ = t * (g * z * g⁻¹) := by group
    have hX : g * z * g⁻¹ = 1 := mul_left_cancel (a := t) (h1.symm.trans (mul_one t).symm)
    exact hz1 (calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hX]; group)
  refine ⟨p, hpA, hpK, hpt, ?_, ?_, ?_⟩
  · exact sec5b_mem_tclass h36 h37 h52b h53 tab hC h2 hpA hp1 hpTz
  · exact sec5b_mem_tclass h36 h37 h52b h53 tab hC h2 hpzA hpz' hpzTz
  · exact sec5b_mem_tclass h36 h37 h52b h53 tab hC h2 (A.mul_mem htA hzA) htz1 htzTz

theorem asc82Lemma512H_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (h510 : Asc82Lemma510) (fact : Asc82Fact512H) :
    Asc82Lemma512H := by
  intro G _ _ t L S z r B A K₁ K₂ hK
  have hR : Sec5RCtx G t L S z r B A := hK.toSec5RCtx
  have hC : Sec5Ctx G t L S z := hR.toSec5Ctx
  have h2 : Case59Two t z A := h510 G t L S z r B A hR
  obtain ⟨hcard, htA⟩ := sec5b_card_t_mem hR
  have hzA : z ∈ A := sec5b_z_mem_A hcard h2
  obtain ⟨p, hpA, hpK, hpt, hp, hpz, htz⟩ :=
    sec5b_exists_p h36 h37 h52b h53 tab fact hK h2 hzA
  obtain ⟨c1, c2, c3, Alt, hAlt, φ, hφ⟩ := h2
  have hd := sec5b_heartData hφ
  have hAlt' : alternatingGroup (Fin 8) ≤ Alt := by
    rcases hAlt with rfl | rfl
    · exact le_rfl
    · exact le_top
  have ht1 : t ≠ 1 := fun h => by
    have := hC.involution
    rw [h, orderOf_one] at this
    omega
  have hz1 : z ≠ 1 := fun h => by
    have := hR.pocket.1
    rw [h, orderOf_one] at this
    omega
  have hcard28 : Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 28 := by
    rw [← c2]; exact c3
  have hzt : z ∉ conjClassIn (normalizer (A : Set G)) t := by
    intro hz
    rw [← c2, c1] at hz
    exact hz.2 ⟨1, (normalizer (A : Set G)).one_mem, by simp⟩
  obtain ⟨h', hh'M, hh'z, hh't, hh'sq⟩ :=
    sec5b_exists_h hAlt' hd htA hzA hpA ht1 hz1 hcard28 hzt hp hpz htz hpt
  refine ⟨h'⁻¹, { toSec5KCtx := hK, h_mem := inv_mem hh'M, h_t := ?_, h_sq := ?_, h_z := ?_ }⟩
  · rw [inv_inv, hh't]
    exact hpK
  · have hcomm : Commute (h' * h') t := mul_inv_eq_iff_eq_mul.mp (hh'sq t htA)
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_rev]
    exact hcomm.inv_left
  · have hcomm : Commute h' z := mul_inv_eq_iff_eq_mul.mp hh'z
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.inv_left

end CFSG.OddStandard.SmallF3.Omega
