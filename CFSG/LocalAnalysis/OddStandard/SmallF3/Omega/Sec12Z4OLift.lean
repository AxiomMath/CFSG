module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem z4o_sq_mul {V B : Subgroup G} (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hBV : B ≤ V) (hB2 : ∀ b ∈ B, b * b = 1) {v b : G} (hv : v ∈ V) (hb : b ∈ B) :
    v * b * (v * b) = v * v := by
  have hc : b * v = v * b := hVc _ (hBV hb) _ hv
  calc v * b * (v * b) = v * (b * v) * b := by group
    _ = v * v * (b * b) := by rw [hc]; group
    _ = v * v := by rw [hB2 b hb, mul_one]

private theorem z4o_step [Finite G] {t : G} {L S V : Subgroup G} (F : Sec12Frame t L S)
    (hV : IsZ4Pow4 V) (hBV : secB S L ≤ V) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) {q : G} (hqL : q ∈ L) (hqV : q ∈ normalizer (V : Set G))
    {σ : Equiv.Perm (Fin 5)} (hq : SecActs φ q σ) {c : Fin 5} (hσ2 : σ * σ = 1)
    (hσc : σ c = c) {v : G} (hv : v ∈ V) (hvv : v * v = φ (wvec c)) :
    ∃ x, IsEvenVec x ∧ permVec σ x = x ∧ q * v * q⁻¹ = v * φ x := by
  have hVc := sec124_z4_comm hV
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => hφ.mul_self_eq_one hb
  have hw : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hqV v).mp hv
  have hww : q * v * q⁻¹ * (q * v * q⁻¹) = φ (wvec c) := by
    calc q * v * q⁻¹ * (q * v * q⁻¹) = q * (v * v) * q⁻¹ := by group
      _ = φ (wvec c) := by rw [hvv, hq _ (wvec_even c), permVec_wvec, hσc]
  have hu : v⁻¹ * (q * v * q⁻¹) ∈ secB S L := by
    refine sec124_z4_mem_of_sq hV hBV F.bdata.2.1 hB2 _ (V.mul_mem (V.inv_mem hv) hw) ?_
    have hc : q * v * q⁻¹ * v⁻¹ = v⁻¹ * (q * v * q⁻¹) := hVc _ hw _ (V.inv_mem hv)
    calc v⁻¹ * (q * v * q⁻¹) * (v⁻¹ * (q * v * q⁻¹))
        = v⁻¹ * (q * v * q⁻¹ * v⁻¹) * (q * v * q⁻¹) := by group
      _ = (v * v)⁻¹ * (q * v * q⁻¹ * (q * v * q⁻¹)) := by rw [hc]; group
      _ = 1 := by rw [hww, hvv, inv_mul_cancel]
  obtain ⟨x, hx, hxu⟩ := hφ.onto _ hu
  have hqx : q * v * q⁻¹ = v * φ x := by rw [hxu]; group
  refine ⟨x, hx, ?_, hqx⟩
  have hqq1 : SecActs φ (q * q) 1 := by rw [← hσ2]; exact hq.mul hq
  have hqq : q * q * v * (q * q)⁻¹ = v := by
    rw [z4o_act_eq F hBV hVc hφ (L.mul_mem hqL hqL) L.one_mem hqq1 (z4o_secActs_one φ) hv]
    group
  have h1 : q * q * v * (q * q)⁻¹ = q * v * q⁻¹ * (q * φ x * q⁻¹) := by
    calc q * q * v * (q * q)⁻¹ = q * (q * v * q⁻¹) * q⁻¹ := by group
      _ = q * (v * φ x) * q⁻¹ := by rw [hqx]
      _ = q * v * q⁻¹ * (q * φ x * q⁻¹) := by group
  rw [hqq, hqx, hq x hx, mul_assoc] at h1
  have h2 : φ (x + permVec σ x) = φ 0 := by
    rw [hφ.mul _ _ hx (isEvenVec_permVec σ hx), left_eq_mul.mp h1, hφ.map_zero]
  exact (sec123_eq_of_add_eq_zero (hφ.inj _ _ (sec123_isEvenVec_add hx
    (isEvenVec_permVec σ hx)) sec123_isEvenVec_zero h2)).symm

private theorem z4o_step_fix {φ : (Fin 5 → ZMod 2) → G} {B : Subgroup G}
    (hφ : SecNatCoord φ B) {q v : G} {σ : Equiv.Perm (Fin 5)} (hq : SecActs φ q σ)
    {x y : Fin 5 → ZMod 2} (hy : IsEvenVec y) (hqv : q * v * q⁻¹ = v * φ x)
    (hxy : x = y + permVec σ y) : q * (v * φ y) * q⁻¹ = v * φ y := by
  subst hxy
  have hσy := isEvenVec_permVec σ hy
  calc q * (v * φ y) * q⁻¹ = q * v * q⁻¹ * (q * φ y * q⁻¹) := by group
    _ = v * (φ y * (φ (permVec σ y) * φ (permVec σ y))) := by
        rw [hqv, hq y hy, hφ.mul _ _ hy hσy]; group
    _ = v * φ y := by rw [hφ.mul_self_eq_one (hφ.mem _ hσy), mul_one]

theorem z4o_exists_fix [Finite G] {t : G} {L S E : Subgroup G} (F : Sec12Frame t L S)
    (hE : IsSylow2Of E (secCMB t S L)) (hZ : IsZ4Pow4 (secV t S L E))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    (c : Fin 5) :
    ∃ v ∈ secV t S L E, v * v = φ (wvec c) ∧ Z4OFix (secM t S L ⊓ L) φ c v := by
  have hφ : SecNatCoord φ (secB S L) :=
    ⟨fun v hv => (hperm.2.2.1 _).mpr ⟨v, hv, rfl⟩, hperm.1, hperm.2.1,
      fun x hx => (hperm.2.2.1 x).mp hx⟩
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hVc := sec124_z4_comm hZ
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => hφ.mul_self_eq_one hb
  have hYV := sec121_Y_le_normalizer_V F hE
  obtain ⟨v0, hv0, hv00⟩ := sec124_z4_root hZ hBV hB2 (φ (wvec c)) (hφ.mem _ (wvec_even c))
  obtain ⟨q1, hq1Y, h1⟩ := hperm.2.2.2.2 (z4oS1 c) (z4oS1_mem c)
  obtain ⟨q2, hq2Y, h2⟩ := hperm.2.2.2.2 (z4oS2 c) (z4oS2_mem c)
  have h1 : SecActs φ q1 (z4oS1 c) := h1
  have h2 : SecActs φ q2 (z4oS2 c) := h2
  obtain ⟨x1, hx1, hx1f, hq1v0⟩ := z4o_step F hZ hBV hφ hq1Y.2 (hYV hq1Y) h1
    (z4oS1_mul_self c) (z4oS1_apply c) hv0 hv00
  obtain ⟨y1, hy1, hxy1⟩ := z4o_h1_one c hx1 hx1f
  have hv1 : v0 * φ y1 ∈ secV t S L E := mul_mem hv0 (hBV (hφ.mem _ hy1))
  have hv11 : v0 * φ y1 * (v0 * φ y1) = φ (wvec c) :=
    (z4o_sq_mul hVc hBV hB2 hv0 (hφ.mem _ hy1)).trans hv00
  have hq1v1 : q1 * (v0 * φ y1) * q1⁻¹ = v0 * φ y1 := z4o_step_fix hφ h1 hy1 hq1v0 hxy1
  obtain ⟨x2, hx2, hx2f, hq2v1⟩ := z4o_step F hZ hBV hφ hq2Y.2 (hYV hq2Y) h2
    (z4oS2_mul_self c) (z4oS2_apply c) hv1 hv11
  have hx2f1 : permVec (z4oS1 c) x2 = x2 := by
    have h21 : SecActs φ (q2 * q1) (z4oS1 c * z4oS2 c) := by
      rw [z4oS_comm c]; exact h2.mul h1
    have he := z4o_act_eq F hBV hVc hφ (L.mul_mem hq1Y.2 hq2Y.2) (L.mul_mem hq2Y.2 hq1Y.2)
      (h1.mul h2) h21 hv1
    have hL : q1 * q2 * (v0 * φ y1) * (q1 * q2)⁻¹ =
        v0 * φ y1 * φ (permVec (z4oS1 c) x2) := by
      calc q1 * q2 * (v0 * φ y1) * (q1 * q2)⁻¹
          = q1 * (q2 * (v0 * φ y1) * q2⁻¹) * q1⁻¹ := by group
        _ = q1 * (v0 * φ y1 * φ x2) * q1⁻¹ := by rw [hq2v1]
        _ = q1 * (v0 * φ y1) * q1⁻¹ * (q1 * φ x2 * q1⁻¹) := by group
        _ = v0 * φ y1 * φ (permVec (z4oS1 c) x2) := by rw [hq1v1, h1 x2 hx2]
    have hR : q2 * q1 * (v0 * φ y1) * (q2 * q1)⁻¹ = v0 * φ y1 * φ x2 := by
      calc q2 * q1 * (v0 * φ y1) * (q2 * q1)⁻¹
          = q2 * (q1 * (v0 * φ y1) * q1⁻¹) * q2⁻¹ := by group
        _ = v0 * φ y1 * φ x2 := by rw [hq1v1, hq2v1]
    rw [hL, hR] at he
    exact hφ.inj _ _ (isEvenVec_permVec _ hx2) hx2 (mul_left_cancel he)
  obtain ⟨y2, hy2, hy2f, hxy2⟩ := z4o_h1_two c hx2 hx2f1 hx2f
  have hv2 : v0 * φ y1 * φ y2 ∈ secV t S L E := mul_mem hv1 (hBV (hφ.mem _ hy2))
  refine ⟨v0 * φ y1 * φ y2, hv2,
    (z4o_sq_mul hVc hBV hB2 hv1 (hφ.mem _ hy2)).trans hv11, ?_⟩
  refine z4o_fix_of_gen F hBV hVc hφ hq1Y.2 hq2Y.2 h1 h2 hv2 ?_
    (z4o_step_fix hφ h2 hy2 hq2v1 hxy2)
  calc q1 * (v0 * φ y1 * φ y2) * q1⁻¹ = q1 * (v0 * φ y1) * q1⁻¹ * (q1 * φ y2 * q1⁻¹) := by
        group
    _ = v0 * φ y1 * φ y2 := by rw [hq1v1, h1 y2 hy2, hy2f]

theorem z4o_fix_unique [Finite G] {t : G} {L S E : Subgroup G} (F : Sec12Frame t L S)
    (hE : IsSylow2Of E (secCMB t S L)) (hZ : IsZ4Pow4 (secV t S L E))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    {c : Fin 5} {v w : G} (hv : v ∈ secV t S L E) (hw : w ∈ secV t S L E)
    (hvv : v * v = φ (wvec c)) (hww : w * w = φ (wvec c))
    (hfv : Z4OFix (secM t S L ⊓ L) φ c v) (hfw : Z4OFix (secM t S L ⊓ L) φ c w) :
    w = v ∨ w = v⁻¹ := by
  have hφ : SecNatCoord φ (secB S L) :=
    ⟨fun v hv => (hperm.2.2.1 _).mpr ⟨v, hv, rfl⟩, hperm.1, hperm.2.1,
      fun x hx => (hperm.2.2.1 x).mp hx⟩
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hVc := sec124_z4_comm hZ
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => hφ.mul_self_eq_one hb
  have hu : v⁻¹ * w ∈ secB S L := by
    refine sec124_z4_mem_of_sq hZ hBV F.bdata.2.1 hB2 _ (mul_mem (inv_mem hv) hw) ?_
    have hc : w * v⁻¹ = v⁻¹ * w := hVc _ hw _ (inv_mem hv)
    calc v⁻¹ * w * (v⁻¹ * w) = v⁻¹ * (w * v⁻¹) * w := by group
      _ = (v * v)⁻¹ * (w * w) := by rw [hc]; group
      _ = 1 := by rw [hvv, hww, inv_mul_cancel]
  obtain ⟨x, hx, hxu⟩ := hφ.onto _ hu
  have hfix : ∀ σ ∈ alternatingGroup (Fin 5), σ c = c → σ * σ = 1 → permVec σ x = x := by
    intro σ hσA hσc hσ2
    obtain ⟨q, hqY, hq⟩ := hperm.2.2.2.2 σ hσA
    have hs := Equiv.Perm.mem_alternatingGroup.mp hσA
    have h1 := hfv q hqY σ hq hσc hσ2 hs
    have h2 := hfw q hqY σ hq hσc hσ2 hs
    have h3 : q * φ x * q⁻¹ = φ x := by
      rw [hxu]
      calc q * (v⁻¹ * w) * q⁻¹ = (q * v * q⁻¹)⁻¹ * (q * w * q⁻¹) := by group
        _ = v⁻¹ * w := by rw [h1, h2]
    exact hφ.inj _ _ (isEvenVec_permVec σ hx) hx ((hq x hx).symm.trans h3)
  rcases z4o_fix_klein c hx (hfix _ (z4oS1_mem c) (z4oS1_apply c) (z4oS1_mul_self c))
      (hfix _ (z4oS2_mem c) (z4oS2_apply c) (z4oS2_mul_self c)) with rfl | rfl
  · left
    rw [hφ.map_zero] at hxu
    calc w = v * (v⁻¹ * w) := by group
      _ = v := by rw [← hxu, mul_one]
  · right
    rw [← hvv] at hxu
    apply eq_inv_of_mul_eq_one_left
    calc w * v = v * (v⁻¹ * w) * v := by group
      _ = v * (v * v) * v := by rw [← hxu]
      _ = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := sec124_z4_pow_four hZ v hv

end CFSG.OddStandard.SmallF3.Omega
