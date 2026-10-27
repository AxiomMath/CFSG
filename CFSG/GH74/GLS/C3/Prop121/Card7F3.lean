module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Prop121.Card7F2
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Prop121.Card7F3Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F3Inputs
public import Certificates.Certificate5076
public import Certificates.Certificate5077

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem mem_CL {u c : F7} : c ∈ CL u ↔ c * u = u * c := by simp [CL, mem_F7L]

theorem mem_CXL {u c : F7} : c ∈ CXL u ↔ c * u = u * c ∧ XF c := by simp [CXL, mem_CL]

theorem mem_CYL {u c : F7} : c ∈ CYL u ↔ c * u = u * c ∧ YF c := by simp [CYL, mem_CL]

theorem CXL_nodup (u : F7) : (CXL u).Nodup := (F7L_nodup.filter _).filter _

theorem CYL_nodup (u : F7) : (CYL u).Nodup := (F7L_nodup.filter _).filter _

theorem mem_PL {p : F7 × F7} : p ∈ PL ↔ p.1 ∈ CXL f0 ∧ p.2 ∈ CYL f0 := by
  obtain ⟨a, b⟩ := p
  exact List.mem_product

theorem PL_nodup : PL.Nodup := (CXL_nodup f0).product (CYL_nodup f0)

theorem powB_iff {N : ℕ} {g x : F7} : powB N g x = true ↔ ∃ n < N, g ^ n = x := by
  simp [powB]

theorem chk_pow12 :
    ∀ p ∈ PL, (p.1 * p.2) ^ 12 = 1 :=
  Certificates.certificate5077.1

theorem chk_rz :
    PL.countP (fun p => powB 12 (p.1 * p.2) x0F) = 27 :=
  Certificates.certificate5077.2.1

theorem chk_N96 :
    (CYL f0).countP (fun b => decide (ccardB f0 b = 96)) = 3 :=
  Certificates.certificate5077.2.2.1

theorem chk_N48 :
    (CYL f0).countP (fun b => decide (ccardB f0 b = 48)) = 6 :=
  Certificates.certificate5077.2.2.2.1

theorem chk_Yvals :
    ∀ b ∈ CYL f0, ccardB f0 b = 96 ∨ ccardB f0 b = 48 :=
  Certificates.certificate5077.2.2.2.2.1

theorem chk_c33 : ∀ b ∈ CYL g0, ccardB g0 b = 12 :=
  Certificates.certificate5077.2.2.2.2.2

theorem F7_rz :
    Nat.card {p : F7 × F7 // p.1 * f0 = f0 * p.1 ∧ p.2 * f0 = f0 * p.2 ∧ XF p.1 ∧
    YF p.2 ∧ x0F ∈ zpowers (p.1 * p.2)} = 27 := by
  rw [← chk_rz]
  refine card_subtype_eq_countP PL PL_nodup _ _ (fun p => ?_)
  constructor
  · rintro ⟨h1, h2, hx, hy, hz⟩
    have hp : p ∈ PL := mem_PL.2 ⟨mem_CXL.2 ⟨h1, hx⟩, mem_CYL.2 ⟨h2, hy⟩⟩
    refine ⟨hp, ?_⟩
    rw [powB_iff]
    exact (mem_zpowers_iff_exists_pow_lt (by norm_num) (chk_pow12 p hp)).1 hz
  · rintro ⟨hp, hq⟩
    obtain ⟨hx, hy⟩ := mem_PL.1 hp
    obtain ⟨h1, hX⟩ := mem_CXL.1 hx
    obtain ⟨h2, hY⟩ := mem_CYL.1 hy
    refine ⟨h1, h2, hX, hY, ?_⟩
    exact (mem_zpowers_iff_exists_pow_lt (by norm_num) (chk_pow12 p hp)).2 (powB_iff.1 hq)

theorem F7_N96 :
    Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 96} = 3 := by
  rw [← chk_N96]
  refine card_subtype_eq_countP (CYL f0) (CYL_nodup f0) _ _ (fun b => ?_)
  rw [mem_CYL, ccard_eq_ccardB]
  simp [and_assoc]

theorem F7_N48 :
    Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = 48} = 6 := by
  rw [← chk_N48]
  refine card_subtype_eq_countP (CYL f0) (CYL_nodup f0) _ _ (fun b => ?_)
  rw [mem_CYL, ccard_eq_ccardB]
  simp [and_assoc]

theorem F7_Yvals :
    ∀ b : F7, b * f0 = f0 * b → YF b → ccard F7 f0 b = 96 ∨ ccard F7 f0 b = 48 := by
  intro b h1 h2
  rw [ccard_eq_ccardB]
  exact chk_Yvals b (mem_CYL.2 ⟨h1, h2⟩)

theorem F7_c33 :
    ∀ f : F7, Ty33 f → ∀ b : F7, b * f = f * b → YF b → ccard F7 f b = 12 := by
  intro f hf b hbf hb
  obtain ⟨k, hk⟩ := F7_conj33 f hf
  rw [← ccard_conj k f b, hk]
  have h1 : (k * b * k⁻¹) * g0 = g0 * (k * b * k⁻¹) := by
    rw [← hk]
    exact (commute_conj_iff k b f).2 hbf
  have h2 : YF (k * b * k⁻¹) := (yf_conj_iff k b).2 hb
  rw [ccard_eq_ccardB]
  exact chk_c33 _ (mem_CYL.2 ⟨h1, h2⟩)

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
