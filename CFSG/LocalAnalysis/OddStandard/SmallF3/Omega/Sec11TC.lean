module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Idx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L116
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec11_conj_mem_oTwoRes {Y : Subgroup G} {g : G}
    (hg : ∀ y, y ∈ Y ↔ g * y * g⁻¹ ∈ Y) :
    ∀ x ∈ oTwoRes Y, g * x * g⁻¹ ∈ oTwoRes Y := by
  intro x hx
  change x ∈ Subgroup.closure {a : G | a ∈ Y ∧ Odd (orderOf a)} at hx
  have hgen : ∀ y ∈ ({a : G | a ∈ Y ∧ Odd (orderOf a)} : Set G),
      (MulAut.conj g) y ∈ ({a : G | a ∈ Y ∧ Odd (orderOf a)} : Set G) := by
    rintro y ⟨hyY, hyodd⟩
    have hconj : orderOf ((MulAut.conj g) y) = orderOf y := (MulAut.conj g).orderOf_eq y
    exact ⟨(hg y).mp hyY, by rw [hconj]; exact hyodd⟩
  have hle : (Subgroup.closure {a : G | a ∈ Y ∧ Odd (orderOf a)}).map
      (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure {a : G | a ∈ Y ∧ Odd (orderOf a)} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨a, ha, rfl⟩
    exact hgen a ha
  have hx' : (MulAut.conj g) x ∈ Subgroup.closure {a : G | a ∈ Y ∧ Odd (orderOf a)} :=
    hle (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  simpa [oTwoRes, MulAut.conj_apply] using hx'

private lemma sec11_commute_of_commute_mul {c t z : G} (hz2 : z * z = 1)
    (h1 : c * (t * z) = (t * z) * c) (h2 : c * z = z * c) : c * t = t * c := by
  have htzz : t * z * z = t := by rw [mul_assoc, hz2, mul_one]
  calc c * t = c * (t * z * z) := by rw [htzz]
    _ = (c * (t * z)) * z := by simp only [mul_assoc]
    _ = ((t * z) * c) * z := by rw [h1]
    _ = (t * z) * (c * z) := by simp only [mul_assoc]
    _ = (t * z) * (z * c) := by rw [h2]
    _ = ((t * z) * z) * c := by simp only [mul_assoc]
    _ = t * c := by rw [htzz]

private lemma sec11_conj_mem_centralizers {t z ρ y : G} (hz2 : z * z = 1)
    (hρz : ρ * z * ρ⁻¹ = z) (hu : ρ * t * ρ⁻¹ = t ∨ ρ * t * ρ⁻¹ = t * z)
    (hyt : y * t = t * y) (hyz : y * z = z * y) :
    (ρ * y * ρ⁻¹) * t = t * (ρ * y * ρ⁻¹) ∧
      (ρ * y * ρ⁻¹) * z = z * (ρ * y * ρ⁻¹) := by
  have hcommt : (MulAut.conj ρ) y * (MulAut.conj ρ) t =
      (MulAut.conj ρ) t * (MulAut.conj ρ) y := by
    rw [← map_mul (MulAut.conj ρ) y t, ← map_mul (MulAut.conj ρ) t y, hyt]
  have hφz : (MulAut.conj ρ) z = z := by rw [MulAut.conj_apply, hρz]
  have hcommz : (MulAut.conj ρ) y * z = z * (MulAut.conj ρ) y := by
    rw [← hφz, ← map_mul (MulAut.conj ρ) y z, ← map_mul (MulAut.conj ρ) z y, hyz]
  have hu' : (MulAut.conj ρ) t = t ∨ (MulAut.conj ρ) t = t * z := by
    rw [MulAut.conj_apply]
    exact hu
  constructor
  · rcases hu' with h | h
    · rw [← MulAut.conj_apply ρ y, ← h]
      exact hcommt
    · rw [← MulAut.conj_apply ρ y]
      exact sec11_commute_of_commute_mul hz2 (by rw [← h]; exact hcommt) hcommz
  · rw [← MulAut.conj_apply ρ y]
    exact hcommz

theorem sec11_normalizer_oTwoRes {Y : Subgroup G} {g : G} (hg : ∀ y, y ∈ Y ↔ g * y * g⁻¹ ∈ Y) :
    g ∈ normalizer (oTwoRes Y : Set G) := by
  have hg' : ∀ y, y ∈ Y ↔ g⁻¹ * y * (g⁻¹)⁻¹ ∈ Y := by
    intro y
    have h := hg (g⁻¹ * y * g)
    have h' : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [h'] at h
    simpa using h.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => sec11_conj_mem_oTwoRes hg x hx, fun hx => ?_⟩
  have h := sec11_conj_mem_oTwoRes (g := g⁻¹) hg' (g * x * g⁻¹) hx
  have h' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h'] at h

theorem sec11_T_normalizes_K0 {t z : G} {T : Subgroup G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) (hz1 : z ≠ 1) (hclass : conjClassIn T t = {t, t * z}) :
    T ≤ normalizer (secK0 t z : Set G) := by
  intro σ hσ
  have hTz : ∀ ρ ∈ T, ρ * z * ρ⁻¹ = z := sec11_fix_z_of_class ht2 hz2 htz hz1 hclass
  obtain ⟨hconjT, -⟩ := sec11_conj_cases hclass
  have hconjY : ∀ ρ ∈ T, ∀ y ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G),
      ρ * y * ρ⁻¹ ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
    intro ρ hρ y hy
    obtain ⟨hyt, hyz⟩ := Subgroup.mem_inf.mp hy
    have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
    have hyz' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyz
    obtain ⟨hct, hcz⟩ := sec11_conj_mem_centralizers hz2 (hTz ρ hρ) (hconjT ρ hρ) hyt' hyz'
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hct,
        Subgroup.mem_centralizer_singleton_iff.mpr hcz⟩
  refine sec11_normalizer_oTwoRes
    (Y := centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) ?_
  intro y
  refine ⟨fun hy => hconjY σ hσ y hy, fun hy => ?_⟩
  have h := hconjY σ⁻¹ (T.inv_mem hσ) (σ * y * σ⁻¹) hy
  have h' : σ⁻¹ * (σ * y * σ⁻¹) * (σ⁻¹)⁻¹ = y := by group
  rwa [h'] at h

theorem sec11_Q_eq_inf [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    secQ K1 K2 = S ⊓ secK0 t z := by
  apply le_antisymm
  · refine le_inf (le_trans (sec10J_Q_le hP5 hb hctx) inf_le_left) ?_
    have hKle : secQ K1 K2 ≤ K1 ⊔ K2 :=
      Subgroup.map_subtype_le (pCore 2 ↥(K1 ⊔ K2))
    rw [(hK0 G t L S z K1 K2 hctx).1]
    exact le_trans hKle (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · intro s hs
    obtain ⟨hsS, hsK0⟩ := Subgroup.mem_inf.mp hs
    have hv2 : ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hctx.sylow.2.1 ⟨s, hsS⟩
      exact ⟨m, by simpa using hm⟩
    exact sec10T_two_elem_K0 hK0 h36 hP5 hC5 hb hctx hsK0 hv2

theorem sec11_T_normalizes_Q [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {T : Subgroup G} (hST : S ≤ T) (hidx : S.relIndex T = 2)
    (hTK0 : T ≤ normalizer (secK0 t z : Set G)) : T ≤ normalizer (secQ K1 K2 : Set G) := by
  intro σ hσ
  have hSN : σ ∈ normalizer (S : Set G) := sec11_le_normalizer_of_relIndex_two hST hidx hσ
  have hK0N : σ ∈ normalizer (secK0 t z : Set G) := hTK0 hσ
  rw [sec11_Q_eq_inf hK0 h36 hP5 hC5 hb hctx]
  rw [Subgroup.mem_normalizer_iff] at hSN hK0N ⊢
  intro x
  simp only [Subgroup.mem_inf, hSN x, hK0N x]

end CFSG.OddStandard.SmallF3.Omega
