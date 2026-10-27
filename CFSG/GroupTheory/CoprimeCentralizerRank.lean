module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

private theorem map_conj_eq_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) _).mpr
        (by simpa [mul_assoc] using hx)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem exists_map_conj_le_centralizer_of_commutator_le [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] {N R B : Subgroup G} (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hR : IsPGroup p R) (hB : IsPGroup q B) (hpN : ¬ p ∣ Nat.card N)
    (hqN : ¬ q ∣ Nat.card N) (hcomm : ⁅R, B⁆ ≤ N) :
    ∃ n ∈ N, R.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (B : Set G) := by
  classical
  have hbot : R ⊓ N = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpN hR
  have hstep : ∀ b ∈ B, ∀ y ∈ (R ⊔ N : Subgroup G), b * y * b⁻¹ ∈ R ⊔ N := by
    intro b hb y hy
    have hy' : y ∈ (R : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R N hRN]
      exact hy
    obtain ⟨r, hr, n, hn, rfl⟩ := hy'
    have hmem : ⁅b, r⁆ ∈ N :=
      hcomm (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hb hr)
    have hbr : b * r * b⁻¹ ∈ R ⊔ N := by
      have hbr_eq : b * r * b⁻¹ = ⁅b, r⁆ * r := by
        rw [commutatorElement_def]
        group
      rw [hbr_eq]
      exact (R ⊔ N).mul_mem (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left hr)
    have hbn : b * n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hBN hb) n).mp hn
    have hsplit : b * (r * n) * b⁻¹ = (b * r * b⁻¹) * (b * n * b⁻¹) := by group
    rw [hsplit]
    exact (R ⊔ N).mul_mem hbr (Subgroup.mem_sup_right hbn)
  have hBNX : B ≤ Subgroup.normalizer ((R ⊔ N : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨fun hy => hstep b hb y hy, fun hy => ?_⟩
    have h1 := hstep b⁻¹ (B.inv_mem hb) (b * y * b⁻¹) hy
    have h2 : b⁻¹ * (b * y * b⁻¹) * (b⁻¹)⁻¹ = y := by group
    rwa [h2] at h1
  have hXB : ⁅R ⊔ N, B⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx b hb
    have hx' : x ∈ (R : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R N hRN]
      exact hx
    obtain ⟨r, hr, n, hn, rfl⟩ := hx'
    rw [CFSG.commutator_mul_left]
    have h1 : ⁅r, b⁆ ∈ N := hcomm (Subgroup.commutator_mem_commutator hr hb)
    have h2 : ⁅n, b⁆ ∈ N := by
      have hbn : b * n⁻¹ * b⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hBN hb) n⁻¹).mp (N.inv_mem hn)
      have hcomm'n : ⁅n, b⁆ = n * (b * n⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [hcomm'n]
      exact N.mul_mem hn hbn
    have hconj : r * ⁅n, b⁆ * r⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hRN hr) ⁅n, b⁆).mp h2
    exact N.mul_mem hconj h1
  have hcardX : Nat.card (R ⊔ N : Subgroup G) = Nat.card R * Nat.card N := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (A := R) (B := N)
    rw [hbot, Subgroup.card_bot, mul_one] at h
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R N hRN] at h
    simpa using h
  have hrel : R.relIndex (R ⊔ N) = Nat.card N := by
    have h := Subgroup.relIndex_mul_card R (R ⊔ N)
    rw [inf_eq_left.mpr (le_sup_left : R ≤ R ⊔ N), hcardX] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥R)) (by rw [h]; exact mul_comm _ _)
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p R (R ⊔ N) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_sup_left, hR, by rw [hrel]; exact hpN⟩
  obtain ⟨S, hSsyl, hScent⟩ :=
    exists_isSylowOf_le_centralizer_of_commutator_le (p := q) (q := p) (X := R ⊔ N)
      (N := N) (R := B) le_sup_right hBNX hBN hB hqN hXB hpN
  obtain ⟨k, hkX, hkconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hRsyl hSsyl
  have hSk : S = R.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨k⁻¹ * x * k, (hkconj x).mp hx, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨y, hy, rfl⟩
      refine (hkconj (k * y * k⁻¹)).mpr ?_
      have h : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [h]
  have hk' : k ∈ (R : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R N hRN]
    exact hkX
  obtain ⟨r, hr, n, hn, hk_eq⟩ := hk'
  set n' : G := r * n * r⁻¹ with hn'_def
  have hnN : n' ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hRN hr) n).mp hn
    simpa [hn'_def] using this
  have hk_n'r : k = n' * r := by
    rw [← hk_eq]
    simp only [hn'_def]
    group
  have hmap : R.map (MulAut.conj k).toMonoidHom = R.map (MulAut.conj n').toMonoidHom := by
    rw [hk_n'r]
    have hcomp : (MulAut.conj (n' * r)).toMonoidHom =
        (MulAut.conj n').toMonoidHom.comp (MulAut.conj r).toMonoidHom := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, map_conj_eq_self_of_mem hr]
  refine ⟨n', hnN, ?_⟩
  calc R.map (MulAut.conj n').toMonoidHom = R.map (MulAut.conj k).toMonoidHom := hmap.symm
    _ = S := hSk.symm
    _ ≤ Subgroup.centralizer (B : Set G) := hScent

theorem pRank_le_pRank_inf_centralizer_of_commutator_le [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] {M N R B : Subgroup G} (hRM : R ≤ M) (hNM : N ≤ M)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hR : IsPGroup p R) (hB : IsPGroup q B) (hpN : ¬ p ∣ Nat.card N)
    (hqN : ¬ q ∣ Nat.card N) (hcomm : ⁅R, B⁆ ≤ N) :
    CFSG.Open.pRank p R ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G)) := by
  obtain ⟨n, hn, hnle⟩ :=
    exists_map_conj_le_centralizer_of_commutator_le hRN hBN hR hB hpN hqN hcomm
  have hle : R.map (MulAut.conj n).toMonoidHom ≤
      M ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_inf ?_ hnle
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem (hNM hn) (hRM hy)) (M.inv_mem (hNM hn))
  have hcomp : (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hmap : (R.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = R := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hrank : CFSG.Open.pRank p (R.map (MulAut.conj n).toMonoidHom) =
      CFSG.Open.pRank p R := by
    refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map hp1 _ (MulAut.conj n).injective R)
    calc CFSG.Open.pRank p (R.map (MulAut.conj n).toMonoidHom)
        ≤ CFSG.Open.pRank p ((R.map (MulAut.conj n).toMonoidHom).map
            (MulAut.conj n⁻¹).toMonoidHom) :=
          CFSG.SectionRank.pRank_le_map hp1 _ (MulAut.conj n⁻¹).injective _
      _ = CFSG.Open.pRank p R := by rw [hmap]
  calc CFSG.Open.pRank p R = CFSG.Open.pRank p (R.map (MulAut.conj n).toMonoidHom) :=
        hrank.symm
    _ ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G)) :=
        CFSG.SectionRank.pRank_mono hp1 hle

end CFSG.GroupTheory
