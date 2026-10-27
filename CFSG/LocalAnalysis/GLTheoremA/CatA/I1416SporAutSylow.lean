module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open Pointwise

variable {T : Type} [Group T] [Finite T]

theorem eq_one_of_smul_sylow_eq [IsSimpleGroup T] {p : ℕ} [Fact p.Prime]
    {P : Sylow p T} (hPn : Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤) {h : T}
    (hh : ∀ Q : Sylow p T, h • Q = Q) : h = 1 := by
  set φ := MulAction.toPermHom T (Sylow p T)
  have hk : h ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    ext Q
    simp [φ, hh Q]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
  · rw [hb] at hk
    exact hk
  · exfalso
    apply hPn
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ φ.ker := ht ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    have hgP : g • P = P := by
      have := congrArg (fun σ : Equiv.Perm (Sylow p T) => σ P) hg
      simpa [φ] using this
    exact (Sylow.smul_eq_iff_mem_normalizer).1 hgP

theorem toPermHom_mulAut_injective [IsSimpleGroup T] {p : ℕ} [Fact p.Prime]
    {P : Sylow p T} (hPn : Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤) :
    Function.Injective (MulAction.toPermHom (MulAut T) (Sylow p T)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hfix : ∀ Q : Sylow p T, α • Q = Q := by
    intro Q
    have := congrArg (fun σ : Equiv.Perm (Sylow p T) => σ Q) hα
    simpa using this
  have hfix' : ∀ Q : Sylow p T, α⁻¹ • Q = Q := by
    intro Q
    conv_lhs => rw [← hfix Q]
    rw [inv_smul_smul]
  ext g
  have hconj : MulAut.conj (α g) = α * MulAut.conj g * α⁻¹ := by
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply]
    rw [map_mul, map_mul, MulAut.apply_inv_self, map_inv]
  have hh : ∀ Q : Sylow p T, (α g * g⁻¹) • Q = Q := by
    intro Q
    rw [mul_smul, Sylow.smul_def (g := α g), hconj, mul_smul, mul_smul,
      hfix' (g⁻¹ • Q), Sylow.smul_def (g := g⁻¹), ← mul_smul (MulAut.conj g), ← map_mul,
      mul_inv_cancel, map_one, one_smul, hfix Q]
  have h1 := eq_one_of_smul_sylow_eq hPn hh
  rw [mul_inv_eq_one] at h1
  simpa using h1

theorem card_mulAut_dvd_factorial [IsSimpleGroup T] {p : ℕ} [Fact p.Prime]
    {P : Sylow p T} (hPn : Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤) :
    Nat.card (MulAut T) ∣ (Nat.card (Sylow p T)).factorial := by
  have hinj := toPermHom_mulAut_injective hPn
  rw [← Nat.card_perm]
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Subgroup.card_subgroup_dvd_card _

theorem not_sq_seven_dvd_card_mulAut_of_card_168 [IsSimpleGroup T] (hT : Nat.card T = 168) :
    ¬ 7 ^ 2 ∣ Nat.card (MulAut T) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
  set n := Nat.card (Sylow 7 T) with hn
  have hn1 : n ≡ 1 [MOD 7] := card_sylow_modEq_one 7 T
  have hnidx : n = (Subgroup.normalizer ((P : Subgroup T) : Set T)).index :=
    Sylow.card_eq_index_normalizer P
  have hidx : (Subgroup.normalizer ((P : Subgroup T) : Set T)).index ∣ (P : Subgroup T).index :=
    Subgroup.index_dvd_of_le Subgroup.le_normalizer
  have hidx24 : (P : Subgroup T).index ∣ 24 := by
    have h1 : (P : Subgroup T).index ∣ 168 := hT ▸ Subgroup.index_dvd_card _
    have h2 : ¬ 7 ∣ (P : Subgroup T).index := P.not_dvd_index
    have hcop : Nat.Coprime (P : Subgroup T).index 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h2).symm
    exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
  have hn24 : n ∣ 24 := hnidx ▸ hidx.trans hidx24
  have key : ∀ m : ℕ, m ∣ 24 → m % 7 = 1 → m = 1 ∨ m = 8 := by
    intro m hm h
    have hle := Nat.le_of_dvd (by norm_num) hm
    interval_cases m <;> simp_all
  have h7 : 7 ∣ Nat.card T := by rw [hT]; norm_num
  have hPn : Subgroup.normalizer ((P : Subgroup T) : Set T) ≠ ⊤ := by
    intro hN
    have hPn : (P : Subgroup T).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup T) with hb | ht
    · have := P.dvd_card_of_dvd_card h7
      rw [hb, Subgroup.card_bot] at this
      norm_num at this
    · have hc : Nat.card (P : Subgroup T) ∣ 7 ^ 1 := by
        have h1 := P.card_eq_multiplicity
        rw [h1]
        refine Nat.pow_dvd_pow 7 ?_
        rw [hT]
        have : (168 : ℕ) = 7 ^ 1 * 24 := by norm_num
        rw [this, Nat.factorization_mul_apply_of_coprime (by norm_num)]
        simp [Nat.Prime.factorization_self (show Nat.Prime 7 by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 24 by norm_num)]
      rw [ht, Subgroup.card_top, hT] at hc
      norm_num at hc
  have hn8 : n = 8 := by
    rcases key n hn24 hn1 with h1 | h8
    · exfalso
      apply hPn
      rw [← Subgroup.index_eq_one, ← hnidx, h1]
    · exact h8
  have hd := card_mulAut_dvd_factorial hPn
  rw [← hn, hn8] at hd
  intro h49
  have := h49.trans hd
  norm_num [Nat.factorial] at this

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
