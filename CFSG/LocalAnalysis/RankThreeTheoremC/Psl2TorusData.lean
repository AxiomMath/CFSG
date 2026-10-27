module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.GorensteinWalter
open scoped MatrixGroups
open Matrix

section Psl2TorusAux

variable {K : Type*} [Field K]

private def psl2TorusDiag (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

private theorem psl2TorusDiag_mem_borel (a : Kˣ) : psl2TorusDiag a ∈ sl2Borel K := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  simp [psl2TorusDiag]

private theorem psl2TorusDiag_conj (a : Kˣ) (x : K) :
    psl2TorusDiag a * sl2UpperUnipotent x * (psl2TorusDiag a)⁻¹ =
      sl2UpperUnipotent ((a : K) ^ 2 * x) := by
  rw [sl2Borel_conj_upperUnipotent (psl2TorusDiag_mem_borel a)]
  simp [psl2TorusDiag]

private theorem psl2TorusDiag_conj_psl2 (a : Kˣ) (x : K) :
    psl2QuotientMap K (psl2TorusDiag a) * psl2QuotientMap K (sl2UpperUnipotent x) *
      (psl2QuotientMap K (psl2TorusDiag a))⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent ((a : K) ^ 2 * x)) := by
  rw [← map_inv, ← map_mul, ← map_mul, psl2TorusDiag_conj]

private theorem psl2_conj_mem_unipotent {A : SL(2, K)} (hA : A ∈ sl2Borel K) {h : PSL2 K}
    (hh : h ∈ psl2UpperUnipotentSubgroup K) :
    psl2QuotientMap K A * h * (psl2QuotientMap K A)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 hh
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]
  exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨_, rfl⟩

private theorem psl2_mem_normalizer_of_borel {A : SL(2, K)} (hA : A ∈ sl2Borel K) :
    psl2QuotientMap K A ∈
      Subgroup.normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨fun hh => psl2_conj_mem_unipotent hA hh, fun hh => ?_⟩
  have := psl2_conj_mem_unipotent (inv_mem hA) hh
  simpa [mul_assoc] using this

private theorem psl2_unip_pow (x : K) (n : ℕ) :
    psl2QuotientMap K (sl2UpperUnipotent x) ^ n =
      psl2QuotientMap K (sl2UpperUnipotent ((n : K) * x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← map_mul, sl2UpperUnipotent_mul, Nat.cast_succ, add_mul, one_mul]

private theorem psl2_unip_injective {x y : K}
    (h : psl2QuotientMap K (sl2UpperUnipotent x) = psl2QuotientMap K (sl2UpperUnipotent y)) :
    x = y := by
  have hcenter : sl2UpperUnipotent (x - y) ∈ Subgroup.center (SL(2, K)) := by
    have hq : psl2QuotientMap K (sl2UpperUnipotent (x - y)) = 1 := by
      rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv, h,
        mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

private theorem natCast_pow_prime (p : ℕ) [Fact p.Prime] [CharP K p] (k : ℕ) : (k : K) ^ p = k := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (k : ZMod p))
  rwa [map_pow, map_natCast] at h

private theorem units_pow_ne_natCast [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hcard : Nat.card K = p ^ 2) (hp5 : 5 ≤ p) {g : Kˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {c : ℕ} (hc0 : 0 < c) (hc4 : c ≤ 4) (k : ℕ) : (g : K) ^ c ≠ (k : K) := by
  intro hk
  have hpow : (g : K) ^ (c * p) = (g : K) ^ c := by
    rw [pow_mul, hk]
    exact natCast_pow_prime p k
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have e : c * p = c * (p - 1) + c := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [Nat.mul_succ]
  have h1 : (g : K) ^ (c * (p - 1)) = 1 := by
    have h2 : (g : K) ^ (c * (p - 1)) * (g : K) ^ c = 1 * (g : K) ^ c := by
      rw [one_mul, ← pow_add, ← e]
      exact hpow
    exact mul_right_cancel₀ (pow_ne_zero c hg0) h2
  have h3 : g ^ (c * (p - 1)) = 1 := Units.ext (by simpa using h1)
  have h4 : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have h5 : 0 < c * (p - 1) := Nat.mul_pos hc0 (by omega)
  have h6 := Nat.le_of_dvd h5 (orderOf_dvd_of_pow_eq_one h3)
  rw [h4] at h6
  have h7 : 5 * p ≤ p ^ 2 := by nlinarith
  have h8 : c * (p - 1) ≤ 4 * (p - 1) := Nat.mul_le_mul_right _ hc4
  omega

private theorem psl2_exists_not_mem_conj (p : ℕ) [Fact p.Prime]
    (σ : PSL2 K) (s : K) (hs : ∀ k : ℕ, s ≠ k)
    (hσ : ∀ x : K, σ * psl2QuotientMap K (sl2UpperUnipotent x) * σ⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (s * x)))
    (H : Subgroup (PSL2 K)) (hHU : H ≤ psl2UpperUnipotentSubgroup K)
    (hH : Nat.card H = p) :
    ∃ h ∈ H, σ * h * σ⁻¹ ∉ H := by
  by_contra hcon
  push Not at hcon
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp)
  have hnt : Nontrivial H :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; exact (Fact.out : p.Prime).one_lt)
  obtain ⟨⟨h, hh⟩, hne⟩ := exists_ne (1 : H)
  obtain ⟨x0, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 (hHU hh)
  have hx0 : x0 ≠ 0 := by
    rintro rfl
    exact hne (Subtype.ext (by simp))
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_of_prime_card hH hne (g' := ⟨σ * _ * σ⁻¹, hcon _ hh⟩))
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow] at hk'
  rw [psl2_unip_pow, hσ] at hk'
  have := psl2_unip_injective hk'
  exact hs k (mul_right_cancel₀ hx0 this).symm

end Psl2TorusAux

theorem psl2_torus_data (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ (U : Subgroup PSL(2, GaloisField p 2)) (τ σ : PSL(2, GaloisField p 2)),
      Nat.card U = p ^ 2 ∧ (∀ u ∈ U, u ^ p = 1) ∧ (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧
      τ ∈ Subgroup.normalizer (U : Set PSL(2, GaloisField p 2)) ∧
      (∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹) ∧
      σ ∈ Subgroup.normalizer (U : Set PSL(2, GaloisField p 2)) ∧
      (∀ H : Subgroup PSL(2, GaloisField p 2), H ≤ U → Nat.card H = p →
        ∃ h ∈ H, σ * h * σ⁻¹ ∉ H) ∧
      (∀ H : Subgroup PSL(2, GaloisField p 2), H ≤ U → Nat.card H = p →
        ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H) := by
  have hcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hsq : IsSquare (-1 : GaloisField p 2) := by
    have : Fintype (GaloisField p 2) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    have hodd : p % 2 = 1 := by
      rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
      · omega
      · exact h
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h | h <;> simp [Nat.pow_mod, h]
  obtain ⟨i, hi⟩ := hsq
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hi2 : ((Units.mk0 i hi0 : (GaloisField p 2)ˣ) : GaloisField p 2) ^ 2 = -1 := by
    rw [Units.val_mk0, sq, ← hi]
  refine ⟨psl2UpperUnipotentSubgroup (GaloisField p 2),
    psl2QuotientMap _ (psl2TorusDiag (Units.mk0 i hi0)), psl2QuotientMap _ (psl2TorusDiag g),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [psl2UpperUnipotentSubgroup_card, hcard]
  · intro u hu
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    rw [psl2_unip_pow, CharP.cast_eq_zero, zero_mul, sl2UpperUnipotent_zero, map_one]
  · intro u hu v hv
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).1 hv
    rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
  · exact psl2_mem_normalizer_of_borel (psl2TorusDiag_mem_borel _)
  · intro u hu
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    rw [psl2TorusDiag_conj_psl2, hi2, neg_one_mul, ← sl2UpperUnipotent_inv, map_inv]
  · exact psl2_mem_normalizer_of_borel (psl2TorusDiag_mem_borel _)
  · intro H hHU hH
    exact psl2_exists_not_mem_conj p _ ((g : GaloisField p 2) ^ 2)
      (units_pow_ne_natCast p hcard hp5 hg (by norm_num) (by norm_num))
      (fun x => psl2TorusDiag_conj_psl2 g x) H hHU hH
  · intro H hHU hH
    set σ := psl2QuotientMap (GaloisField p 2) (psl2TorusDiag g) with hσ
    have key : ∀ x : GaloisField p 2, σ * σ * psl2QuotientMap _ (sl2UpperUnipotent x) *
        (σ * σ)⁻¹ = psl2QuotientMap _ (sl2UpperUnipotent ((g : GaloisField p 2) ^ 4 * x)) := by
      intro x
      have e : σ * σ * psl2QuotientMap _ (sl2UpperUnipotent x) * (σ * σ)⁻¹ =
          σ * (σ * psl2QuotientMap _ (sl2UpperUnipotent x) * σ⁻¹) * σ⁻¹ := by group
      have e2 : (g : GaloisField p 2) ^ 2 * ((g : GaloisField p 2) ^ 2 * x) =
          (g : GaloisField p 2) ^ 4 * x := by ring
      rw [e, hσ, psl2TorusDiag_conj_psl2, psl2TorusDiag_conj_psl2, e2]
    obtain ⟨h, hh, hn⟩ := psl2_exists_not_mem_conj p (σ * σ) ((g : GaloisField p 2) ^ 4)
      (units_pow_ne_natCast p hcard hp5 hg (by norm_num) (by norm_num)) key H hHU hH
    refine ⟨h, hh, ?_⟩
    have e : σ * (σ * h * σ⁻¹) * σ⁻¹ = σ * σ * h * (σ * σ)⁻¹ := by group
    rwa [e]

end CFSG.LocalAnalysis.RankThreeTheoremC
