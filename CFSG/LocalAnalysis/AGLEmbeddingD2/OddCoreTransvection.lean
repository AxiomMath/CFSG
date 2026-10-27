module

import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreHeis
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding
open scoped commutatorElement IsMulCommutative

section Powers

variable {Y : Type*} [Group Y]

theorem pow_conj_mul_inv_mem_zpowers_of_transvection {A : Subgroup Y} {ζ b : Y}
    (hbζ : b * ζ * b⁻¹ = ζ) (hb : ∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers ζ) (k : ℕ)
    {y : Y} (hy : y ∈ A) : b ^ k * y * (b ^ k)⁻¹ * y⁻¹ ∈ Subgroup.zpowers ζ := by
  have hcomm : Commute b ζ := mul_inv_eq_iff_eq_mul.mp hbζ
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hb y hy)
    have hcn : Commute (b ^ k) (ζ ^ n) := (hcomm.pow_left k).zpow_right n
    have h1 : b ^ k * (b * y * b⁻¹ * y⁻¹) * (b ^ k)⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      rw [← hn, hcn.eq, mul_inv_cancel_right]
    have h2 : b ^ (k + 1) * y * (b ^ (k + 1))⁻¹ * y⁻¹ =
        (b ^ k * (b * y * b⁻¹ * y⁻¹) * (b ^ k)⁻¹) * (b ^ k * y * (b ^ k)⁻¹ * y⁻¹) := by
      group
    rw [h2, h1]
    exact Subgroup.mul_mem _ (hb y hy) ih

end Powers

section Rank

open Subgroup

theorem stmtOddCoreRankTransvection {Y : Type} [Group Y] [Finite Y] {s p : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (Sg A : Subgroup Y) (ζ b a₀ : Y)
    (hSg : IsPGroup s Sg) (hAS : A ≤ normalizer (Sg : Set Y))
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAexp : ∀ x ∈ A, x ^ p = 1) (hζA : ζ ∈ A)
    (hbS : b ∈ normalizer (Sg : Set Y)) (hbA : b ∈ normalizer (A : Set Y))
    (hbζ : b * ζ * b⁻¹ = ζ) (htrans : ∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ zpowers ζ) (ha₀ : a₀ ∈ A)
    (hmove : ∀ k : ℕ, 0 < k → k < p → b ^ k * a₀ * (b ^ k)⁻¹ ≠ a₀)
    (hnc : ζ ∉ centralizer (Sg : Set Y)) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have := Fact.mk hp
  have hζ1 : ζ ≠ 1 := fun h => hnc (h ▸ Subgroup.one_mem _)
  have hζord : orderOf ζ = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hAexp ζ hζA))).resolve_left
      fun h => hζ1 (orderOf_eq_one_iff.mp h)
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexpD, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  have : IsMulCommutative A := ⟨⟨fun x y => Subtype.ext (hAc x x.2 y y.2)⟩⟩
  let ψ : A →* MulAut D := φ.comp (Subgroup.inclusion hAS)
  let α : MulAut A := A.normalizerMonoidHom ⟨b, hbA⟩
  let ζA : A := ⟨ζ, hζA⟩
  have hατ : ∀ x : A, φ ⟨b, hbS⟩ * ψ x = ψ (α x) * φ ⟨b, hbS⟩ := fun x => by
    change φ ⟨b, hbS⟩ * φ (Subgroup.inclusion hAS x) =
      φ (Subgroup.inclusion hAS (α x)) * φ ⟨b, hbS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change b * (x : Y) = b * x * b⁻¹ * b
    group
  have hψ : ψ ζA ≠ 1 := by
    intro hall
    apply hnc
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨ζ, hAS hζA⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) hall
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨ζ, hAS hζA⟩ : normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hAexp ζ hζA)
      change (Sg.normalizerMonoidHom ⟨ζ, hAS hζA⟩) ^ p = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs hp).mpr hsp)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ζ * y * ζ⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexpD d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hαζ : α ζA = ζA := Subtype.ext hbζ
  have hαx : ∀ (k : ℕ) (x : A), (α ^ k) x * x⁻¹ ∈ zpowers ζA := fun k x => by
    refine mem_zpowers_of_coe_mem_zpowers ?_
    have h1 : (((α ^ k) x * x⁻¹ : A) : Y) = b ^ k * (x : Y) * (b ^ k)⁻¹ * (x : Y)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom_pow_apply hbA k x]
    rw [h1]
    exact pow_conj_mul_inv_mem_zpowers_of_transvection hbζ htrans k x.2
  have hαa : ∀ k : ℕ, 0 < k → k < p → (α ^ k) ⟨a₀, ha₀⟩ ≠ ⟨a₀, ha₀⟩ := fun k hk0 hkp h =>
    hmove k hk0 hkp (by
      have h1 := congrArg Subtype.val h
      rwa [coe_normalizerMonoidHom_pow_apply hbA k] at h1)
  have hζA' : orderOf ζA = p := by
    rw [← Subgroup.orderOf_coe]
    exact hζord
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_four_le_card_of_heisenberg hp5 hsp
    (fun x : A => Subtype.ext (hAexp x x.2)) hD hc ψ (ζ := ζA) hψ hατ
    fun k hk0 hkp F hF hζF => map_pow_ne_of_heisenberg (a₀ := ⟨a₀, ha₀⟩) hζA' hαζ hαx hαa hk0 hkp
      hF hζF
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end Rank

end CFSG.AGLEmbeddingD2
