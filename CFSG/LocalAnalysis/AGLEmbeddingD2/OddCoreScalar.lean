module

import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.ClassTwoRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreLemmaS
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCorePiecesD2
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.Open
open scoped commutatorElement

section Conjugation

variable {Y : Type*} [Group Y]

theorem pow_mem_normalizer_map_subtype {X : Subgroup Y} {t : Y}
    (htX : t ∈ Subgroup.normalizer (X : Set Y)) (k : ℕ) {F : Subgroup X}
    (hF : F.map (X.normalizerMonoidHom ⟨t, htX⟩ ^ k).toMonoidHom = F) :
    t ^ k ∈ Subgroup.normalizer ((F.map X.subtype : Subgroup Y) : Set Y) := by
  set α := X.normalizerMonoidHom ⟨t, htX⟩ ^ k with hαdef
  have hα : ∀ x : X, ((α x : X) : Y) = t ^ k * x * (t ^ k)⁻¹ :=
    coe_normalizerMonoidHom_pow_apply htX k
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨α x, ?_, hα x⟩
    rw [← hF]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hx'eq⟩
    have hyX : y ∈ X := by
      have hmem : t ^ k * y * (t ^ k)⁻¹ ∈ X := hx'eq ▸ x'.2
      exact ((Subgroup.mem_normalizer_iff.mp (pow_mem htX k)) y).mpr hmem
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have h1 : α ⟨y, hyX⟩ = x' := Subtype.ext (by rw [hα]; exact hx'eq.symm)
    have h2 : α ⟨y, hyX⟩ ∈ F.map α.toMonoidHom := by rw [hF, h1]; exact hx'
    obtain ⟨z, hz, hzeq⟩ := h2
    rwa [α.injective hzeq] at hz

theorem map_normalizerMonoidHom_pow_ne {X : Subgroup Y} {t : Y} {p m : ℕ} [Fact p.Prime]
    (htX : t ∈ Subgroup.normalizer (X : Set Y)) (hXc : Nat.card X = p ^ 2)
    (horb : ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup Y, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set Y))
    {k : ℕ} (hk0 : 0 < k) (hkm : k < m) {F : Subgroup X} (hF : F.index = p) :
    F.map (X.normalizerMonoidHom ⟨t, htX⟩ ^ k).toMonoidHom ≠ F := by
  intro h
  have hcard : Nat.card (F.map X.subtype) = p := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    have h1 := F.card_mul_index
    rw [hF, hXc, sq] at h1
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h1
  exact horb k hk0 hkm _ (Subgroup.map_subtype_le F) hcard
    (pow_mem_normalizer_map_subtype htX k h)

end Conjugation

section Pieces

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem pow_two_mul_le_card_of_scalar [Finite A] [Finite V] {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1)
    (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v) (hα : ∀ a, (α ^ m) a = a ^ lam)
    (hlam : ¬ p ∣ lam - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F) :
    s ^ (2 * m) ≤ Nat.card V :=
  pow_two_mul_le_card_of_equivariant hsp hA (fun v => ⟨1, by rw [pow_one]; exact hV v⟩) hnt hαβ
    hlen fun _ hF hne => two_le_log_fixedPiece Fact.out Fact.out hsp hA hV hαβ m lam hα hlam hF hne

end Pieces

section Abstract

open Subgroup

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

open scoped IsMulCommutative in
theorem pow_two_mul_le_card_center_of_scalar {s p m lam : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1) (ψ : A →* MulAut D)
    {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) (hlam : ¬ p ∣ lam - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hnt : ∃ a : A, ∃ z ∈ center D, ψ a z ≠ z) : s ^ (2 * m) ≤ Nat.card (center D) := by
  let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
  let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  obtain ⟨a, z, hz, haz⟩ := hnt
  refine pow_two_mul_le_card_of_scalar hsp hA (fun z => Subtype.ext (hD z))
    ⟨a, ⟨z, hz⟩, fun h => haz (congrArg Subtype.val h)⟩ (β := ρ τ) (fun a v => ?_) hα hlam hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

open scoped IsMulCommutative in
theorem pow_two_mul_le_card_quotient_center_of_scalar {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (ψ : A →* MulAut D) (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A}
    {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ) (hα : ∀ a, (α ^ m) a = a ^ lam)
    (hlam : ¬ p ∣ lam - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z) : s ^ (2 * m) ≤ Nat.card (D ⧸ center D) := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hcomm : IsMulCommutative (D ⧸ center D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
  let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
  let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
    induction v using QuotientGroup.induction_on with
    | H d => rw [← QuotientGroup.mk_pow, hD d]; rfl
  have hnt : ∃ (a : A) (v : D ⧸ center D), a • v ≠ v := by
    obtain ⟨a, ha⟩ := hψ
    obtain ⟨d, hd⟩ : ∃ d : D, ψ a d ≠ d := by
      by_contra h
      push Not at h
      exact ha (MulEquiv.ext h)
    refine ⟨a, d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes hp hs).mpr
      hsp.symm) hD ?_ (hZ a) h)⟩
    rw [← map_pow, hA a, map_one]
  refine pow_two_mul_le_card_of_scalar hsp hA hV hnt (β := ρ τ) (fun a v => ?_) hα hlam hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

theorem exists_isMulCommutative_pow_four_le_card_of_scalar {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hm : 5 ≤ 2 * m)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D)
    (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) (hlam : ¬ p ∣ lam - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hs : s.Prime := Fact.out
  by_cases hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z
  · exact exists_isMulCommutative_pow_four_le_card hs hD hc
      ((Nat.pow_le_pow_right hs.pos hm).trans (pow_two_mul_le_card_quotient_center_of_scalar hsp hA
        hD hc ψ hψ hατ hα hlam hlen hZ))
  · push Not at hZ
    exact ⟨center D, inferInstance, (Nat.pow_le_pow_right hs.pos (by omega)).trans
      (pow_two_mul_le_card_center_of_scalar hsp hA hD ψ hατ hα hlam hlen hZ)⟩

end Abstract

theorem stmtOddCoreRankScalar {Y : Type} [Group Y] [Finite Y] {s p : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (Sg X : Subgroup Y) (t : Y)
    (lam : ℕ) (hSg : IsPGroup s Sg) (hXS : X ≤ Subgroup.normalizer (Sg : Set Y))
    (hX : IsElemAbelian p X) (hXc : Nat.card X = p ^ 2)
    (htS : t ∈ Subgroup.normalizer (Sg : Set Y)) (htX : t ∈ Subgroup.normalizer (X : Set Y))
    (hlam : ¬ p ∣ lam - 1)
    (hscal : ∀ x ∈ X, t ^ ((p + 1) / 2) * x * (t ^ ((p + 1) / 2))⁻¹ = x ^ lam)
    (horb : ∀ k, 0 < k → k < (p + 1) / 2 → ∀ Y₀ : Subgroup Y, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set Y))
    (hnc : ¬ X ≤ Subgroup.centralizer (Sg : Set Y)) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have := Fact.mk hp
  have hm : 5 ≤ 2 * ((p + 1) / 2) := by
    obtain ⟨r, hr⟩ := hp.odd_of_ne_two (by omega)
    omega
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup X := @IsMulCommutative.instCommGroup _ _ hX.1
  let ψ : X →* MulAut D := φ.comp (Subgroup.inclusion hXS)
  let α : MulAut X := X.normalizerMonoidHom ⟨t, htX⟩
  have hατ : ∀ x : X, φ ⟨t, htS⟩ * ψ x = ψ (α x) * φ ⟨t, htS⟩ := fun x => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hXS x) =
      φ (Subgroup.inclusion hXS (α x)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (x : Y) = t * x * t⁻¹ * t
    group
  have hψ : ∃ x : X, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxX, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hXS hxX⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxX⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨x, hXS hxX⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hX.2 x hxX)
      change (Sg.normalizerMonoidHom ⟨x, hXS hxX⟩) ^ p = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs hp).mpr hsp)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hαm : ∀ x : X, (α ^ ((p + 1) / 2)) x = x ^ lam := fun x =>
    Subtype.ext (by
      rw [coe_normalizerMonoidHom_pow_apply htX, hscal x x.2]
      rfl)
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_four_le_card_of_scalar hsp
    (fun x => Subtype.ext (hX.2 x x.2)) hm hD hc ψ hψ hατ hαm hlam
    (fun k hk0 hkm F hF => map_normalizerMonoidHom_pow_ne htX hXc horb hk0 hkm hF)
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [hm] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hm (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end CFSG.AGLEmbeddingD2
