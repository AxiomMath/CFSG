module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreScalar
import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbeddingD2 CFSG.Open
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem map_pow_ne_of_index {A : Subgroup Y} {t : Y} {p k : ℕ}
    (htA : t ∈ Subgroup.normalizer (A : Set Y))
    (horb : ∀ F : Subgroup Y, F ≤ A → F.relIndex A = p →
      t ^ k ∉ Subgroup.normalizer (F : Set Y))
    {F : Subgroup A} (hF : F.index = p) :
    F.map (A.normalizerMonoidHom ⟨t, htA⟩ ^ k).toMonoidHom ≠ F := by
  intro h
  refine horb _ (Subgroup.map_subtype_le F) ?_ (pow_mem_normalizer_map_subtype htA k h)
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective, hF]

theorem le_centralizer_of_fixing {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hsp : s ≠ p)
    {Sg A : Subgroup Y} (hAS : A ≤ Subgroup.normalizer (Sg : Set Y))
    (hA : IsElemAbelian p A) {D : Subgroup Sg} [D.Characteristic]
    (hfix : IsPGroup s (fixingSubgroup (MulAut Sg) (D : Set Sg)))
    (hall : ∀ x : A, ((MulAut.characteristic D).comp Sg.normalizerMonoidHom).comp
      (Subgroup.inclusion hAS) x = 1) :
    A ≤ Subgroup.centralizer (Sg : Set Y) := by
  intro x hxA
  let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hAS hxA⟩
  have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxA⟩)
  obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
  have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
  have hθp : θ ^ p = 1 := by
    have hn : (⟨x, hAS hxA⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
      Subtype.ext (hA.2 x hxA)
    change (Sg.normalizerMonoidHom ⟨x, hAS hxA⟩) ^ p = 1
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

theorem stmtOddCoreRankScalarGen [Finite Y] {s p : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hp : p.Prime) (hsp : s ≠ p) (Sg A : Subgroup Y) (t : Y) (m lam : ℕ) (hm : 5 ≤ 2 * m)
    (hSg : IsPGroup s Sg) (hAS : A ≤ Subgroup.normalizer (Sg : Set Y))
    (hA : IsElemAbelian p A) (htS : t ∈ Subgroup.normalizer (Sg : Set Y))
    (htA : t ∈ Subgroup.normalizer (A : Set Y)) (hlam : ¬ p ∣ lam - 1)
    (hscal : ∀ a ∈ A, t ^ m * a * (t ^ m)⁻¹ = a ^ lam)
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup Y, F ≤ A → F.relIndex A = p →
      t ^ k ∉ Subgroup.normalizer (F : Set Y))
    (hnc : ¬ A ≤ Subgroup.centralizer (Sg : Set Y)) : 4 ≤ CFSG.Open.pRank s Sg := by
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup A := @IsMulCommutative.instCommGroup _ _ hA.1
  let ψ : A →* MulAut D := φ.comp (Subgroup.inclusion hAS)
  let α : MulAut A := A.normalizerMonoidHom ⟨t, htA⟩
  have hατ : ∀ x : A, φ ⟨t, htS⟩ * ψ x = ψ (α x) * φ ⟨t, htS⟩ := fun x => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hAS x) =
      φ (Subgroup.inclusion hAS (α x)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (x : Y) = t * x * t⁻¹ * t
    group
  have hψ : ∃ x : A, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnc (le_centralizer_of_fixing hs hp hsp hAS hA hfix hall)
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hαm : ∀ x : A, (α ^ m) x = x ^ lam := fun x =>
    Subtype.ext (by
      rw [coe_normalizerMonoidHom_pow_apply htA, hscal x x.2]
      rfl)
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_four_le_card_of_scalar hsp
    (fun x => Subtype.ext (hA.2 x x.2)) hm hD hc ψ hψ hατ hαm hlam
    (fun k hk0 hkm F hF => map_pow_ne_of_index htA (horb k hk0 hkm) hF)
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end CFSG.AGLEmbedding
