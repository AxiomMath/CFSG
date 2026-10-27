module

import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.ClassTwoRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding
open scoped commutatorElement

theorem eq_one_of_pow_seven_of_card_eq {V : Type*} [Group V] [Finite V] {n : ℕ} (hn : n ≤ 5)
    (hV : Nat.card V = 3 ^ n) {σ : MulAut V} (hσ : σ ^ 7 = 1) : σ = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hG : IsPGroup 7 (Subgroup.zpowers σ) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have hmod := hG.card_modEq_card_fixedPoints V
  let C : Subgroup V := FixedPoints.subgroup (Subgroup.zpowers σ) V
  have hC : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) V) = Nat.card C := rfl
  obtain ⟨c, hc, hcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (hV ▸ Subgroup.card_subgroup_dvd_card C)
  rw [hV, hC, hcard] at hmod
  have hcn : c = n := by
    have key : ∀ n ≤ 5, ∀ c ≤ n, 3 ^ n ≡ 3 ^ c [MOD 7] → c = n := by decide
    exact key n hn c hc hmod
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hcard, hV, hcn])
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ C := htop ▸ Subgroup.mem_top v
  exact hv ⟨σ, Subgroup.mem_zpowers σ⟩

theorem mem_centralizer_of_pow_seven {Y : Type*} [Group Y] [Finite Y] {T : Subgroup Y}
    (hT : IsPGroup 3 T) (hrank : Open.pRank 3 T ≤ 3) {x : Y} (hx : x ^ 7 = 1)
    (hxT : x ∈ Subgroup.normalizer (T : Set Y)) : x ∈ Subgroup.centralizer (T : Set Y) := by
  let θ : MulAut T := T.normalizerMonoidHom ⟨x, hxT⟩
  have hθ7 : θ ^ 7 = 1 := by
    change (T.normalizerMonoidHom ⟨x, hxT⟩) ^ 7 = 1
    rw [← map_pow, show (⟨x, hxT⟩ : Subgroup.normalizer (T : Set Y)) ^ 7 = 1 from Subtype.ext hx,
      map_one]
  suffices hθ : θ = 1 by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut T => ((f ⟨y, hy⟩ : T) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rcases subsingleton_or_nontrivial T with hsub | hnt
  · exact MulEquiv.ext fun t => Subsingleton.elim _ _
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by decide) hT
  have hD3 : ∀ d : D, d ^ 3 = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hD3p : IsPGroup 3 D := fun d => ⟨1, by rw [pow_one]; exact hD3 d⟩
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : T), (y : T)⁆ ∈ ⁅D, (⊤ : Subgroup T)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : T) z.2)
  have hrD : Open.pRank 3 D ≤ 3 :=
    (CFSG.SectionRank.pRank_le_map (by decide) T.subtype T.subtype_injective D).trans
      ((CFSG.SectionRank.pRank_mono (by decide) (Subgroup.map_subtype_le D)).trans hrank)
  have hquot : Nat.card (D ⧸ Subgroup.center D) < 3 ^ 5 := by
    by_contra h
    have h4 := four_le_pRank_of_classTwo Nat.prime_three hexp hc (not_lt.mp h)
    omega
  obtain ⟨n, hn⟩ := (hD3p.to_quotient (Subgroup.center D)).exists_card_eq
  have hn5 : n ≤ 5 := by
    rw [hn] at hquot
    exact ((Nat.pow_lt_pow_iff_right (by decide)).mp hquot).le
  obtain ⟨c, hc'⟩ := (hD3p.to_subgroup (Subgroup.center D)).exists_card_eq
  have hc3 : c ≤ 3 :=
    (CFSG.SectionRank.le_pRank_of_injective (A := Subgroup.center D) (by decide)
      (fun a b => mul_comm' a b) (fun e => Subtype.ext (hD3 e)) hc'
      (T.subtype.comp (D.subtype.comp (Subgroup.center D).subtype))
      (T.subtype_injective.comp (D.subtype_injective.comp
        (Subgroup.center D).subtype_injective)) (by
        rintro _ ⟨e, rfl⟩
        exact ((e : D) : T).2)).trans hrank
  let ρ : MulAut D := MulAut.characteristic D θ
  have hρ7 : ρ ^ 7 = 1 := by rw [← map_pow, hθ7, map_one]
  have hρZ : ∀ z ∈ Subgroup.center D, ρ z = z := by
    have h1 : MulAut.characteristic (Subgroup.center D) ρ = 1 :=
      eq_one_of_pow_seven_of_card_eq (by omega) hc' (by rw [← map_pow, hρ7, map_one])
    intro z hz
    exact congrArg (fun f : MulAut (Subgroup.center D) => ((f ⟨z, hz⟩ : Subgroup.center D) : D)) h1
  have hρ : ∀ d : D, ρ d = d := by
    have h1 : quotientCenterAut ρ = 1 :=
      eq_one_of_pow_seven_of_card_eq hn5 hn (by rw [← map_pow, hρ7, map_one])
    intro d
    refine apply_eq_of_mk_apply_eq (s := 3) (p := 7) (by decide) hD3 hρ7 hρZ ?_
    rw [← quotientCenterAut_apply_mk, h1]
    rfl
  have hθfix : θ ∈ fixingSubgroup (MulAut T) (D : Set T) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact congrArg (fun d : D => (d : T)) (hρ ⟨y, hy⟩)
  obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
  have hθk : θ ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθ7⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by decide)), pow_one] at h1

end CFSG.AGLEmbeddingD2
