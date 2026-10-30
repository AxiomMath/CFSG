module

public import CFSG.LieType.Ree.SmallReeThreeDerived
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeThreeModel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28

open Subgroup

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {A : Subgroup G} [Finite A] {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card A ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : A.map (MulAut.conj g).toMonoidHom = A := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨a, ha, hax⟩ := hx
  have : a = x := by
    have h2 : g * a * g⁻¹ = g * x * g⁻¹ := hax
    exact mul_left_cancel (mul_right_cancel h2)
  rw [← this]
  exact ha

theorem card_eq_eight_of_normalized {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 504)
    {A : Subgroup G} {g : G} (hg7 : orderOf g = 7) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAg : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hAg' : ∃ x ∈ A, g * x * g⁻¹ ≠ x) :
    Nat.card A = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hgN : g ∈ normalizer (A : Set G) := mem_normalizer_of_conj_mem hAg
  have hApg : IsPGroup 2 A := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hA2 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hApg
  have hdvd : Nat.card A ∣ 504 := hG ▸ Subgroup.card_subgroup_dvd_card A
  have hn3 : n ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h16 : 2 ^ 4 ∣ 504 := (Nat.pow_dvd_pow 2 hlt).trans (hn ▸ hdvd)
    norm_num at h16
  let φ : ↥(normalizer (A : Set G)) →* Equiv.Perm ↥A :=
    (MulAut.toPerm ↥A).comp A.normalizerMonoidHom
  have hφne : φ ⟨g, hgN⟩ ≠ 1 := by
    obtain ⟨x, hx, hxg⟩ := hAg'
    intro h1
    apply hxg
    have := congrArg (fun f : Equiv.Perm ↥A => ((f ⟨x, hx⟩ : ↥A) : G)) h1
    exact this
  have hφ7 : orderOf (φ ⟨g, hgN⟩) = 7 := by
    have hd : orderOf (φ ⟨g, hgN⟩) ∣ 7 := by
      have := orderOf_map_dvd φ (⟨g, hgN⟩ : ↥(normalizer (A : Set G)))
      rwa [Subgroup.orderOf_mk, hg7] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφne
    · exact h
  have h7 : 7 ∣ (Nat.card A).factorial := by
    have := orderOf_dvd_natCard (φ ⟨g, hgN⟩)
    rwa [hφ7, Nat.card_perm] at this
  have hle : 7 ≤ Nat.card A := (Nat.Prime.dvd_factorial (by norm_num)).mp h7
  rw [hn] at hle ⊢
  interval_cases n <;> simp_all

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.SignalizerFunctorTheorem.CatalogBridge


theorem reeL28_sub {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (h8 : ∀ S : Sylow 2 ↥(ReeTag.G2.reeGamma K a),
      Nat.card (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) = 8) :
    ∃ (D : Subgroup ↥(ReeTag.G2.reeGamma K a)) (S : Sylow 2 ↥(ReeTag.G2.reeGamma K a))
      (g : ↥(ReeTag.G2.reeGamma K a)), IsSimpleGroup D ∧ Nat.card D = 504 ∧
        (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) ≤ D ∧ g ∈ D ∧ orderOf g = 7 ∧
        g ∈ normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
          Set ↥(ReeTag.G2.reeGamma K a)) := by
  classical
  haveI : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Finite ↥(ReeTag.G2.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨e⟩ := nonempty_srD_mulEquiv (K := K) hw₀
  have hDΓ : Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ≤
      ReeTag.G2.reeGamma K a := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ReeTag.g2U₀_mem_reeGamma K a
    · exact ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := a) hw₀
  let ι : srP →* ↥(ReeTag.G2.reeGamma K a) := (Subgroup.inclusion hDΓ).comp e.symm.toMonoidHom
  have hι : Function.Injective ι := (Subgroup.inclusion_injective hDΓ).comp e.symm.injective
  obtain ⟨g, -, A, hg, -, -, hA2, hAg, hAg'⟩ := srP_data
  have hA8 : Nat.card A = 8 := card_eq_eight_of_normalized card_srP hg hA2 hAg hAg'
  have hgN : g ∈ normalizer (A : Set srP) := mem_normalizer_of_conj_mem hAg
  have hA'8 : Nat.card (A.map ι) = 8 := by
    rw [Subgroup.card_map_of_injective hι, hA8]
  have hA'pg : IsPGroup 2 (A.map ι) := IsPGroup.of_card (n := 3) (by rw [hA'8]; norm_num)
  obtain ⟨S, hS⟩ := hA'pg.exists_le_sylow
  have hSeq : A.map ι = (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :=
    Subgroup.eq_of_le_of_card_ge hS (by rw [h8 S, hA'8])
  refine ⟨ι.range, S, ι g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MonoidHom.ofInjective hι).isSimpleGroup_congr.mp isSimpleGroup_srP
  · exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm.trans card_srP
  · rw [← hSeq]
    exact Subgroup.map_le_range ι A
  · exact ⟨g, rfl⟩
  · rw [orderOf_injective ι hι g]
    exact hg
  · rw [← hSeq]
    exact Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι hgN)

end Ree

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28
