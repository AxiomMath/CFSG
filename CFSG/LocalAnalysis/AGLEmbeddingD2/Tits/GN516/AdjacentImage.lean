module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleImage
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Quasithin CFSG.Quasithin.B6


theorem le_of_perfect_of_two_quotient {G : Type*} [Group G] [Finite G] {L D : Subgroup G}
    (hL : ⁅L, L⁆ = L) (hn : L ≤ Subgroup.normalizer (D : Set G))
    (h2 : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ D) : L ≤ D := by
  set K : Subgroup L := D.subgroupOf L with hK
  have hKn : K.Normal := ⟨fun x hx g => by
    have := (Subgroup.mem_normalizer_iff.1 (hn g.2) (x : G)).1 hx
    simpa [hK, Subgroup.mem_subgroupOf, mul_assoc] using this⟩
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.2 hL
  have hperfQ : Group.IsPerfect (L ⧸ K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hp : IsPGroup 2 (L ⧸ K) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := h2 x x.2
    exact ⟨k, by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_subgroupOf).2 (by simpa using hk)⟩
  have : Group.IsNilpotent (L ⧸ K) := hp.isNilpotent
  have hsub : Subsingleton (L ⧸ K) := by
    by_contra hns
    have : Nontrivial (L ⧸ K) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (L ⧸ K) inferInstance
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : L) : L ⧸ K) = 1 := Subsingleton.elim _ _
  exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 h1)


theorem false_of_quasisimple_mod_image {Y A : Type*} [Group Y] [Finite Y] [Group A] [Finite A]
    (C : Subgroup Y) (N : Subgroup ↥(twoResidual C)) [N.Normal] (hN : IsPGroup 2 N)
    (hperf : commutator (↥(twoResidual C) ⧸ N) = ⊤)
    (hsimple : IsSimpleGroup ((↥(twoResidual C) ⧸ N) ⧸ Subgroup.center (↥(twoResidual C) ⧸ N)))
    (hodd : ∀ z ∈ Subgroup.center (↥(twoResidual C) ⧸ N), Odd (orderOf z))
    (P : Subgroup (↥(twoResidual C) ⧸ N)) (hP : IsPGroup 2 P)
    (hnon : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) (ρ : ↥C →* A) (S : Subgroup A)
    (hS : ∀ e : ↥C, (e : Y) ∈ twoResidual C → ρ e ∈ S)
    (hS2 : ∀ Q : Subgroup A, Q ≤ S → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    {Lf : Subgroup A} (hLf : ⁅Lf, Lf⁆ = Lf) (hne : Lf ≠ ⊥) (hLQ : Lf ≤ ρ.range) : False := by
  have hEC : twoResidual C ≤ C := twoResidual_le C
  let ψ : ↥(twoResidual C) →* A := ρ.comp (Subgroup.inclusion hEC)
  have hψS : ∀ e : ↥(twoResidual C), ψ e ∈ S := fun e => hS (Subgroup.inclusion hEC e) e.2
  have hrS : ψ.range ≤ S := by
    rintro _ ⟨e, rfl⟩
    exact hψS e
  have hab : ∀ Q : Subgroup ↥ψ.range, IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro Q hQ x hx y hy
    have hQ' : IsPGroup 2 (Q.map ψ.range.subtype) := hQ.map _
    have hle : Q.map ψ.range.subtype ≤ S := by
      rintro _ ⟨q, -, rfl⟩
      exact hrS q.2
    exact Subtype.ext (hS2 _ hle hQ' _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  have hD2 : IsPGroup 2 ↥ψ.range :=
    isPGroup_range_of_quasisimple_quotient N hN hperf hsimple hodd P hP hnon
      ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) hab
  have hnorm : ρ.range ≤ Subgroup.normalizer (ψ.range : Set A) := by
    rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨e, rfl⟩ := ha
    have hcE : (c : Y) * (e : Y) * (c : Y)⁻¹ ∈ twoResidual C :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual C c.2) (e : Y)).1 e.2
    refine ⟨⟨_, hcE⟩, ?_⟩
    simp only [ψ, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hLD : Lf ≤ ψ.range := by
    refine le_of_perfect_of_two_quotient hLf (fun x hx => hnorm (hLQ hx)) ?_
    intro x hx
    obtain ⟨c, rfl⟩ := hLQ hx
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient C (c : Y) c.2
    refine ⟨k, ⟨⟨(c : Y) ^ 2 ^ k, hk⟩, ?_⟩⟩
    simp only [ψ, MonoidHom.comp_apply]
    rw [← map_pow]
    rfl
  have hLp : IsPGroup 2 ↥Lf := hD2.to_le hLD
  have : Group.IsPerfect ↥Lf := Subgroup.isPerfect_iff.2 hLf
  have : Nontrivial ↥Lf := (Subgroup.nontrivial_iff_ne_bot Lf).2 hne
  exact Group.IsPerfect.not_isNilpotent ↥Lf hLp.isNilpotent

end CFSG.AGLEmbeddingD2.Tits.GN516
