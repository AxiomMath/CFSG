module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem RankThreeWitness.map_mulEquiv {S T : Type*} [Group S] [Group T] [Finite S] {p : ℕ}
    [Fact p.Prime] (f : S ≃* T) {x : S} (hx : RankThreeWitness p x) :
    RankThreeWitness p (f x) := by
  rcases hx with ⟨P, hP⟩ | ⟨Q, Z, hexp, hZQ, hZc, hZ, hcomm, hcard, hxQ, hxZ⟩ |
    ⟨E, hE, hcard, hxE⟩
  · have hf : Function.Surjective f.toMonoidHom := f.surjective
    refine Or.inl ⟨P.mapSurjective hf, ?_⟩
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hP hy)
    exact Subgroup.mem_centralizer_singleton_iff.2 (by
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, h1])
  · refine Or.inr (Or.inl ⟨Q.map f.toMonoidHom, Z.map f.toMonoidHom, ?_, Subgroup.map_mono hZQ,
      ?_, ?_, ?_, ?_, ⟨x, hxQ, rfl⟩, ?_⟩)
    · rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hexp y hy, map_one]
    · rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hZc z hz y hy]
    · rw [Subgroup.card_map_of_injective f.injective, hZ]
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
      refine ⟨y * w * y⁻¹ * w⁻¹, hcomm y hy w hw, ?_⟩
      simp
    · rw [Subgroup.card_map_of_injective f.injective]
      exact hcard
    · rintro ⟨z, hz, hzx⟩
      exact hxZ (f.injective hzx ▸ hz)
  · refine Or.inr (Or.inr ⟨E.map f.toMonoidHom,
      CFSG.SectionRank.isElemAbelian_map hE _, ?_, ⟨x, hxE, rfl⟩⟩)
    rw [Subgroup.card_map_of_injective f.injective, hcard]

theorem RankThreeWitness.of_mulEquiv {S T : Type*} [Group S] [Group T] [Finite S] {p : ℕ}
    [Fact p.Prime] (f : S ≃* T) {x : S} (hx : RankThreeWitness p (f x)) :
    RankThreeWitness p x := by
  haveI : Finite T := Finite.of_equiv S f.toEquiv
  simpa using hx.map_mulEquiv f.symm

theorem RankThreeWitness.conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x y : G} (g : G) (h : g * x * g⁻¹ = y) (hx : RankThreeWitness p x) :
    RankThreeWitness p y := by
  have := hx.map_mulEquiv (MulAut.conj g)
  rwa [MulAut.conj_apply, h] at this

theorem RankThreeWitness.of_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} (g : G) (hx : RankThreeWitness p (g * x * g⁻¹)) : RankThreeWitness p x :=
  hx.conj_eq g⁻¹ (by group)

theorem RankThreeWitness.pow_of_sylow_le {G : Type*} [Group G] {p : ℕ} {z : G}
    (P : Sylow p G) (hP : (P : Subgroup G) ≤ centralizer ({z} : Set G)) (c : ℕ) :
    RankThreeWitness p (z ^ c) := by
  refine Or.inl ⟨P, fun g hg => ?_⟩
  have hz : Commute g z := Subgroup.mem_centralizer_singleton_iff.1 (hP hg)
  exact Subgroup.mem_centralizer_singleton_iff.2 (hz.pow_right c).eq

theorem RankThreeWitness.of_mem_of_not_mem_zpowers {G : Type*} [Group G] {p : ℕ}
    {Q : Subgroup G} {z : G} (hexp : ∀ y ∈ Q, y ^ p = 1) (hzQ : z ∈ Q)
    (hzc : ∀ y ∈ Q, z * y = y * z) (hzo : orderOf z = p)
    (hcomm : ∀ y ∈ Q, ∀ w ∈ Q, y * w * y⁻¹ * w⁻¹ ∈ zpowers z) (hcard : p ^ 5 ≤ Nat.card Q)
    {y : G} (hy : y ∈ Q) (hyz : y ∉ zpowers z) : RankThreeWitness p y := by
  refine Or.inr (Or.inl ⟨Q, zpowers z, hexp, (Subgroup.zpowers_le).2 hzQ, ?_, ?_, hcomm, hcard,
    hy, hyz⟩)
  · rintro _ ⟨k, rfl⟩ w hw
    exact ((Commute.zpow_left (show Commute z w from hzc w hw) k)).eq
  · rw [Nat.card_zpowers, hzo]

end CFSG.LocalAnalysis.RankFourTheoremC
