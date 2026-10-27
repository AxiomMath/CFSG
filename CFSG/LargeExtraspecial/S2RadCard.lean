module

public import CFSG.LargeExtraspecial.S2SixAut
public import CFSG.LargeExtraspecial.S2SixSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem natCard_submodule (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem card_radFix {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {p : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0)
    (hp : q p = 0) : Nat.card (radFix q F p) = 2 ^ (2 * m - 2) := by
  obtain ⟨p₁, hp₁F, -, hpp₁⟩ := exists_hyperbolic_partner hq hF hpF hp0 hp
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  let ψ : perp q K → radFix q F p := fun v => ⟨eichler q p v, (mem_radFix_iff hq hp0 hp hpF).mpr
    ⟨v, (mem_perp_sup_span_pair.mp v.2).1, (mem_perp_sup_span_pair.mp v.2).2.1, rfl⟩⟩
  have hbij : Function.Bijective ψ := by
    refine ⟨fun v w h => Subtype.ext (eq_of_eichler_eq hp hpp₁ v.2 w.2
      (congrArg Subtype.val h)), fun t => ?_⟩
    obtain ⟨u, hu, htu⟩ := exists_eq_eichler_perp hq hpF hp0 hp hpp₁ t.2
    exact ⟨⟨u, hu⟩, Subtype.ext htu.symm⟩
  rw [← Nat.card_eq_of_bijective ψ hbij, natCard_submodule]
  congr 1
  omega

theorem card_spRadFix {f : BilinForm (ZMod 2) V} (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {m : ℕ}
    (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m) {p : V} (hpF : p ∈ spPerp f F)
    (hp0 : p ≠ 0) : Nat.card (spRadFix f F p) = 2 ^ (2 * m - 1) := by
  obtain ⟨p₁, hp₁F, hpp₁⟩ := sp_exists_partner hf hnd hF hpF hp0
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
    finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  let ψ : spPerp f K × ZMod 2 → spRadFix f F p := fun x =>
    ⟨spSiegel f hf p x.1 x.2, (mem_spRadFix_iff hf hnd hp0 hpF).mpr
      ⟨x.1, (mem_spPerp_sup_span_pair.mp x.1.2).1, (mem_spPerp_sup_span_pair.mp x.1.2).2.1, x.2,
        rfl⟩⟩
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => ?_, fun t => ?_⟩
    · obtain ⟨h1, h2⟩ := sp_eq_of_spSiegel_eq hf hpp₁ x.1.2 y.1.2 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h1) h2
    · obtain ⟨u, hu, c, htu⟩ := sp_exists_eq_spSiegel_perp hf hnd hpF hp0 hpp₁ t.2
      exact ⟨(⟨u, hu⟩, c), Subtype.ext htu.symm⟩
  rw [← Nat.card_eq_of_bijective ψ hbij, Nat.card_prod, natCard_submodule, Nat.card_zmod,
    ← pow_succ]
  congr 1
  have : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hdim
      exact absurd (Submodule.finrank_eq_zero.mp hdim ▸ hpF) (by
        rw [Submodule.mem_bot]
        exact hp0)
    · exact h
  omega

end S2

end CFSG.LargeExtraspecial
