module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219

open Subgroup CFSG.RankThree.PartTwo.Sec21
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_conj_mem_center_of_isCentral218 [Finite G] {P₀ : Subgroup G}
    (hP₀ : Nat.card P₀ = 3 ^ (Nat.card G).factorization 3) {x : G}
    (hx : IsCentral218 (⊤ : Subgroup G) x) :
    ∃ g : G, g⁻¹ * x * g ∈ P₀ ⊓ centralizer (P₀ : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, ⟨Q, hQ⟩, hxS⟩ := hx
  have hxmem : x ∈ S ∧ ∀ t ∈ S, t * x = x * t := by
    obtain ⟨s, hsZ, rfl⟩ := mem_map.mp hxS
    exact ⟨s.2, fun t ht => congrArg Subtype.val (mem_center_iff.mp hsZ ⟨t, ht⟩)⟩
  obtain ⟨hsS, hscomm⟩ := hxmem
  have hScard : Nat.card S = 3 ^ (Nat.card G).factorization 3 := by
    rw [← hQ, card_map_of_injective (⊤ : Subgroup G).subtype_injective,
      Sylow.card_eq_multiplicity, Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv]
  let S' : Sylow 3 G := Sylow.ofCard S hScard
  let P' : Sylow 3 G := Sylow.ofCard P₀ hP₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' S'
  have hSg : S = MulAut.conj g • P₀ := by
    have := congrArg (fun T : Sylow 3 G => (T : Subgroup G)) hg
    simpa [S', P', Sylow.coe_subgroup_smul] using this.symm
  refine ⟨g, mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [hSg, mem_smul_pointwise_iff_exists] at hsS
    obtain ⟨p, hp, hps⟩ := hsS
    rw [← hps, MulAut.smul_def, MulAut.conj_apply]
    simpa [mul_assoc] using hp
  · rw [mem_centralizer_iff]
    intro p hp
    have hgp : g * p * g⁻¹ ∈ S := by
      rw [hSg, mem_smul_pointwise_iff_exists]
      exact ⟨p, hp, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    have h := hscomm _ hgp
    calc p * (g⁻¹ * x * g) = g⁻¹ * ((g * p * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * p * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * p := by group

noncomputable def centralizerConjEquiv (g y : G) :
    centralizer ({g * y * g⁻¹} : Set G) ≃* centralizer ({y} : Set G) :=
  (MulEquiv.subgroupCongr (by
      ext c
      simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hc
        refine ⟨g⁻¹ * c * g, ?_, by rw [MulAut.conj_apply]; group⟩
        calc g⁻¹ * c * g * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * c) * g := by rw [hc]
          _ = y * (g⁻¹ * c * g) := by group
      · rintro ⟨d, hd, rfl⟩
        rw [MulAut.conj_apply]
        calc g * d * g⁻¹ * (g * y * g⁻¹) = g * (d * y) * g⁻¹ := by group
          _ = g * (y * d) * g⁻¹ := by rw [hd]
          _ = g * y * g⁻¹ * (g * d * g⁻¹) := by group :
      centralizer ({g * y * g⁻¹} : Set G) =
        (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom)).trans
    ((centralizer ({y} : Set G)).equivMapOfInjective _ (MulAut.conj g).injective).symm

theorem map_center_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X).map e.toMonoidHom = center Y := by
  ext y
  simp only [mem_map, MulEquiv.coe_toMonoidHom, mem_center_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, hx v]
  · intro hy
    refine ⟨e.symm y, fun v => e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply, hy (e v)]

theorem isTripleCover_of_mulEquiv {X X' Y : Type*} [Group X] [Group X'] [Group Y] (e : X ≃* X')
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover X' Y) :
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover X Y := by
  obtain ⟨hc, ⟨q⟩⟩ := h
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e (map_center_mulEquiv e)).trans q⟩⟩
  rw [← hc, ← map_center_mulEquiv e, card_map_of_injective e.injective]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219
