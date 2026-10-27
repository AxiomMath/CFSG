module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverF0

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table Subgroup

theorem card_map_mul_ker {X L : Type*} [Group X] [Group L] [Finite X] (π : X →* L)
    (S : Subgroup X) (hS : π.ker ≤ S) :
    Nat.card S = Nat.card (S.map π) * Nat.card π.ker := by
  have hsurj : Function.Surjective (π.subgroupMap S) := π.subgroupMap_surjective S
  have hk : (π.subgroupMap S).ker = π.ker.subgroupOf S := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hcard : Nat.card S = Nat.card (S.map π) * Nat.card (π.subgroupMap S).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.subgroupMap S).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv] at hcard
  exact hcard

theorem map_conj_comp {X L : Type*} [Group X] [Group L] (π : X →* L) (t : X) :
    π.comp (MulAut.conj t).toMonoidHom = (MulAut.conj (π t)).toMonoidHom.comp π := by
  ext x
  simp [MulAut.conj_apply]

theorem center_eq_zpowers_zeta {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
    (hZ : Nat.card (center X) = 3) : center X = zpowers (evalW k zw) := by
  have hne : evalW k zw ≠ 1 := by
    have := h.basisProd_ne_one (a := ![0, 0, 0, 1]) (by
      intro h0
      have := congrFun h0 3
      simp at this)
    simpa [basisProd_xB, show (1 : ZMod 3).val = 1 from rfl] using this
  have hp : Nat.Prime 3 := Nat.prime_three
  have hord : orderOf (evalW k zw) = 3 := orderOf_eq_prime h.zeta_pow_three hne
  have hle : zpowers (evalW k zw) ≤ center X := (zpowers_le).2 h.zc
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hZ, Nat.card_zpowers, hord]

theorem center_le_F0 {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
    (hZ : Nat.card (center X) = 3) : center X ≤ F0 k := by
  rw [center_eq_zpowers_zeta h hZ, zpowers_le]
  exact h.xB_mem_F0 3

theorem cover_core {X L : Type*} [Group X] [Finite X] [Group L]
    (π : X →* L) (hπ : Function.Surjective π) (hker : π.ker = center X)
    (hZ : Nat.card (center X) = 3)
    (hConj : ∀ A A' : Subgroup L, IsElementaryAbelian 3 A → IsElementaryAbelian 3 A' →
      Nat.card A = 27 → Nat.card A' = 27 → ∃ g : L, A.map (MulAut.conj g).toMonoidHom = A')
    (hNorm : ∀ A : Subgroup L, IsElementaryAbelian 3 A → Nat.card A = 27 →
      Nat.card (normalizer (A : Set L)) ≤ 1944)
    {k : Fin 6 → X} (hk : J3Pkg k) (hkz : center X ≤ Subgroup.closure (Set.range k))
    (hH : Nat.card ((Subgroup.closure (Set.range k)).map π) = 1944)
    {F : Subgroup X} (hF : IsElementaryAbelian 3 (F.map π)) (hZF : center X ≤ F)
    (hF81 : Nat.card F = 81) :
    ∃ t : X, F = F0 (fun i => t * k i * t⁻¹) ∧
      ∀ y ∈ normalizer (F : Set X),
        y ∈ Subgroup.closure (Set.range fun i => t * k i * t⁻¹) := by
  have hB81 := hk.card_F0
  have hker_F0 : π.ker ≤ F0 k := by rw [hker]; exact center_le_F0 hk hZ
  have hker_F : π.ker ≤ F := by rw [hker]; exact hZF
  have hBbar : Nat.card ((F0 k).map π) = 27 := by
    have := card_map_mul_ker π (F0 k) hker_F0
    rw [hker, hZ, hB81] at this
    omega
  have hFbar : Nat.card (F.map π) = 27 := by
    have := card_map_mul_ker π F hker_F
    rw [hker, hZ, hF81] at this
    omega
  obtain ⟨g, hg⟩ := hConj _ _ (IsElementaryAbelian.map_hom π hk.isElementaryAbelian_F0)
    hF hBbar hFbar
  obtain ⟨t, rfl⟩ := hπ g
  have hk' : J3Pkg (fun i => t * k i * t⁻¹) := hk.conj t
  set k' : Fin 6 → X := fun i => t * k i * t⁻¹ with hk'def
  have hF0 : (F0 k').map π = F.map π := by
    rw [hk'def, F0_conj, Subgroup.map_map, map_conj_comp, ← Subgroup.map_map, hg]
  have hker_F0' : π.ker ≤ F0 k' := by rw [hker]; exact center_le_F0 hk' hZ
  have hFeq : F = F0 k' := by
    have e1 : F = (F.map π).comap π := (comap_map_eq_self hker_F).symm
    have e2 : F0 k' = ((F0 k').map π).comap π := (comap_map_eq_self hker_F0').symm
    rw [e2, hF0, ← e1]
  refine ⟨t, hFeq, ?_⟩
  have hcl : Subgroup.closure (Set.range k') =
      (Subgroup.closure (Set.range k)).map (MulAut.conj t).toMonoidHom := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
  have hH'card : Nat.card ((Subgroup.closure (Set.range k')).map π) = 1944 := by
    rw [hcl, Subgroup.map_map, map_conj_comp, ← Subgroup.map_map,
      Subgroup.card_map_of_injective (MulAut.conj (π t)).injective, hH]
  have hle : (Subgroup.closure (Set.range k')).map π ≤ normalizer ((F.map π : Subgroup L) : Set L) := by
    refine (Subgroup.map_mono (hFeq ▸ hk'.closure_le_normalizer)).trans ?_
    exact Subgroup.le_normalizer_map π
  have hN := hNorm _ hF hFbar
  have : Finite L := Finite.of_surjective π hπ
  have heq := eq_of_le_of_card_ge hle (by rw [hH'card]; exact hN)
  intro y hy
  have hy' : π y ∈ normalizer ((F.map π : Subgroup L) : Set L) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hy)
  rw [← heq] at hy'
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.1 hy'
  have hcz : c⁻¹ * y ∈ center X := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
  have hzmem : c⁻¹ * y ∈ Subgroup.closure (Set.range k') := by
    rw [hcl]
    refine ⟨c⁻¹ * y, hkz hcz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := Subgroup.mem_center_iff.1 hcz t
    rw [this, mul_inv_cancel_right]
  have : y = c * (c⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ hc hzmem

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
