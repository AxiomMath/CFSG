module

public import CFSG.CharacterTheory.DihedralTIFusion.InducedCharacters
public import CFSG.CharacterTheory.DihedralTIFusion.DihedralNormalizer

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed TwoRankLowerBound.Helpers

variable {G : Type} [Group G] {W : Subgroup G} {u : G}

theorem mem_normalizer_of_eq_sup
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    u ∈ Subgroup.normalizer (W : Set G) := by
  rw [hnormalizer]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem mem_or_mul_mem_of_mem_normalizer (hu2 : u * u = 1)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) : n ∈ W ∨ n * u ∈ W :=
  (mem_sup_zpowers_iff hu2 hinvert n).mp (hnormalizer ▸ hn)

theorem subgroupOf_normalizer_index_eq_two (hu2 : u * u = 1) (huW : u ∉ W)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    (W.subgroupOf (Subgroup.normalizer (W : Set G))).index = 2 := by
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    ⟨⟨u, mem_normalizer_of_eq_sup hnormalizer⟩, ?_, fun b => ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact huW
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact (mem_or_mul_mem_of_mem_normalizer hu2 hinvert hnormalizer b.2).symm

theorem inverts_of_mem_normalizer (hWcyclic : IsCyclic W) (hu2 : u * u = 1)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (hnW : n ∉ W) {w : G} (hw : w ∈ W) :
    n⁻¹ * w * n = w⁻¹ := by
  have : IsMulCommutative W := IsCyclic.isMulCommutative
  exact inv_conj_eq_inv_of_mul_mem (fun a ha b hb => setLike_mul_comm (s := W) ha hb) hu2
    hinvert ((mem_or_mul_mem_of_mem_normalizer hu2 hinvert hnormalizer hn).resolve_left hnW) hw

theorem subgroupOf_normalizer_free (hWcyclic : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hu2 : u * u = 1) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    ∀ n : Subgroup.normalizer (W : Set G), n ∉ W.subgroupOf (Subgroup.normalizer (W : Set G)) →
      W.subgroupOf (Subgroup.normalizer (W : Set G)) ⊓ Subgroup.centralizer ({n} : Set _) =
        ⊥ := by
  intro n hn
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hk
  rw [Subgroup.mem_subgroupOf] at hn
  rw [Subgroup.mem_bot]
  have hcomm : (k : G) * n = n * k := congrArg Subtype.val hk.2
  have hfix : (n : G)⁻¹ * k * n = k := by
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [inverts_of_mem_normalizer hWcyclic hu2 hinvert hnormalizer n.2 hn hk.1] at hfix
  have hkk : (k : G) * k = 1 := by
    calc (k : G) * k = (k : G)⁻¹ * k := by rw [hfix]
      _ = 1 := inv_mul_cancel _
  exact Subtype.ext (eq_one_of_mul_self_eq_one_of_odd hWodd hk.1 hkk)

theorem subgroupOf_isMulCommutative (hWcyclic : IsCyclic W) (H : Subgroup G) :
    IsMulCommutative (W.subgroupOf H) := by
  have : IsMulCommutative W := IsCyclic.isMulCommutative
  exact ⟨⟨fun a b => Subtype.ext (Subtype.ext (setLike_mul_comm (s := W)
    (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩

theorem transport_mem_blocksIrr {H : Subgroup G} (hWH : W ≤ H) {μ : W → ℂ}
    (hμ : μ ∈ BlocksIrr W \ {1}) :
    (fun x : W.subgroupOf H => μ ⟨x.1.1, x.2⟩) ∈ BlocksIrr (W.subgroupOf H) \ {1} := by
  let e := Subgroup.subgroupOfEquivOfLe hWH
  refine ⟨?_, fun h => hμ.2 ?_⟩
  · obtain ⟨V, _, _, _, ρ, hρ, hρμ⟩ := hμ.1
    refine ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp e.toMonoidHom,
      LyonsUnitaryFour.isIrreducible_comp_surjective e.toMonoidHom e.surjective ρ hρ, ?_⟩
    rw [← hρμ]
    rfl
  · funext w
    exact congrFun h (e.symm w)

variable [Fintype G]

theorem dihedral_induced_character (hWcyclic : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hu2 : u * u = 1) (huW : u ∉ W) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) {μ : W → ℂ}
    (hμ : μ ∈ BlocksIrr W \ {1}) :
    inducedFunction (W.subgroupOf (Subgroup.normalizer (W : Set G)))
        (fun x => μ ⟨x.1.1, x.2⟩) ∈ BlocksIrr (Subgroup.normalizer (W : Set G)) \ {1} ∧
      inducedFunction (W.subgroupOf (Subgroup.normalizer (W : Set G)))
        (fun x => μ ⟨x.1.1, x.2⟩) 1 = 2 ∧
      (∀ x : Subgroup.normalizer (W : Set G), (x : G) ∉ W →
        inducedFunction (W.subgroupOf (Subgroup.normalizer (W : Set G)))
          (fun x => μ ⟨x.1.1, x.2⟩) x = 0) ∧
      ∀ (w : G) (hw : w ∈ W),
        inducedFunction (W.subgroupOf (Subgroup.normalizer (W : Set G)))
          (fun x => μ ⟨x.1.1, x.2⟩) ⟨w, Subgroup.le_normalizer hw⟩ =
            μ ⟨w, hw⟩ + μ ⟨w⁻¹, W.inv_mem hw⟩ := by
  set K := W.subgroupOf (Subgroup.normalizer (W : Set G)) with hK
  set μ' : K → ℂ := fun x => μ ⟨x.1.1, x.2⟩ with hμ'def
  have hab := subgroupOf_isMulCommutative hWcyclic (Subgroup.normalizer (W : Set G))
  have hfree := subgroupOf_normalizer_free hWcyclic hWodd hu2 hinvert hnormalizer
  have hidx := subgroupOf_normalizer_index_eq_two hu2 huW hinvert hnormalizer
  have hμ' : μ' ∈ BlocksIrr K \ {1} := transport_mem_blocksIrr Subgroup.le_normalizer hμ
  obtain ⟨hirr, hdeg, hvan, hres, -⟩ := induced_nontrivial_character hab hfree hμ'
  set u' : Subgroup.normalizer (W : Set G) := ⟨u, mem_normalizer_of_eq_sup hnormalizer⟩
  have hu'K : u' ∉ K := by
    rw [hK, Subgroup.mem_subgroupOf]
    exact huW
  have hne : μ' ≠ conjugateNormalCharacter K μ' u' := fun h =>
    hu'K ((conjugateNormalCharacter_eq_self_iff hab hfree hμ'.1 hμ'.2 u').mp h.symm)
  have himage : Finset.univ.image (conjugateNormalCharacter K μ') =
      {μ', conjugateNormalCharacter K μ' u'} := by
    ext ν
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨n, rfl⟩
      by_cases hn : n ∈ K
      · exact Or.inl ((conjugateNormalCharacter_eq_self_iff hab hfree hμ'.1 hμ'.2 n).mpr hn)
      · refine Or.inr ((conjugateNormalCharacter_eq_iff_mem hab hfree hμ' n u').mpr ?_)
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false (fun h => hn (by simpa using K.inv_mem h)) hu'K
    · rintro (rfl | rfl)
      · exact ⟨1, conjugateNormalCharacter_one K μ'⟩
      · exact ⟨u', rfl⟩
  refine ⟨hirr, by rw [hdeg, hidx, Nat.cast_ofNat], fun x hx => hvan x ?_, fun w hw => ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hx
  · have hval := congrFun hres ⟨⟨w, Subgroup.le_normalizer hw⟩, hw⟩
    rw [himage, Finset.sum_pair hne, Pi.add_apply] at hval
    refine hval.trans (congrArg (μ ⟨w, hw⟩ + ·) ?_)
    rw [conjugateNormalCharacter_apply]
    exact congrArg μ (Subtype.ext (hinvert w hw))

omit [Fintype G] in
theorem dihedral_sign_character (hu2 : u * u = 1) (huW : u ∉ W)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    (fun x : Subgroup.normalizer (W : Set G) => if (x : G) ∈ W then (1 : ℂ) else -1) ∈
      BlocksIrr (Subgroup.normalizer (W : Set G)) \ {1} := by
  have hidx := subgroupOf_normalizer_index_eq_two hu2 huW hinvert hnormalizer
  let ε : Subgroup.normalizer (W : Set G) →* ℂ :=
    { toFun := fun x => if (x : G) ∈ W then (1 : ℂ) else -1
      map_one' := by simp [W.one_mem]
      map_mul' := fun a b => by
        have h := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
        by_cases ha : (a : G) ∈ W <;> by_cases hb : (b : G) ∈ W <;> simp [ha, hb, h] }
  refine ⟨CentralSL2.monoidHom_mem_blocksIrr ε, fun h => ?_⟩
  have hu := congrFun h ⟨u, mem_normalizer_of_eq_sup hnormalizer⟩
  simp only [huW, ↓reduceIte, Pi.one_apply] at hu
  norm_num at hu

end CFSG.DihedralTIFusion
