module

public import CFSG.LargeExtraspecial.O62Native

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Code Check

theorem exists_conj_mem_of_isPGroup {G : Type*} [Group G] [Finite G] {K A P : Subgroup G}
    (hA : A ≤ K) (hP : P ≤ K) (hA2 : IsPGroup 2 A) (hP2 : IsPGroup 2 P)
    (hmax : ∀ B : Subgroup G, B ≤ K → IsPGroup 2 B → Nat.card B ≤ Nat.card A) :
    ∃ g ∈ K, ∀ x ∈ P, g⁻¹ * x * g ∈ A := by
  classical
  have hA' : IsPGroup 2 (A.subgroupOf K) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
  have hP' : IsPGroup 2 (P.subgroupOf K) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
  obtain ⟨S, hS⟩ := hA'.exists_le_sylow
  have hcardS : Nat.card (S : Subgroup K) ≤ Nat.card (A.subgroupOf K) := by
    have h1 := hmax ((S : Subgroup K).map K.subtype) (Subgroup.map_subtype_le _)
      (S.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective K.subtype_injective] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
  have hAS : A.subgroupOf K = S := Subgroup.eq_of_le_of_card_ge hS hcardS
  obtain ⟨S₂, hS₂⟩ := hP'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S S₂
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hP hx⟩ : K) ∈ (S₂ : Subgroup K) :=
    hS₂ (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hAS,
    Subgroup.mem_subgroupOf] at hxS
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hxS

theorem checkSylow_spec (minus : Bool) :
    (∀ w ∈ sylowWords minus, ∀ n ∈ w, qB minus n = true) ∧ [] ∈ sylowWords minus ∧
    (∀ a ∈ sylowWords minus, ∀ b ∈ sylowWords minus,
      ∃ c ∈ sylowWords minus, wordC c = mul (wordC a) (wordC b)) ∧
    (∀ a ∈ sylowWords minus, ∃ c ∈ sylowWords minus, wordC c = wordC a.reverse) ∧
    ((sylowWords minus).map wordC).Nodup ∧ (sylowWords minus).length = 128 ∧
    ((sylowWords minus).filter fun w => w.length % 2 == 0).length = 64 := by
  have h := checkSylow_eq_true minus
  simp only [checkSylow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem, List.mem_map] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, fun a ha b hb => ?_, fun a ha => h4 a ha, h5, h6, h7⟩
  exact h3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩

noncomputable def sylowT
    (minus : Bool) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) where
  carrier := {g | ∃ w ∈ sylowWords minus, wordProd w = g}
  one_mem' := ⟨[], (checkSylow_spec minus).2.1, wordProd_nil⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hcode⟩ := (checkSylow_spec minus).2.2.1 a ha b hb
    refine ⟨c, hc, ?_⟩
    have h1 := hasCode_wordProd c
    rw [hcode] at h1
    exact h1.eq_of_equiv ((hasCode_wordProd a).mul (hasCode_wordProd b))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc, hcode⟩ := (checkSylow_spec minus).2.2.2.1 a ha
    refine ⟨c, hc, ?_⟩
    rw [wordProd_inv]
    exact (wordProd_eq_iff _ _).mpr hcode

theorem mem_sylowT {minus : Bool} {g : V₀ ≃ₗ[ZMod 2] V₀} :
    g ∈ sylowT minus ↔ ∃ w ∈ sylowWords minus, wordProd w = g :=
  Iff.rfl

theorem sylowT_le_orthogonalGroup (minus : Bool) :
    sylowT minus ≤ O₀ minus := by
  rintro _ ⟨w, hw, rfl⟩
  exact wordProd_mem_orthogonalGroup ((checkSylow_spec minus).1 w hw)

theorem injOn_wordProd (minus : Bool) :
    Set.InjOn wordProd {w | w ∈ sylowWords minus} := by
  intro a ha b hb hab
  exact List.inj_on_of_nodup_map (checkSylow_spec minus).2.2.2.2.1 ha hb
    ((wordProd_eq_iff a b).mp hab)

theorem card_sylowT
    (minus : Bool) : Nat.card (sylowT minus) = 128 := by
  classical
  have hset : ((sylowT minus : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Set (V₀ ≃ₗ[ZMod 2] V₀)) =
      wordProd '' {w | w ∈ sylowWords minus} := by
    ext g
    simp only [SetLike.mem_coe, mem_sylowT, Set.mem_image, Set.mem_ofPred_eq]
  have hnd : (sylowWords minus).Nodup := (checkSylow_spec minus).2.2.2.2.1.of_map _
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, (injOn_wordProd minus).ncard_image,
    ← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd, (checkSylow_spec minus).2.2.2.2.2.1]

theorem finrank_V₀ : finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun _

theorem exists_conj_mem_sylowT
    {minus : Bool} {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hP : P ≤ O₀ minus) (h2 : IsPGroup 2 P) :
    ∃ g ∈ O₀ minus,
      ∀ x ∈ P, g⁻¹ * x * g ∈ sylowT minus := by
  have := finite_linearEquiv (V := V₀)
  refine exists_conj_mem_of_isPGroup (sylowT_le_orthogonalGroup minus) hP
    (IsPGroup.of_card (n := 7) (card_sylowT minus)) h2 fun B hB hB2 => ?_
  rw [card_sylowT]
  exact card_le_of_isPGroup finrank_V₀ (qModel_nondegenerate minus) hB hB2

end CFSG.LargeExtraspecial.O62
