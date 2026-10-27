module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
public import TauCeti.GroupTheory.Elementary

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
  Topology

variable {τ : Tag} {k : Type} [Field k]

theorem closedIdentityComponent_mono {H K : Subgroup (ModGL τ k)} (hHK : H ≤ K) :
    closedIdentityComponent H ≤ closedIdentityComponent K := by
  refine subset_closedIdentityComponent ?_ (closedIdentityComponent H).one_mem
    (isPointIrreducible_closedIdentityComponent H)
  exact (closedIdentityComponent_le H).trans hHK

theorem closedIdentityComponent_inf_centralizer_eq
    (C : Subgroup (ModGL τ k)) (e : ModGL τ k) :
    closedIdentityComponent (C ⊓ Subgroup.centralizer {e}) =
      closedIdentityComponent (closedIdentityComponent C ⊓ Subgroup.centralizer {e}) := by
  apply le_antisymm
  · have hD0C : closedIdentityComponent (C ⊓ Subgroup.centralizer {e}) ≤ C :=
      (closedIdentityComponent_le _).trans inf_le_left
    have hD0M : closedIdentityComponent (C ⊓ Subgroup.centralizer {e}) ≤
        closedIdentityComponent C := by
      refine subset_closedIdentityComponent ?_ (closedIdentityComponent _).one_mem
        (isPointIrreducible_closedIdentityComponent _)
      exact hD0C
    have hD0K : closedIdentityComponent (C ⊓ Subgroup.centralizer {e}) ≤
        closedIdentityComponent C ⊓ Subgroup.centralizer {e} :=
      le_inf hD0M ((closedIdentityComponent_le _).trans inf_le_right)
    exact subset_closedIdentityComponent hD0K (closedIdentityComponent _).one_mem
      (isPointIrreducible_closedIdentityComponent _)
  · exact closedIdentityComponent_mono (inf_le_inf_right _ (closedIdentityComponent_le C))

theorem isPGroup_quotient_inf_centralizer
    {p : ℕ} {C : Subgroup (ModGL τ k)} {e : ModGL τ k}
    (hC : IsPGroup p (C ⧸ (closedIdentityComponent C).subgroupOf C))
    (hK : IsPGroup p
      (↥(closedIdentityComponent C ⊓ Subgroup.centralizer {e}) ⧸
        (closedIdentityComponent (closedIdentityComponent C ⊓ Subgroup.centralizer {e})).subgroupOf
          (closedIdentityComponent C ⊓ Subgroup.centralizer {e}))) :
    IsPGroup p
      (↥(C ⊓ Subgroup.centralizer {e}) ⧸
        (closedIdentityComponent (C ⊓ Subgroup.centralizer {e})).subgroupOf
          (C ⊓ Subgroup.centralizer {e})) := by
  let D : Subgroup (ModGL τ k) := C ⊓ Subgroup.centralizer {e}
  let K : Subgroup (ModGL τ k) := closedIdentityComponent C ⊓ Subgroup.centralizer {e}
  have hK0D0 : closedIdentityComponent K = closedIdentityComponent D :=
    (closedIdentityComponent_inf_centralizer_eq C e).symm
  refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem
    (p := p) (C := (closedIdentityComponent D).subgroupOf D) ?_
  intro x
  let xC : C := ⟨(x : ModGL τ k), x.2.1⟩
  obtain ⟨j, hj⟩ := hC (QuotientGroup.mk xC)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
  have hxjM : ((x : ModGL τ k) ^ p ^ j) ∈ closedIdentityComponent C := by
    simpa using (Subgroup.mem_subgroupOf.1 hj)
  have hxjK : ((x : ModGL τ k) ^ p ^ j) ∈ K :=
    ⟨hxjM, Subgroup.pow_mem (Subgroup.centralizer {e}) x.2.2 (p ^ j)⟩
  let xK : K := ⟨(x : ModGL τ k) ^ p ^ j, hxjK⟩
  obtain ⟨m, hm⟩ := hK (QuotientGroup.mk xK)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm
  have hxjmK0 : (((x : ModGL τ k) ^ p ^ j) ^ p ^ m) ∈ closedIdentityComponent K := by
    simpa using (Subgroup.mem_subgroupOf.1 hm)
  have hxjmD0 : (((x : ModGL τ k) ^ p ^ j) ^ p ^ m) ∈ closedIdentityComponent D := by
    rwa [hK0D0] at hxjmK0
  refine ⟨j + m, ?_⟩
  rw [Subgroup.mem_subgroupOf]
  simpa [pow_add, pow_mul] using hxjmD0

theorem isPGroup_centralizer_componentGroup_of_finite
    (p : ℕ) (G E : Subgroup (ModGL τ k)) [Finite E]
    (hG : IsPGroup p (G ⧸ (closedIdentityComponent G).subgroupOf G))
    (hLocal : ∀ (s : Finset E) (e : E), e ∉ s →
      let C := G ⊓ Subgroup.centralizer ((s : Set E).image (Subtype.val : E → ModGL τ k))
      let K := closedIdentityComponent C ⊓ Subgroup.centralizer {((e : E) : ModGL τ k)}
      IsPGroup p (K ⧸ (closedIdentityComponent K).subgroupOf K)) :
    IsPGroup p
      (↥(G ⊓ Subgroup.centralizer (E : Set (ModGL τ k))) ⧸
        (closedIdentityComponent (G ⊓ Subgroup.centralizer (E : Set (ModGL τ k)))).subgroupOf
          (G ⊓ Subgroup.centralizer (E : Set (ModGL τ k)))) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let C : Finset E → Subgroup (ModGL τ k) := fun s =>
    G ⊓ Subgroup.centralizer ((s : Set E).image (Subtype.val : E → ModGL τ k))
  have hCempty : C ∅ = G := by
    dsimp only [C]
    have hcent : Subgroup.centralizer (∅ : Set (ModGL τ k)) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      simp
    rw [Finset.coe_empty, Set.image_empty, hcent, inf_top_eq]
  have hCinsert : ∀ (s : Finset E) (e : E), e ∉ s →
      C (insert e s) = C s ⊓ Subgroup.centralizer {((e : E) : ModGL τ k)} := by
    intro s e _
    have hcent : Subgroup.centralizer
          (((insert e s : Finset E) : Set E).image (Subtype.val : E → ModGL τ k)) =
        Subgroup.centralizer {((e : E) : ModGL τ k)} ⊓
          Subgroup.centralizer (((s : Finset E) : Set E).image (Subtype.val : E → ModGL τ k)) := by
      ext x
      change x ∈ Set.centralizer (((insert e s : Finset E) : Set E).image
          (Subtype.val : E → ModGL τ k)) ↔
        x ∈ Set.centralizer {((e : E) : ModGL τ k)} ∩
          Set.centralizer (((s : Finset E) : Set E).image (Subtype.val : E → ModGL τ k))
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, Set.centralizer_union]
    simp only [C, hcent, inf_assoc]
    ac_rfl
  have hInd : ∀ s : Finset E,
      IsPGroup p (C s ⧸ (closedIdentityComponent (C s)).subgroupOf (C s)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [hCempty]
        exact hG
    | insert e s he ih =>
        rw [hCinsert s e he]
        have hK := hLocal s e he
        dsimp only at hK
        exact isPGroup_quotient_inf_centralizer (C := C s) (e := ((e : E) : ModGL τ k)) ih hK
  have hEnd : C Finset.univ = G ⊓ Subgroup.centralizer (E : Set (ModGL τ k)) := by
    dsimp only [C]
    rw [Finset.coe_univ, Set.image_univ, Subtype.range_coe]
  rw [← hEnd]
  exact hInd Finset.univ

theorem isPGroup_centralizer_componentGroup_of_finite_three
    (G E : Subgroup (ModGL τ k)) [Finite E]
    (hG : IsPGroup 3 (G ⧸ (closedIdentityComponent G).subgroupOf G))
    (hLocal : ∀ (s : Finset E) (e : E), e ∉ s →
      let C := G ⊓ Subgroup.centralizer ((s : Set E).image (Subtype.val : E → ModGL τ k))
      let K := closedIdentityComponent C ⊓ Subgroup.centralizer {((e : E) : ModGL τ k)}
      IsPGroup 3 (K ⧸ (closedIdentityComponent K).subgroupOf K)) :
    IsPGroup 3
      (↥(G ⊓ Subgroup.centralizer (E : Set (ModGL τ k))) ⧸
        (closedIdentityComponent (G ⊓ Subgroup.centralizer (E : Set (ModGL τ k)))).subgroupOf
          (G ⊓ Subgroup.centralizer (E : Set (ModGL τ k)))) :=
  isPGroup_centralizer_componentGroup_of_finite 3 G E hG hLocal

end CFSG.LieType.AlgebraicGroups

end
