module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  full_central_kernel_involution_fixed_component_correspondence)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel)

@[expose] def ModelIn (ℓ : ℕ) (T : Set (StatedLieTag × ℕ × ℕ)) (L : Type) [Group L] : Prop :=
  ∃ t n f, (t, n, f) ∈ T ∧ CentralModel ℓ t n f L

theorem ModelIn.of_centralModel {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)} {t : StatedLieTag}
    {n f : ℕ} (hT : (t, n, f) ∈ T) {L : Type} [Group L] (h : CentralModel ℓ t n f L) :
    ModelIn ℓ T L :=
  ⟨t, n, f, hT, h⟩

theorem ModelIn.of_mulEquiv {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)} {L M : Type} [Group L]
    [Group M] (e : L ≃* M) (h : ModelIn ℓ T M) : ModelIn ℓ T L := by
  obtain ⟨t, n, f, hT, h⟩ := h
  exact ⟨t, n, f, hT, h.of_mulEquiv e⟩

theorem ModelIn.of_centerQuotient_equiv {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)} {L M : Type}
    [Group L] [Group M] (e : L ⧸ center L ≃* M ⧸ center M) (h : ModelIn ℓ T M) :
    ModelIn ℓ T L := by
  obtain ⟨t, n, f, hT, h⟩ := h
  exact ⟨t, n, f, hT, h.of_centerQuotient_equiv e⟩

theorem ModelIn.mono {ℓ : ℕ} {T T' : Set (StatedLieTag × ℕ × ℕ)} (hT : T ⊆ T') {L : Type}
    [Group L] (h : ModelIn ℓ T L) : ModelIn ℓ T' L := by
  obtain ⟨t, n, f, h₁, h⟩ := h
  exact ⟨t, n, f, hT h₁, h⟩

theorem modelIn_of_component_equiv {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)} {G H : Type}
    [Group G] [Group H] (e : G ≃* H) (h : ∀ N : Subgroup H, IsComponent N → ModelIn ℓ T N)
    {M : Subgroup G} (hM : IsComponent M) : ModelIn ℓ T M :=
  (h _ (LocalCores.isComponent_map_mulEquiv e hM)).of_mulEquiv
    (M.equivMapOfInjective e.toMonoidHom e.injective)

theorem component_cases_of_centralLift {P S : Type} [Group P] [Group S] [Finite P]
    {π : P →* S} (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P}
    {α : MulAut S} (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s)
    (hcomm : ∀ x, π (a x) = α (π x)) {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)}
    (h : ∀ Q : Subgroup (fixedSubgroup a), IsComponent Q →
      (∃ w ∈ Q, (∀ y ∈ Q, w * y = y * w) ∧ w * w = 1 ∧ π w ≠ 1) ∨ ModelIn ℓ T Q)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) :
    (∃ z ∈ L, (∀ y ∈ L, z * y = y * z) ∧ z * z = 1 ∧ z ≠ 1) ∨ ModelIn ℓ T L := by
  obtain ⟨-, -, -, hlift, -⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  set R := L.map (fixedSubgroup α).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup α) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup α) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQR, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  set Q := ⁅R.comap π, R.comap π⁆ with hQdef
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  rcases h _ hQ' with ⟨w, hwQ, hwc, hww, hw1⟩ | hm
  ·
    left
    have hwQ' : ((w : fixedSubgroup a) : P) ∈ Q := hwQ
    set t : S := π (w : P) with htdef
    have htR : t ∈ R := hQR ▸ Subgroup.mem_map_of_mem _ hwQ'
    obtain ⟨z, hzL, hzt0⟩ := Subgroup.mem_map.1 htR
    have hzt : (z : S) = t := hzt0
    refine ⟨z, hzL, fun y hy => ?_, ?_, ?_⟩
    ·
      have hyR : (y : S) ∈ R := Subgroup.mem_map_of_mem _ hy
      rw [← hQR] at hyR
      obtain ⟨u, huQ, huy⟩ := Subgroup.mem_map.1 hyR
      have huB : u ∈ fixedSubgroup a := hQ.1 huQ
      have hu' : (⟨u, huB⟩ : fixedSubgroup a) ∈ Q.subgroupOf (fixedSubgroup a) := huQ
      have h1 := hwc _ hu'
      have h2 := congrArg (fun g : fixedSubgroup a => π (g : P)) h1
      simp only [Subgroup.coe_mul, map_mul] at h2
      apply Subtype.ext
      change (z : S) * y = y * z
      rw [hzt, ← huy]
      exact h2
    ·
      apply Subtype.ext
      change (z : S) * z = 1
      rw [hzt, htdef, ← map_mul]
      change π ((w * w : fixedSubgroup a) : P) = 1
      rw [hww]
      exact map_one _
    ·
      intro h1
      apply hw1
      rw [← hzt, h1]
      rfl
  ·
    right
    exact ((((hm.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm).of_centerQuotient_equiv
      eQR.symm).of_mulEquiv
        (L.equivMapOfInjective (fixedSubgroup α).subtype (subtype_injective _))))

end CFSG.ComponentClassification.CatLeafProof.X10Lin
