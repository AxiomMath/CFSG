module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Strings
public import CFSG.LieType.Chevalley.AllRootWeylConjugation

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section WeylConj


variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem allRootWeylSign_cast_eq_one {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank) :
    ((allRootWeylSign τ i α : ℤ) : K) = 1 := by
  have h := allRootWeylSign_eq hα i
  set F := rootOperatorFamily τ
  have h1 : F.pinnedFamilySign α * F.pinnedFamilySign α = 1 := by
    rcases F.pinnedFamilySign_eq α with h | h <;> rw [h] <;> norm_num
  have h2 : F.sign i ⟨α, hα⟩ * F.sign i ⟨α, hα⟩ = 1 := F.sign_mul_self i _
  have h3 : F.pinnedFamilySign (reflect τ i α) * F.pinnedFamilySign (reflect τ i α) = 1 := by
    rcases F.pinnedFamilySign_eq (reflect τ i α) with h | h <;> rw [h] <;> norm_num
  have hsq : allRootWeylSign τ i α * allRootWeylSign τ i α = 1 := by
    rw [h]
    calc _ = (F.pinnedFamilySign α * F.pinnedFamilySign α) * (F.sign i ⟨α, hα⟩ * F.sign i ⟨α, hα⟩) *
        (F.pinnedFamilySign (reflect τ i α) * F.pinnedFamilySign (reflect τ i α)) := by ring
      _ = 1 := by rw [h1, h2, h3]; norm_num
  have h4 : (((allRootWeylSign τ i α : ℤ) : K) - 1) ^ 2 = 0 := by
    have : (((allRootWeylSign τ i α * allRootWeylSign τ i α : ℤ)) : K) = 1 := by
      rw [hsq]; simp
    push_cast at this
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    calc (((allRootWeylSign τ i α : ℤ) : K) - 1) ^ 2
        = ((allRootWeylSign τ i α : ℤ) : K) * ((allRootWeylSign τ i α : ℤ) : K) - 2 *
          ((allRootWeylSign τ i α : ℤ) : K) + 1 := by ring
      _ = 0 := by rw [this, h22]; simp [one_add_one_eq_two, h22]
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h4)

theorem nC_conj_pinnedX (i : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : K) :
    weylElt τ K i 1 * pinnedX τ K β c * (weylElt τ K i 1)⁻¹ = pinnedX τ K (reflect τ i β) c := by
  rw [weylElt_one_mul_pinnedX_mul_inv K i hβ c, allRootWeylSign_cast_eq_one hβ i, one_mul]

variable [Finite K]

theorem nWC_conj_pinnedX (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (w : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : K) :
    IsRoot τ (w • β) ∧
      ((nWC τ K w : adjointGroup τ K) : ModGL τ K) * pinnedX τ K β c *
        ((nWC τ K w : adjointGroup τ K) : ModGL τ K)⁻¹ = pinnedX τ K (w • β) c := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  revert β c
  induction ω with
  | nil =>
    intro β hβ c
    have h1 : nWC τ K ((coxeterSystem τ).wordProd []) = 1 := (chevDatum τ K 2 hw).nW_one
    rw [(coxeterSystem τ).wordProd_nil, one_smul]
    refine ⟨hβ, ?_⟩
    rw [(coxeterSystem τ).wordProd_nil] at h1
    rw [h1]; simp
  | cons s ω ih =>
    intro β hβ c
    have hred : (coxeterSystem τ).IsReduced ω := by simpa using hω.drop 1
    have hlen : (coxeterSystem τ).length ((coxeterSystem τ).simple s * (coxeterSystem τ).wordProd ω) =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) + 1 := by
      rw [← (coxeterSystem τ).wordProd_cons, hω.eq, hred.eq, List.length_cons]
    obtain ⟨hroot, hconj⟩ := ih hred hβ c
    have hnW : nWC τ K ((coxeterSystem τ).wordProd (s :: ω)) =
        nC τ K s * nWC τ K ((coxeterSystem τ).wordProd ω) := by
      rw [(coxeterSystem τ).wordProd_cons]
      exact (chevDatum τ K 2 hw).nW_simple_mul _ _ hlen
    have hsm : (coxeterSystem τ).wordProd (s :: ω) • β =
        reflect τ s ((coxeterSystem τ).wordProd ω • β) := by
      rw [(coxeterSystem τ).wordProd_cons, mul_smul, simple_smul]
    rw [hsm]
    refine ⟨IsRoot.reflect s hroot, ?_⟩
    rw [hnW, Subgroup.coe_mul]
    have : ((nC τ K s : adjointGroup τ K) : ModGL τ K) = weylElt τ K s 1 := rfl
    rw [this]
    calc weylElt τ K s 1 * ((nWC τ K ((coxeterSystem τ).wordProd ω) : adjointGroup τ K) : ModGL τ K) *
          pinnedX τ K β c * (weylElt τ K s 1 *
            ((nWC τ K ((coxeterSystem τ).wordProd ω) : adjointGroup τ K) : ModGL τ K))⁻¹
        = weylElt τ K s 1 * (((nWC τ K ((coxeterSystem τ).wordProd ω) : adjointGroup τ K) :
            ModGL τ K) * pinnedX τ K β c *
          ((nWC τ K ((coxeterSystem τ).wordProd ω) : adjointGroup τ K) : ModGL τ K)⁻¹) *
            (weylElt τ K s 1)⁻¹ := by group
      _ = _ := by rw [hconj]; exact nC_conj_pinnedX s hroot c

theorem nWC_commute_rankOne (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (w : WeylGroup τ) (s : Fin τ.rank)
    (hws : w • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1) (g : SL(2, K)) :
    nWC τ K w * rankOne τ K s g = rankOne τ K s g * nWC τ K w := by
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  set S : Subgroup (SL(2, K)) :=
    (Subgroup.centralizer ({nWC τ K w} : Set (adjointGroup τ K))).comap (rankOne τ K s) with hS
  have hmem : ∀ x : SL(2, K), x ∈ S ↔ nWC τ K w * rankOne τ K s x = rankOne τ K s x * nWC τ K w := by
    intro x
    simp only [hS, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
  have hroot : IsRoot τ (Pi.single s 1 : Fin τ.rank → ℤ) := isRoot_single τ s
  have hroot' : IsRoot τ (-Pi.single s 1 : Fin τ.rank → ℤ) := isRoot_neg_single τ s
  have hcomm : ∀ (β : Fin τ.rank → ℤ), IsRoot τ β → w • β = β → ∀ c : K,
      ((nWC τ K w : adjointGroup τ K) : ModGL τ K) * pinnedX τ K β c =
        pinnedX τ K β c * ((nWC τ K w : adjointGroup τ K) : ModGL τ K) := by
    intro β hβ hwβ c
    have := (nWC_conj_pinnedX hw w hβ c).2
    rw [hwβ] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c ∈ S
      have e : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uElt c := rfl
      rw [e, hmem, rankOne_u]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      show _ * xUnit τ K s c = xUnit τ K s c * _
      rw [← pinnedX_single]
      exact hcomm _ hroot hws c
    · show CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c ∈ S
      have e : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
      rw [e, hmem, rankOne_l]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      show _ * yUnit τ K s c = yUnit τ K s c * _
      rw [← pinnedX_neg_single]
      refine hcomm _ hroot' ?_ c
      rw [smul_neg, hws]
  have : g ∈ S := hle (by rw [hcl]; exact Subgroup.mem_top g)
  exact (hmem g).1 this

end WeylConj

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
