module

public import CFSG.Blueprint.ChevalleyWeyl
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint.Chevalley

namespace FourGroupChevalley

variable {τ : Tag} {K : Type*} [Field K]

@[expose] noncomputable def rootDiag (a : Fin τ.rank → Kˣ) : Module.End K (RootModule τ K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl i => hVec τ K i
    | Sum.inr α => ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) 1

theorem rootDiag_single_inl (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootDiag a (Finsupp.single (Sum.inl i) 1) = Finsupp.single (Sum.inl i) (1 : K) := by
  rw [rootDiag, Finsupp.linearCombination_single, one_smul]
  rfl

theorem rootDiag_single_inr (a : Fin τ.rank → Kˣ) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootDiag a (Finsupp.single (Sum.inr α) 1) =
      ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) (1 : K) := by
  rw [rootDiag, Finsupp.linearCombination_single, one_smul]

theorem end_ext_single {f g : Module.End K (RootModule τ K)}
    (h : ∀ b : Label τ, f (Finsupp.single b 1) = g (Finsupp.single b 1)) : f = g :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (h b)

theorem rootVec_eq_single {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootVec τ K α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 :=
  dite_eq_left hα

@[expose] def torusSign (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : Kˣ :=
  (-1 : Kˣ) ^ (∑ j, τ.cartan i j * α j)

theorem torusElt_single_inl (i j : Fin τ.rank) :
    (torusElt τ K i (-1) : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inl j) 1) =
      Finsupp.single (Sum.inl j) 1 :=
  torusElt_hVec i j (-1)

theorem torusElt_single_inr (i : Fin τ.rank) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    (torusElt τ K i (-1) : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr α) 1) =
      ((torusSign i α.1 : Kˣ) : K) • Finsupp.single (Sum.inr α) 1 := by
  rw [← rootVec_eq_single α.2, torusElt_rootVec i (-1) α.2]
  rfl

theorem torusSign_sq (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    ((torusSign i α : Kˣ) : K) = 1 ∨ ((torusSign i α : Kˣ) : K) = -1 := by
  rcases Int.even_or_odd (∑ j, τ.cartan i j * α j) with h | h
  · left
    rw [torusSign, h.neg_one_zpow, Units.val_one]
  · right
    rw [torusSign, h.neg_one_zpow, Units.val_neg, Units.val_one]

theorem sum_cartan_single (i k : Fin τ.rank) :
    ∑ j, τ.cartan i j * (Pi.single k (1 : ℤ) : Fin τ.rank → ℤ) j = τ.cartan i k := by
  simp [Pi.single_apply]

theorem torusElt_neg_one_mul_self (i : Fin τ.rank) :
    torusElt τ K i (-1) * torusElt τ K i (-1) = 1 := by
  rw [← torusElt_mul, neg_one_mul, neg_neg, torusElt_one]

theorem entrywise_torusElt (σ : K →+* K) (i : Fin τ.rank) :
    entrywise σ (torusElt τ K i (-1) : Module.End K (RootModule τ K)) =
      (torusElt τ K i (-1) : Module.End K (RootModule τ K)) := by
  refine end_ext_single fun b => ?_
  rw [entrywise_single]
  rcases b with j | α
  · rw [torusElt_single_inl, Finsupp.mapRange_single, map_one]
  · rw [torusElt_single_inr, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single]
    congr 1
    rcases torusSign_sq (K := K) i α.1 with h | h <;> rw [h] <;> simp

theorem rootDiag_mul_torusElt (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootDiag a * (torusElt τ K i (-1) : Module.End K (RootModule τ K)) =
      (torusElt τ K i (-1) : Module.End K (RootModule τ K)) * rootDiag a := by
  refine end_ext_single fun b => ?_
  simp only [Module.End.mul_apply]
  rcases b with j | α
  · rw [torusElt_single_inl, rootDiag_single_inl, torusElt_single_inl]
  · rw [torusElt_single_inr, map_smul, rootDiag_single_inr, map_smul, torusElt_single_inr,
      smul_comm]

theorem exists_four_of_indices (hK : ringChar K ≠ 2) (i j k₁ k₂ : Fin τ.rank)
    (h₁ : τ.cartan i k₁ % 2 = 1) (h₂ : τ.cartan j k₁ % 2 = 0) (h₃ : τ.cartan j k₂ % 2 = 1) :
    ∃ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K ∧ CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 4 ∧
      (∀ σ : K ≃+* K, ∀ g ∈ A,
        entrywise (σ : K →+* K) (g : Module.End K (RootModule τ K)) = g) ∧
      ∀ a : Fin τ.rank → Kˣ, ∀ g ∈ A,
        rootDiag a * (g : Module.End K (RootModule τ K)) = g * rootDiag a := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set s := torusElt τ K i (-1)
  set t := torusElt τ K j (-1)
  have hneg : ∀ v : RootModule τ K, v ≠ 0 → -v ≠ v := fun v hv h => hv (by
    have : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel v
    exact (smul_eq_zero.1 this).resolve_left h2)
  let e : Fin τ.rank → {v : Fin τ.rank → ℤ // IsRoot τ v} := fun k => ⟨Pi.single k 1, .basis k⟩
  have hsign : ∀ (l k : Fin τ.rank), ((torusSign l (e k).1 : Kˣ) : K) =
      if τ.cartan l k % 2 = 1 then -1 else 1 := fun l k => by
    rw [torusSign, sum_cartan_single]
    split_ifs with h
    · rw [(Int.odd_iff.2 h).neg_one_zpow, Units.val_neg, Units.val_one]
    · rw [(Int.even_iff.2 (by omega)).neg_one_zpow, Units.val_one]
  have hv : ∀ k : Fin τ.rank, (Finsupp.single (Sum.inr (e k)) 1 : RootModule τ K) ≠ 0 :=
    fun k => Finsupp.single_ne_zero.2 one_ne_zero
  have hs₁ : (s : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr (e k₁)) 1) =
      -Finsupp.single (Sum.inr (e k₁)) 1 := by
    rw [torusElt_single_inr, hsign]
    simp [h₁]
  have ht₁ : (t : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr (e k₁)) 1) =
      Finsupp.single (Sum.inr (e k₁)) 1 := by
    rw [torusElt_single_inr, hsign]
    simp [show ¬ τ.cartan j k₁ % 2 = 1 by omega]
  have ht₂ : (t : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr (e k₂)) 1) =
      -Finsupp.single (Sum.inr (e k₂)) 1 := by
    rw [torusElt_single_inr, hsign]
    simp [h₃]
  have hs1 : s ≠ 1 := fun h => hneg _ (hv k₁) (by
    rw [← hs₁, h, Units.val_one, Module.End.one_apply])
  have ht1 : t ≠ 1 := fun h => hneg _ (hv k₂) (by
    rw [← ht₂, h, Units.val_one, Module.End.one_apply])
  have hst : s ≠ t := fun h => hneg _ (hv k₁) (by rw [← hs₁, h, ht₁])
  obtain ⟨A, hAmem, hAle, hA, hAcard⟩ := FourGroup.exists_kleinFour
    (torusElt_neg_one_mul_self i) (torusElt_neg_one_mul_self j) (torusElt_mul_comm i j _ _)
    hs1 ht1 hst
  refine ⟨A, hAle _ (torusElt_mem_adjointGroup i _) (torusElt_mem_adjointGroup j _), hA, hAcard,
    fun σ g hg => ?_, fun a g hg => ?_⟩
  · rcases hAmem g hg with rfl | rfl | rfl | rfl
    · exact entrywise_one _
    · exact entrywise_torusElt _ i
    · exact entrywise_torusElt _ j
    · rw [Units.val_mul, entrywise_mul, entrywise_torusElt, entrywise_torusElt]
  · rcases hAmem g hg with rfl | rfl | rfl | rfl
    · rw [Units.val_one, mul_one, one_mul]
    · exact rootDiag_mul_torusElt a i
    · exact rootDiag_mul_torusElt a j
    · rw [Units.val_mul, ← mul_assoc, rootDiag_mul_torusElt, mul_assoc, rootDiag_mul_torusElt,
        mul_assoc]

end FourGroupChevalley

open FourGroupChevalley

theorem chevalley_coordinate_fields_fixed_four_group (τ : Tag) {K : Type*} [Field K]
    (hK : ringChar K ≠ 2) :
    ∃ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K ∧ CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 4 ∧
      (∀ σ : K ≃+* K, ∀ g ∈ A,
        entrywise (σ : K →+* K) (g : Module.End K (RootModule τ K)) = g) ∧
      ∀ a : Fin τ.rank → Kˣ, ∀ g ∈ A,
        rootDiag a * (g : Module.End K (RootModule τ K)) = g * rootDiag a := by
  cases τ with
  | G2 =>
    exact exists_four_of_indices (τ := .G2) hK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
      ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  | F4 =>
    exact exists_four_of_indices (τ := .F4) hK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
      ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  | D4 =>
    exact exists_four_of_indices (τ := .D4) hK ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨2, by decide⟩
      ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  | E6 =>
    exact exists_four_of_indices (τ := .E6) hK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
      ⟨3, by decide⟩ (by decide) (by decide) (by decide)
  | E7 =>
    exact exists_four_of_indices (τ := .E7) hK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
      ⟨3, by decide⟩ (by decide) (by decide) (by decide)
  | E8 =>
    exact exists_four_of_indices (τ := .E8) hK ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
      ⟨3, by decide⟩ (by decide) (by decide) (by decide)

theorem odd_chevalley_coordinate_fields_fixed_four_group (τ : Tag) {K : Type*} [Field K]
    [Finite K] (hK : ringChar K ≠ 2) :
    ∃ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K ∧ CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 4 ∧
      (∀ σ : K ≃+* K, ∀ g ∈ A,
        entrywise (σ : K →+* K) (g : Module.End K (RootModule τ K)) = g) ∧
      ∀ a : Fin τ.rank → Kˣ, ∀ g ∈ A,
        rootDiag a * (g : Module.End K (RootModule τ K)) = g * rootDiag a :=
  chevalley_coordinate_fields_fixed_four_group τ hK

end CFSG.LocalAnalysis.ComponentInitial
