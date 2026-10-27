module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Steinberg.Adjoint (iform iform_add_left iform_add_right iform_smul_left
  iform_smul_right iform_comm)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem single_mem_c3PerpRoots :
    ∀ i : Fin Tag.F4.rank, i ≠ ⟨0, by decide⟩ →
      iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 47) = 0 := by
  decide

theorem f4Pairing_cartan_root : ∀ k : Fin 48, ∀ i : Fin Tag.F4.rank,
    f4Pairing (Tag.F4.cartan i) (Tag.F4.rootCertificate.root k) = 0 ∨
      f4Pairing (Tag.F4.cartan i) (Tag.F4.rootCertificate.root k) = 1 ∨
      f4Pairing (Tag.F4.cartan i) (Tag.F4.rootCertificate.root k) = -1 ∨
      f4Pairing (Tag.F4.cartan i) (Tag.F4.rootCertificate.root k) = 2 ∨
      f4Pairing (Tag.F4.cartan i) (Tag.F4.rootCertificate.root k) = -2 := by
  decide

theorem eq_or_eq_neg_of_f4Pairing_cartan_eq_zero : ∀ k : Fin 48,
    f4Pairing (Tag.F4.cartan ⟨1, by decide⟩) (Tag.F4.rootCertificate.root k) = 0 →
    f4Pairing (Tag.F4.cartan ⟨2, by decide⟩) (Tag.F4.rootCertificate.root k) = 0 →
    f4Pairing (Tag.F4.cartan ⟨3, by decide⟩) (Tag.F4.rootCertificate.root k) = 0 →
      Tag.F4.rootCertificate.root k = orbitCertRoot .F4 47 ∨
        Tag.F4.rootCertificate.root k = -orbitCertRoot .F4 47 := by
  decide

theorem eq_or_eq_sub_of_iform_single_eq : ∀ k : Fin 48,
    (∀ j : Fin Tag.F4.rank, j ≠ ⟨0, by decide⟩ →
      iform (Tag.F4.rootCertificate.root k) (Pi.single j 1) =
        iform (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1)) →
      Tag.F4.rootCertificate.root k = Pi.single ⟨0, by decide⟩ 1 ∨
        Tag.F4.rootCertificate.root k = Pi.single ⟨0, by decide⟩ 1 - orbitCertRoot .F4 47 := by
  decide

theorem rootCharKernel_inter_closed {a : Fin Tag.F4.rank → Kˣ} {S : Set (Fin Tag.F4.rank → ℤ)}
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot .F4 (m • α + n • β) →
      m • α + n • β ∈ S) :
    ∀ α ∈ rootCharKernel a ∩ S, ∀ β ∈ rootCharKernel a ∩ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot .F4 (m • α + n • β) → m • α + n • β ∈ rootCharKernel a ∩ S := by
  intro α hα β hβ m n hm hn hr
  refine ⟨⟨hr, ?_⟩, hScl α hα.2 β hβ.2 m n hm hn hr⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add,
    ← Nat.cast_smul_eq_nsmul ℤ m α, ← Nat.cast_smul_eq_nsmul ℤ n β, rootChar_zsmul,
    rootChar_zsmul, hα.1.2, hβ.1.2, one_zpow, one_zpow, one_mul]

@[expose] def f4WordV : List (Fin Tag.F4.rank) := ([0, 1, 2, 1, 0, 3, 2, 0, 1] : List (Fin 4))

@[expose] def f4WordVRev : List (Fin Tag.F4.rank) := ([1, 0, 2, 3, 0, 1, 2, 1, 0] : List (Fin 4))

@[expose] noncomputable def f4WeylV : WeylGroup .F4 := (coxeterSystem .F4).wordProd f4WordV

theorem f4WeylV_inv : f4WeylV⁻¹ = (coxeterSystem .F4).wordProd f4WordVRev := by
  rw [f4WeylV, ← CoxeterSystem.wordProd_reverse]
  rfl

theorem f4WeylV_smul_single_zero :
    f4WeylV • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) = orbitCertRoot .F4 47 := by
  decide

theorem f4WeylV_inv_smul_single_zero :
    f4WeylV⁻¹ • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) =
      Pi.single ⟨0, by decide⟩ 1 - orbitCertRoot .F4 47 := by
  decide

theorem f4WeylR_smul :
    (∀ j : Fin Tag.F4.rank, j ≠ ⟨0, by decide⟩ →
      (f4WeylV * simple .F4 ⟨0, by decide⟩ * f4WeylV⁻¹) • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) =
        Pi.single j 1) ∧
    (f4WeylV * simple .F4 ⟨0, by decide⟩ * f4WeylV⁻¹) •
        (Pi.single ⟨0, by decide⟩ 1 - orbitCertRoot .F4 47 : Fin Tag.F4.rank → ℤ) =
      Pi.single ⟨0, by decide⟩ 1 := by
  decide

theorem exists_ne_zero_ne_one_of_four_le [Finite K] (hq : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · exact absurd ⟨x, hx, hx1⟩ hcon
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

section Form


theorem iform_self_bounds_F4 {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) :
    2 ≤ iform γ γ ∧ iform γ γ ≤ 4 := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hγ
  clear hγ
  revert k
  decide

theorem not_isRoot_add_of_iform_eq_zero {ρ γ : Fin Tag.F4.rank → ℤ} (hρ4 : iform ρ ρ = 4)
    (hγ : IsRoot .F4 γ) (hργ : iform ρ γ = 0) : ¬ IsRoot .F4 (ρ + γ) := by
  intro h
  have h1 := (iform_self_bounds_F4 h).2
  have h2 := (iform_self_bounds_F4 hγ).1
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm γ ρ, hρ4, hργ] at h1
  omega

end Form


@[expose] noncomputable def highestRootRankOne (K : Type) [Field K] : Subgroup (ModGL .F4 K) :=
  rootSubgroup .F4 K (orbitCertRoot .F4 47) ⊔ rootSubgroup .F4 K (-orbitCertRoot .F4 47)

theorem highestRootRankOne_le_adjointGroup : highestRootRankOne K ≤ adjointGroup .F4 K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem highestRoot_long :
    IsRoot .F4 (orbitCertRoot .F4 47) ∧ iform (orbitCertRoot .F4 47) (orbitCertRoot .F4 47) = 4 :=
  ⟨(f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1, by decide⟩

theorem rootSubgroup_le_centralizer_c3PerpLevi {ρ : Fin Tag.F4.rank → ℤ}
    (hρ : ρ = orbitCertRoot .F4 47 ∨ ρ = -orbitCertRoot .F4 47) :
    rootSubgroup .F4 K ρ ≤ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) := by
  obtain ⟨hr, hr4⟩ := highestRoot_long
  have hρroot : IsRoot .F4 ρ := by
    rcases hρ with rfl | rfl
    · exact hr
    · exact IsRoot.neg hr
  have hρ4 : iform ρ ρ = 4 := by
    rcases hρ with rfl | rfl
    · exact hr4
    · rw [iform_neg_left, iform_comm, iform_neg_left, neg_neg, hr4]
  have hργ : ∀ γ ∈ c3PerpRoots, iform ρ γ = 0 := by
    intro γ hγ
    rcases hρ with rfl | rfl
    · rw [iform_comm]
      exact hγ.2
    · rw [iform_neg_left, iform_comm, hγ.2, neg_zero]
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨d, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  exact pinnedX_commute_of_iform_eq_zero K hρroot hγ.1 (hργ γ hγ)
    (not_isRoot_add_of_iform_eq_zero hρ4 hγ.1 (hργ γ hγ)) c d

theorem highestRootRankOne_le_centralizer_c3PerpLevi :
    highestRootRankOne K ≤ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) :=
  sup_le (rootSubgroup_le_centralizer_c3PerpLevi (Or.inl rfl))
    (rootSubgroup_le_centralizer_c3PerpLevi (Or.inr rfl))

theorem xUnit_mem_c3PerpLevi {i : Fin Tag.F4.rank} (hi : i ≠ ⟨0, by decide⟩) (c : K) :
    xUnit .F4 K i c ∈ c3PerpLevi K := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (S := c3PerpRoots) ⟨isRoot_single .F4 i, single_mem_c3PerpRoots i hi⟩ c

theorem yUnit_mem_c3PerpLevi {i : Fin Tag.F4.rank} (hi : i ≠ ⟨0, by decide⟩) (c : K) :
    yUnit .F4 K i c ∈ c3PerpLevi K := by
  rw [← pinnedX_neg_single]
  exact pinnedX_mem_rootSpan (S := c3PerpRoots) ⟨IsRoot.neg (isRoot_single .F4 i), by
    rw [iform_neg_left, single_mem_c3PerpRoots i hi, neg_zero]⟩ c

theorem torusElt_mem_c3PerpLevi {i : Fin Tag.F4.rank} (hi : i ≠ ⟨0, by decide⟩) (t : Kˣ) :
    torusElt .F4 K i t ∈ c3PerpLevi K := by
  have hw : ∀ s : Kˣ, weylElt .F4 K i s ∈ c3PerpLevi K := fun s => by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (xUnit_mem_c3PerpLevi hi _) (yUnit_mem_c3PerpLevi hi _))
      (xUnit_mem_c3PerpLevi hi _)
  exact mul_mem (hw t) (hw (-1))

theorem f4Pairing_eq_zero_of_rootChar_eq_one [CharP K 2] {l : Kˣ} (hl : l ≠ 1)
    (i : Fin Tag.F4.rank) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (h : rootChar (fun j => l ^ Tag.F4.cartan i j) α = 1) :
    f4Pairing (Tag.F4.cartan i) α = 0 := by
  rw [rootChar_zpow l (Tag.F4.cartan i) α] at h
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hα
  rcases f4Pairing_cartan_root k i with h0 | h1 | h1 | h1 | h1
  · exact h0
  all_goals exact absurd h (zpow_ne_one_of_charTwo hl (by rw [h1]; norm_num))

theorem mem_rootSpan_inter_of_mem_centralizer {a : Fin Tag.F4.rank → Kˣ}
    {S : Set (Fin Tag.F4.rank → ℤ)} (hSpos : ∀ α ∈ S, IsRoot .F4 α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot .F4 (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL .F4 K} (hx : x ∈ rootSpan .F4 K S)
    (hxa : x ∈ centralizer ({rootDiagUnit .F4 a} : Set (ModGL .F4 K))) :
    x ∈ rootSpan .F4 K (rootCharKernel a ∩ S) := by
  have hfin : S.Finite := (finite_setOf_isRoot .F4).subset fun α hα => (hSpos α hα).1
  refine mem_rootSpan_inter_of_conj_eq a hfin (fun α hα => (hSpos α hα).1)
    (fun α hα hrange => bijOn_prod_pinnedX K hSpos hScl α hα hrange) hx ?_
  rw [Subgroup.mem_centralizer_iff.1 hxa _ (Set.mem_singleton _), mul_inv_cancel_right]

theorem mem_rootSubgroup_highestRoot_of_forall [CharP K 2] {l : Kˣ} (hl : l ≠ 1)
    {S : Set (Fin Tag.F4.rank → ℤ)} (hSpos : ∀ α ∈ S, IsRoot .F4 α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot .F4 (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL .F4 K}
    (hx : ∀ i : Fin Tag.F4.rank, i ≠ ⟨0, by decide⟩ →
      x ∈ rootSpan .F4 K (rootCharKernel (fun j => l ^ Tag.F4.cartan i j) ∩ S)) :
    x ∈ rootSubgroup .F4 K (orbitCertRoot .F4 47) := by
  have hcent : ∀ i : Fin Tag.F4.rank, i ≠ ⟨0, by decide⟩ →
      x ∈ centralizer ({rootDiagUnit .F4 (fun j => l ^ Tag.F4.cartan i j)} :
        Set (ModGL .F4 K)) := fun i hi =>
    rootSpan_le_centralizer _ Set.inter_subset_left (hx i hi)
  have hS₁pos : ∀ α ∈ rootCharKernel (fun j => l ^ Tag.F4.cartan ⟨1, by decide⟩ j) ∩ S,
      IsRoot .F4 α ∧ 0 < height α := fun α hα => hSpos α hα.2
  have hx₂ := mem_rootSpan_inter_of_mem_centralizer hS₁pos (rootCharKernel_inter_closed hScl)
    (hx ⟨1, by decide⟩ (by decide)) (hcent ⟨2, by decide⟩ (by decide))
  have hx₃ := mem_rootSpan_inter_of_mem_centralizer (fun α hα => hS₁pos α hα.2)
    (rootCharKernel_inter_closed (rootCharKernel_inter_closed hScl)) hx₂
    (hcent ⟨3, by decide⟩ (by decide))
  refine (iSup₂_le fun α hα => ?_ : _ ≤ rootSubgroup .F4 K (orbitCertRoot .F4 47)) hx₃
  obtain ⟨⟨hα3r, hα3⟩, ⟨-, hα2⟩, ⟨-, hα1⟩, hαS⟩ := hα
  have hpos := (hSpos α hαS).2
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hα3r
  rcases eq_or_eq_neg_of_f4Pairing_cartan_eq_zero k
      (f4Pairing_eq_zero_of_rootChar_eq_one hl _ hα3r hα1)
      (f4Pairing_eq_zero_of_rootChar_eq_one hl _ hα3r hα2)
      (f4Pairing_eq_zero_of_rootChar_eq_one hl _ hα3r hα3) with h | h
  · rw [h]
  · rw [h] at hpos
    exact absurd hpos (by decide)

theorem eq_of_pinnedX_eq_pinnedX_of_pos {δ γ : Fin Tag.F4.rank → ℤ} (hδ : IsRoot .F4 δ)
    (hγ : IsRoot .F4 γ) (hγp : 0 < height γ) {d e : K} (he : e ≠ 0)
    (h : pinnedX .F4 K δ d = pinnedX .F4 K γ e) : δ = γ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hδ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [δ, γ]
      (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hδ, hpos⟩
        · exact ⟨hγ, hγp⟩)
      (fun α => if α = δ then d else 0)
      (fun α => if α = γ then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
          Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      γ (by simp)
    simp only [Ne.symm hne, ↓reduceIte] at hL
    exact he hL.symm
  · have hneg' : pinnedX .F4 K δ d ∈ negUnipotent .F4 K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ height α < 0}) ⟨hδ, hneg⟩ d
    have hB : pinnedX .F4 K δ d ∈ borelGroup .F4 K := by
      rw [h]
      exact Subgroup.mem_sup_right
        (pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α}) ⟨hγ, hγp⟩ e)
    have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, h] at h0
    exact he (pinnedX_injective .F4 K _ (h0.trans (pinnedX_zero .F4 K _).symm))

theorem map_conj_rankOne_single_zero :
    (rootSubgroup .F4 K (Pi.single ⟨0, by decide⟩ 1) ⊔
        rootSubgroup .F4 K (-Pi.single ⟨0, by decide⟩ 1)).map
      (MulAut.conj (canonicalRep (coxeterSystem .F4) K f4WeylV)).toMonoidHom =
      highestRootRankOne K := by
  rw [Subgroup.map_sup, (canonical_weyl_root_transport .F4 K).2.1 _ _ (isRoot_single .F4 _),
    (canonical_weyl_root_transport .F4 K).2.1 _ _ (IsRoot.neg (isRoot_single .F4 _)), smul_neg,
    f4WeylV_smul_single_zero]
  rfl

theorem weylElt_mem_rankOne (i : Fin Tag.F4.rank) (t : Kˣ) :
    weylElt .F4 K i t ∈
      rootSubgroup .F4 K (Pi.single i 1) ⊔ rootSubgroup .F4 K (-Pi.single i 1) := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, ← pinnedX_single, ← pinnedX_neg_single]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)))
    (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩))

theorem conj_mem_highestRootRankOne {x : ModGL .F4 K}
    (hx : x ∈ rootSubgroup .F4 K (Pi.single ⟨0, by decide⟩ 1) ⊔
      rootSubgroup .F4 K (-Pi.single ⟨0, by decide⟩ 1)) :
    canonicalRep (coxeterSystem .F4) K f4WeylV * x *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ ∈ highestRootRankOne K := by
  rw [← map_conj_rankOne_single_zero]
  exact ⟨x, hx, rfl⟩

theorem weylR_mem_highestRootRankOne :
    canonicalRep (coxeterSystem .F4) K f4WeylV * weylElt .F4 K ⟨0, by decide⟩ 1 *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ ∈ highestRootRankOne K :=
  conj_mem_highestRootRankOne (weylElt_mem_rankOne _ 1)

theorem torusR_mem_highestRootRankOne (μ : Kˣ) :
    canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ ∈ highestRootRankOne K :=
  conj_mem_highestRootRankOne (mul_mem (weylElt_mem_rankOne _ μ) (weylElt_mem_rankOne _ (-1)))

theorem torusR_mem_torusGroup (μ : Kˣ) :
    canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ ∈ torusGroup .F4 K :=
  (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer f4WeylV) _).1
    (torusElt_mem_torusGroup _ μ)

theorem torusR_conj_pinnedX_single_zero [CharP K 2] (μ : Kˣ) :
    (canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹) *
      pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) 1 *
      (canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹)⁻¹ =
      pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) μ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hβ : IsRoot .F4 (f4WeylV⁻¹ • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ)) :=
    IsRoot.smul (isRoot_single .F4 _) _
  have h1 : (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ *
      pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) 1 * canonicalRep (coxeterSystem .F4) K f4WeylV =
      pinnedX .F4 K (f4WeylV⁻¹ • Pi.single ⟨0, by decide⟩ 1) 1 := by
    have e := canonicalRep_mul_pinnedX_mul_inv_of_two h2 f4WeylV hβ 1
    rw [smul_inv_smul] at e
    rw [← e]
    group
  have h3 : torusElt .F4 K ⟨0, by decide⟩ μ *
      pinnedX .F4 K (f4WeylV⁻¹ • Pi.single ⟨0, by decide⟩ 1) 1 *
      (torusElt .F4 K ⟨0, by decide⟩ μ)⁻¹ =
      pinnedX .F4 K (f4WeylV⁻¹ • Pi.single ⟨0, by decide⟩ 1) μ := by
    rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hβ, rootChar_zpow μ
      (Tag.F4.cartan ⟨0, by decide⟩), f4WeylV_inv_smul_single_zero,
      (by decide : f4Pairing (Tag.F4.cartan ⟨0, by decide⟩)
        (Pi.single ⟨0, by decide⟩ 1 - orbitCertRoot .F4 47) = 1), zpow_one, mul_one]
  have h4 : canonicalRep (coxeterSystem .F4) K f4WeylV *
      pinnedX .F4 K (f4WeylV⁻¹ • Pi.single ⟨0, by decide⟩ 1) μ *
      (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ =
      pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) μ := by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 f4WeylV hβ, smul_inv_smul]
  calc (canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
          (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹) *
        pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) 1 *
        (canonicalRep (coxeterSystem .F4) K f4WeylV * torusElt .F4 K ⟨0, by decide⟩ μ *
          (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹)⁻¹ =
      canonicalRep (coxeterSystem .F4) K f4WeylV * (torusElt .F4 K ⟨0, by decide⟩ μ *
        ((canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ *
          pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) 1 *
          canonicalRep (coxeterSystem .F4) K f4WeylV) *
        (torusElt .F4 K ⟨0, by decide⟩ μ)⁻¹) *
        (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹ := by group
    _ = pinnedX .F4 K (Pi.single ⟨0, by decide⟩ 1) μ := by rw [h1, h3, h4]

theorem eq_one_of_rootDiagUnit_mem_centralizer {b : Fin Tag.F4.rank → Kˣ}
    (hb : rootDiagUnit .F4 b ∈ centralizer (c3PerpLevi K : Set (ModGL .F4 K)))
    {j : Fin Tag.F4.rank} (hj : j ≠ ⟨0, by decide⟩) : b j = 1 := by
  have hx : pinnedX .F4 K (Pi.single j 1) 1 ∈ c3PerpLevi K :=
    pinnedX_mem_rootSpan (S := c3PerpRoots) ⟨isRoot_single .F4 j, single_mem_c3PerpRoots j hj⟩ 1
  have hc := Subgroup.mem_centralizer_iff.1 hb _ hx
  have e : pinnedX .F4 K (Pi.single j 1) ((rootChar b (Pi.single j 1) : K) * 1) =
      pinnedX .F4 K (Pi.single j 1) 1 := by
    rw [← rootDiagUnit_conj_pinnedX b (isRoot_single .F4 j), ← hc, mul_inv_cancel_right]
  have e' := pinnedX_injective .F4 K _ e
  rw [mul_one, rootChar_single] at e'
  exact Units.ext e'

theorem mem_highestRootRankOne_of_mem_torusGroup [CharP K 2] {t : ModGL .F4 K}
    (ht : t ∈ torusGroup .F4 K) (htD : t ∈ centralizer (c3PerpLevi K : Set (ModGL .F4 K))) :
    t ∈ highestRootRankOne K := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hsJ := torusR_mem_highestRootRankOne (K := K) (b ⟨0, by decide⟩)
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (torusR_mem_torusGroup (K := K) (b ⟨0, by decide⟩))
  have hb'D : rootDiagUnit .F4 b' ∈ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) := by
    rw [← hb']
    exact highestRootRankOne_le_centralizer_c3PerpLevi hsJ
  have hb'0 : b' ⟨0, by decide⟩ = b ⟨0, by decide⟩ := by
    have e := torusR_conj_pinnedX_single_zero (K := K) (b ⟨0, by decide⟩)
    rw [hb', rootDiagUnit_conj_pinnedX b' (isRoot_single .F4 _), mul_one] at e
    have e' := pinnedX_injective .F4 K _ e
    rw [rootChar_single] at e'
    exact Units.ext e'
  have hbb : b' = b := funext fun j => by
    by_cases hj : j = ⟨0, by decide⟩
    · subst hj
      exact hb'0
    · rw [eq_one_of_rootDiagUnit_mem_centralizer hb'D hj,
        eq_one_of_rootDiagUnit_mem_centralizer htD hj]
  rw [← hbb, ← hb']
  exact hsJ

theorem mem_highestRootRankOne_of_mem_centralizer [CharP K 2] (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {g : ModGL .F4 K} (hg : g ∈ adjointGroup .F4 K)
    (hgD : g ∈ centralizer (c3PerpLevi K : Set (ModGL .F4 K))) : g ∈ highestRootRankOne K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c, hc0, hc1⟩ := hK
  have hl1 : Units.mk0 c hc0 ≠ 1 := fun h => hc1 (by simpa using congrArg Units.val h)
  have hr := highestRoot_long.1
  have hJD := highestRootRankOne_le_centralizer_c3PerpLevi (K := K)
  have hJ : ∀ {x : ModGL .F4 K}, x ∈ rootSubgroup .F4 K (orbitCertRoot .F4 47) →
      x ∈ highestRootRankOne K := fun hx => Subgroup.mem_sup_left hx
  have htor : ∀ i : Fin Tag.F4.rank, i ≠ ⟨0, by decide⟩ →
      g ∈ toralCentralizer .F4 K (fun j => Units.mk0 c hc0 ^ Tag.F4.cartan i j) := by
    intro i hi
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    have ht := torusElt_mem_c3PerpLevi hi (Units.mk0 c hc0)
    rw [torusElt_eq_rootDiagUnit] at ht
    rw [Subgroup.mem_centralizer_iff.1 hgD _ ht, mul_inv_cancel_right]
  have hB := Chevalley_toral_centralizer_Bruhat_factors .F4 K
    (fun j => Units.mk0 c hc0 ^ Tag.F4.cartan ⟨1, by decide⟩ j)
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ := hB.1 g (htor _ (by decide))
  have hfac : ∀ i : Fin Tag.F4.rank, i ≠ ⟨0, by decide⟩ →
      u ∈ rootSpan .F4 K (rootCharKernel (fun j => Units.mk0 c hc0 ^ Tag.F4.cartan i j) ∩
        {α | IsRoot .F4 α ∧ 0 < height α}) ∧
      v ∈ rootSpan .F4 K (rootCharKernel (fun j => Units.mk0 c hc0 ^ Tag.F4.cartan i j) ∩
        inversionSet w) := by
    intro i hi
    obtain ⟨w', -, h', hh', u', hu', v', hv', hgdec'⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors .F4 K
        (fun j => Units.mk0 c hc0 ^ Tag.F4.cartan i j)).1 g (htor i hi)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
      (rootSpan_mono Set.inter_subset_right hu) (rootSpan_mono Set.inter_subset_right hu')
      (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
      (hgdec.symm.trans hgdec')
    exact ⟨hu', hv'⟩
  have hposcl : ∀ α ∈ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α},
      ∀ β ∈ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}, ∀ m n : ℕ, 1 ≤ m →
        1 ≤ n → IsRoot .F4 (m • α + n • β) →
          m • α + n • β ∈ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have hur : u ∈ rootSubgroup .F4 K (orbitCertRoot .F4 47) :=
    mem_rootSubgroup_highestRoot_of_forall hl1 (fun α hα => hα) hposcl fun i hi => (hfac i hi).1
  have hvr : v ∈ rootSubgroup .F4 K (orbitCertRoot .F4 47) :=
    mem_rootSubgroup_highestRoot_of_forall hl1 (fun α hα => inversionSet_pos hα)
      (inversionSet_closed w) fun i hi => (hfac i hi).2
  have hu' : h * u * h⁻¹ ∈ rootSubgroup .F4 K (orbitCertRoot .F4 47) :=
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr hh) u).1 hur
  have hgJ : g = (h * u * h⁻¹) * (h * canonicalRep (coxeterSystem .F4) K w) * v := by
    rw [hgdec]
    group
  have hm : h * canonicalRep (coxeterSystem .F4) K w ∈
      centralizer (c3PerpLevi K : Set (ModGL .F4 K)) := by
    have e : h * canonicalRep (coxeterSystem .F4) K w = (h * u * h⁻¹)⁻¹ * g * v⁻¹ := by
      rw [hgJ]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hJD (hJ hu'))) hgD) (inv_mem (hJD (hJ hvr)))
  have hwj : ∀ j : Fin Tag.F4.rank, j ≠ ⟨0, by decide⟩ →
      w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Pi.single j 1 := by
    intro j hj
    have hx : pinnedX .F4 K (Pi.single j 1) 1 ∈ c3PerpLevi K :=
      pinnedX_mem_rootSpan (S := c3PerpRoots) ⟨isRoot_single .F4 j, single_mem_c3PerpRoots j hj⟩ 1
    have hc := Subgroup.mem_centralizer_iff.1 hm _ hx
    have hroot := IsRoot.smul (isRoot_single .F4 j) w
    have e : pinnedX .F4 K (w • Pi.single j 1) (torusRootChar h (w • Pi.single j 1) * 1) =
        pinnedX .F4 K (Pi.single j 1) 1 := by
      rw [← conj_pinnedX_of_mem_torusGroup hh hroot,
        ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single .F4 j)]
      calc h * (canonicalRep (coxeterSystem .F4) K w * pinnedX .F4 K (Pi.single j 1) 1 *
            (canonicalRep (coxeterSystem .F4) K w)⁻¹) * h⁻¹ =
          pinnedX .F4 K (Pi.single j 1) 1 * (h * canonicalRep (coxeterSystem .F4) K w) *
            (h * canonicalRep (coxeterSystem .F4) K w)⁻¹ := by rw [hc]; group
        _ = pinnedX .F4 K (Pi.single j 1) 1 := mul_inv_cancel_right _ _
    exact eq_of_pinnedX_eq_pinnedX_of_pos hroot (isRoot_single .F4 j)
      (by rw [height_single]; norm_num) one_ne_zero e
  have hw0 : w • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) = Pi.single ⟨0, by decide⟩ 1 ∨
      w • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) =
        Pi.single ⟨0, by decide⟩ 1 - orbitCertRoot .F4 47 := by
    obtain ⟨k, hk⟩ := isRoot_f4_iff.1 (IsRoot.smul (isRoot_single .F4 ⟨0, by decide⟩) w)
    rw [← hk]
    refine eq_or_eq_sub_of_iform_single_eq k fun j hj => ?_
    rw [hk]
    calc iform (w • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ)) (Pi.single j 1) =
        iform (w • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ))
          (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) := by rw [hwj j hj]
      _ = iform (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1) :=
        iform_smul w _ _
  rcases hw0 with h0 | h0
  ·
    have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = ⟨0, by decide⟩
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hwj i hi, height_single]
        norm_num
    subst hw1
    rw [canonicalRep_one, mul_one] at hm hgJ
    rw [hgJ]
    exact mul_mem (mul_mem (hJ hu') (mem_highestRootRankOne_of_mem_torusGroup hh hm)) (hJ hvr)
  ·
    obtain ⟨hR1, hR0⟩ := f4WeylR_smul
    have hwr : (f4WeylV * simple .F4 ⟨0, by decide⟩ * f4WeylV⁻¹) * w = 1 :=
      eq_one_of_forall_height_pos fun i => by
        by_cases hi : i = ⟨0, by decide⟩
        · subst hi
          rw [mul_smul, h0, hR0, height_single]
          norm_num
        · rw [mul_smul, hwj i hi, hR1 i hi, height_single]
          norm_num
    have hw : w * (f4WeylV * simple .F4 ⟨0, by decide⟩ * f4WeylV⁻¹) = 1 := by
      rw [eq_inv_of_mul_eq_one_right hwr, inv_mul_cancel]
    have hnrJ := weylR_mem_highestRootRankOne (K := K)
    have ht : h * canonicalRep (coxeterSystem .F4) K w *
        (canonicalRep (coxeterSystem .F4) K f4WeylV * weylElt .F4 K ⟨0, by decide⟩ 1 *
          (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹) ∈ torusGroup .F4 K := by
      refine mem_torusGroup_of_mapsRootLines_one ?_ ?_
      · exact mul_mem (mul_mem (Subgroup.mem_sup_left hh) (canonicalRep_mem_monomialSubgroup K w))
          (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K _)
            (weylElt_mem_monomialSubgroup ⟨0, by decide⟩))
            (inv_mem (canonicalRep_mem_monomialSubgroup K _)))
      · have hmaps := ((mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w)).mul
          (((mapsRootLines_canonicalRep f4WeylV).mul (mapsRootLines_weylElt ⟨0, by decide⟩)).mul
            (mapsRootLines_canonicalRep f4WeylV).inv)
        rwa [one_mul, hw] at hmaps
    have htJ := mem_highestRootRankOne_of_mem_torusGroup ht (mul_mem hm (hJD hnrJ))
    have e : h * canonicalRep (coxeterSystem .F4) K w =
        (h * canonicalRep (coxeterSystem .F4) K w *
          (canonicalRep (coxeterSystem .F4) K f4WeylV * weylElt .F4 K ⟨0, by decide⟩ 1 *
            (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹)) *
        (canonicalRep (coxeterSystem .F4) K f4WeylV * weylElt .F4 K ⟨0, by decide⟩ 1 *
          (canonicalRep (coxeterSystem .F4) K f4WeylV)⁻¹)⁻¹ := by group
    rw [hgJ, e]
    exact mul_mem (mul_mem (hJ hu') (mul_mem htJ (inv_mem hnrJ))) (hJ hvr)

theorem centralizer_c3PerpLevi_eq_of_exists_ne_zero_ne_one [CharP K 2]
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    adjointGroup .F4 K ⊓ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) =
      highestRootRankOne K := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf highestRootRankOne_le_adjointGroup highestRootRankOne_le_centralizer_c3PerpLevi)
  exact mem_highestRootRankOne_of_mem_centralizer hK hg.1 hg.2

theorem centralizer_c3PerpLevi_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    adjointGroup .F4 K ⊓ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) =
      highestRootRankOne K :=
  centralizer_c3PerpLevi_eq_of_exists_ne_zero_ne_one (exists_ne_zero_ne_one_of_four_le hq)

theorem exists_eq_conj_highestRootRankOne_of_fix_c3PerpLevi {f : ℕ} (hf : 2 ≤ f) [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ c3PerpLevi K → β x = x) :
    ∃ g : adjointGroup .F4 K, β = MulAut.conj g ∧ (g : ModGL .F4 K) ∈ highestRootRankOne K := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, hg, hgD⟩ := exists_eq_conj_of_fix_c3PerpLevi (by omega) hK β hβ
  refine ⟨g, hg, mem_highestRootRankOne_of_mem_centralizer (exists_ne_zero_ne_one_of_four_le hq)
    g.2 ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxC : x ∈ adjointGroup .F4 K :=
    (iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ : c3PerpLevi K ≤ adjointGroup .F4 K) hx
  exact (congrArg Subtype.val (hgD ⟨x, hxC⟩ hx)).symm

end CFSG.SeitzReduction.F4Pilot
