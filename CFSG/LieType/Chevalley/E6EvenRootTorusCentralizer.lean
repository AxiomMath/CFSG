module

public import CFSG.LieType.Chevalley.E6EvenRootTorusLevi
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.E6EvenRootTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.E6EvenRootTorus

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot

variable {K : Type} [Field K]

@[expose] def pairE6 (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  ∑ j, TwistTag.E6.tag.cartan i j * v j

@[expose] def CentCheck (n : ℕ) : Prop :=
  (∀ i, pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = 0 ∨
      pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = 1 ∨
      pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = -1 ∨
      pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = 2 ∨
      pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = -2) ∧
    ((∀ i, i ≠ e6Idx 1 → pairE6 i (TwistTag.E6.tag.rootCertificate.root n) = 0) →
      TwistTag.E6.tag.rootCertificate.root n = e6HighestRoot ∨
        TwistTag.E6.tag.rootCertificate.root n = -e6HighestRoot) ∧
    ((∀ j, j ≠ e6Idx 1 → pairE6 j (TwistTag.E6.tag.rootCertificate.root n) =
        pairE6 j (Pi.single (e6Idx 1) 1)) →
      TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 1) 1 ∨
        TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 1) 1 - e6HighestRoot)

instance (n : ℕ) : Decidable (CentCheck n) := by
  unfold CentCheck
  infer_instance

theorem centCheck : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, CentCheck n := by
  decide +kernel

theorem iform_single_eq_pairE6
    (v : Fin TwistTag.E6.tag.rank → ℤ) (i : Fin TwistTag.E6.tag.rank) :
    iform v (Pi.single i 1) = pairE6 i v := by
  rw [iform_single_right, RootTorus.symmetrizer_E6, one_mul, pairE6]

theorem centCheck_of_isRoot
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    (∀ i, pairE6 i β = 0 ∨ pairE6 i β = 1 ∨ pairE6 i β = -1 ∨ pairE6 i β = 2 ∨
      pairE6 i β = -2) ∧
    ((∀ i, i ≠ e6Idx 1 → pairE6 i β = 0) → β = e6HighestRoot ∨ β = -e6HighestRoot) ∧
    ((∀ j, j ≠ e6Idx 1 → pairE6 j β = pairE6 j (Pi.single (e6Idx 1) 1)) →
      β = Pi.single (e6Idx 1) 1 ∨ β = Pi.single (e6Idx 1) 1 - e6HighestRoot) := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  exact centCheck n hn

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem rootChar_cartan (l : Kˣ) (i : Fin TwistTag.E6.tag.rank)
    (α : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (fun j => l ^ TwistTag.E6.tag.cartan i j) α = l ^ pairE6 i α := by
  simp only [rootChar, pairE6, ← zpow_mul]
  exact prod_zpow_eq_zpow_sum _ _ _

theorem pairE6_eq_zero_of_rootChar_eq_one
    (h2 : (2 : K) = 0) {l : Kˣ} (hl : l ≠ 1)
    (i : Fin TwistTag.E6.tag.rank) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α)
    (h : rootChar (fun j => l ^ TwistTag.E6.tag.cartan i j) α = 1) : pairE6 i α = 0 := by
  rw [rootChar_cartan] at h
  have hl2 := RootTorus.sq_ne_one_of_two h2 hl
  rcases (centCheck_of_isRoot hα).1 i with h0 | h1 | h1 | h1 | h1
  · exact h0
  all_goals exact absurd h (RootTorus.zpow_ne_one hl hl2 (by rw [h1]; norm_num))

theorem rootCharKernel_inter_closed {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.E6.tag (m • α + n • β) →
      m • α + n • β ∈ S) :
    ∀ α ∈ rootCharKernel a ∩ S, ∀ β ∈ rootCharKernel a ∩ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot TwistTag.E6.tag (m • α + n • β) → m • α + n • β ∈ rootCharKernel a ∩ S := by
  intro α hα β hβ m n hm hn hr
  refine ⟨⟨hr, ?_⟩, hScl α hα.2 β hβ.2 m n hm hn hr⟩
  rw [rootChar_add, ← Nat.cast_smul_eq_nsmul ℤ m α, ← Nat.cast_smul_eq_nsmul ℤ n β,
    rootChar_zsmul, rootChar_zsmul, hα.1.2, hβ.1.2, one_zpow, one_zpow, one_mul]

theorem mem_rootSpan_inter_of_mem_centralizer
    {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hSpos : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.E6.tag (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ rootSpan TwistTag.E6.tag K S)
    (hxa : x ∈ centralizer ({rootDiagUnit TwistTag.E6.tag a} : Set (ModGL TwistTag.E6.tag K))) :
    x ∈ rootSpan TwistTag.E6.tag K (rootCharKernel a ∩ S) := by
  have hfin : S.Finite := (finite_setOf_isRoot TwistTag.E6.tag).subset fun α hα => (hSpos α hα).1
  refine mem_rootSpan_inter_of_conj_eq a hfin (fun α hα => (hSpos α hα).1)
    (fun α hα hrange => bijOn_prod_pinnedX K hSpos hScl α hα hrange) hx ?_
  rw [Subgroup.mem_centralizer_iff.1 hxa _ (Set.mem_singleton _), mul_inv_cancel_right]

theorem forall_ne_two {P : Fin TwistTag.E6.tag.rank → Prop} (h0 : P (e6Idx 0))
    (h2 : P (e6Idx 2)) (h3 : P (e6Idx 3)) (h4 : P (e6Idx 4)) (h5 : P (e6Idx 5)) :
    ∀ i, i ≠ e6Idx 1 → P i := by
  intro i hi
  fin_cases i
  · exact h0
  · exact absurd rfl hi
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem mem_rootSubgroup_theta_of_forall
    (h2 : (2 : K) = 0) {l : Kˣ} (hl : l ≠ 1)
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hSpos : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.E6.tag (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL TwistTag.E6.tag K}
    (hx : ∀ i, i ≠ e6Idx 1 → x ∈ rootSpan TwistTag.E6.tag K
      (rootCharKernel (fun j => l ^ TwistTag.E6.tag.cartan i j) ∩ S)) :
    x ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
  have hcent : ∀ i, i ≠ e6Idx 1 →
      x ∈ centralizer ({rootDiagUnit TwistTag.E6.tag (fun j => l ^ TwistTag.E6.tag.cartan i j)} :
        Set (ModGL TwistTag.E6.tag K)) := fun i hi =>
    rootSpan_le_centralizer _ Set.inter_subset_left (hx i hi)
  have hS0 : ∀ α ∈ rootCharKernel (fun j => l ^ TwistTag.E6.tag.cartan (e6Idx 0) j) ∩ S,
      IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => hSpos α hα.2
  have hx2 := mem_rootSpan_inter_of_mem_centralizer hS0 (rootCharKernel_inter_closed hScl)
    (hx (e6Idx 0) (by decide)) (hcent (e6Idx 2) (by decide))
  have hx3 := mem_rootSpan_inter_of_mem_centralizer (fun α hα => hS0 α hα.2)
    (rootCharKernel_inter_closed (rootCharKernel_inter_closed hScl)) hx2
    (hcent (e6Idx 3) (by decide))
  have hx4 := mem_rootSpan_inter_of_mem_centralizer (fun α hα => hS0 α hα.2.2)
    (rootCharKernel_inter_closed (rootCharKernel_inter_closed (rootCharKernel_inter_closed hScl)))
    hx3 (hcent (e6Idx 4) (by decide))
  have hx5 := mem_rootSpan_inter_of_mem_centralizer (fun α hα => hS0 α hα.2.2.2)
    (rootCharKernel_inter_closed (rootCharKernel_inter_closed (rootCharKernel_inter_closed
      (rootCharKernel_inter_closed hScl)))) hx4 (hcent (e6Idx 5) (by decide))
  refine (iSup₂_le fun α hα => ?_ : _ ≤ rootSubgroup TwistTag.E6.tag K e6HighestRoot) hx5
  obtain ⟨⟨hαr, h5⟩, ⟨-, h4⟩, ⟨-, h3⟩, ⟨-, h2'⟩, ⟨-, h0⟩, hαS⟩ := hα
  have hpos := (hSpos α hαS).2
  rcases (centCheck_of_isRoot hαr).2.1 (forall_ne_two
      (pairE6_eq_zero_of_rootChar_eq_one h2 hl _ hαr h0)
      (pairE6_eq_zero_of_rootChar_eq_one h2 hl _ hαr h2')
      (pairE6_eq_zero_of_rootChar_eq_one h2 hl _ hαr h3)
      (pairE6_eq_zero_of_rootChar_eq_one h2 hl _ hαr h4)
      (pairE6_eq_zero_of_rootChar_eq_one h2 hl _ hαr h5)) with h | h
  · rw [h]
  · rw [h, height_neg] at hpos
    exact absurd hpos (by decide)

theorem eq_of_pinnedX_eq_pinnedX_of_pos
    {δ γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hγ : IsRoot TwistTag.E6.tag γ) (hγp : 0 < height γ)
    {d e : K} (he : e ≠ 0)
    (h : pinnedX TwistTag.E6.tag K δ d = pinnedX TwistTag.E6.tag K γ e) : δ = γ := by
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
  · have hneg' : pinnedX TwistTag.E6.tag K δ d ∈ negUnipotent TwistTag.E6.tag K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ height α < 0}) ⟨hδ, hneg⟩ d
    have hB : pinnedX TwistTag.E6.tag K δ d ∈ borelGroup TwistTag.E6.tag K := by
      rw [h]
      exact Subgroup.mem_sup_right
        (pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) ⟨hγ, hγp⟩ e)
    have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, h] at h0
    exact he (pinnedX_injective TwistTag.E6.tag K _
      (h0.trans (pinnedX_zero TwistTag.E6.tag K _).symm))

theorem pinnedX_single_mem
    {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ e6Idx 1) :
    pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 ∈ subsystemGroup TwistTag.E6.tag K setA := by
  rw [pinnedX_single]
  exact xUnit_mem_subsystemGroup hj 1

theorem rootChar_single' (b : Fin TwistTag.E6.tag.rank → Kˣ) (j : Fin TwistTag.E6.tag.rank) :
    rootChar b (Pi.single j 1) = b j := by
  rw [rootChar, Finset.prod_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, zpow_one]

theorem mem_thetaRankOneGroup_of_torus
    (h2 : (2 : K) = 0) {t : ModGL TwistTag.E6.tag K}
    (ht : t ∈ torusGroup TwistTag.E6.tag K)
    (htL : t ∈ centralizer (subsystemGroup TwistTag.E6.tag K setA :
      Set (ModGL TwistTag.E6.tag K))) :
    t ∈ thetaRankOneGroup (RingHom.id K) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hb : ∀ j, j ≠ e6Idx 1 → b j = 1 := fun j hj => by
    have hc := Subgroup.mem_centralizer_iff.1 htL _ (pinnedX_single_mem hj)
    have e : pinnedX TwistTag.E6.tag K (Pi.single j 1) ((rootChar b (Pi.single j 1) : K) * 1) =
        pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 := by
      rw [← rootDiagUnit_conj_pinnedX b (isRoot_single TwistTag.E6.tag j), ← hc,
        mul_inv_cancel_right]
    have e' := pinnedX_injective TwistTag.E6.tag K _ e
    rw [mul_one, rootChar_single'] at e'
    exact Units.ext e'
  have hbθ : b = Pi.mulSingle (e6Idx 1) (b (e6Idx 1)) := funext fun j => by
    by_cases hj : j = e6Idx 1
    · subst hj
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, hb j hj]
  refine thetaTorus_le_thetaRankOneGroup h2 ⟨b (e6Idx 1), ?_⟩
  rw [hbθ]
  rfl

abbrev wTheta : WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd E6GraphRootSL2.thetaWord

abbrev sTheta : WeylGroup TwistTag.E6.tag := wTheta * simple TwistTag.E6.tag (e6Idx 0) * wTheta⁻¹

theorem sTheta_smul
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    sTheta • v = E6GraphRootSL2.thetaWord.foldr (reflect TwistTag.E6.tag)
      (reflect TwistTag.E6.tag (e6Idx 0)
        (E6GraphRootSL2.thetaWord.reverse.foldr (reflect TwistTag.E6.tag) v)) := by
  rw [mul_smul, mul_smul, ← CoxeterSystem.wordProd_reverse, wordProd_smul, simple_smul,
    wordProd_smul]

theorem sTheta_smul_single
    {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ e6Idx 1) :
    sTheta • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1 := by
  rw [sTheta_smul]
  revert j
  decide +kernel

theorem sTheta_smul_sub :
    sTheta • ((Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) - e6HighestRoot) =
      Pi.single (e6Idx 1) 1 := by
  rw [sTheta_smul]
  decide +kernel

theorem mapsRootLines_nTheta
    (h2 : (2 : K) = 0) :
    MapsRootLines (E6GraphLevi.thetaSL2 K WSL) sTheta := by
  rw [E6GraphRootSL2.thetaSL2_WSL, wordElt_eq_canonicalRep h2]
  exact ((mapsRootLines_canonicalRep _).mul (mapsRootLines_weylElt _)).mul
    (mapsRootLines_canonicalRep _).inv

theorem nTheta_mem_monomialSubgroup
    (h2 : (2 : K) = 0) :
    E6GraphLevi.thetaSL2 K WSL ∈ monomialSubgroup TwistTag.E6.tag K := by
  rw [E6GraphRootSL2.thetaSL2_WSL, wordElt_eq_canonicalRep h2]
  exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K _)
    (weylElt_mem_monomialSubgroup _)) (inv_mem (canonicalRep_mem_monomialSubgroup K _))

theorem nTheta_mem_thetaRankOneGroup
    (h2 : (2 : K) = 0) :
    E6GraphLevi.thetaSL2 K WSL ∈ thetaRankOneGroup (RingHom.id K) := by
  rw [thetaRankOneGroup_eq_range h2]
  refine ⟨WSL, ?_⟩
  rw [MonoidHom.comp_apply]
  congr 1

theorem rootSubgroup_le_thetaRankOneGroup :
    rootSubgroup TwistTag.E6.tag K e6HighestRoot ≤ thetaRankOneGroup (RingHom.id K) := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  exact Subgroup.mem_sup_left ((mem_thetaRootGroup (RingHom.id K)).2 ⟨c, rfl⟩)

theorem thetaRankOneGroup_le_centralizer
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) :
    thetaRankOneGroup (RingHom.id K) ≤
      centralizer (subsystemGroup TwistTag.E6.tag K setA : Set (ModGL TwistTag.E6.tag K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro l hl
  rw [← centralizer_thetaRankOneGroup hf hk] at hl
  exact ((mem_centralizer_iff.1 (mem_inf.1 hl).2) x hx).symm

theorem mem_thetaRankOneGroup_of_mem_centralizer
    {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card K = 2 ^ f) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ adjointGroup TwistTag.E6.tag K)
    (hgL : g ∈ centralizer (subsystemGroup TwistTag.E6.tag K setA :
      Set (ModGL TwistTag.E6.tag K))) :
    g ∈ thetaRankOneGroup (RingHom.id K) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hf hk
  obtain ⟨c, hc0, hc1⟩ := hK
  have hl1 : Units.mk0 c hc0 ≠ 1 := fun h => hc1 (by simpa using congrArg Units.val h)
  have hXL := thetaRankOneGroup_le_centralizer (K := K) hf hk
  have hJ : ∀ {x : ModGL TwistTag.E6.tag K}, x ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot →
      x ∈ thetaRankOneGroup (RingHom.id K) := fun hx => rootSubgroup_le_thetaRankOneGroup hx
  have htor : ∀ i, i ≠ e6Idx 1 → g ∈ toralCentralizer TwistTag.E6.tag K
      (fun j => Units.mk0 c hc0 ^ TwistTag.E6.tag.cartan i j) := by
    intro i hi
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    have ht := subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (K := K)
      (A := setA) (show i ∈ setA from hi) (Units.mk0 c hc0))
    rw [torusElt_eq_rootDiagUnit] at ht
    rw [Subgroup.mem_centralizer_iff.1 hgL _ ht, mul_inv_cancel_right]
  have hB := Chevalley_toral_centralizer_Bruhat_factors TwistTag.E6.tag K
    (fun j => Units.mk0 c hc0 ^ TwistTag.E6.tag.cartan (e6Idx 0) j)
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ := hB.1 g (htor _ (by decide))
  have hfac : ∀ i, i ≠ e6Idx 1 →
      u ∈ rootSpan TwistTag.E6.tag K (rootCharKernel
        (fun j => Units.mk0 c hc0 ^ TwistTag.E6.tag.cartan i j) ∩
          {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) ∧
      v ∈ rootSpan TwistTag.E6.tag K (rootCharKernel
        (fun j => Units.mk0 c hc0 ^ TwistTag.E6.tag.cartan i j) ∩ inversionSet w) := by
    intro i hi
    obtain ⟨w', -, h', hh', u', hu', v', hv', hgdec'⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors TwistTag.E6.tag K
        (fun j => Units.mk0 c hc0 ^ TwistTag.E6.tag.cartan i j)).1 g (htor i hi)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
      (rootSpan_mono Set.inter_subset_right hu) (rootSpan_mono Set.inter_subset_right hu')
      (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
      (hgdec.symm.trans hgdec')
    exact ⟨hu', hv'⟩
  have hposcl : ∀ α ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      ∀ β ∈ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
        ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.E6.tag (m • α + n • β) →
          m • α + n • β ∈
            {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have hur : u ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
    mem_rootSubgroup_theta_of_forall h2 hl1 (fun α hα => hα) hposcl fun i hi => (hfac i hi).1
  have hvr : v ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
    mem_rootSubgroup_theta_of_forall h2 hl1 (fun α hα => inversionSet_pos hα)
      (inversionSet_closed w) fun i hi => (hfac i hi).2
  have hu' : h * u * h⁻¹ ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
    (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot hh) u).1 hur
  have hgJ : g = (h * u * h⁻¹) * (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) * v := by
    rw [hgdec]
    group
  have hm : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈
      centralizer (subsystemGroup TwistTag.E6.tag K setA : Set (ModGL TwistTag.E6.tag K)) := by
    have e : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w = (h * u * h⁻¹)⁻¹ * g * v⁻¹ := by
      rw [hgJ]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hXL (hJ hu'))) hgL) (inv_mem (hXL (hJ hvr)))
  have hwj : ∀ j, j ≠ e6Idx 1 →
      w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1 := by
    intro j hj
    have hc := Subgroup.mem_centralizer_iff.1 hm _ (pinnedX_single_mem (K := K) hj)
    have hroot := IsRoot.smul (isRoot_single TwistTag.E6.tag j) w
    have e : pinnedX TwistTag.E6.tag K (w • Pi.single j 1)
        (torusRootChar h (w • Pi.single j 1) * 1) =
          pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 := by
      rw [← conj_pinnedX_of_mem_torusGroup hh hroot,
        ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single TwistTag.E6.tag j)]
      calc h * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
            pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * h⁻¹ =
          pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 *
            (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) *
            (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by rw [hc]; group
        _ = pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 := mul_inv_cancel_right _ _
    exact eq_of_pinnedX_eq_pinnedX_of_pos hroot (isRoot_single TwistTag.E6.tag j)
      (by rw [height_single]; norm_num) one_ne_zero e
  have hw2 := (centCheck_of_isRoot (IsRoot.smul (isRoot_single TwistTag.E6.tag (e6Idx 1)) w)).2.2
    fun j hj => by
      rw [← iform_single_eq_pairE6, ← iform_single_eq_pairE6]
      calc iform (w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ))
            (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by rw [hwj j hj]
        _ = iform (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single j 1) :=
          iform_smul w _ _
  rcases hw2 with h0 | h0
  ·
    have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = e6Idx 1
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hwj i hi, height_single]
        norm_num
    subst hw1
    rw [canonicalRep_one, mul_one] at hm hgJ
    rw [hgJ]
    exact mul_mem (mul_mem (hJ hu') (mem_thetaRankOneGroup_of_torus h2 hh hm)) (hJ hvr)
  ·
    have hsw : sTheta * w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = e6Idx 1
      · subst hi
        rw [mul_smul, h0, sTheta_smul_sub, height_single]
        norm_num
      · rw [mul_smul, hwj i hi, sTheta_smul_single hi, height_single]
        norm_num
    have hws : w * sTheta = 1 := by
      rw [eq_inv_of_mul_eq_one_right hsw, inv_mul_cancel]
    have hnJ := nTheta_mem_thetaRankOneGroup (K := K) h2
    have ht : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * E6GraphLevi.thetaSL2 K WSL ∈
        torusGroup TwistTag.E6.tag K := by
      refine mem_torusGroup_of_mapsRootLines_one ?_ ?_
      · exact mul_mem (mul_mem (torusGroup_le_monomialSubgroup hh)
          (canonicalRep_mem_monomialSubgroup K w)) (nTheta_mem_monomialSubgroup h2)
      · have hmaps := ((mapsRootLines_of_mem_torusGroup hh).mul
          (mapsRootLines_canonicalRep w)).mul (mapsRootLines_nTheta (K := K) h2)
        rwa [one_mul, hws] at hmaps
    have htJ := mem_thetaRankOneGroup_of_torus h2 ht (mul_mem hm (hXL hnJ))
    have e : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w =
        (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * E6GraphLevi.thetaSL2 K WSL) *
          (E6GraphLevi.thetaSL2 K WSL)⁻¹ := by group
    rw [hgJ, e]
    exact mul_mem (mul_mem (hJ hu') (mul_mem htJ (inv_mem hnJ))) (hJ hvr)

theorem centralizer_subsystemGroup
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card K = 2 ^ f) :
    adjointGroup TwistTag.E6.tag K ⊓
        centralizer (subsystemGroup TwistTag.E6.tag K setA : Set (ModGL TwistTag.E6.tag K)) =
      thetaRankOneGroup (RingHom.id K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 ≤ Nat.card K := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : Fintype K := Fintype.ofFinite K
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine le_antisymm (fun g hg => mem_thetaRankOneGroup_of_mem_centralizer (by omega) hk hK
    (mem_inf.1 hg).1 (mem_inf.1 hg).2) (le_inf ?_ (thetaRankOneGroup_le_centralizer (by omega) hk))
  exact E6GraphRadical.thetaRankOneGroup_le_adjointGroup (RingHom.id K)

end CFSG.LieType.Chevalley.E6EvenRootTorus
