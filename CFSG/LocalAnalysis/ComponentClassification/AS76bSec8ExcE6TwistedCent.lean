module

public import CFSG.LieType.Chevalley.E6EvenRootTorusAutFix
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6EvenRootTorus

theorem eq_zero_of_dvd_add_mul {q : ℤ} (hq : 4 ≤ q) {a b : ℤ} (ha : |a| ≤ 2) (hb : |b| ≤ 2)
    (h : q ^ 2 - 1 ∣ a + q * b) : a = 0 ∧ b = 0 := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  have hq0 : (0 : ℤ) ≤ q := by linarith
  have h1 : q * b ≤ q * 2 := mul_le_mul_of_nonneg_left hb2 hq0
  have h2 : q * (-2) ≤ q * b := mul_le_mul_of_nonneg_left hb1 hq0
  have h0 : a + q * b = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    rw [abs_lt]
    constructor <;> nlinarith
  have hb0 : b = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : q * b ≤ q * (-1) := mul_le_mul_of_nonneg_left (by omega) hq0
      linarith
    · have : q * 1 ≤ q * b := mul_le_mul_of_nonneg_left (by omega) hq0
      linarith
  subst hb0
  exact ⟨by linarith, rfl⟩

variable {K : Type} [Field K]

theorem perm_perm_E6 :
    ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  decide

theorem eq_of_single_eq {i j : Fin TwistTag.E6.tag.rank}
    (h : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1) : i = j := by
  by_contra hne
  have := congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
  exact one_ne_zero this

theorem torusElt_mul_mem
    (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (hi' : TwistTag.E6.perm i ≠ e6Idx 1)
    (u : Kˣ) :
    torusElt TwistTag.E6.tag K i u *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm i) (Units.map σ.toMonoidHom u) ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  refine mem_inf.2 ⟨mul_mem (subsystemTorus_le_subsystemGroup
    (torusElt_mem_subsystemTorus (A := setA) (show i ∈ setA from hi) u))
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (A := setA)
        (show TwistTag.E6.perm i ∈ setA from hi') _)), ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _), ?_⟩
  have hρρ : TwistTag.E6.perm (TwistTag.E6.perm i) = i := perm_perm_E6 i
  have hu : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u) = u := Units.ext (hσσ u)
  rw [map_mul, twistHom_torusElt, twistHom_torusElt, hρρ, hu]
  exact RootTorus.torusGroup_mul_comm (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem torusElt_four_mem
    (σ : K →+* K) {s : Kˣ}
    (hs : Units.map σ.toMonoidHom s = s) :
    torusElt TwistTag.E6.tag K (e6Idx 3) s ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  refine mem_inf.2 ⟨subsystemTorus_le_subsystemGroup
    (torusElt_mem_subsystemTorus (A := setA)
      (show e6Idx 3 ∈ setA from (by decide : e6Idx 3 ≠ e6Idx 1)) s), ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨torusElt_mem_adjointGroup _ _, ?_⟩
  rw [twistHom_torusElt, hs]
  rfl

theorem xUnit_mul_mem
    [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6Idx 1) (hi' : TwistTag.E6.perm i ≠ e6Idx 1)
    (hρ : TwistTag.E6.perm i ≠ i)
    (hnr : ¬IsRoot TwistTag.E6.tag
      (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ))
    (c : K) :
    xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c) ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  refine mem_inf.2 ⟨mul_mem (xUnit_mem_subsystemGroup (show i ∈ setA from hi) c)
    (xUnit_mem_subsystemGroup (show TwistTag.E6.perm i ∈ setA from hi') _), ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _), ?_⟩
  have hρρ : TwistTag.E6.perm (TwistTag.E6.perm i) = i := perm_perm_E6 i
  rw [map_mul, twistHom_xUnit, twistHom_xUnit, hρρ, hσσ, ← pinnedX_single, ← pinnedX_single]
  have hne : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      Pi.single i 1 := fun h => hρ (eq_of_single_eq h)
  have hne' : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      -Pi.single i 1 := fun h => by
    have := congrFun h i
    rw [Pi.single_eq_of_ne (Ne.symm hρ), Pi.neg_apply, Pi.single_eq_same] at this
    omega
  exact (commute_pinnedX_of_not_isRoot (isRoot_single _ _) (isRoot_single _ _) hne hne'
    (by rwa [add_comm]) (σ c) c).eq

theorem pinnedX_fixed_mem
    [CharP K 2] (σ : K →+* K)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (h0 : β (e6Idx 1) = 0)
    (hρ : permLattice TwistTag.E6.perm β = β) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K β c ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  refine mem_inf.2 ⟨rootSubgroup_le_subsystemGroup (mem_parabolicRoots_of hβ h0)
    (mem_rootSubgroup.2 ⟨c, rfl⟩), ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨pinnedX_mem_adjointGroup _ _, ?_⟩
  rw [CFSG.SeitzReduction.twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ hβ, hρ, hc]

theorem rootChar_mul_twisted (a b : Fin TwistTag.E6.tag.rank → Kˣ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (a * b) γ = rootChar a γ * rootChar b γ := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem torusElt_mul_eq
    (i j : Fin TwistTag.E6.tag.rank) (u v : Kˣ) :
    torusElt TwistTag.E6.tag K i u * torusElt TwistTag.E6.tag K j v =
      rootDiagUnit TwistTag.E6.tag ((fun l => u ^ TwistTag.E6.tag.cartan i l) *
        fun l => v ^ TwistTag.E6.tag.cartan j l) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, rootDiagUnit_mul]

theorem abs_pairE6_le
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (i : Fin TwistTag.E6.tag.rank) : |pairE6 i γ| ≤ 2 := by
  rcases (centCheck_of_isRoot hγ).1 i with h | h | h | h | h <;> rw [h] <;> norm_num

theorem pairE6_eq_zero_of_rootChar_pair
    {q : ℕ} (hq : 4 ≤ q) {u : Kˣ}
    (hu : orderOf u = q ^ 2 - 1) (i j : Fin TwistTag.E6.tag.rank)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (h : rootChar ((fun l => u ^ TwistTag.E6.tag.cartan i l) *
      fun l => (u ^ q) ^ TwistTag.E6.tag.cartan j l) γ = 1) :
    pairE6 i γ = 0 ∧ pairE6 j γ = 0 := by
  rw [rootChar_mul_twisted, rootChar_cartan, rootChar_cartan, ← zpow_natCast, ← zpow_mul,
    ← zpow_add] at h
  have hd := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hu] at hd
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by push_cast [Nat.cast_sub hq1]; ring
  rw [hcast] at hd
  exact eq_zero_of_dvd_add_mul (by exact_mod_cast hq) (abs_pairE6_le hγ i) (abs_pairE6_le hγ j)
    hd

theorem exists_factor_of_commute_twisted
    (h2 : (2 : K) = 0) {q : ℕ} (hq : 4 ≤ q)
    {u s : Kˣ} (hu : orderOf u = q ^ 2 - 1) (hs : s ≠ 1) {g : ModGL TwistTag.E6.tag K}
    (h₁ : g ∈ toralCentralizer TwistTag.E6.tag K
      ((fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 0) l) *
        fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 5) l))
    (h₃ : g ∈ toralCentralizer TwistTag.E6.tag K
      ((fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 2) l) *
        fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 4) l))
    (h₄ : g ∈ toralCentralizer TwistTag.E6.tag K
      (fun l => s ^ TwistTag.E6.tag.cartan (e6Idx 3) l)) :
    ∃ w : WeylGroup TwistTag.E6.tag, ∃ h ∈ torusGroup TwistTag.E6.tag K,
      ∃ x ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot,
        ∃ y ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot,
          g = h * x * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * y := by
  have hB := Chevalley_toral_centralizer_Bruhat_factors TwistTag.E6.tag K
    ((fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 0) l) *
      fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 5) l)
  obtain ⟨w, -, h, hh, x, hx, y, hy, hgdec⟩ := hB.1 g h₁
  have hfac : ∀ a, g ∈ toralCentralizer TwistTag.E6.tag K a →
      x ∈ rootSpan TwistTag.E6.tag K (rootCharKernel a ∩
        {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) ∧
      y ∈ rootSpan TwistTag.E6.tag K (rootCharKernel a ∩ inversionSet w) := by
    intro a ha
    obtain ⟨w', -, h', hh', x', hx', y', hy', hgdec'⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors TwistTag.E6.tag K a).1 g ha
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hB.2.1 w w' h h' x x' y y' hh hh'
      (rootSpan_mono Set.inter_subset_right hx) (rootSpan_mono Set.inter_subset_right hx')
      (rootSpan_mono Set.inter_subset_right hy) (rootSpan_mono Set.inter_subset_right hy')
      (hgdec.symm.trans hgdec')
    exact ⟨hx', hy'⟩
  have hθ : ∀ {S : Set (Fin TwistTag.E6.tag.rank → ℤ)},
      (∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.E6.tag (m • α + n • β) →
        m • α + n • β ∈ S) → ∀ {z : ModGL TwistTag.E6.tag K},
      z ∈ rootSpan TwistTag.E6.tag K (rootCharKernel ((fun l => u ^ TwistTag.E6.tag.cartan
        (e6Idx 0) l) * fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 5) l) ∩ S) →
      z ∈ rootSpan TwistTag.E6.tag K (rootCharKernel ((fun l => u ^ TwistTag.E6.tag.cartan
        (e6Idx 2) l) * fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 4) l) ∩ S) →
      z ∈ rootSpan TwistTag.E6.tag K (rootCharKernel
        (fun l => s ^ TwistTag.E6.tag.cartan (e6Idx 3) l) ∩ S) →
      z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
    intro S hSpos hScl z hz1 hz3 hz4
    have hc3 := rootSpan_le_centralizer _ Set.inter_subset_left hz3
    have hc4 := rootSpan_le_centralizer _ Set.inter_subset_left hz4
    have hS1 : ∀ α ∈ rootCharKernel ((fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 0) l) *
        fun l => (u ^ q) ^ TwistTag.E6.tag.cartan (e6Idx 5) l) ∩ S,
        IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => hSpos α hα.2
    have hz13 := mem_rootSpan_inter_of_mem_centralizer hS1 (rootCharKernel_inter_closed hScl)
      hz1 hc3
    have hz134 := mem_rootSpan_inter_of_mem_centralizer (fun α hα => hS1 α hα.2)
      (rootCharKernel_inter_closed (rootCharKernel_inter_closed hScl)) hz13 hc4
    refine (iSup₂_le fun α hα => ?_ :
      _ ≤ rootSubgroup TwistTag.E6.tag K e6HighestRoot) hz134
    obtain ⟨⟨hαr, h4⟩, ⟨-, h3⟩, ⟨-, h1⟩, hαS⟩ := hα
    have hpos := (hSpos α hαS).2
    obtain ⟨p0, p5⟩ := pairE6_eq_zero_of_rootChar_pair hq hu (e6Idx 0) (e6Idx 5) hαr h1
    obtain ⟨p2, p4⟩ := pairE6_eq_zero_of_rootChar_pair hq hu (e6Idx 2) (e6Idx 4) hαr h3
    have p3 := pairE6_eq_zero_of_rootChar_eq_one h2 hs (e6Idx 3) hαr h4
    rcases (centCheck_of_isRoot hαr).2.1 (forall_ne_two p0 p2 p3 p4 p5) with e | e
    · rw [e]
    · rw [e, height_neg] at hpos
      exact absurd hpos (by decide)
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
  refine ⟨w, h, hh, x, hθ (fun α hα => hα) hposcl (hfac _ h₁).1 (hfac _ h₃).1 (hfac _ h₄).1,
    y, hθ (fun α hα => inversionSet_pos hα) (inversionSet_closed w) (hfac _ h₁).2 (hfac _ h₃).2
      (hfac _ h₄).2, hgdec⟩

theorem smul_eq_of_commute
    (h2 : (2 : K) = 0) {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ torusGroup TwistTag.E6.tag K) (w : WeylGroup TwistTag.E6.tag)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (hβp : 0 < height β)
    (hc : pinnedX TwistTag.E6.tag K β 1 * (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) =
      h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * pinnedX TwistTag.E6.tag K β 1) :
    w • β = β := by
  have hroot := IsRoot.smul hβ w
  have e : pinnedX TwistTag.E6.tag K (w • β) (torusRootChar h (w • β) * 1) =
      pinnedX TwistTag.E6.tag K β 1 := by
    rw [← conj_pinnedX_of_mem_torusGroup hh hroot,
      ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hβ]
    calc h * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * pinnedX TwistTag.E6.tag K β 1 *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * h⁻¹ =
        pinnedX TwistTag.E6.tag K β 1 * (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) *
          (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by rw [hc]; group
      _ = pinnedX TwistTag.E6.tag K β 1 := mul_inv_cancel_right _ _
  exact eq_of_pinnedX_eq_pinnedX_of_pos hroot hβ hβp one_ne_zero e

theorem eq_of_pinnedX_mul_eq
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j)
    {a b a' b' : K}
    (h : pinnedX TwistTag.E6.tag K (Pi.single i 1) a * pinnedX TwistTag.E6.tag K (Pi.single j 1) b =
      pinnedX TwistTag.E6.tag K (Pi.single i 1) a' *
        pinnedX TwistTag.E6.tag K (Pi.single j 1) b') :
    a = a' ∧ b = b' := by
  have hne : (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single i 1 :=
    fun e => hij (eq_of_single_eq e).symm
  have hL := pinnedX_list_prod_injective (R := K) [Pi.single i 1, Pi.single j 1]
    (by simpa using hne.symm)
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl
      · exact ⟨isRoot_single _ _, by rw [height_single]; norm_num⟩
      · exact ⟨isRoot_single _ _, by rw [height_single]; norm_num⟩)
    (fun α => if α = Pi.single i 1 then a else b) (fun α => if α = Pi.single i 1 then a' else b')
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, hne]
      exact h)
  have h1 := hL (Pi.single i 1) (by simp)
  have h2 := hL (Pi.single j 1) (by simp)
  simp only [↓reduceIte, hne] at h1 h2
  exact ⟨h1, h2⟩

theorem not_swap
    (h2 : (2 : K) = 0) (σ : K →+* K) (hσ1 : ∃ c, σ c ≠ c)
    {h : ModGL TwistTag.E6.tag K} (hh : h ∈ torusGroup TwistTag.E6.tag K)
    (w : WeylGroup TwistTag.E6.tag) {i : Fin TwistTag.E6.tag.rank}
    (hρ : TwistTag.E6.perm i ≠ i)
    (hnr : ¬IsRoot TwistTag.E6.tag
      (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ))
    (hwi : w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (TwistTag.E6.perm i) 1)
    (hwj : w • (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single i 1)
    (hc : ∀ c : K, xUnit TwistTag.E6.tag K i c *
        xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c) *
          (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) =
      h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c))) :
    False := by
  have hne : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      Pi.single i 1 := fun e => hρ (eq_of_single_eq e)
  have hne' : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      -Pi.single i 1 := fun e => by
    have := congrFun e i
    rw [Pi.single_eq_of_ne (Ne.symm hρ), Pi.neg_apply, Pi.single_eq_same] at this
    omega
  have hcomm := commute_pinnedX_of_not_isRoot (E := K) (isRoot_single _ _) (isRoot_single _ _)
    hne hne' (by rwa [add_comm])
  have key : ∀ c : K,
      torusRootChar h (Pi.single i 1) * σ c = c ∧
        torusRootChar h (Pi.single (TwistTag.E6.perm i) 1) * c = σ c := by
    intro c
    have e := hc c
    have e2 : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c)) *
          (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
        xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c) := by
      rw [← e, mul_inv_cancel_right]
    rw [show h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c)) *
          (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
        h * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * xUnit TwistTag.E6.tag K i c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * h⁻¹ *
        (h * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) (σ c) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * h⁻¹) by group,
      ← pinnedX_single, ← pinnedX_single,
      canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ _),
      canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ _), hwi, hwj,
      conj_pinnedX_of_mem_torusGroup hh (isRoot_single _ _),
      conj_pinnedX_of_mem_torusGroup hh (isRoot_single _ _), (hcomm _ _).eq] at e2
    obtain ⟨e3, e4⟩ := eq_of_pinnedX_mul_eq (Ne.symm hρ) e2
    exact ⟨e3, e4⟩
  have h1 := (key 1).2
  rw [map_one, mul_one] at h1
  obtain ⟨c, hc'⟩ := hσ1
  have h3 := (key c).2
  rw [h1, one_mul] at h3
  exact hc' h3.symm


theorem not_isRoot_single_add_0_5
    : ¬IsRoot TwistTag.E6.tag
    (Pi.single (e6Idx 0) 1 + Pi.single (TwistTag.E6.perm (e6Idx 0)) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) := fun h => by
  obtain ⟨n, hn, e⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
  revert n
  decide +kernel

theorem not_isRoot_single_add_2_4
    : ¬IsRoot TwistTag.E6.tag
    (Pi.single (e6Idx 2) 1 + Pi.single (TwistTag.E6.perm (e6Idx 2)) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) := fun h => by
  obtain ⟨n, hn, e⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
  revert n
  decide +kernel


@[expose] def ImageCheckOne (n : ℕ) : Prop :=
  iform (TwistTag.E6.tag.rootCertificate.root n) (Pi.single (e6Idx 3) 1) = 0 →
    iform (TwistTag.E6.tag.rootCertificate.root n)
      (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1) = -1 →
    iform (TwistTag.E6.tag.rootCertificate.root n)
      (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1) = 2 →
      TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 0) 1 ∨
        TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 5) 1

@[expose] def ImageCheckThree (n : ℕ) : Prop :=
  iform (TwistTag.E6.tag.rootCertificate.root n) (Pi.single (e6Idx 3) 1) = -1 →
    iform (TwistTag.E6.tag.rootCertificate.root n)
      (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1) = 2 →
    iform (TwistTag.E6.tag.rootCertificate.root n)
      (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1) = -1 →
      TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 2) 1 ∨
        TwistTag.E6.tag.rootCertificate.root n = Pi.single (e6Idx 4) 1

instance (n : ℕ) : Decidable (ImageCheckOne n) := by
  unfold ImageCheckOne
  infer_instance

instance (n : ℕ) : Decidable (ImageCheckThree n) := by
  unfold ImageCheckThree
  infer_instance

theorem imageCheckOne :
    ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, ImageCheckOne n := by
  decide +kernel

theorem imageCheckThree :
    ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, ImageCheckThree n := by
  decide +kernel

theorem isRoot_345
    : IsRoot TwistTag.E6.tag
    (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1) :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 (by decide +kernel)

theorem isRoot_A
    : IsRoot TwistTag.E6.tag
    (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 +
      Pi.single (e6Idx 4) 1 + Pi.single (e6Idx 5) 1) :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 (by decide +kernel)

theorem mem_thetaRankOneGroup_of_torus_twisted
    [CharP K 2] (σ : K →+* K)
    (hσσ : ∀ c, σ (σ c) = c) {t : ModGL TwistTag.E6.tag K} (ht : t ∈ torusGroup TwistTag.E6.tag K)
    (htL : ∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ,
      l * t = t * l) :
    t ∈ thetaRankOneGroup (RingHom.id K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hconj : ∀ x ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ,
      rootDiagUnit TwistTag.E6.tag b * x * (rootDiagUnit TwistTag.E6.tag b)⁻¹ = x := fun x hx => by
    rw [← htL x hx, mul_inv_cancel_right]
  have h4 : b (e6Idx 3) = 1 := by
    have e := hconj _ (pinnedX_fixed_mem σ (isRoot_single _ (e6Idx 3)) (by decide) (by decide)
      (map_one σ))
    rw [rootDiagUnit_conj_pinnedX b (isRoot_single _ _), mul_one] at e
    have e' := pinnedX_injective _ _ _ e
    rw [rootChar_single'] at e'
    exact Units.ext e'
  have hpair : ∀ {i : Fin TwistTag.E6.tag.rank}, i ≠ e6Idx 1 → TwistTag.E6.perm i ≠ e6Idx 1 →
      TwistTag.E6.perm i ≠ i → ¬IsRoot TwistTag.E6.tag
        (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) →
      b i = 1 ∧ b (TwistTag.E6.perm i) = 1 := by
    intro i hi hi' hρ hnr
    have e := hconj _ (xUnit_mul_mem σ hσσ hi hi' hρ hnr 1)
    rw [map_one, show rootDiagUnit TwistTag.E6.tag b * (xUnit TwistTag.E6.tag K i 1 *
        xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) 1) * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      rootDiagUnit TwistTag.E6.tag b * xUnit TwistTag.E6.tag K i 1 *
          (rootDiagUnit TwistTag.E6.tag b)⁻¹ *
        (rootDiagUnit TwistTag.E6.tag b * xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) 1 *
          (rootDiagUnit TwistTag.E6.tag b)⁻¹) by group,
      ← pinnedX_single, ← pinnedX_single, rootDiagUnit_conj_pinnedX b (isRoot_single _ _),
      rootDiagUnit_conj_pinnedX b (isRoot_single _ _), mul_one, mul_one] at e
    obtain ⟨e1, e2⟩ := eq_of_pinnedX_mul_eq (Ne.symm hρ) e
    rw [rootChar_single'] at e1 e2
    exact ⟨Units.ext e1, Units.ext e2⟩
  obtain ⟨h0, h5⟩ := hpair (i := e6Idx 0) (by decide) (by decide) (by decide)
    (not_isRoot_single_add_0_5)
  obtain ⟨h2', h4'⟩ := hpair (i := e6Idx 2) (by decide) (by decide) (by decide)
    (not_isRoot_single_add_2_4)
  rw [show TwistTag.E6.perm (e6Idx 0) = e6Idx 5 by decide] at h5
  rw [show TwistTag.E6.perm (e6Idx 2) = e6Idx 4 by decide] at h4'
  have hb : ∀ j, j ≠ e6Idx 1 → b j = 1 := forall_ne_two h0 h2' h4 h4' h5
  have hbθ : b = Pi.mulSingle (e6Idx 1) (b (e6Idx 1)) := funext fun j => by
    by_cases hj : j = e6Idx 1
    · subst hj
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, hb j hj]
  refine thetaTorus_le_thetaRankOneGroup h2 ⟨b (e6Idx 1), ?_⟩
  rw [hbθ]
  rfl

theorem sigma_sigma [Finite K] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (c : K) : σ (σ c) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK]
  exact FiniteField.pow_card c

theorem mem_thetaRankOneGroup_of_mem_centralizer_twisted
    [Finite K] [CharP K 2]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ adjointGroup TwistTag.E6.tag K)
    (hgL : ∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ,
      l * g = g * l) :
    g ∈ thetaRankOneGroup (RingHom.id K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hσσ : ∀ c, σ (σ c) = c := sigma_sigma hK hσ
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hu' : orderOf u = (2 ^ f) ^ 2 - 1 := by rw [hu, Nat.card_units, hK]
  have hσu : Units.map σ.toMonoidHom u = u ^ 2 ^ f := Units.ext (by simp [hσ])
  have hlt : 2 ^ f + 1 < (2 ^ f) ^ 2 - 1 := by
    have : 4 * 2 ^ f ≤ (2 ^ f) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hq4
    omega
  have hs1 : u ^ (2 ^ f + 1) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by positivity) (by rw [hu']; exact hlt)
  have huq : u ^ (2 ^ f) ^ 2 = u := by
    have h1 : u ^ ((2 ^ f) ^ 2 - 1) = 1 := by rw [← hu']; exact pow_orderOf_eq_one u
    have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    rw [show (2 ^ f) ^ 2 = (2 ^ f) ^ 2 - 1 + 1 by omega, pow_succ, h1, one_mul]
  have hσs : Units.map σ.toMonoidHom (u ^ (2 ^ f + 1)) = u ^ (2 ^ f + 1) := by
    rw [map_pow, hσu, ← pow_mul, show 2 ^ f * (2 ^ f + 1) = (2 ^ f) ^ 2 + 2 ^ f by ring,
      pow_add, huq, pow_succ, mul_comm]
  have hσ1 : ∃ c, σ c ≠ c := by
    refine ⟨(u : K), fun e => ?_⟩
    have e' : u ^ 2 ^ f = u := by
      rw [← hσu]
      exact Units.ext e
    have hlt' : 2 ^ f - 1 < orderOf u := by rw [hu']; omega
    refine pow_ne_one_of_lt_orderOf (n := 2 ^ f - 1) (by omega) hlt' ?_
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [show 2 ^ f = 2 ^ f - 1 + 1 by omega, pow_succ] at e'
    exact mul_eq_right.1 e'
  have hT : ∀ {a : Fin TwistTag.E6.tag.rank → Kˣ}, rootDiagUnit TwistTag.E6.tag a ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ →
      g ∈ toralCentralizer TwistTag.E6.tag K a := fun ha =>
    mem_toralCentralizer.2 ⟨hg, by rw [hgL _ ha, mul_inv_cancel_right]⟩
  have h₁ := hT (a := (fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 0) l) *
      fun l => (u ^ 2 ^ f) ^ TwistTag.E6.tag.cartan (e6Idx 5) l) (by
    have := torusElt_mul_mem σ hσσ (i := e6Idx 0) (by decide) (by decide) u
    rwa [show TwistTag.E6.perm (e6Idx 0) = e6Idx 5 by decide, hσu, torusElt_mul_eq] at this)
  have h₃ := hT (a := (fun l => u ^ TwistTag.E6.tag.cartan (e6Idx 2) l) *
      fun l => (u ^ 2 ^ f) ^ TwistTag.E6.tag.cartan (e6Idx 4) l) (by
    have := torusElt_mul_mem σ hσσ (i := e6Idx 2) (by decide) (by decide) u
    rwa [show TwistTag.E6.perm (e6Idx 2) = e6Idx 4 by decide, hσu, torusElt_mul_eq] at this)
  have h₄ := hT (a := fun l => (u ^ (2 ^ f + 1)) ^ TwistTag.E6.tag.cartan (e6Idx 3) l) (by
    have := torusElt_four_mem σ hσs
    rwa [torusElt_eq_rootDiagUnit] at this)
  obtain ⟨w, h, hh, x, hx, y, hy, hgdec⟩ :=
    exists_factor_of_commute_twisted h2 hq4 hu' hs1 h₁ h₃ h₄
  have hXL : ∀ {z : ModGL TwistTag.E6.tag K}, z ∈ thetaRankOneGroup (RingHom.id K) →
      z ∈ centralizer (subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ :
        Set (ModGL TwistTag.E6.tag K)) := fun hz => mem_centralizer_iff.2 fun l hl =>
    mem_centralizer_iff.1 (thetaRankOneGroup_le_centralizer (f := 2 * f) (by omega)
      (by rw [hK, ← pow_mul, mul_comm]) hz) l (mem_inf.1 hl).1
  have hx' : h * x * h⁻¹ ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
    (mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot hh) x).1 hx
  have hgJ : g = (h * x * h⁻¹) * (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w) * y := by
    rw [hgdec]
    group
  have hmC : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈
      centralizer (subsystemGroup TwistTag.E6.tag K setA ⊓ twistedFixedGroup TwistTag.E6 K σ :
        Set (ModGL TwistTag.E6.tag K)) := by
    rw [show h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w =
      (h * x * h⁻¹)⁻¹ * g * y⁻¹ by rw [hgJ]; group]
    exact mul_mem (mul_mem (inv_mem (hXL (rootSubgroup_le_thetaRankOneGroup hx')))
      (mem_centralizer_iff.2 hgL)) (inv_mem (hXL (rootSubgroup_le_thetaRankOneGroup hy)))
  have hm := mem_centralizer_iff.1 hmC
  have hfix : ∀ {β : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag β → 0 < height β →
      β (e6Idx 1) = 0 → permLattice TwistTag.E6.perm β = β → w • β = β :=
    fun hβ hpos h0 hρ =>
      smul_eq_of_commute h2 hh w hβ hpos (hm _ (pinnedX_fixed_mem σ hβ h0 hρ (map_one σ)))
  have hw4 := hfix (β := Pi.single (e6Idx 3) 1) (isRoot_single _ _) (by decide) (by decide)
    (by decide)
  have hw345 := hfix isRoot_345 (by decide) (by decide) (by decide)
  have hwA := hfix isRoot_A (by decide) (by decide) (by decide)
  have hw35 : w • (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1 := by
    have e : (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1) -
          Pi.single (e6Idx 3) 1 := by abel
    rw [e, smul_sub, hw345, hw4]
  have hw16 : w • (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1 :
      Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1 := by
    have e : (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 +
          Pi.single (e6Idx 4) 1 + Pi.single (e6Idx 5) 1) -
        (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1) := by abel
    rw [e, smul_sub, hwA, hw345]
  have hiform : ∀ {α v : Fin TwistTag.E6.tag.rank → ℤ}, w • v = v →
      iform (w • α) v = iform α v := fun hv => by
    conv_lhs => rw [← hv]
    exact iform_smul w _ _
  have hpairfix : ∀ {i : Fin TwistTag.E6.tag.rank}, i ≠ e6Idx 1 →
      TwistTag.E6.perm i ≠ e6Idx 1 → TwistTag.E6.perm i ≠ i →
      ¬IsRoot TwistTag.E6.tag
        (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) →
      w • (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 →
      (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single i 1 ∨
        w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (TwistTag.E6.perm i) 1) →
      w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single i 1 ∧
        w • (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
          Pi.single (TwistTag.E6.perm i) 1 := by
    intro i hi hi' hρ hnr hsum hcases
    have hother : ∀ {a b : Fin TwistTag.E6.tag.rank → ℤ}, w • (Pi.single i 1 : Fin _ → ℤ) = a →
        a + b = Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 →
        w • (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) = b := by
      intro a b ha hab
      have e := hsum
      rw [smul_add, ha, ← hab] at e
      exact add_left_cancel e
    rcases hcases with e | e
    · exact ⟨e, hother e rfl⟩
    · exfalso
      exact not_swap h2 σ hσ1 hh w hρ hnr e (hother e (add_comm _ _))
        (fun c => hm _ (xUnit_mul_mem σ hσσ hi hi' hρ hnr c))
  have hcand : ∀ (j : Fin TwistTag.E6.tag.rank),
      (∀ n < TwistTag.E6.tag.rootCertificate.roots.length,
        iform (TwistTag.E6.tag.rootCertificate.root n) (Pi.single (e6Idx 3) 1) =
          iform (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single (e6Idx 3) 1) →
        iform (TwistTag.E6.tag.rootCertificate.root n)
          (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1) =
          iform (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)
            (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 4) 1) →
        iform (TwistTag.E6.tag.rootCertificate.root n)
          (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1) =
          iform (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)
            (Pi.single (e6Idx 0) 1 + Pi.single (e6Idx 5) 1) →
        TwistTag.E6.tag.rootCertificate.root n = Pi.single j 1 ∨
          TwistTag.E6.tag.rootCertificate.root n = Pi.single (TwistTag.E6.perm j) 1) →
      w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1 ∨
        w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (TwistTag.E6.perm j) 1 := by
    intro j hchk
    obtain ⟨n, hn, e⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1
      (IsRoot.smul (isRoot_single _ j) w)
    rw [← e]
    exact hchk n hn (by rw [e, hiform hw4]) (by rw [e, hiform hw35]) (by rw [e, hiform hw16])
  obtain ⟨hw1, hw6⟩ := hpairfix (i := e6Idx 0) (by decide) (by decide) (by decide)
    not_isRoot_single_add_0_5 hw16 (hcand (e6Idx 0) imageCheckOne)
  obtain ⟨hw3, hw5⟩ := hpairfix (i := e6Idx 2) (by decide) (by decide) (by decide)
    not_isRoot_single_add_2_4 hw35 (hcand (e6Idx 2) imageCheckThree)
  rw [show TwistTag.E6.perm (e6Idx 0) = e6Idx 5 by decide] at hw6
  rw [show TwistTag.E6.perm (e6Idx 2) = e6Idx 4 by decide] at hw5
  have hwj : ∀ j, j ≠ e6Idx 1 →
      w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1 :=
    forall_ne_two hw1 hw3 hw4 hw5 hw6
  have hw2 := (centCheck_of_isRoot (IsRoot.smul (isRoot_single TwistTag.E6.tag (e6Idx 1)) w)).2.2
    fun j hj => by
      rw [← iform_single_eq_pairE6, ← iform_single_eq_pairE6]
      calc iform (w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ))
            (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by rw [hwj j hj]
        _ = iform (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single j 1) :=
          iform_smul w _ _
  have hJ := fun {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot) =>
      rootSubgroup_le_thetaRankOneGroup (K := K) hz
  rcases hw2 with h0 | h0
  ·
    have hw1' : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = e6Idx 1
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hwj i hi, height_single]
        norm_num
    subst hw1'
    rw [canonicalRep_one, mul_one] at hm hgJ
    rw [hgJ]
    exact mul_mem (mul_mem (hJ hx') (mem_thetaRankOneGroup_of_torus_twisted σ hσσ hh hm))
      (hJ hy)
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
    have htJ := mem_thetaRankOneGroup_of_torus_twisted σ hσσ ht
      (mem_centralizer_iff.1 (mul_mem hmC (hXL hnJ)))
    have e : h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w =
        (h * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * E6GraphLevi.thetaSL2 K WSL) *
          (E6GraphLevi.thetaSL2 K WSL)⁻¹ := by group
    rw [hgJ, e]
    exact mul_mem (mul_mem (hJ hx') (mul_mem htJ (inv_mem hnJ))) (hJ hy)

theorem mem_thetaRankOneGroup_of_mem_twistedFixedGroup
    {k : Type} [Field k] [Finite k]
    [Algebra k K] {f : ℕ} (hk : Nat.card k = 2 ^ f) (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL TwistTag.E6.tag K}
    (hgX : g ∈ thetaRankOneGroup (RingHom.id K))
    (hgΓ : g ∈ twistedFixedGroup TwistTag.E6 K σ) :
    g ∈ thetaRankOneGroup (algebraMap k K) := by
  rw [thetaRankOneGroup_eq_range h2] at hgX ⊢
  obtain ⟨B, rfl⟩ := hgX
  have hfix := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hgΓ).2
  rw [MonoidHom.comp_apply, twistHom_thetaSL2 h2] at hfix
  have hB := thetaSL2_injective h2 hfix
  have hent : ∀ i j, ((Matrix.SpecialLinearGroup.map (RingHom.id K) B : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap k K) := by
    intro i j
    have e := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) i j) hB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at e
    refine mem_range_algebraMap_of_pow_card_eq ?_
    rw [hk, ← hσ]
    simpa using e
  choose c hc using hent
  have hdet : (Matrix.of fun i j => c i j).det = 1 := by
    apply (algebraMap k K).injective
    have hB1 := (Matrix.SpecialLinearGroup.map (RingHom.id K) B).2
    rw [Matrix.det_fin_two] at hB1
    rw [Matrix.det_fin_two, map_one, ← hB1]
    simp only [Matrix.of_apply, map_sub, map_mul, hc]
  refine ⟨(⟨Matrix.of fun i j => c i j, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) k), ?_⟩
  show thetaSL2 K (Matrix.SpecialLinearGroup.map (algebraMap k K)
      (⟨Matrix.of fun i j => c i j, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) k)) =
    thetaSL2 K (Matrix.SpecialLinearGroup.map (RingHom.id K) B)
  exact congrArg (thetaSL2 K) (E6GraphRootSL2.SL2_ext fun i j => hc i j)

theorem centralizer_twisted
    {k : Type} [Field k] [Algebra k K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    graphFixedRootGroup TwistTag.E6 K σ ⊓
        centralizer ((subsystemGroup TwistTag.E6.tag K setA ⊓
          graphFixedRootGroup TwistTag.E6 K σ : Subgroup (ModGL TwistTag.E6.tag K)) :
            Set (ModGL TwistTag.E6.tag K)) =
      thetaRankOneGroup (algebraMap k K) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, -, -, -, -, -, -, -, hLX, -, -, -, -, -, -, -, -, -, -, -, hLeq, -⟩ :=
    (even_E6_graph_finite_Levi_intersections f (by omega) k K hk hK σ hσ).2
  obtain ⟨hXC, -⟩ := (even_E6_graph_root_SL2_normalizer f (by omega) k K hk hK σ hσ).2
  refine le_antisymm (fun g hg => ?_) (le_inf hXC fun x hx => mem_centralizer_iff.2 fun l hl =>
    mem_centralizer_iff.1 (hLX hl) x hx |>.symm)
  obtain ⟨hgC, hgL⟩ := mem_inf.1 hg
  have hgΓ : g ∈ twistedFixedGroup TwistTag.E6 K σ := graphFixedRootGroup_le _ _ _ hgC
  have hX := mem_thetaRankOneGroup_of_mem_centralizer_twisted hf hK hσ (mem_inf.1 hgΓ).1
    fun l hl => by
      rw [← hLeq] at hl
      exact mem_centralizer_iff.1 hgL l hl
  exact mem_thetaRankOneGroup_of_mem_twistedFixedGroup hk h2 hσ hX hgΓ

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
