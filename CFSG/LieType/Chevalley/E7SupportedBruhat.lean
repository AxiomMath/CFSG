module

public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}

theorem rootSubgroup_le_subsystemGroup
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ J) :
    rootSubgroup τ K α ≤ subsystemGroup τ K J := by
  rcases IsRoot.height_pos_or_neg hα.1 with hpos | hneg
  · exact (le_iSup₂_of_le α (mem_parabolicPosRoots_of hα hpos) le_rfl :
      rootSubgroup τ K α ≤ parabolicLeviUnipotent τ K J).trans
      parabolicLeviUnipotent_le_subsystemGroup
  · have hmem : -α ∈ parabolicPosRoots τ J :=
      mem_parabolicPosRoots_of (neg_mem_parabolicRoots hα) (by rw [height_neg]; omega)
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-α) rfl hmem
    have hα' : α = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by
      rw [smul_neg, hwj, neg_neg]
    rw [hα', ← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ j)]
    rintro _ ⟨u, hu, rfl⟩
    have huQ : u ∈ subsystemGroup τ K J := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_subsystemGroup hj c
    have hn := canonicalRep_mem_subsystemGroup (K := K) hw
    exact mul_mem (mul_mem hn huQ) (inv_mem hn)

theorem subsystemGroup_eq_rootSpan
    (J : Set (Fin τ.rank)) :
    subsystemGroup τ K J = rootSpan τ K (parabolicRoots τ J) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (iSup₂_le fun α hα => rootSubgroup_le_subsystemGroup hα)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (single_mem_parabolicRoots hj) c
  · rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan (neg_mem_parabolicRoots (single_mem_parabolicRoots hj)) c

theorem subsystemGroup_inf_torusGroup_eq_supportedTorus
    (J : Set (Fin τ.rank)) :
    subsystemGroup τ K J ⊓ torusGroup τ K = supportedTorus τ K J := by
  rw [subsystemGroup_inf_torusGroup, supportedTorus_eq_subsystemTorus]

variable (τ K) in
@[expose] def supportedCell
    (J : Set (Fin τ.rank)) (v : WeylGroup τ) : Set (ModGL τ K) :=
  (supportedTorus τ K J : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set (ModGL τ K)) *
    {canonicalRep (coxeterSystem τ) K v} *
      (rootSpan τ K (parabolicRoots τ J ∩ inversionSet v) : Set (ModGL τ K))

theorem mem_supportedCell
    {v : WeylGroup τ} {g : ModGL τ K} :
    g ∈ supportedCell τ K J v ↔ ∃ h ∈ supportedTorus τ K J, ∃ u ∈ parabolicLeviUnipotent τ K J,
      ∃ u' ∈ rootSpan τ K (parabolicRoots τ J ∩ inversionSet v),
        h * u * canonicalRep (coxeterSystem τ) K v * u' = g := by
  simp only [supportedCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨_, ⟨h, hh, u, hu, rfl⟩, _, rfl, rfl⟩, u', hu', rfl⟩
    exact ⟨h, hh, u, hu, u', hu', rfl⟩
  · rintro ⟨h, hh, u, hu, u', hu', rfl⟩
    exact ⟨_, ⟨_, ⟨h, hh, u, hu, rfl⟩, _, rfl, rfl⟩, u', hu', rfl⟩

theorem parabolicRoots_inter_inversionSet
    {v : WeylGroup τ} (hv : v ∈ parabolicWeylGroup τ J) :
    parabolicRoots τ J ∩ inversionSet v = inversionSet v :=
  Set.inter_eq_right.2 fun _ hα => (inversionSet_subset_parabolicPosRoots hv hα).1

theorem supportedCell_eq_subsystemCell
    {v : WeylGroup τ} (hv : v ∈ parabolicWeylGroup τ J) :
    supportedCell τ K J v = subsystemCell τ K J v := by
  rw [subsystemCell_eq_mul hv, coe_subsystemBorel, supportedCell,
    supportedTorus_eq_subsystemTorus, parabolicRoots_inter_inversionSet hv]

theorem supportedCell_subset_bruhatCell
    (v : WeylGroup τ) :
    supportedCell τ K J v ⊆ bruhatCell τ K v := by
  intro g hg
  obtain ⟨h, hh, u, hu, u', hu', rfl⟩ := mem_supportedCell.1 hg
  have hu'B : u' ∈ borelGroup τ K :=
    ((rootSpan_le_posUnipotent fun α hα => ⟨hα.2.1, hα.2.2.1⟩).trans le_sup_right :
      rootSpan τ K (parabolicRoots τ J ∩ inversionSet v) ≤ borelGroup τ K) hu'
  refine mem_bruhatCell.2 ⟨h * u, mul_mem
    (torusGroup_le_borelGroup (supportedTorus_le_torusGroup J hh))
    (((parabolicLeviUnipotent_le_posUnipotent J).trans le_sup_right :
      parabolicLeviUnipotent τ K J ≤ borelGroup τ K) hu), u', hu'B, rfl⟩

theorem disjoint_supportedCell
    {v v' : WeylGroup τ} (h : v ≠ v') :
    Disjoint (supportedCell τ K J v) (supportedCell τ K J v') :=
  (disjoint_bruhatCell h).mono (supportedCell_subset_bruhatCell v)
    (supportedCell_subset_bruhatCell v')

theorem coe_subsystemGroup_eq_iUnion_supportedCell
    (J : Set (Fin τ.rank)) :
    (subsystemGroup τ K J : Set (ModGL τ K)) =
      ⋃ v ∈ parabolicWeylGroup τ J, supportedCell τ K J v := by
  rw [subsystemGroup_eq_subsystemCells]
  ext x
  simp only [subsystemCells, Set.mem_iUnion, exists_prop]
  exact exists_congr fun v => and_congr_right fun hv => by rw [supportedCell_eq_subsystemCell hv]

theorem bijOn_supportedCell
    (v : WeylGroup τ) :
    Set.BijOn (fun p : ModGL τ K × ModGL τ K × ModGL τ K =>
        p.1 * p.2.1 * canonicalRep (coxeterSystem τ) K v * p.2.2)
      ((supportedTorus τ K J : Set (ModGL τ K)) ×ˢ
        (parabolicLeviUnipotent τ K J : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (parabolicRoots τ J ∩ inversionSet v) : Set (ModGL τ K)))
      (supportedCell τ K J v) := by
  have hH : ∀ h ∈ supportedTorus τ K J, h ∈ torusGroup τ K := fun h hh =>
    supportedTorus_le_torusGroup J hh
  have hU : ∀ u ∈ parabolicLeviUnipotent τ K J, u ∈ posUnipotent τ K := fun u hu =>
    parabolicLeviUnipotent_le_posUnipotent J hu
  have hB : ∀ h ∈ supportedTorus τ K J, ∀ u ∈ parabolicLeviUnipotent τ K J,
      h * u ∈ borelGroup τ K := fun h hh u hu =>
    mul_mem (torusGroup_le_borelGroup (hH h hh)) (Subgroup.mem_sup_right (hU u hu))
  have hI : rootSpan τ K (parabolicRoots τ J ∩ inversionSet v) ≤ rootSpan τ K (inversionSet v) :=
    rootSpan_mono Set.inter_subset_right
  refine ⟨fun p hp => mem_supportedCell.2 ⟨p.1, hp.1, p.2.1, hp.2.1, p.2.2, hp.2.2, rfl⟩,
    fun p hp q hq hpq => ?_, fun g hg => ?_⟩
  · have h1 := (bijOn_bruhatCell (K := K) v).injOn (x₁ := (p.1 * p.2.1, p.2.2))
      (x₂ := (q.1 * q.2.1, q.2.2)) ⟨hB _ hp.1 _ hp.2.1, hI hp.2.2⟩ ⟨hB _ hq.1 _ hq.2.1, hI hq.2.2⟩
      hpq
    obtain ⟨h2, h3⟩ := Prod.ext_iff.1 h1
    obtain ⟨h4, h5⟩ := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.1 p.1 (hH _ hp.1) q.1
      (hH _ hq.1) p.2.1 (hU _ hp.2.1) q.2.1 (hU _ hq.2.1) h2
    exact Prod.ext h4 (Prod.ext h5 h3)
  · obtain ⟨h, hh, u, hu, u', hu', rfl⟩ := mem_supportedCell.1 hg
    exact ⟨(h, u, u'), ⟨hh, hu, hu'⟩, rfl⟩

theorem existsUnique_supportedCell_factors
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) :
    ∃! p : WeylGroup τ × ModGL τ K × ModGL τ K × ModGL τ K, p.1 ∈ parabolicWeylGroup τ J ∧
      p.2.1 ∈ supportedTorus τ K J ∧ p.2.2.1 ∈ parabolicLeviUnipotent τ K J ∧
      p.2.2.2 ∈ rootSpan τ K (parabolicRoots τ J ∩ inversionSet p.1) ∧
      p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem τ) K p.1 * p.2.2.2 = g := by
  have hg' : g ∈ ⋃ v ∈ parabolicWeylGroup τ J, supportedCell τ K J v := by
    rw [← coe_subsystemGroup_eq_iUnion_supportedCell]
    exact hg
  simp only [Set.mem_iUnion, exists_prop] at hg'
  obtain ⟨v, hv, hgv⟩ := hg'
  obtain ⟨h, hh, u, hu, u', hu', rfl⟩ := mem_supportedCell.1 hgv
  refine ⟨(v, h, u, u'), ⟨hv, hh, hu, hu', rfl⟩, ?_⟩
  rintro ⟨v₂, h₂, u₂, u₂'⟩ ⟨-, hh₂, hu₂, hu₂', he⟩
  have hv₂ : v₂ = v := by
    by_contra hne
    have h1 : h₂ * u₂ * canonicalRep (coxeterSystem τ) K v₂ * u₂' ∈ supportedCell τ K J v₂ :=
      mem_supportedCell.2 ⟨_, hh₂, _, hu₂, _, hu₂', rfl⟩
    rw [he] at h1
    exact Set.disjoint_left.1 (disjoint_supportedCell hne) h1 hgv
  subst hv₂
  have h1 := (bijOn_supportedCell (K := K) (J := J) v₂).injOn (x₁ := (h₂, u₂, u₂'))
    (x₂ := (h, u, u')) ⟨hh₂, hu₂, hu₂'⟩ ⟨hh, hu, hu'⟩ he
  rw [h1]

theorem bijOn_prod_pinnedX_parabolicPosRoots
    {m : ℕ} (α : Fin m → Fin τ.rank → ℤ)
    (hα : Function.Injective α) (hrange : Set.range α = parabolicPosRoots τ J) :
    Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) Set.univ
      (parabolicLeviUnipotent τ K J) :=
  bijOn_prod_pinnedX K (fun _ h => h.2)
    (fun _ hβ _ hγ _ _ ha hb hr => add_mem_parabolicPosRoots hβ hγ ha hb hr) α hα hrange

theorem bijOn_prod_pinnedX_parabolicRoots_inter_inversionSet
    (v : WeylGroup τ) {m : ℕ}
    (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hrange : Set.range α = parabolicRoots τ J ∩ inversionSet v) :
    Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) Set.univ
      (rootSpan τ K (parabolicRoots τ J ∩ inversionSet v)) :=
  bijOn_prod_pinnedX K (S := parabolicRoots τ J ∩ inversionSet v) (fun _ h => ⟨h.2.1, h.2.2.1⟩)
    (fun β hβ γ hγ a b ha hb hr => ⟨⟨hr, fun i hi => by simp [hβ.1.2 i hi, hγ.1.2 i hi]⟩,
      inversionSet_closed v β hβ.2 γ hγ.2 a b ha hb hr⟩) α hα hrange

theorem mem_supportedTorus_of_mem_center
    {g : subsystemGroup τ K J}
    (hg : g ∈ Subgroup.center (subsystemGroup τ K J)) :
    (g : ModGL τ K) ∈ supportedTorus τ K J := by
  have hcomm : ∀ x ∈ subsystemGroup τ K J, x * (g : ModGL τ K) = g * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hg ⟨x, hx⟩)
  obtain ⟨v, hv, hgv⟩ := mem_subsystemCells.1 (subsystemGroup_subset_subsystemCells g.2)
  rw [subsystemCell_eq_mul hv] at hgv
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, u, hu, hbu⟩ := hgv
  beta_reduce at hbu
  have hv1 : v = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (weyl_exchange_condition τ).2.2.2 v hne
    have hiJ : i ∈ J := by
      by_contra hiJ
      have h1 := (IsRoot.height_neg_iff hi.1).1 hi.2 i
      rw [smul_apply_of_mem_parabolicWeylGroup hv _ hiJ, Pi.single_eq_same] at h1
      omega
    have hI : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ inversionSet v :=
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos, hi⟩
    have hx : xUnit τ K i 1 ∈ rootSpan τ K (inversionSet v) := by
      rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan hI 1
    have hc := hcomm _ (xUnit_mem_subsystemGroup hiJ 1)
    rw [← hbu] at hc
    have h1 := (bijOn_subsystemCell (K := K) hv).injOn (x₁ := (xUnit τ K i 1 * b, u))
      (x₂ := (b, u * xUnit τ K i 1)) ⟨mul_mem (xUnit_mem_subsystemBorel hiJ 1) hb, hu⟩
      ⟨hb, mul_mem hu hx⟩ (by
        simp only [mul_assoc] at hc ⊢
        exact hc)
    have h2 : xUnit τ K i 1 = 1 := by
      have h3 := (Prod.ext_iff.1 h1).1
      simpa using h3
    have h4 : pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 := by
      rw [pinnedX_single, pinnedX_zero, h2]
    exact one_ne_zero (pinnedX_injective τ K _ h4)
  subst hv1
  have hu1 : u = 1 := by
    rw [inversionSet_one] at hu
    simpa [rootSpan] using hu
  have hgB : (g : ModGL τ K) ∈ subsystemBorel τ K J := by
    rw [← hbu, hu1, canonicalRep_one, mul_one, mul_one]
    exact hb
  rw [← SetLike.mem_coe, coe_subsystemBorel] at hgB
  obtain ⟨t, ht, w', hw', htw⟩ := hgB
  obtain ⟨wJ, ⟨hwJ, hwJΦ⟩, -⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.2.2
  set n := canonicalRep (coxeterSystem τ) K wJ
  have hconj : n * (g : ModGL τ K) * n⁻¹ = g := by
    rw [hcomm n (canonicalRep_mem_subsystemGroup hwJ), mul_inv_cancel_right]
  have hnt : n * t * n⁻¹ ∈ torusGroup τ K :=
    subsystemTorus_le_torusGroup (canonicalRep_conj_mem_subsystemTorus hwJ ht)
  have hnw : n * w' * n⁻¹ ∈ negUnipotent τ K := by
    have h1 := canonicalRep_conj_mem_rootSpan (w := wJ) (S := parabolicPosRoots τ J)
      (fun α hα => hα.2.1) hw'
    rw [hwJΦ] at h1
    refine rootSpan_le_negUnipotent ?_ h1
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.neg hα.2.1, by rw [height_neg]; linarith [hα.2.2]⟩
  have hmem : (n * t * n⁻¹)⁻¹ * (g : ModGL τ K) ∈ borelGroup τ K ⊓ negUnipotent τ K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (torusGroup_le_borelGroup (inv_mem hnt)) ?_, ?_⟩
    · rw [← htw]
      exact mul_mem (torusGroup_le_borelGroup (subsystemTorus_le_torusGroup ht))
        (Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent J hw'))
    · have e : n * (g : ModGL τ K) * n⁻¹ = n * t * n⁻¹ * (n * w' * n⁻¹) := by
        rw [← htw]
        group
      rw [← hconj, e, inv_mul_cancel_left]
      exact hnw
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
  have hgH : (g : ModGL τ K) ∈ torusGroup τ K := by
    rw [← inv_mul_eq_one.1 hmem]
    exact hnt
  rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus]
  exact Subgroup.mem_inf.2 ⟨g.2, hgH⟩

theorem mem_center_subsystemGroup_iff
    (g : subsystemGroup τ K J) :
    g ∈ Subgroup.center (subsystemGroup τ K J) ↔ (g : ModGL τ K) ∈ supportedTorus τ K J ∧
      ∀ α ∈ parabolicRoots τ J, torusRootChar (g : ModGL τ K) α = 1 := by
  constructor
  · intro hg
    have hgH := mem_supportedTorus_of_mem_center hg
    refine ⟨hgH, fun α hα => ?_⟩
    refine (commute_pinnedX_iff (supportedTorus_le_torusGroup J hgH) hα.1).1 fun c => ?_
    have hx : pinnedX τ K α c ∈ subsystemGroup τ K J := by
      rw [subsystemGroup_eq_rootSpan]
      exact pinnedX_mem_rootSpan hα c
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hg ⟨_, hx⟩)).symm
  · rintro ⟨hgH, hχ⟩
    have hT := supportedTorus_le_torusGroup J hgH
    have hle : subsystemGroup τ K J ≤ Subgroup.centralizer {(g : ModGL τ K)} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
        exact ((commute_pinnedX_iff hT (isRoot_single τ j)).2
          (hχ _ (single_mem_parabolicRoots hj)) c).symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
        exact ((commute_pinnedX_iff hT (isRoot_neg_single τ j)).2
          (hχ _ (neg_mem_parabolicRoots (single_mem_parabolicRoots hj))) c).symm
    refine Subgroup.mem_center_iff.2 fun x => Subtype.ext ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle x.2)

variable (τ K J) in
theorem supported_Bruhat_and_exact_native_torus_kernel :
    subsystemGroup τ K J = rootSpan τ K (parabolicRoots τ J) ∧
    subsystemGroup τ K J ⊓ torusGroup τ K = supportedTorus τ K J ∧
    supportedTorus τ K J = subsystemTorus τ K J ∧
    (∀ v ∈ parabolicWeylGroup τ J, parabolicRoots τ J ∩ inversionSet v = inversionSet v) ∧
    (subsystemGroup τ K J : Set (ModGL τ K)) =
      ⋃ v ∈ parabolicWeylGroup τ J, supportedCell τ K J v ∧
    (∀ v v' : WeylGroup τ, v ≠ v' → Disjoint (supportedCell τ K J v) (supportedCell τ K J v')) ∧
    (∀ v : WeylGroup τ, Set.BijOn (fun p : ModGL τ K × ModGL τ K × ModGL τ K =>
        p.1 * p.2.1 * canonicalRep (coxeterSystem τ) K v * p.2.2)
      ((supportedTorus τ K J : Set (ModGL τ K)) ×ˢ
        (parabolicLeviUnipotent τ K J : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (parabolicRoots τ J ∩ inversionSet v) : Set (ModGL τ K)))
      (supportedCell τ K J v)) ∧
    (∀ g ∈ subsystemGroup τ K J,
      ∃! p : WeylGroup τ × ModGL τ K × ModGL τ K × ModGL τ K, p.1 ∈ parabolicWeylGroup τ J ∧
        p.2.1 ∈ supportedTorus τ K J ∧ p.2.2.1 ∈ parabolicLeviUnipotent τ K J ∧
        p.2.2.2 ∈ rootSpan τ K (parabolicRoots τ J ∩ inversionSet p.1) ∧
        p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem τ) K p.1 * p.2.2.2 = g) ∧
    (∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = parabolicPosRoots τ J →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (parabolicLeviUnipotent τ K J)) ∧
    (∀ (v : WeylGroup τ) {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = parabolicRoots τ J ∩ inversionSet v →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K (parabolicRoots τ J ∩ inversionSet v))) ∧
    (∀ [Fintype J] (a : J → Kˣ), a ∈ (supportedTorusHom τ K J).ker ↔
      ∀ i : Fin τ.rank, ∏ j : J, a j ^ τ.cartan j i = 1) ∧
    (∀ h ∈ torusGroup τ K, ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (h : Module.End K (RootModule τ K)) (rootVec τ K α) = torusRootChar h α • rootVec τ K α ∧
      (∀ c : K, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (torusRootChar h α * c)) ∧
      ∀ s : K, (∀ c : K, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (s * c)) →
        s = torusRootChar h α) ∧
    ∀ g : subsystemGroup τ K J, g ∈ Subgroup.center (subsystemGroup τ K J) ↔
      (g : ModGL τ K) ∈ supportedTorus τ K J ∧
        ∀ α ∈ parabolicRoots τ J, torusRootChar (g : ModGL τ K) α = 1 :=
  ⟨subsystemGroup_eq_rootSpan J, subsystemGroup_inf_torusGroup_eq_supportedTorus J,
    supportedTorus_eq_subsystemTorus J, fun _ hv => parabolicRoots_inter_inversionSet hv,
    coe_subsystemGroup_eq_iUnion_supportedCell J, fun _ _ h => disjoint_supportedCell h,
    bijOn_supportedCell, fun _ hg => existsUnique_supportedCell_factors hg,
    fun α hα hrange => bijOn_prod_pinnedX_parabolicPosRoots α hα hrange,
    fun v _ α hα hrange => bijOn_prod_pinnedX_parabolicRoots_inter_inversionSet v α hα hrange,
    fun a => (supportedTorusHom τ K J).mem_ker.trans (supportedTorusHom_eq_one_iff J a),
    fun _ hh _ hα => ⟨apply_rootVec_of_mem_torusGroup hh hα,
      conj_pinnedX_of_mem_torusGroup hh hα, fun _ hs => eq_torusRootChar_of_conj hh hα hs⟩,
    mem_center_subsystemGroup_iff⟩

theorem E7_supported_Bruhat_and_exact_native_torus_kernel
    (K : Type) [Field K]
    (J : Set (Fin Tag.E7.rank)) :
    subsystemGroup Tag.E7 K J = rootSpan Tag.E7 K (parabolicRoots Tag.E7 J) ∧
    subsystemGroup Tag.E7 K J ⊓ torusGroup Tag.E7 K = supportedTorus Tag.E7 K J ∧
    supportedTorus Tag.E7 K J = subsystemTorus Tag.E7 K J ∧
    (∀ v ∈ parabolicWeylGroup Tag.E7 J,
      parabolicRoots Tag.E7 J ∩ inversionSet v = inversionSet v) ∧
    (subsystemGroup Tag.E7 K J : Set (ModGL Tag.E7 K)) =
      ⋃ v ∈ parabolicWeylGroup Tag.E7 J, supportedCell Tag.E7 K J v ∧
    (∀ v v' : WeylGroup Tag.E7, v ≠ v' →
      Disjoint (supportedCell Tag.E7 K J v) (supportedCell Tag.E7 K J v')) ∧
    (∀ v : WeylGroup Tag.E7,
      Set.BijOn (fun p : ModGL Tag.E7 K × ModGL Tag.E7 K × ModGL Tag.E7 K =>
          p.1 * p.2.1 * canonicalRep (coxeterSystem Tag.E7) K v * p.2.2)
        ((supportedTorus Tag.E7 K J : Set (ModGL Tag.E7 K)) ×ˢ
          (parabolicLeviUnipotent Tag.E7 K J : Set (ModGL Tag.E7 K)) ×ˢ
            (rootSpan Tag.E7 K (parabolicRoots Tag.E7 J ∩ inversionSet v) :
              Set (ModGL Tag.E7 K)))
        (supportedCell Tag.E7 K J v)) ∧
    (∀ g ∈ subsystemGroup Tag.E7 K J,
      ∃! p : WeylGroup Tag.E7 × ModGL Tag.E7 K × ModGL Tag.E7 K × ModGL Tag.E7 K,
        p.1 ∈ parabolicWeylGroup Tag.E7 J ∧ p.2.1 ∈ supportedTorus Tag.E7 K J ∧
        p.2.2.1 ∈ parabolicLeviUnipotent Tag.E7 K J ∧
        p.2.2.2 ∈ rootSpan Tag.E7 K (parabolicRoots Tag.E7 J ∩ inversionSet p.1) ∧
        p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem Tag.E7) K p.1 * p.2.2.2 = g) ∧
    (∀ {m : ℕ} (α : Fin m → Fin Tag.E7.rank → ℤ), Function.Injective α →
      Set.range α = parabolicPosRoots Tag.E7 J →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX Tag.E7 K (α k) (c k)).prod)
        Set.univ (parabolicLeviUnipotent Tag.E7 K J)) ∧
    (∀ (v : WeylGroup Tag.E7) {m : ℕ} (α : Fin m → Fin Tag.E7.rank → ℤ), Function.Injective α →
      Set.range α = parabolicRoots Tag.E7 J ∩ inversionSet v →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX Tag.E7 K (α k) (c k)).prod)
        Set.univ (rootSpan Tag.E7 K (parabolicRoots Tag.E7 J ∩ inversionSet v))) ∧
    (∀ [Fintype J] (a : J → Kˣ), a ∈ (supportedTorusHom Tag.E7 K J).ker ↔
      ∀ i : Fin Tag.E7.rank, ∏ j : J, a j ^ Tag.E7.cartan j i = 1) ∧
    (∀ h ∈ torusGroup Tag.E7 K, ∀ α : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 α →
      (h : Module.End K (RootModule Tag.E7 K)) (rootVec Tag.E7 K α) =
        torusRootChar h α • rootVec Tag.E7 K α ∧
      (∀ c : K, h * pinnedX Tag.E7 K α c * h⁻¹ = pinnedX Tag.E7 K α (torusRootChar h α * c)) ∧
      ∀ s : K, (∀ c : K, h * pinnedX Tag.E7 K α c * h⁻¹ = pinnedX Tag.E7 K α (s * c)) →
        s = torusRootChar h α) ∧
    ∀ g : subsystemGroup Tag.E7 K J, g ∈ Subgroup.center (subsystemGroup Tag.E7 K J) ↔
      (g : ModGL Tag.E7 K) ∈ supportedTorus Tag.E7 K J ∧
        ∀ α ∈ parabolicRoots Tag.E7 J, torusRootChar (g : ModGL Tag.E7 K) α = 1 :=
  supported_Bruhat_and_exact_native_torus_kernel Tag.E7 K J

end CFSG.LieType.Chevalley
