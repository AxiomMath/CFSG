module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Third

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem sup_oddCoreIn_eq_of_moves_only {X M Y : Subgroup G} (hM : IsTwoComponentIn M X)
    (hYX : Y ≤ twoLayerIn X) (hY : ⁅Y, Y⁆ = Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hm : ¬ Y ≤ coreActionKernel M)
    (ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥Y ⧸ Open.fusionZStar ↥Y))
    (hother : ∀ J : Subgroup G, IsTwoComponentIn J X → J ≠ M → Y ≤ coreActionKernel J) :
    Y ⊔ oddCoreIn X = M ⊔ oddCoreIn X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYX' : Y ≤ X := hYX.trans (map_subtype_le _)
  have hYperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  have hOn : (pPrimeCore 2 ↥X).Normal := pPrimeCore_normal
  have hMc : IsComponent ((M.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X))) :=
    (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥X) 2).2.1 hM.2
  let ρ : ↥Y →* ↥X ⧸ pPrimeCore 2 ↥X :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥X)).comp (Subgroup.inclusion hYX')
  have hρ : ρ.range = (Y.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
    rw [← Subgroup.inclusion_range hYX']
    exact MonoidHom.range_comp _ _
  have hYE : ρ.range ≤ layer (↥X ⧸ pPrimeCore 2 ↥X) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le
    rintro _ ⟨y, rfl⟩
    refine mem_map_of_mem (QuotientGroup.mk' (pPrimeCore 2 ↥X)) ?_
    obtain ⟨z, hz, hzy⟩ := hYX y.2
    have : Subgroup.inclusion hYX' y = z := Subtype.ext hzy.symm
    rw [this]
    exact hz
  have hYp : ⁅ρ.range, ρ.range⁆ = ρ.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  have hfix : ∀ K : Subgroup (↥X ⧸ pPrimeCore 2 ↥X), IsComponent K →
      ¬ ρ.range ≤ centralizer (K : Set _) →
      K.map (MulAut.conj (1 : ↥X ⧸ pPrimeCore 2 ↥X)).toMonoidHom = K →
      K ≤ (M.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
    intro K hK hYK _
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥X) 2).1 K hK
    have hKt0 : ((CatalogueBPrimeJoin.canonicalPrimeLift 2 K).map X.subtype).subgroupOf X =
        CatalogueBPrimeJoin.canonicalPrimeLift 2 K := by
      rw [← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
    have hKtX : IsTwoComponentIn ((CatalogueBPrimeJoin.canonicalPrimeLift 2 K).map X.subtype) X :=
      ⟨map_subtype_le _, by rw [hKt0]; exact hK0⟩
    have hmove : ¬ Y ≤ coreActionKernel ((CatalogueBPrimeJoin.canonicalPrimeLift 2 K).map
        X.subtype) := by
      intro hc
      apply hYK
      rintro _ ⟨j, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, ← hK0map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 := oddCoreIn_le_of_isTwoComponentIn hKtX
        ((hc j.2).2 (k : G) (mem_map_of_mem X.subtype hk))
      have h2 := (mk_mul_comm_iff (N := X) k ⟨j, hYX' j.2⟩).mpr h1
      exact h2
    have hKtM : (CatalogueBPrimeJoin.canonicalPrimeLift 2 K).map X.subtype = M := by
      by_contra hne
      exact hmove (hother _ hKtX hne)
    have h0 : CatalogueBPrimeJoin.canonicalPrimeLift 2 K = M.subgroupOf X := by
      rw [← hKt0, hKtM]
    exact (hK0map.symm.trans (by rw [h0])).le
  have hYM : ρ.range ≤ (M.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
    refine le_of_pieces hYp hYE (fun _ _ => Commute.one_left _) (fun x _ => by simp)
      (fun x _ => mem_centralizer_singleton_iff.mpr (by simp)) hfix ?_
    intro K _ _ hK1
    exfalso
    apply hK1
    have : (MulAut.conj (1 : ↥X ⧸ pPrimeCore 2 ↥X)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, map_id]
  set Mb := (M.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) with hMb
  have hρM : ∀ y : ↥Y, ρ y ∈ Mb := fun y => hYM ⟨y, rfl⟩
  let f : ↥Y →* ↥Mb ⧸ center ↥Mb := (QuotientGroup.mk' (center ↥Mb)).comp (ρ.codRestrict Mb hρM)
  have hf : ∀ y : ↥Y, f y = QuotientGroup.mk' (center ↥Mb) ⟨ρ y, hρM y⟩ := fun _ => rfl
  have hkerf : f.ker ≠ ⊤ := by
    intro htop
    apply hm
    intro j hj
    have h1 : f ⟨j, hj⟩ = 1 := MonoidHom.mem_ker.mp (by rw [htop]; exact mem_top _)
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hjN : j ∈ normalizer (M : Set G) :=
      (hYX.trans (FooteLit.twoLayerIn_le_normalizer hM.1 hM.2)) hj
    refine ⟨hjN, fun a ha => ?_⟩
    have h2 := congrArg Subtype.val ((mem_center_iff.mp h1)
      ⟨QuotientGroup.mk' (pPrimeCore 2 ↥X) ⟨a, hM.1 ha⟩, ⟨a, hM.1 ha⟩, mem_subgroupOf.mpr ha, rfl⟩)
    have h3 : a⁻¹ * j⁻¹ * a * j ∈ oddCoreIn X :=
      (mk_mul_comm_iff (N := X) ⟨a, hM.1 ha⟩ ⟨j, hYX' hj⟩).mp h2
    have hmemA : a⁻¹ * j⁻¹ * a * j ∈ M := by
      have h4 : j⁻¹ * a * j⁻¹⁻¹ ∈ M := (mem_normalizer_iff.mp (inv_mem hjN) a).mp ha
      rw [inv_inv] at h4
      rw [mul_assoc, mul_assoc]
      refine mul_mem (inv_mem ha) ?_
      simpa [mul_assoc] using h4
    exact oddCoreIn_inf_le hM.1 (mem_inf.mpr ⟨h3, hmemA⟩)
  have hleZ : f.ker ≤ Open.fusionZStar ↥Y :=
    le_fusionZStar_of_normal hYperf hYq f.normal_ker hkerf
  have hMK : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = (center ↥Mb).index := by
    have h3 := index_fusionZStar_eq_index_center hMc.2 (L := M.subgroupOf X) rfl
    have h2 : Nat.card (↥M ⧸ Open.fusionZStar ↥M) =
        Nat.card (↥(M.subgroupOf X) ⧸ Open.fusionZStar ↥(M.subgroupOf X)) :=
      Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hM.1).symm).toEquiv
    rw [h2]
    exact h3
  have hrange : f.range = ⊤ := by
    have hidx : (Open.fusionZStar ↥Y).index = (center ↥Mb).index := by
      change Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = _
      rw [← ht, hMK]
    apply eq_top_of_card_eq
    apply le_antisymm (card_le_of_le le_top |>.trans (by rw [card_top]))
    change (center ↥Mb).index ≤ _
    rw [← hidx, ← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (index_dvd_of_le hleZ)
  have hsup : ρ.range.subgroupOf Mb ⊔ center ↥Mb = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨y, hy⟩ : QuotientGroup.mk' (center ↥Mb) m ∈ f.range := hrange ▸ mem_top _
    have hz : (⟨ρ y, hρM y⟩ : ↥Mb)⁻¹ * m ∈ center ↥Mb := by
      rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hy
      exact hy
    have hyM : (⟨ρ y, hρM y⟩ : ↥Mb) ∈ ρ.range.subgroupOf Mb := by
      rw [mem_subgroupOf]
      exact ⟨y, rfl⟩
    rw [show m = ⟨ρ y, hρM y⟩ * ((⟨ρ y, hρM y⟩ : ↥Mb)⁻¹ * m) by group]
    exact mul_mem (mem_sup_left hyM) (mem_sup_right hz)
  have htop := Sol76.eq_top_of_sup_center_eq_top' hMc.1.1.commutator_eq_top hsup
  have hMY : Mb ≤ ρ.range := fun m hm => by
    have h1 : (⟨m, hm⟩ : ↥Mb) ∈ ρ.range.subgroupOf Mb := by rw [htop]; trivial
    exact mem_subgroupOf.mp h1
  have hYbeq : (Y.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) = Mb := by
    rw [← hρ]
    exact le_antisymm hYM hMY
  have h2 := congrArg (fun H => (H.comap (QuotientGroup.mk' (pPrimeCore 2 ↥X))).map X.subtype)
    hYbeq
  simp only [hMb, comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hYX', map_subgroupOf_eq_of_le hM.1] at h2
  exact h2

theorem conjClosure_le_of_moves_only {X M Y : Subgroup G} (hM : IsTwoComponentIn M X)
    (hYX : Y ≤ twoLayerIn X) (hY : ⁅Y, Y⁆ = Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hm : ¬ Y ≤ coreActionKernel M)
    (ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥Y ⧸ Open.fusionZStar ↥Y))
    (hother : ∀ J : Subgroup G, IsTwoComponentIn J X → J ≠ M → Y ≤ coreActionKernel J) :
    conjClosure Y (twoLayerIn X) ≤ oddCoreIn (twoLayerIn X) ⊔ Y := by
  have heq := sup_oddCoreIn_eq_of_moves_only hM hYX hY hYq hm ht hother
  have hLX : twoLayerIn X ≤ X := map_subtype_le _
  have hYX' : Y ≤ X := hYX.trans hLX
  have hXO : X ≤ normalizer (oddCoreIn X : Set G) := le_normalizer_map_subtype' (pPrimeCore 2 ↥X)
  have hLN : twoLayerIn X ≤ normalizer ((M ⊔ oddCoreIn X : Subgroup G) : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (FooteLit.twoLayerIn_le_normalizer hM.1 hM.2 hl),
      mem_normalizer_iff_map_conj_eq.mp (hXO (hLX hl))]
  have h1 : conjClosure Y (twoLayerIn X) ≤ M ⊔ oddCoreIn X :=
    Sol78.conjClosure_le (heq ▸ le_sup_left) hLN
  have h2 : conjClosure Y (twoLayerIn X) ≤ twoLayerIn X := Sol78.conjClosure_le hYX le_normalizer
  intro z hz
  have hz1 : z ∈ oddCoreIn X ⊔ Y := by
    have h3 := h1 hz
    rwa [← heq, sup_comm] at h3
  obtain ⟨o, ho, y, hy, rfl⟩ := exists_mul_of_mem_sup_normalizer (fun y hy => hXO (hYX' hy)) hz1
  have hoL : o ∈ twoLayerIn X := by
    have h3 : o = o * y * y⁻¹ := by group
    rw [h3]
    exact mul_mem (h2 hz) (inv_mem (hYX hy))
  exact mul_mem (mem_sup_left (oddCoreIn_inf_le hLX (mem_inf.mpr ⟨ho, hoL⟩))) (mem_sup_right hy)

theorem conjClosure_le_of_pumpSet_eq {N K' : Subgroup G} (hK' : K' ∈ kStarComponents N) {b : G}
    (hbQ : b ∈ coreActionKernel K') (hb2 : orderOf b = 2) {M : Subgroup G}
    (hM : pumpSet K' (centralizer ({b} : Set G)) = {M}) :
    conjClosure (twoLayerIn (K' ⊓ centralizer ({b} : Set G)))
        (twoLayerIn (centralizer ({b} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({b} : Set G))) ⊔
        twoLayerIn (K' ⊓ centralizer ({b} : Set G)) := by
  obtain ⟨hY2, -, ⟨e⟩, h212, -⟩ := pump_facts hK' hbQ hb2
  have hMp : M ∈ pumpSet K' (centralizer ({b} : Set G)) := by
    rw [hM]
    exact Set.mem_singleton M
  have ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) =
      Nat.card (↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G))) ⧸
        Open.fusionZStar ↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G)))) := by
    rw [card_fusionZStar_of_mem_pumpSet hK' hbQ hb2 hMp, Nat.card_congr e.toEquiv]
  have hother : ∀ J : Subgroup G, IsTwoComponentIn J (centralizer ({b} : Set G)) → J ≠ M →
      twoLayerIn (K' ⊓ centralizer ({b} : Set G)) ≤ coreActionKernel J := by
    intro J hJ hJM
    by_contra hYJ
    by_cases hJs : J ∈ solomonKStar G
    · have hJp : J ∈ pumpSet K' (centralizer ({b} : Set G)) := ⟨⟨hJ, hJs⟩, hYJ⟩
      rw [hM] at hJp
      exact hJM hJp
    · apply hYJ
      refine h212.trans (iSup₂_le fun J' hJ' => ?_)
      exact GSThmB.B5a.le_coreActionKernel_of_ne hJ.1 hJ'.1.1 hJ.2 hJ'.1.2
        fun h => hJs (h ▸ hJ'.2)
  exact conjClosure_le_of_moves_only hMp.1.1 (h212.trans (solomonKStarOf_le_twoLayerIn _))
    (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
    (isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2) hMp.2 ht hother

theorem lemma32InputFor_of_twoPart {𝒜 : Thm13Ambient} (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hR1 : Lemma32ConditionTwoInputFor 𝒜)
    (hv : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N' : Subgroup G, IsKBalanced N' →
      ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G)) :
    Lemma32InputFor 𝒜 := by
  intro G _ _ hG N hN K hK K' hK' hne b hbK hb2 _
  have hbQ := mem_coreActionKernel_of_ne hK hK' hne hbK
  obtain ⟨M, hM⟩ := pumpSet_nonempty hK' hbQ hb2
  have h1 : (pumpSet K' (centralizer ({b} : Set G))).ncard = 1 := by
    have hle : (pumpSet K' (centralizer ({b} : Set G))).ncard ≤ 1 := by
      by_contra h
      exact false_of_two_le_ncard_pumpSet hq (h𝒜 G hG) hR1 hG (hv G hG) hN hK hK' hne hbK hb2
        (by omega)
    have hpos := (Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hM⟩
    omega
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp h1
  exact conjClosure_le_of_pumpSet_eq hK' hbQ hb2 hM'

end CFSG.ComponentClassification.Sol76T13
