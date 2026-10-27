module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixLift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUHelp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.QuasithinUnique

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T L : Subgroup X}

theorem commutator_eq_self_of_isC2 (hL : IsC2 L) : ⁅L, L⁆ = L := by
  set N : Subgroup X := ⁅L, L⁆ with hN
  have hNL : N ≤ L := Subgroup.commutator_le_self L
  have hmap : N.map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    have hperf : ⁅barO2 L, barO2 L⁆ = barO2 L :=
      commutator_eq_self_of_isQuasisimple hL.component.2.2
    rw [hN]
    calc (⁅L, L⁆).map (QuotientGroup.mk' (CFSG.pCore 2 X))
        = ⁅L.map (QuotientGroup.mk' (CFSG.pCore 2 X)),
            L.map (QuotientGroup.mk' (CFSG.pCore 2 X))⁆ :=
          Subgroup.map_commutator L L (QuotientGroup.mk' (CFSG.pCore 2 X))
      _ = barO2 L := hperf
      _ = L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := rfl
  have hsup : L ≤ N ⊔ CFSG.pCore 2 X := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 X))) hmap
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
    rw [h]
    exact le_sup_left
  have key : ∀ x ∈ L, Odd (orderOf x) → x ∈ N := by
    intro x hxL hodd
    obtain ⟨n, hn, c, hc, hxc⟩ := Subgroup.mem_sup_of_normal_right.1 (hsup hxL)
    have hcL : c ∈ L := by
      have hcl : c = n⁻¹ * x := by rw [← hxc]; group
      rw [hcl]
      exact L.mul_mem (L.inv_mem (hNL hn)) hxL
    haveI : (N.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2
        (Subgroup.normalizer_commutator_ge_left L L)
    let f : L →* L ⧸ (N.subgroupOf L) := QuotientGroup.mk' (N.subgroupOf L)
    have hnQ : f ⟨n, hNL hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf L) (⟨n, hNL hn⟩ : L)).mpr
        (Subgroup.mem_subgroupOf.mpr hn)
    have hxcQ : f ⟨x, hxL⟩ = f ⟨c, hcL⟩ := by
      have h1 : (⟨x, hxL⟩ : L) = ⟨n, hNL hn⟩ * ⟨c, hcL⟩ := by
        ext
        exact hxc.symm
      rw [h1, map_mul, hnQ, one_mul]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := X))) ⟨c, hc⟩
    have hc_ord : orderOf c = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨c, hc⟩ : ↥(CFSG.pCore 2 X))).trans hk
    have hdvd : orderOf (f ⟨c, hcL⟩) ∣ 2 ^ k := by
      rw [← hc_ord, Subgroup.orderOf_coe (⟨c, hcL⟩ : L)]
      exact orderOf_map_dvd f ⟨c, hcL⟩
    have hoddQ : Odd (orderOf (f ⟨c, hcL⟩)) := by
      rw [← hxcQ]
      exact Odd.of_dvd_nat hodd
        (by simpa [Subgroup.orderOf_coe] using orderOf_map_dvd f ⟨x, hxL⟩)
    have hcop : Nat.Coprime (orderOf (f ⟨c, hcL⟩)) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hoddQ).pow_right k
    have hone : orderOf (f ⟨c, hcL⟩) = 1 := hcop.eq_one_of_dvd hdvd
    have hxQ : f ⟨x, hxL⟩ = 1 := by
      rw [hxcQ, ← orderOf_eq_one_iff]
      exact hone
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := N.subgroupOf L) (⟨x, hxL⟩ : L)).mp hxQ)
  apply le_antisymm hNL
  calc L = oddHull L := hL.2.1.symm
    _ ≤ N := (Subgroup.closure_le N).2 fun x hx => key x hx.1 hx.2

theorem isComponentOf_map_toStar (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) :
    CFSG.Open.IsComponentOf (L.map (toStar T)) ⊤ := by
  have hle : CFSG.pCore 2 X ≤ gnC T := pCore_le_gnC hX
  have hsurj : Function.Surjective (barToStar T hle) := barToStar_surjective T hle
  have hker : (barToStar T hle).ker = (gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    ker_barToStar T hle
  have hmap : (barO2 L).map (barToStar T hle) = L.map (toStar T) := by
    unfold barO2
    rw [Subgroup.map_map]
    rfl
  have hnot : ¬ barO2 L ≤ (barToStar T hle).ker := by
    intro hsub
    apply hLC
    rw [hker] at hsub
    have h1 : L ⊔ CFSG.pCore 2 X ≤ gnC T ⊔ CFSG.pCore 2 X := by
      have h2 := Subgroup.comap_mono (f := QuotientGroup.mk' (CFSG.pCore 2 X)) hsub
      rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    calc L ≤ L ⊔ CFSG.pCore 2 X := le_sup_left
      _ ≤ gnC T ⊔ CFSG.pCore 2 X := h1
      _ = gnC T := sup_eq_left.mpr (pCore_le_gnC hX)
  have h := CFSG.AGLEmbedding.isComponentOf_map_top_of_surj (barToStar T hle) hsurj
    hL.component hnot
  rwa [hmap] at h

theorem gnC_le_normalizer (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) :
    gnC T ≤ Subgroup.normalizer (L : Set X) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hc1 : toStar T c = 1 := (QuotientGroup.eq_one_iff (N := gnC T) c).mpr hc
  have hx : toStar T c ∈ Subgroup.normalizer ((L.map (toStar T) : Subgroup (X ⧸ gnC T)) :
      Set (X ⧸ gnC T)) := by
    rw [hc1]
    exact Subgroup.one_mem _
  exact liftOf_conj hX (isComponentOf_map_toStar hX hL hLC) ⟨hL, rfl⟩ c hx

theorem commutator_inf_gnC_le (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) :
    ⁅L, L ⊓ gnC T⁆ ≤ L ⊓ CFSG.pCore 2 X := by
  have hLs : CFSG.Open.IsComponentOf (L.map (toStar T)) ⊤ :=
    isComponentOf_map_toStar hX hL hLC
  have hcentral := (liftOf_central_ext hX hLs ⟨hL, rfl⟩).1
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator ha hb.1)
  · set p := QuotientGroup.mk' (CFSG.pCore 2 X) with hp
    have hbmap : p b ∈ (Subgroup.center ↥(barO2 L)).map (barO2 L).subtype :=
      hcentral (Subgroup.mem_map_of_mem p hb)
    obtain ⟨z, hz, hzb⟩ := hbmap
    have hcomm : p a * p b = p b * p a := by
      have h2 := Subgroup.mem_center_iff.1 hz (⟨p a, Subgroup.mem_map_of_mem p ha⟩ : ↥(barO2 L))
      have h3 : p a * (barO2 L).subtype z = (barO2 L).subtype z * p a := by
        simpa using congrArg Subtype.val h2
      rwa [hzb] at h3
    have hcomm' : ⁅p a, p b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    have himg : p ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, hcomm']
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 X) ⁅a, b⁆).mp himg

theorem isSylowTwoOf_inf (hX : GNSetting X T) (hL : IsC2 L) : IsSylowTwoOf (T ⊓ L) L :=
  CFSG.AGLEmbedding.AscEightSix.isSylowTwoOf_inf_of_isSubnormal_of_isSylowTwoOf hL.1 hX.sylow

theorem inf_pCore_le_inf (hX : GNSetting X T) (L : Subgroup X) :
    L ⊓ CFSG.pCore 2 X ≤ T ⊓ L := by
  intro x hx
  exact Subgroup.mem_inf.mpr ⟨pCore_le_gnC_aux1 hX.sylow hx.2, hx.1⟩

omit [Finite X] in
theorem gnImg_inf_map_eq {K : Subgroup X} (hK : gnC T ≤ K) (L : Subgroup X) :
    gnImg T K ⊓ L.map (toStar T) = (L ⊓ K).map (toStar T) := by
  have hKcomap : (K.map (toStar T)).comap (toStar T) = K := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hK
  unfold gnImg
  change K.map (toStar T) ⊓ L.map (toStar T) = (L ⊓ K).map (toStar T)
  calc K.map (toStar T) ⊓ L.map (toStar T)
      = L.map (toStar T) ⊓ K.map (toStar T) := inf_comm _ _
    _ = (L ⊓ (K.map (toStar T)).comap (toStar T)).map (toStar T) :=
        (Subgroup.map_inf_comap L (K.map (toStar T)) (toStar T)).symm
    _ = (L ⊓ K).map (toStar T) := by rw [hKcomap]

omit [Finite X] in
theorem gnC_le_centralizer {B : Subgroup X} (hB : B ≤ CFSG.Quasithin.omegaOneCenterOf T) :
    gnC T ≤ Subgroup.centralizer (B : Set X) :=
  Subgroup.centralizer_le (hB.trans Subgroup.subset_normalClosure)

theorem pElementSubgroup_two_gnA_le (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T)
    {B : Subgroup X} (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    pElementSubgroup 2 (gnA T B (L.map (toStar T))) ≤
      (L ⊓ Subgroup.normalizer (B : Set X)).map (toStar T) := by
  unfold gnA gnImg
  change pElementSubgroup 2
      (Subgroup.map (toStar T) (Subgroup.normalizer (B : Set X)) ⊓
        Subgroup.map (toStar T) L) ≤
    Subgroup.map (toStar T) (L ⊓ Subgroup.normalizer (B : Set X))
  rw [inf_comm]
  exact pElementSubgroup_two_map_inf_le (C := gnC T) (L := L) (B := B) (S := T ⊓ L)
    (gnC_le_normalizer hX hL hLC) (inf_le_left.trans hTB) (isSylowTwoOf_inf hX hL)

theorem le_of_map_toStar_le (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T)
    {H : Subgroup X} (hHL : H ≤ L) (hTH : T ⊓ L ≤ H)
    (hmap : L.map (toStar T) ≤ H.map (toStar T)) : L ≤ H := by
  have hsup : L ≤ H ⊔ gnC T := by
    intro x hx
    rw [CFSG.AGLEmbeddingD2.GN.mem_sup_gnC_iff]
    exact hmap (Subgroup.mem_map_of_mem (toStar T) hx)
  exact le_of_le_sup_of_perfect hHL (commutator_eq_self_of_isC2 hL)
    ((commutator_inf_gnC_le hX hL hLC).trans ((inf_pCore_le_inf hX L).trans hTH)) hsup

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
