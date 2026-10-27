module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixAltCGT
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixAltFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltDefs
public import CFSG.GroupTheory.PermSylowTwo.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.QuasithinUnique

open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X] {T L : Subgroup X}

theorem barO2_inf_normalizer_le (hX : GNSetting X T) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T)
    (hN : L.map (toStar T) ⊓ Subgroup.normalizer ((T ⊓ L).map (toStar T) : Set (X ⧸ gnC T)) ≤
      (T ⊓ L).map (toStar T)) :
    barO2 L ⊓ Subgroup.normalizer (barO2 (T ⊓ L) : Set (X ⧸ CFSG.pCore 2 X)) ≤
      barO2 (T ⊓ L) ⊔ Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := by
  have hle : CFSG.pCore 2 X ≤ gnC T := pCore_le_gnC hX
  have hcomp : (barToStar T hle).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) = toStar T := rfl
  intro x hx
  obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
  have hfxL : barToStar T hle x ∈ L.map (toStar T) := by
    have h1 : barToStar T hle x ∈ (barO2 L).map (barToStar T hle) :=
      Subgroup.mem_map_of_mem _ hxL
    rw [barO2, Subgroup.map_map, hcomp] at h1
    exact h1
  have hfxN : barToStar T hle x ∈
      Subgroup.normalizer ((T ⊓ L).map (toStar T) : Set (X ⧸ gnC T)) := by
    have h1 := Subgroup.le_normalizer_map (H := barO2 (T ⊓ L)) (barToStar T hle)
    have h2 := h1 (Subgroup.mem_map_of_mem (barToStar T hle) hxN)
    rw [barO2, Subgroup.map_map, hcomp] at h2
    exact h2
  have hfxS : barToStar T hle x ∈ (T ⊓ L).map (toStar T) :=
    hN (Subgroup.mem_inf.mpr ⟨hfxL, hfxN⟩)
  obtain ⟨s, hs, hfs⟩ := Subgroup.mem_map.mp hfxS
  set k : X ⧸ CFSG.pCore 2 X := (QuotientGroup.mk' (CFSG.pCore 2 X) s)⁻¹ * x with hk
  have hks : barToStar T hle (QuotientGroup.mk' (CFSG.pCore 2 X) s) = barToStar T hle x := hfs
  have hkker : k ∈ (barToStar T hle).ker := by
    rw [MonoidHom.mem_ker]
    rw [hk, map_mul, map_inv, hks, inv_mul_cancel]
  rw [ker_barToStar] at hkker
  have hkL : k ∈ L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_map_of_mem _ hs.2)) hxL
  have hcomap : ((gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X)) = gnC T := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hle
  have hk' : k ∈ (L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    have heq : (gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ⊓
        L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
        (L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
      rw [inf_comm, ← Subgroup.map_inf_comap L ((gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)))
        (QuotientGroup.mk' (CFSG.pCore 2 X)), hcomap]
    rw [← heq]
    exact Subgroup.mem_inf.mpr ⟨hkker, hkL⟩
  obtain ⟨c, hc, hcπ⟩ := Subgroup.mem_map.mp hk'
  have hkC : k ∈ Subgroup.centralizer ((barO2 L : Subgroup _) : Set (X ⧸ CFSG.pCore 2 X)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp hy
    rw [← hly, ← hcπ]
    have hmem := commutator_inf_gnC_le hX hL hLC
      (Subgroup.commutator_mem_commutator (H₁ := L) (H₂ := L ⊓ gnC T) hl hc)
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⁅l, c⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem.2
    have h2 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) l, QuotientGroup.mk' (CFSG.pCore 2 X) c⁆ = 1 := by
      rw [← map_commutatorElement, h1]
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hxeq : QuotientGroup.mk' (CFSG.pCore 2 X) s * k = x := by rw [hk]; group
  rw [← hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hs))
    (Subgroup.mem_sup_right hkC)

theorem le_cgsIn (hCGT : CFSG.AGLEmbedding.AschbacherLocalCGTBlock) (hX : GNSetting X T)
    (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) (hZ : Subgroup.center ↥(L.map (toStar T)) = ⊥)
    (hN : L.map (toStar T) ⊓ Subgroup.normalizer ((T ⊓ L).map (toStar T) : Set (X ⧸ gnC T)) ≤
      (T ⊓ L).map (toStar T)) :
    L ≤ CFSG.Quasithin.cgsIn L T := by
  have hle : CFSG.pCore 2 X ≤ gnC T := pCore_le_gnC hX
  have hcomp : (barToStar T hle).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) = toStar T := rfl
  have hT : T ≠ ⊥ := hX.ne_bot_of_isComponentOf (isComponentOf_map_toStar hX hL hLC)
  set W : Subgroup X :=
    (Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X)) with hW
  set K : Subgroup X := Subgroup.normalClosure (L : Set X)
  have hKcgs : K ≤ CFSG.Quasithin.cgsIn K T :=
    le_cgsIn_of_normal hCGT hX (K := K) Subgroup.normalClosure_normal
  have hKJ : CFSG.Quasithin.cgsIn K T ≤ CFSG.Quasithin.cgsIn L T ⊔ W := by
    unfold CFSG.Quasithin.cgsIn
    refine iSup_le fun B => iSup_le fun hBT => iSup_le fun hB => iSup_le fun hBc => ?_
    have hBnorm : (B.subgroupOf T).Normal :=
      Subgroup.normal_of_characteristic (B.subgroupOf T) (h := hBc)
    have hTB : T ≤ Subgroup.normalizer (B : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mp hBnorm
    have h1 := normalClosure_inf_normalizer_le hX hL
      (barO2_inf_normalizer_le hX hL hLC hN) hTB
    have h2 : L ⊓ Subgroup.normalizer (B : Set X) ≤ CFSG.Quasithin.cgsIn L T :=
      le_iSup_of_le B (le_iSup_of_le hBT (le_iSup_of_le hB (le_iSup_of_le hBc le_rfl)))
    exact h1.trans (sup_le_sup h2 le_rfl)
  have hLJW : L ≤ CFSG.Quasithin.cgsIn L T ⊔ W :=
    Subgroup.le_normalClosure.trans (hKcgs.trans hKJ)
  have hWstar : W.map (toStar T) ≤
      Subgroup.centralizer ((L.map (toStar T)) : Set (X ⧸ gnC T)) := by
    have h1 : W.map (toStar T) =
        (Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X))).map (barToStar T hle) := by
      rw [← hcomp, hW, ← Subgroup.map_map,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective
          (CFSG.pCore 2 X)) (Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)))]
    rw [h1]
    rintro y ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe] at hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hval : (toStar T) x =
        (barToStar T hle) (QuotientGroup.mk' (CFSG.pCore 2 X) x) := rfl
    have hcx := hc _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X)) hx)
    calc (toStar T) x * (barToStar T hle) c
        = (barToStar T hle) ((QuotientGroup.mk' (CFSG.pCore 2 X) x) * c) := by rw [hval, map_mul]
      _ = (barToStar T hle) (c * (QuotientGroup.mk' (CFSG.pCore 2 X) x)) := by rw [hcx]
      _ = (barToStar T hle) c * (toStar T) x := by rw [map_mul, hval]
  have hLJstar : L.map (toStar T) ≤ (CFSG.Quasithin.cgsIn L T).map (toStar T) := by
    have h1 : L.map (toStar T) ≤
        (CFSG.Quasithin.cgsIn L T).map (toStar T) ⊔ W.map (toStar T) := by
      have h2 : L.map (toStar T) ≤
          (CFSG.Quasithin.cgsIn L T ⊔ W).map (toStar T) := Subgroup.map_mono hLJW
      rwa [Subgroup.map_sup] at h2
    have hJle : CFSG.Quasithin.cgsIn L T ≤ L := CFSG.Quasithin.cgsIn_le L T
    have hJstar : (CFSG.Quasithin.cgsIn L T).map (toStar T) ≤ L.map (toStar T) :=
      Subgroup.map_mono hJle
    have hcentle : Subgroup.centralizer ((L.map (toStar T)) : Set (X ⧸ gnC T)) ≤
        Subgroup.centralizer (((CFSG.Quasithin.cgsIn L T).map (toStar T)) :
          Set (X ⧸ gnC T)) :=
      Subgroup.centralizer_le hJstar
    have hWn : W.map (toStar T) ≤ Subgroup.normalizer
        (((CFSG.Quasithin.cgsIn L T).map (toStar T)) : Set (X ⧸ gnC T)) :=
      hWstar.trans (hcentle.trans (Subgroup.centralizer_le_normalizer _))
    intro y hy
    have hy1 : y ∈ (CFSG.Quasithin.cgsIn L T).map (toStar T) ⊔ W.map (toStar T) := h1 hy
    rw [sup_comm ((CFSG.Quasithin.cgsIn L T).map (toStar T)) (W.map (toStar T))] at hy1
    have hy' : y ∈ (W.map (toStar T) : Set (X ⧸ gnC T)) *
        ((CFSG.Quasithin.cgsIn L T).map (toStar T) : Set (X ⧸ gnC T)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (H := W.map (toStar T))
        (N := (CFSG.Quasithin.cgsIn L T).map (toStar T)) hWn]
      exact hy1
    rw [Set.mem_mul] at hy'
    obtain ⟨w, hw, j, hj, hwj⟩ := hy'
    have hwL : w ∈ L.map (toStar T) := by
      have hweq : w = y * j⁻¹ := by rw [← hwj]; group
      rw [hweq]
      exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ (hJstar hj))
    have hwC : w ∈ Subgroup.centralizer ((L.map (toStar T)) : Set (X ⧸ gnC T)) :=
      hWstar hw
    have hwcenter : (⟨w, hwL⟩ : ↥(L.map (toStar T))) ∈ Subgroup.center ↥(L.map (toStar T)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC g g.2)
    have hw1 : w = 1 := by
      have hmem : (⟨w, hwL⟩ : ↥(L.map (toStar T))) ∈ (⊥ : Subgroup ↥(L.map (toStar T))) :=
        hZ ▸ hwcenter
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    rw [← hwj, hw1, one_mul]
    exact hj
  have hTJ : T ⊓ L ≤ CFSG.Quasithin.cgsIn L T :=
    (le_inf inf_le_right (inf_le_left.trans (Subgroup.le_normalizer (H := T)))).trans
      (CFSG.Quasithin.inf_normalizer_le_cgsIn (H := L) (S := T) hT)
  exact le_of_map_toStar_le hX hL hLC (CFSG.Quasithin.cgsIn_le L T) hTJ hLJstar

theorem cgsIn_le_threeNormalizerJoin {C₁ : Subgroup X}
    (h1 : C₁ ≤ CFSG.Quasithin.omegaOneCenterOf T) (hne : C₁ ≠ ⊥)
    (hc : (C₁.subgroupOf T).Characteristic)
    (h3 : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (C₁ : Set X)))
    (habs : ∀ H : Subgroup (X ⧸ gnC T), (T ⊓ L).map (toStar T) ≤ H → H ≤ L.map (toStar T) →
      ¬ 3 ∣ Nat.card H → H ≤ (T ⊓ L).map (toStar T)) :
    CFSG.Quasithin.cgsIn L T ≤ threeNormalizerJoin T L := by
  unfold CFSG.Quasithin.cgsIn
  refine iSup_le fun B => iSup_le fun hBT => iSup_le fun hB => iSup_le fun hBc => ?_
  have hBnorm : (B.subgroupOf T).Normal :=
    Subgroup.normal_of_characteristic (B.subgroupOf T) (h := hBc)
  have hTB : T ≤ Subgroup.normalizer (B : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mp hBnorm
  by_cases h3B : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (B : Set X))
  · exact inf_normalizer_le_threeNormalizerJoin hBT hB hBc h3B
  ·
    set H : Subgroup (X ⧸ gnC T) :=
      (L ⊓ Subgroup.normalizer (B : Set X)).map (toStar T) with hH
    have hSH : (T ⊓ L).map (toStar T) ≤ H := by
      rw [hH]
      exact Subgroup.map_mono (le_inf inf_le_right (inf_le_left.trans hTB))
    have hHL : H ≤ L.map (toStar T) := by
      rw [hH]
      exact Subgroup.map_mono inf_le_left
    have h3H : ¬ 3 ∣ Nat.card H := fun h =>
      h3B (h.trans (Subgroup.card_map_dvd _ _))
    have hle := habs H hSH hHL h3H
    have hsup : L ⊓ Subgroup.normalizer (B : Set X) ≤ (T ⊓ L) ⊔ gnC T := by
      intro x hx
      rw [CFSG.AGLEmbeddingD2.GN.mem_sup_gnC_iff]
      exact hle (Subgroup.mem_map_of_mem _ hx)
    have hC₁T : C₁ ≤ T := h1.trans (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
    have hC₁norm : (C₁.subgroupOf T).Normal :=
      Subgroup.normal_of_characteristic (C₁.subgroupOf T) (h := hc)
    have hTN : T ≤ Subgroup.normalizer (C₁ : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁T).mp hC₁norm
    have hCN : gnC T ≤ Subgroup.normalizer (C₁ : Set X) :=
      (gnC_le_centralizer h1).trans (Subgroup.centralizer_le_normalizer _)
    have hleN : L ⊓ Subgroup.normalizer (B : Set X) ≤
        Subgroup.normalizer (C₁ : Set X) :=
      hsup.trans (sup_le (inf_le_left.trans hTN) hCN)
    exact (le_inf inf_le_left hleN).trans
      (inf_normalizer_le_threeNormalizerJoin hC₁T hne hc h3)

theorem agl81FiveTwentySixAlt_of (hAF : CFSG.AGLEmbeddingD2.GN.GNAltFacts)
    (hCGT : CFSG.AGLEmbedding.AschbacherLocalCGTBlock) : AGL81FiveTwentySixAlt := by
  intro Y _ _ T L hX hL C₁ C₂ hP hY n hn he
  obtain ⟨e⟩ := he
  have hpair := CFSG.AGLEmbeddingD2.GN.isGNPair_of_isC118Pair hP
  have hcomp : CFSG.Open.IsComponentOf (L.map (toStar T)) ⊤ := hY.1
  have hT : T ≠ ⊥ := hX.ne_bot_of_isComponentOf hcomp
  have hn4 : 4 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hLC : ¬ L ≤ gnC T := by
    intro h
    have hbot : L.map (toStar T) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := gnC T) x).mpr (h hx)
    haveI : Subsingleton ↥(L.map (toStar T)) := by rw [hbot]; infer_instance
    haveI : Subsingleton (↥(L.map (toStar T)) ⧸
        Subgroup.center ↥(L.map (toStar T))) :=
      ⟨fun a b => by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim a' b']⟩
    obtain ⟨a, b, hab⟩ := hcomp.2.2.2.toNontrivial.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hZ : Subgroup.center ↥(L.map (toStar T)) = ⊥ := by
    have hc : Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simpa using hn4)
    refine le_antisymm (fun z hz => ?_) bot_le
    have hmem : ((Subgroup.centerCongr e) ⟨z, hz⟩ : ↥(alternatingGroup (Fin n))) ∈
        (⊥ : Subgroup ↥(alternatingGroup (Fin n))) := by
      rw [← hc]
      exact ((Subgroup.centerCongr e) ⟨z, hz⟩).2
    have h1 : (Subgroup.centerCongr e) ⟨z, hz⟩ = 1 := by
      apply Subtype.ext
      simpa using Subgroup.mem_bot.mp hmem
    have h2 : (⟨z, hz⟩ : ↥(Subgroup.center ↥(L.map (toStar T)))) = 1 := by
      apply (Subgroup.centerCongr e).injective
      rw [h1, map_one]
    simpa using congrArg Subtype.val h2
  have he' : Nonempty ((↥(L.map (toStar T)) ⧸ Subgroup.center ↥(L.map (toStar T))) ≃*
      alternatingGroup (Fin n)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot).trans e)⟩
  have hfacts := hAF Y T hX hT C₁ C₂ hP (L.map (toStar T)) hY n hn he'
  have hne3 : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 3
      (gnA T C₁ (L.map (toStar T))) ≠ ⊥ := by
    intro hbot
    exact hfacts.2.1 (by rw [hbot, hZ]; exact bot_le)
  have hex : ∃ x ∈ gnA T C₁ (L.map (toStar T)), ∃ k : ℕ, orderOf x = 3 ^ k ∧ x ≠ 1 := by
    by_contra h
    apply hne3
    have hle : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 3
        (gnA T C₁ (L.map (toStar T))) ≤ ⊥ := by
      rw [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup, Subgroup.closure_le]
      rintro y ⟨hyA, k, hk⟩
      by_contra hy1
      exact h ⟨y, hyA, k, hk, by simpa [Subgroup.mem_bot] using hy1⟩
    rwa [le_bot_iff] at hle
  obtain ⟨x, hxA, k, hxk, hx1⟩ := hex
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exfalso
      apply hx1
      exact orderOf_eq_one_iff.mp (by rw [hxk, hk0]; simp)
    · exact hk0
  have h3dvd : 3 ∣ orderOf x := by
    rw [hxk]
    exact dvd_pow_self 3 (Nat.ne_of_gt hk1)
  obtain ⟨y, hyA, hyord⟩ : ∃ y ∈ gnA T C₁ (L.map (toStar T)), orderOf y = 3 :=
    ⟨x ^ (orderOf x / 3), Subgroup.pow_mem _ hxA _,
      orderOf_pow_orderOf_div (orderOf_pos x).ne' h3dvd⟩
  have hCN : gnC T ≤ Subgroup.normalizer (C₁ : Set Y) :=
    (gnC_le_centralizer hpair.le_center).trans (Subgroup.centralizer_le_normalizer _)
  have hgnA : gnA T C₁ (L.map (toStar T)) =
      (L ⊓ Subgroup.normalizer (C₁ : Set Y)).map (toStar T) := by
    unfold CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnA
    exact gnImg_inf_map_eq hCN L
  have h3C₁ : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (C₁ : Set Y)) :=
    three_dvd_card_of_mem_map (toStar T) (hgnA ▸ hyA) hyord
  have hS : IsSylowTwoOf ((T ⊓ L).map (toStar T)) (L.map (toStar T)) :=
    CFSG.AGLEmbedding.AscEightFive.isSylowTwoOf_map (isSylowTwoOf_inf hX hL) (toStar T)
  refine (le_cgsIn hCGT hX hL hLC hZ
    (CFSG.GroupTheory.PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt hn6 e hS)).trans
    (cgsIn_le_threeNormalizerJoin hpair.le_center hpair.ne_bot₁ hpair.char₁ h3C₁ ?_)
  intro H hSH hHL h3H
  exact CFSG.GroupTheory.PermSylowTwo.le_of_isSylowTwoOf_of_mulEquiv_alt hn6 e hS hSH hHL h3H

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
