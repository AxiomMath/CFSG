module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Basic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

variable {G : Type} [Group G] [Finite G]

section Family

variable {Φ : Set (Subgroup G)}

theorem aViol_symm (hΦ : HypOmegaGen Φ) {K J : Subgroup G} {zK zJ : G} (hK : K ∈ Φ)
    (h : AViol Φ K J zK zJ) : AViol Φ J K zJ zK where
  star := Q3T6.Mu.omegaStarNbr_symm hΦ hK h.mem h.star
  not_nbr := fun hn => h.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ h.mem hK hn)
  hzK := h.hzJ
  hzJ := h.hzK
  no_conj := by
    intro g hg hcon
    have hg' : g ∈ pairNormalizers K J zK zJ := by
      unfold pairNormalizers at hg ⊢
      rw [Set.pair_comm, sup_comm]
      exact hg
    apply h.no_conj g⁻¹ ((pairNormalizers K J zK zJ).inv_mem hg')
    rw [← hcon, conjSub_inv_conjSub]

theorem twinSet_eq_pair_of_aViol (hΦ : HypOmegaGen Φ) {M J : Subgroup G} {zM zJ : G}
    (hM : M ∈ Φ) (hv : AViol Φ M J zM zJ) :
    ∃ Mstar : Subgroup G, Mstar ≠ M ∧ twinSet Φ M = {M, Mstar} ∧ ∃ y : G, conjSub y J = Mstar := by
  obtain ⟨-, -, -, -, Mstar, -, -, -, -, -, -, -, -, -, -, -, -, -, hne, htw, ⟨y, -, hy⟩, -⟩ :=
    Sec6Gen.l6_4ThreeGen G Φ hΦ M hM J hv.mem
      ⟨hv.star, hv.not_nbr, zM, zJ, hv.hzK, hv.hzJ, fun ⟨g, hg, hgc⟩ => hv.no_conj g hg hgc⟩
      zM zJ hv.hzK hv.hzJ _ _ rfl rfl
  exact ⟨Mstar, hne, htw, y, hy⟩

theorem mem_aStar_of_mem_twinSet {K M : Subgroup G} (hM : M ∈ twinSet Φ K) : M ∈ aStar Φ K := by
  by_cases hMK : M = K
  · rw [hMK]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hM.1, Or.inr (Or.inr ⟨hM, hMK⟩)⟩

end Family

variable {Φ : Set (Subgroup G)} {K Q : Subgroup G}

theorem S5Hyp.injOn_map (h : S5Hyp Φ K Q) [Q.Normal] :
    Set.InjOn (fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) Φ :=
  fun _ hJ _ hJ' he => h.eq_of_map_eq hJ hJ' he

theorem S5Hyp.mem_omegaNbr_iff (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ Φ) :
    J.map (QuotientGroup.mk' Q) ∈ omegaNbr (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) ↔
      J ∈ omegaNbr Φ L :=
  ⟨h.centQuotGen.omegaNbr_of_map hL hJ, h.centQuotGen.omegaNbr_map hL⟩

theorem S5Hyp.map_mem_USet (h : S5Hyp Φ K Q) [Q.Normal] {U : Subgroup G} (hU : U ∈ USet Φ) :
    U.map (QuotientGroup.mk' Q) ∈ USet (barFam Φ Q) := by
  obtain ⟨R, hR, hUR, hUc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRQ : R ⊓ Q = ⊥ := h.inf_eq_bot_of_le hJ hRJ.1
  have hUQ : U ⊓ Q = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right Q hUR).trans hRQ.le)
  refine mem_USet_of_natCard (map_mem_quotFamily hJ) (Hall196.isSylow2In_map_hom _ hRJ)
    (Subgroup.map_mono hUR) ((MulEquiv.isCyclic (AscQuot.quotRestrictEquiv hUQ)).mp hUc) ?_
  rw [← Nat.card_congr (AscQuot.quotRestrictEquiv hRQ).toEquiv,
    ← Nat.card_congr (AscQuot.quotRestrictEquiv hUQ).toEquiv]
  have hcard : Nat.card U * U.relIndex R = Nat.card R := by
    have := Subgroup.relIndex_mul_card U R
    rwa [inf_eq_left.mpr hUR, mul_comm] at this
  rw [hidx] at hcard
  omega

theorem S5Hyp.mem_omegaStarNbr_iff (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ Φ) :
    J.map (QuotientGroup.mk' Q) ∈ omegaStarNbr (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) ↔
      J ∈ omegaStarNbr Φ L := by
  refine ⟨h.centQuotGen.omegaStarNbr_of_map hL hJ, ?_⟩
  rintro ⟨-, hne, U, hU, hUJ, hUN⟩
  refine ⟨map_mem_quotFamily hJ, fun he => hne (h.eq_of_map_eq hJ hL he),
    U.map (QuotientGroup.mk' Q), h.map_mem_USet hU, Subgroup.map_mono hUJ, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact mk_mem_normalizer_map (hUN hu)

theorem S5Hyp.map_mem_twinSet (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ twinSet Φ L) :
    J.map (QuotientGroup.mk' Q) ∈ twinSet (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) := by
  obtain ⟨hJΦ, z, hzL, hzJ⟩ := hJ
  exact ⟨map_mem_quotFamily hJΦ, QuotientGroup.mk' Q z, h.isUniqueInvolution_map hL hzL,
    h.isUniqueInvolution_map hJΦ hzJ⟩

theorem S5Hyp.map_omegaOfSet (h : S5Hyp Φ K Q) [Q.Normal] {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ Φ) :
    (fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) '' omegaOfSet Φ Δ =
      omegaOfSet (barFam Φ Q) ((fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) '' Δ) := by
  ext Nb
  constructor
  · rintro ⟨N, ⟨hN, hall⟩, rfl⟩
    refine ⟨map_mem_quotFamily hN, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact (h.mem_omegaNbr_iff (hΔ hT) hN).mpr (hall T hT)
  · rintro ⟨⟨N, hN, rfl⟩, hall⟩
    exact ⟨N, ⟨hN, fun T hT => (h.mem_omegaNbr_iff (hΔ hT) hN).mp (hall _ ⟨T, hT, rfl⟩)⟩, rfl⟩

theorem S5Hyp.mem_normalizer_closure_of_map (h : S5Hyp Φ K Q) [Q.Normal] {A : Subgroup G}
    (hA : A ∈ Φ) {x y : G} (hx : IsUniqueInvolution A x) (hy2 : y * y = 1)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hxy : x * y = y * x) {a : G} (ha : a ∈ A)
    (han : QuotientGroup.mk' Q a ∈ Subgroup.normalizer
      ((Subgroup.closure {QuotientGroup.mk' Q x, QuotientGroup.mk' Q y} : Subgroup (G ⧸ Q)) :
        Set (G ⧸ Q))) :
    a ∈ Subgroup.normalizer ((Subgroup.closure {x, y} : Subgroup G) : Set G) := by
  set mk := QuotientGroup.mk' Q with hmk
  set Eb : Subgroup (G ⧸ Q) := Subgroup.closure {mk x, mk y} with hEb
  have hxb : mk x * mk x = 1 := by rw [← map_mul, hx.sq, map_one]
  have hyb : mk y * mk y = 1 := by rw [← map_mul, hy2, map_one]
  have hxyb : mk x * mk y = mk y * mk x := by rw [← map_mul, ← map_mul, hxy]
  have hsq : ∀ e ∈ Eb, e * e = 1 := by
    intro e he
    rcases (Frame.Thm3Quot.mem_closure_pair_iff hxb hyb hxyb).mp he with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact hxb
    · exact hyb
    · calc mk x * mk y * (mk x * mk y) = mk x * (mk y * mk x) * mk y := by group
        _ = mk x * (mk x * mk y) * mk y := by rw [hxyb]
        _ = (mk x * mk x) * (mk y * mk y) := by group
        _ = 1 := by rw [hxb, hyb, one_mul]
  have hyE : mk y ∈ Eb := Subgroup.subset_closure (by simp)
  set c : G := y⁻¹ * (a * y * a⁻¹) with hc
  have hcA : c ∈ A := by
    have h1 : y⁻¹ * a * y⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyA) a).mp ha
    have h2 : c = (y⁻¹ * a * y⁻¹⁻¹) * a⁻¹ := by
      rw [hc, inv_inv]
      group
    rw [h2]
    exact A.mul_mem h1 (A.inv_mem ha)
  have hcE : mk c ∈ Eb := by
    have h1 : mk a * mk y * (mk a)⁻¹ ∈ Eb := (Subgroup.mem_normalizer_iff.mp han (mk y)).mp hyE
    have h2 : mk c = (mk y)⁻¹ * (mk a * mk y * (mk a)⁻¹) := by
      rw [hc]
      simp only [map_mul, map_inv]
    rw [h2]
    exact Eb.mul_mem (Eb.inv_mem hyE) h1
  have hyc : a * y * a⁻¹ = y * c := by
    rw [hc]
    group
  have hxE : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyE' : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  refine T3.mem_normalizer_closure_pair ?_ ?_
  · rw [hx.conj_eq (mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer ha))]
    exact hxE
  · rw [hyc]
    rcases (h.isUniqueInvolution_map hA hx).unique (mk c) (Subgroup.mem_map_of_mem _ hcA)
        (hsq _ hcE) with h1 | h1
    · rw [h.mk_inj hA hcA A.one_mem (by rw [h1, map_one]), mul_one]
      exact hyE'
    · rw [h.mk_inj hA hcA hx.mem h1]
      exact Subgroup.mul_mem _ hyE' hxE

theorem S5Hyp.map_pairNormalizers (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ Φ) (hstar : J ∈ omegaStarNbr Φ L) {zL zJ : G} (hzL : IsUniqueInvolution L zL)
    (hzJ : IsUniqueInvolution J zJ) :
    (pairNormalizers L J zL zJ).map (QuotientGroup.mk' Q) =
      pairNormalizers (L.map (QuotientGroup.mk' Q)) (J.map (QuotientGroup.mk' Q))
        (QuotientGroup.mk' Q zL) (QuotientGroup.mk' Q zJ) := by
  refine le_antisymm (map_pairNormalizers_le L J zL zJ) ?_
  have hc : zL * zJ = zJ * zL := Q3T6D.commute_of_mem_omegaStarNbr h.typeR.hyp hstar hzL hzJ
  have hJn : zJ ∈ Subgroup.normalizer (L : Set G) :=
    Q3T6D.mem_normalizer_of_mem_omegaStarNbr h.typeR.hyp hstar hzJ
  have hstar' : L ∈ omegaStarNbr Φ J := Q3T6.Mu.omegaStarNbr_symm h.typeR.hyp hL hJ hstar
  have hLn : zL ∈ Subgroup.normalizer (J : Set G) :=
    Q3T6D.mem_normalizer_of_mem_omegaStarNbr h.typeR.hyp hstar' hzL
  unfold pairNormalizers
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨⟨k, hk, rfl⟩, hkn⟩
    exact ⟨k, ⟨hk, h.mem_normalizer_closure_of_map hL hzL hzJ.sq hJn hc hk hkn⟩, rfl⟩
  · rintro _ ⟨⟨j, hj, rfl⟩, hjn⟩
    rw [Set.pair_comm] at hjn
    have hj' := h.mem_normalizer_closure_of_map hJ hzJ hzL.sq hLn hc.symm hj hjn
    rw [Set.pair_comm] at hj'
    exact ⟨j, ⟨hj, hj'⟩, rfl⟩

theorem S5Hyp.map_aViol (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ) (hJ : J ∈ Φ)
    {zL zJ : G} (hv : AViol Φ L J zL zJ) :
    AViol (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) (J.map (QuotientGroup.mk' Q))
      (QuotientGroup.mk' Q zL) (QuotientGroup.mk' Q zJ) where
  star := (h.mem_omegaStarNbr_iff hL hJ).mpr hv.star
  not_nbr := fun hn => hv.not_nbr ((h.mem_omegaNbr_iff hL hJ).mp hn)
  hzK := h.isUniqueInvolution_map hL hv.hzK
  hzJ := h.isUniqueInvolution_map hJ hv.hzJ
  no_conj := by
    intro gb hgb hgc
    rw [← h.map_pairNormalizers hL hJ hv.star hv.hzK hv.hzJ] at hgb
    obtain ⟨g, hg, rfl⟩ := hgb
    apply hv.no_conj g hg
    apply h.eq_of_map_eq (h.typeR.hyp.conjInvariant g L hL) hJ
    rw [AscQuot.map_conjSub, hgc]

theorem S5Hyp.aViol_of_map (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ Φ) {zLb zJb : G ⧸ Q}
    (hv : AViol (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) (J.map (QuotientGroup.mk' Q)) zLb zJb)
    {zL zJ : G} (hzL : IsUniqueInvolution L zL) (hzJ : IsUniqueInvolution J zJ) :
    AViol Φ L J zL zJ where
  star := h.centQuotGen.omegaStarNbr_of_map hL hJ hv.star
  not_nbr := fun hn => hv.not_nbr (h.centQuotGen.omegaNbr_map hL hn)
  hzK := hzL
  hzJ := hzJ
  no_conj := by
    intro g hg hgc
    have e1 : QuotientGroup.mk' Q zL = zLb := (h.isUniqueInvolution_map hL hzL).eq hv.hzK
    have e2 : QuotientGroup.mk' Q zJ = zJb := (h.isUniqueInvolution_map hJ hzJ).eq hv.hzJ
    apply hv.no_conj (QuotientGroup.mk' Q g)
    · have h2 := map_pairNormalizers_le (N := Q) L J zL zJ (Subgroup.mem_map_of_mem _ hg)
      rwa [e1, e2] at h2
    · rw [← AscQuot.map_conjSub, hgc]

theorem S5Hyp.mem_aSet_iff (h : S5Hyp Φ K Q) [Q.Normal] {L J : Subgroup G} (hL : L ∈ Φ)
    (hJ : J ∈ Φ) :
    J.map (QuotientGroup.mk' Q) ∈ aSet (barFam Φ Q) (L.map (QuotientGroup.mk' Q)) ↔
      J ∈ aSet Φ L := by
  constructor
  · rintro ⟨zLb, zJb, hv⟩
    obtain ⟨zL, hzL⟩ := (h.typeR.hyp.omega1 L hL).1
    obtain ⟨zJ, hzJ⟩ := (h.typeR.hyp.omega1 J hJ).1
    exact ⟨zL, zJ, h.aViol_of_map hL hJ hv hzL hzJ⟩
  · rintro ⟨zL, zJ, hv⟩
    exact ⟨_, _, h.map_aViol hL hJ hv⟩

theorem S5Hyp.not_aEmpty_quot (h : S5Hyp Φ K Q) [Q.Normal] :
    ¬ AEmpty (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp h.viol
  exact not_aEmpty_iff.mpr ⟨_, _, _, h.map_aViol h.mem hv.mem hv⟩

theorem S5Hyp.not_aEmpty_of_mem_aStar (h : S5Hyp Φ K Q) {M : Subgroup G} (hM : M ∈ aStar Φ K) :
    ¬ AEmpty Φ M := by
  induction hM with
  | refl => exact h.viol
  | tail hab hbc ih =>
    rename_i b c
    have hbΦ : b ∈ Φ := T3Core.mem_of_mem_aStar h.mem hab
    obtain ⟨-, ⟨zb, zc, hv⟩ | ⟨zc, zb, hv⟩ | ⟨htw, hne⟩⟩ := hbc
    · exact not_aEmpty_iff.mpr ⟨b, zc, zb, aViol_symm h.typeR.hyp hbΦ hv⟩
    · exact not_aEmpty_iff.mpr ⟨b, zc, zb, hv⟩
    · obtain ⟨J, zb, zJ, hv⟩ := not_aEmpty_iff.mp ih
      obtain ⟨bstar, -, htwb, y, hy⟩ := twinSet_eq_pair_of_aViol h.typeR.hyp hbΦ hv
      rw [htwb] at htw
      rcases htw with h1 | h1
      · exact absurd h1 hne
      · have h1' : c = bstar := h1
        have hv' := T3CII.aviol_conj h.typeR.hyp.conjInvariant (aViol_symm h.typeR.hyp hbΦ hv) y
        rw [hy] at hv'
        rw [h1']
        exact not_aEmpty_iff.mpr ⟨_, _, _, hv'⟩

theorem S5Hyp.map_twinSet (h : S5Hyp Φ K Q) [Q.Normal] {M : Subgroup G} (hM : M ∈ Φ)
    (hA : ¬ AEmpty Φ M) :
    (fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) '' twinSet Φ M =
      twinSet (barFam Φ Q) (M.map (QuotientGroup.mk' Q)) := by
  obtain ⟨J, zM, zJ, hv⟩ := not_aEmpty_iff.mp hA
  obtain ⟨Ms, hne, htw, -⟩ := twinSet_eq_pair_of_aViol h.typeR.hyp hM hv
  obtain ⟨Msb, -, htwb, -⟩ := twinSet_eq_pair_of_aViol h.typeR_quot.hyp (map_mem_quotFamily hM)
    (h.map_aViol hM hv.mem hv)
  have hMs : Ms ∈ twinSet Φ M := by
    rw [htw]
    exact Or.inr rfl
  have hMsb := h.map_mem_twinSet hM hMs
  rw [htwb] at hMsb
  have hne' : Ms.map (QuotientGroup.mk' Q) ≠ M.map (QuotientGroup.mk' Q) :=
    fun he => hne (h.eq_of_map_eq hMs.1 hM he)
  have he : Ms.map (QuotientGroup.mk' Q) = Msb := hMsb.resolve_left hne'
  rw [htw, htwb, Set.image_pair, he]

theorem S5Hyp.map_mem_aStar (h : S5Hyp Φ K Q) [Q.Normal] {M : Subgroup G} (hM : M ∈ aStar Φ K) :
    M.map (QuotientGroup.mk' Q) ∈ aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
  induction hM with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b c
    have hbΦ : b ∈ Φ := T3Core.mem_of_mem_aStar h.mem hab
    obtain ⟨hcΦ, hv | hv | ⟨htw, hne⟩⟩ := hbc
    · exact ih.tail ⟨map_mem_quotFamily hcΦ, Or.inl ((h.mem_aSet_iff hbΦ hcΦ).mpr hv)⟩
    · exact ih.tail ⟨map_mem_quotFamily hcΦ, Or.inr (Or.inl ((h.mem_aSet_iff hcΦ hbΦ).mpr hv))⟩
    · exact ih.tail ⟨map_mem_quotFamily hcΦ, Or.inr (Or.inr ⟨h.map_mem_twinSet hbΦ htw,
        fun he => hne (h.eq_of_map_eq hcΦ hbΦ he)⟩)⟩

theorem S5Hyp.exists_mem_aStar_of_mem (h : S5Hyp Φ K Q) [Q.Normal] {Mb : Subgroup (G ⧸ Q)}
    (hMb : Mb ∈ aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) :
    ∃ M ∈ aStar Φ K, M.map (QuotientGroup.mk' Q) = Mb := by
  induction hMb with
  | refl => exact ⟨K, Relation.ReflTransGen.refl, rfl⟩
  | tail hab hbc ih =>
    obtain ⟨b, hb, rfl⟩ := ih
    have hbΦ : b ∈ Φ := T3Core.mem_of_mem_aStar h.mem hb
    obtain ⟨⟨c, hcΦ, rfl⟩, hv | hv | ⟨htw, hne⟩⟩ := hbc
    · exact ⟨c, hb.tail ⟨hcΦ, Or.inl ((h.mem_aSet_iff hbΦ hcΦ).mp hv)⟩, rfl⟩
    · exact ⟨c, hb.tail ⟨hcΦ, Or.inr (Or.inl ((h.mem_aSet_iff hcΦ hbΦ).mp hv))⟩, rfl⟩
    · rw [← h.map_twinSet hbΦ (h.not_aEmpty_of_mem_aStar hb)] at htw
      obtain ⟨c', hc', hc'e⟩ := htw
      refine ⟨c', hb.tail ⟨hc'.1, Or.inr (Or.inr ⟨hc', fun he => hne ?_⟩)⟩, hc'e⟩
      rw [← hc'e, he]

theorem S5Hyp.map_aStar (h : S5Hyp Φ K Q) [Q.Normal] :
    (fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) '' aStar Φ K =
      aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
  ext Mb
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact h.map_mem_aStar hM
  · intro hMb
    exact h.exists_mem_aStar_of_mem hMb

theorem S5Hyp.mem_aStar_iff (h : S5Hyp Φ K Q) [Q.Normal] {M : Subgroup G} (hM : M ∈ Φ) :
    M.map (QuotientGroup.mk' Q) ∈ aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) ↔
      M ∈ aStar Φ K := by
  refine ⟨fun hMb => ?_, h.map_mem_aStar⟩
  obtain ⟨M', hM', he⟩ := h.exists_mem_aStar_of_mem hMb
  rwa [← h.eq_of_map_eq (T3Core.mem_of_mem_aStar h.mem hM') hM he]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
