module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27CycA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem center3_of_pairData_cyclic27
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {V T : Subgroup G}
    {hU : IsElemAbelian 2 V} (c : D2L34R27 G d P M A H R Rbar K₀ T)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I)
    {C : Subgroup G} (hCdef : C = Subgroup.centralizer (V : Set G) ⊓ M) (S : Sylow 3 ↥C)
    (hS : IsCyclic ↥((S : Subgroup ↥C).map C.subtype))
    (hS0 : (S : Subgroup ↥C).map C.subtype ≠ ⊥) (hCs : CFSG.HallHigman.IsPSolvable 3 ↥C)
    {C₁ C₂ : Subgroup G} (hdat : FFPairData M T hU I C₁ C₂) : Center3Conclusion M := by
  classical
  have ctx := c.ctx
  have := ctx.amb
  have hT := c.sylow
  have hNT := c.not_normalizer_le
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, hJ₂, hH⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  choose! Hf hHM hHL hH3 hHcase using hH
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  have hCM : C ≤ M := hCdef ▸ inf_le_right
  have hCn : (C.subgroupOf M).Normal := hCdef ▸ centralizer_inf_subgroupOf_normal hU hMN
  have hCnM : M ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hCn
  obtain ⟨Ystar, hYdef⟩ : ∃ Y : Subgroup (MulAut (IntMod V hU)), Y = ⨆ L ∈ I, L := ⟨_, rfl⟩
  have hJM' : autI hU (thompsonJ M) = Ystar := hJM.trans hYdef.symm
  have hYn : ∀ g ∈ autI hU M, ∀ φ ∈ Ystar, g * φ * g⁻¹ ∈ Ystar := by
    intro g hg φ hφ
    rw [← hJM'] at hφ ⊢
    exact autI_thompsonJ_normalized g hg φ hφ
  have hYM : Ystar ≤ autI hU M := hJM' ▸ autI_mono hU (CFSG.Quasithin.B6.thompsonJ_le M)
  have hLY : ∀ L ∈ I, L ≤ Ystar := fun L hL x hx =>
    hYdef ▸ Subgroup.mem_iSup_of_mem L (Subgroup.mem_iSup_of_mem hL hx)
  set AY : Subgroup G := preAutM hU hMN Ystar with hAY
  have hAYM : AY ≤ M := preAutM_le hU hMN Ystar
  have hAYn : M ≤ Subgroup.normalizer (AY : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAYM).1 (preAutM_normal hU hMN hYn)
  set B' : Subgroup G := M ⊓ Subgroup.normalizer (C₂ : Set G) with hB'
  have hB'M : B' ≤ M := inf_le_left
  have hB'N : B' ≤ Subgroup.normalizer (V : Set G) := hB'M.trans hMN
  have hfacAB : ∀ m ∈ M, ∃ a ∈ AY, ∃ b ∈ B', m = a * b := by
    intro m hm
    have hcov : ∀ L ∈ I, L ≤ autI hU AY ∨ L ≤ autI hU (⊥ : Subgroup G) := by
      intro L hL
      left
      intro φ hφ
      have hφY : φ ∈ autI hU (thompsonJ M) := by
        rw [hJM']
        exact hLY L hL hφ
      obtain ⟨g, hgJ, rfl⟩ := (mem_autI hU).1 hφY
      have hgM : (g : G) ∈ M := CFSG.Quasithin.B6.thompsonJ_le M hgJ
      refine (mem_autI hU).2 ⟨g, (mem_preAutM hU hMN).2 ⟨hgM, ?_⟩, rfl⟩
      exact hLY L hL hφ
    obtain ⟨c, hc', a, ha, b, hb, n, hn, hmeq⟩ := exists_factor_of_covering hMN hT
      (C1GN.baum_le T) (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM hAYM bot_le hcov m hm
    have hb1 : b = 1 := by simpa using hb
    refine ⟨c * a, AY.mul_mem (centralizer_inf_le_preAutM hU hMN Ystar (hCdef ▸ hc')) ha, n,
      ⟨hn.1, hJ₂ hn⟩, ?_⟩
    rw [hmeq, hb1, mul_one]
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hW₂idx, hWfac⟩ :=
    exists_sylow_of_normal_mul' hAYM hAYn hB'M hfacAB
  obtain ⟨g, hgM, hWC⟩ := exists_conj_inf_eq_map_sylow hCM hCnM hWM hWp hWidx S
  have hDc : IsCyclic ↥(W ⊓ C) := by
    rw [hWC]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
      ((S : Subgroup ↥C).map C.subtype) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).mp hS
  obtain ⟨P₀, hP₀D₀, hP₀3, hP₀n⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_normal_order_three_of_cyclic_sylow hCM hCn
      hCs ⟨S, rfl⟩ hS hS0
  have hD₀C : (S : Subgroup ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hP₀M : P₀ ≤ M := hP₀D₀.trans (hD₀C.trans hCM)
  set P₁ : Subgroup G := P₀.map (MulAut.conj g).toMonoidHom with hP₁
  have hP₁D : P₁ ≤ W ⊓ C := by
    rw [hWC]
    exact Subgroup.map_mono hP₀D₀
  have hP₁3 : Nat.card P₁ = 3 := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP₀3]
  have hNM : GLBPrimeCore 3 M ⊔ P₀ ≤ M := sup_le (glbPrimeCore_le 3 M) hP₀M
  have hNn : M ≤ Subgroup.normalizer ((GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hP₀M (glbPrimeCore_le 3 M))).1 hP₀n
  have hNW : Nat.card ((GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) ⊓ W : Subgroup G) ≤ 3 :=
    card_le_three_of_isPGroup_le_sup hP₀3 (glbPrimeCore_coprime 3 M)
      (hP₀M.trans (le_normalizer_glbPrimeCore 3 M)) (hWp.to_le inf_le_right) inf_le_left
  have hP₁NW : P₁ ≤ (GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) ⊓ W := by
    refine le_inf ?_ (hP₁D.trans inf_le_left)
    rintro _ ⟨p, hp, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hNn hgM) p).mp (Subgroup.mem_sup_right hp)
  have hwc : ∀ m ∈ M, ∀ p ∈ P₁, m * p * m⁻¹ ∈ W → m * p * m⁻¹ ∈ P₁ := fun m hm p hp hmp =>
    weakly_closed_of_normal_inf hNn hNW hP₁3 hP₁NW hm hp hmp
  have hWCn : ∀ w ∈ W, ∀ e ∈ W ⊓ C, w * e * w⁻¹ ∈ W ⊓ C := fun w hw e he =>
    ⟨W.mul_mem (W.mul_mem hw he.1) (W.inv_mem hw),
      (Subgroup.mem_normalizer_iff.mp (hCnM (hWM hw)) e).mp he.2⟩
  have hP₁cube : ∀ p ∈ P₁, p ^ 3 = 1 := fun p hp =>
    orderOf_dvd_iff_pow_eq_one.mp (hP₁3 ▸ Subgroup.orderOf_dvd_natCard P₁ hp)
  have hP₁cent : ∀ w ∈ W, ∀ p ∈ P₁, w * p = p * w := by
    intro w hw p hp
    have h := conj_eq_of_pow_three_of_cyclic hWp hDc hWCn (hP₁D hp) (hP₁cube p hp) hw
    calc w * p = w * p * w⁻¹ * w := by group
      _ = p * w := by rw [h]
  have hZel : IsElemAbelian 3 (zcl I) := isElemAbelian_zcl hI.comm hcard
  have hZab : ∀ x ∈ zcl I, ∀ y ∈ zcl I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZp : IsPGroup 3 (zcl I) := fun x => ⟨1, Subtype.ext (by simpa using hZel.2 x x.2)⟩
  have hZY : zcl I ≤ Ystar := (Subgroup.closure_le _).2 fun x ⟨L, hL, hxL, _⟩ => hLY L hL hxL
  have hWp' : IsPGroup 3 (W.subgroupOf M) := hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  have hWbarp : IsPGroup 3 ↥(autI hU W) := by
    rw [autI_eq_map_convHom hU hMN hWM]
    exact hWp'.map _
  have hidxW : ¬ 3 ∣ ((autI hU W).subgroupOf (autI hU M)).index := fun h =>
    hWidx (h.trans (relIndex_autI_dvd hMN hWM))
  have hidxW₂ : ¬ 3 ∣ ((autI hU W₂).subgroupOf (autI hU B')).index := fun h =>
    hW₂idx (h.trans (relIndex_autI_dvd hB'N hW₂B))
  have hnormZ : autI hU W ≤ Subgroup.normalizer (zcl I : Set (MulAut (IntMod V hU))) := by
    intro q hq
    have hqM : q ∈ autI hU M := autI_mono hU hWM hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => zcl_conj_mem (fun L hL => (conjAut_eq_map_conj q L) ▸ hperm q hqM L hL) hx
    · intro hx
      have := zcl_conj_mem (fun L hL => (conjAut_eq_map_conj q⁻¹ L) ▸
        hperm q⁻¹ ((autI hU M).inv_mem hqM) L hL) hx
      simpa [mul_assoc] using this
  have hZW : zcl I ≤ autI hU W := by
    have hQp : IsPGroup 3 ↥(autI hU W ⊔ zcl I) :=
      IsPGroup.to_sup_of_normal_right' hWbarp hZp hnormZ
    exact le_sup_right.trans (le_of_isPGroup_of_not_dvd_relIndex le_sup_left
      (sup_le (autI_mono hU hWM) (hZY.trans hYM)) hQp hidxW)
  have hWB : autI hU W ⊓ autI hU B' ≤ autI hU W₂ :=
    le_of_isPGroup_of_not_dvd_relIndex (le_inf (autI_mono hU hW₂W) (autI_mono hU hW₂B))
      inf_le_right (hWbarp.to_le inf_le_left) hidxW₂
  set Q₂ : Subgroup (MulAut (IntMod V hU)) := autI hU W₂ with hQ₂
  set X₁ : Subgroup (MulAut (IntMod V hU)) := ⨆ L ∈ I, ⨆ (_ : r3 L ≤ Q₂), r3 L with hX₁
  set Wst : Subgroup (MulAut (IntMod V hU)) := ⨆ L ∈ I, ⨆ (_ : ¬ r3 L ≤ Q₂), r3 L with hWst
  set D₃ : Subgroup G := W ⊓ preAutM hU hMN Wst with hD₃
  have hX₁Q₂ : X₁ ≤ Q₂ := iSup₂_le fun L hL => iSup_le fun h => h
  have hX₁Z : X₁ ≤ zcl I := iSup₂_le fun L hL => iSup_le fun _ => r3_le_zcl hL
  have hWstZ : Wst ≤ zcl I := iSup₂_le fun L hL => iSup_le fun _ => r3_le_zcl hL
  have hZsplit : zcl I ≤ X₁ ⊔ Wst := by
    refine (Subgroup.closure_le _).2 fun x ⟨L, hL, hxL, hx3⟩ => ?_
    have hxr : x ∈ r3 L := Subgroup.subset_closure ⟨hxL, hx3⟩
    by_cases h : r3 L ≤ Q₂
    · exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem L (Subgroup.mem_iSup_of_mem hL
        (Subgroup.mem_iSup_of_mem h hxr)))
    · exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem L (Subgroup.mem_iSup_of_mem hL
        (Subgroup.mem_iSup_of_mem h hxr)))
  have hXWst : X₁ ≤ Subgroup.normalizer (Wst : Set (MulAut (IntMod V hU))) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hZab x (hX₁Z hx) y (hWstZ hy)).symm)
  have hact : ∀ (w : G) (hwM : w ∈ M), actM hU hMN ⟨w, hwM⟩ = convI hU ⟨w, hMN hwM⟩ :=
    fun w hwM => actM_eq_convI hU hMN ⟨w, hwM⟩
  have hstab : ∀ q ∈ Q₂, ∀ y ∈ Wst, q * y * q⁻¹ ∈ Wst := by
    intro q hq
    have hqM : q ∈ autI hU M := autI_mono hU (hW₂W.trans hWM) hq
    have hle : Wst ≤ Wst.comap (MulAut.conj q).toMonoidHom := by
      refine iSup₂_le fun L hL => iSup_le fun hLout => ?_
      intro x hx
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hL' : L.map (MulAut.conj q).toMonoidHom ∈ I :=
        (conjAut_eq_map_conj q L) ▸ hperm q hqM L hL
      have hL'out : ¬ r3 (L.map (MulAut.conj q).toMonoidHom) ≤ Q₂ := by
        intro hle'
        apply hLout
        intro z hz
        have h1 := hle' (conj_mem_r3 q L hz)
        have h2 := Q₂.mul_mem (Q₂.mul_mem (Q₂.inv_mem hq) h1) hq
        simpa [mul_assoc] using h2
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hL'
        (Subgroup.mem_iSup_of_mem hL'out (conj_mem_r3 q L hx)))
    intro y hy
    have := hle hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hYpart : ∀ a ∈ W ⊓ AY, ∃ (haM : a ∈ M), actM hU hMN ⟨a, haM⟩ ∈ zcl I := by
    intro a ha
    obtain ⟨haM, hπa⟩ := (mem_preAutM hU hMN).1 ha.2
    refine ⟨haM, ?_⟩
    have hπaW : actM hU hMN ⟨a, haM⟩ ∈ autI hU W :=
      (mem_autI hU).2 ⟨⟨a, hMN haM⟩, ha.1, rfl⟩
    have hz : Subgroup.zpowers (actM hU hMN ⟨a, haM⟩) ≤ zcl I :=
      le_zcl_of_isPGroup_le_iSup hI.comm hcard
        (hWbarp.to_le (Subgroup.zpowers_le.mpr hπaW))
        (by rw [← hYdef]; exact Subgroup.zpowers_le.mpr hπa)
    exact hz (Subgroup.mem_zpowers _)
  have hfacD : ∀ w ∈ W, ∃ a ∈ D₃, ∃ b ∈ W₂, w = a * b := by
    intro w hw
    obtain ⟨a, ha, b, hb, hwab⟩ := hWfac w hw
    obtain ⟨haM, hπaZ⟩ := hYpart a ha
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ X₁, ∃ y ∈ Wst, x * y = actM hU hMN ⟨a, haM⟩ := by
      have := hZsplit hπaZ
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X₁ Wst hXWst,
        Set.mem_mul] at this
      exact this
    obtain ⟨k, hkW₂, hkx⟩ := (mem_autI hU).1 (hX₁Q₂ hx)
    have hkM : (k : G) ∈ M := (hW₂W.trans hWM) hkW₂
    have hkW : (k : G) ∈ W := hW₂W hkW₂
    have hπk : actM hU hMN ⟨(k : G), hkM⟩ = x := by rw [hact]; exact hkx
    have hakM : a * (k : G)⁻¹ ∈ M := M.mul_mem haM (M.inv_mem hkM)
    refine ⟨a * (k : G)⁻¹, ⟨W.mul_mem ha.1 (W.inv_mem hkW), ?_⟩, (k : G) * b,
      W₂.mul_mem hkW₂ hb, by rw [hwab]; group⟩
    refine (mem_preAutM hU hMN).2 ⟨hakM, ?_⟩
    have e : actM hU hMN ⟨a * (k : G)⁻¹, hakM⟩ =
        actM hU hMN ⟨a, haM⟩ * (actM hU hMN ⟨(k : G), hkM⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hπk, ← hxy]
    have hcomm := hZab x (hX₁Z hx) y (hWstZ hy)
    have e2 : x * y * x⁻¹ = y := by rw [hcomm]; group
    rw [e2]
    exact hy
  have hDconj : ∀ w ∈ W, ∀ z ∈ D₃, w * z * w⁻¹ ∈ D₃ := by
    intro w hw z hz
    obtain ⟨a, ha, b, hb, hwab⟩ := hWfac w hw
    obtain ⟨haM, hπaZ⟩ := hYpart a ha
    have hwM : w ∈ M := hWM hw
    have hbM : b ∈ M := (hW₂W.trans hWM) hb
    have hπb : actM hU hMN ⟨b, hbM⟩ ∈ Q₂ := (mem_autI hU).2 ⟨⟨b, hMN hbM⟩, hb, rfl⟩
    obtain ⟨hzM, hπz⟩ := (mem_preAutM hU hMN).1 hz.2
    have hπw : actM hU hMN ⟨w, hwM⟩ = actM hU hMN ⟨a, haM⟩ * actM hU hMN ⟨b, hbM⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hwab
    have hwzM : w * z * w⁻¹ ∈ M := M.mul_mem (M.mul_mem hwM hzM) (M.inv_mem hwM)
    refine ⟨W.mul_mem (W.mul_mem hw hz.1) (W.inv_mem hw), (mem_preAutM hU hMN).2 ⟨hwzM, ?_⟩⟩
    have e : actM hU hMN ⟨w * z * w⁻¹, hwzM⟩ = actM hU hMN ⟨w, hwM⟩ * actM hU hMN ⟨z, hzM⟩ *
        (actM hU hMN ⟨w, hwM⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, hπw]
    have hu : actM hU hMN ⟨b, hbM⟩ * actM hU hMN ⟨z, hzM⟩ * (actM hU hMN ⟨b, hbM⟩)⁻¹ ∈ Wst :=
      hstab _ hπb _ hπz
    have hcomm := hZab _ hπaZ _ (hWstZ hu)
    have e2 : actM hU hMN ⟨a, haM⟩ * actM hU hMN ⟨b, hbM⟩ * actM hU hMN ⟨z, hzM⟩ *
        (actM hU hMN ⟨a, haM⟩ * actM hU hMN ⟨b, hbM⟩)⁻¹ =
        actM hU hMN ⟨b, hbM⟩ * actM hU hMN ⟨z, hzM⟩ * (actM hU hMN ⟨b, hbM⟩)⁻¹ := by
      calc _ = actM hU hMN ⟨a, haM⟩ * (actM hU hMN ⟨b, hbM⟩ * actM hU hMN ⟨z, hzM⟩ *
            (actM hU hMN ⟨b, hbM⟩)⁻¹) * (actM hU hMN ⟨a, haM⟩)⁻¹ := by group
        _ = (actM hU hMN ⟨b, hbM⟩ * actM hU hMN ⟨z, hzM⟩ * (actM hU hMN ⟨b, hbM⟩)⁻¹) *
            actM hU hMN ⟨a, haM⟩ * (actM hU hMN ⟨a, haM⟩)⁻¹ := by rw [hcomm]
        _ = _ := by group
    rw [e2]
    exact hu
  have hD₃W : D₃ ≤ W := inf_le_left
  have hD₃N : W ≤ Subgroup.normalizer (D₃ : Set G) := fun w hw =>
    Subgroup.mem_normalizer_iff.2 fun x =>
      ⟨fun hx => hDconj w hw x hx, fun h => by
        simpa [mul_assoc] using hDconj w⁻¹ (W.inv_mem hw) _ h⟩
  set Kout : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ r3 L ≤ Q₂), Hf L with hKout
  have hKoutM : Kout ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKoutN : Kout ≤ Subgroup.normalizer (C₁ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun hLout => by
      by_contra hnot
      have h2 : Hf L ≤ Subgroup.normalizer (C₂ : Set G) := (hHcase L hL).resolve_left hnot
      have h1 : r3 L ≤ autI hU W ⊓ autI hU B' :=
        le_inf ((r3_le_zcl hL).trans hZW)
          ((r3_le L).trans ((hHL L hL).trans (autI_mono hU (le_inf (hHM L hL) h2))))
      exact hLout (h1.trans hWB)
  have hWstK : Wst ≤ autI hU Kout :=
    iSup₂_le fun L hL => iSup_le fun hLout =>
      (r3_le L).trans ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ r3 L ≤ Q₂ => Hf L) hLout))))
  have hD₃N₁ : D₃ ≤ Subgroup.normalizer (C₁ : Set G) := by
    intro z hz
    obtain ⟨hzM, hπz⟩ := (mem_preAutM hU hMN).1 hz.2
    obtain ⟨k, hkK, hkz⟩ := (mem_autI hU).1 (hWstK hπz)
    have hkM : (k : G) ∈ M := hKoutM hkK
    have hπk : actM hU hMN ⟨(k : G), hkM⟩ = actM hU hMN ⟨z, hzM⟩ := by rw [hact]; exact hkz
    have hzkM : z * (k : G)⁻¹ ∈ M := M.mul_mem hzM (M.inv_mem hkM)
    have hone : actM hU hMN ⟨z * (k : G)⁻¹, hzkM⟩ = 1 := by
      have e : actM hU hMN ⟨z * (k : G)⁻¹, hzkM⟩ =
          actM hU hMN ⟨z, hzM⟩ * (actM hU hMN ⟨(k : G), hkM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e, hπk]
      group
    have hzkC : z * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) ⊓ M :=
      ⟨(actM_eq_one_iff hU hMN _).1 hone, hzkM⟩
    have := (Subgroup.normalizer (C₁ : Set G)).mul_mem (hCM₁ hzkC) (hKoutN hkK)
    simpa using this
  have hP₁D₃ : P₁ ≤ D₃ := fun x hx =>
    ⟨(hP₁D hx).1, centralizer_inf_le_preAutM hU hMN Wst (hCdef ▸ (hP₁D hx).2)⟩
  have hD₃c : IsCyclic ↥D₃ := by
    by_contra hnc
    obtain ⟨F, hFW, hFel, hFc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
    have hF27 : Nat.card F = 27 := by rw [hFc]; norm_num
    obtain ⟨E, hED, hEel, hE9, hEcore⟩ :=
      ctx.hasGoodE9_of_noncyclic_normal hWM hWp hD₃W hD₃N hnc hFW hFel hF27
    have hN₁2 : IsTwoLocal (Subgroup.normalizer (C₁ : Set G)) := ⟨C₁, hC₁1, hC₁2, rfl⟩
    have hD₃NM : D₃ ≤ Subgroup.normalizer (C₁ : Set G) ⊓ M := le_inf hD₃N₁ (hD₃W.trans hWM)
    have hP₁E : P₁ ≤ E := by
      intro p hp
      set B : Subgroup G := Subgroup.closure ((E : Set G) ∪ {p}) with hB
      have hBel : IsElemAbelian 3 B := by
        refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.isElemAbelian_closure (p := 3) ?_ ?_
        · rintro x (hx | hx) y (hy | hy)
          · exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
          · rw [Set.mem_singleton_iff.mp hy]
            exact hP₁cent x (hD₃W (hED hx)) p hp
          · rw [Set.mem_singleton_iff.mp hx]
            exact (hP₁cent y (hD₃W (hED hy)) p hp).symm
          · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
        · rintro x (hx | hx)
          · exact hEel.2 x hx
          · rw [Set.mem_singleton_iff.mp hx]
            exact hP₁cube p hp
      have hBD : B ≤ D₃ := (Subgroup.closure_le D₃).2
        (Set.union_subset hED (Set.singleton_subset_iff.2 (hP₁D₃ hp)))
      have hBp : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBel.2 x x.2)⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
      have hk2 : k ≤ 2 := (le_pRank_of_isElemAbelian Nat.prime_three hBel hk).trans
        ((pRank_mono 3 Nat.prime_three (hBD.trans hD₃NM)).trans (ctx.pRank_inf_le_two hN₁2 hN₁))
      have hEB : E ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
      have hBE : E = B := Subgroup.eq_of_le_of_card_ge hEB (by
        rw [hk, hE9]
        calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
          _ = 9 := by norm_num)
      rw [hBE]
      exact Subgroup.subset_closure (Or.inr (Set.mem_singleton p))
    obtain ⟨p, hp⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (show P₁ ≠ ⊥ from fun h => by
      rw [h, Subgroup.card_bot] at hP₁3
      omega)
    obtain ⟨y, hyE, hyP⟩ : ∃ y ∈ E, y ∉ P₁ := by
      by_contra hall
      push Not at hall
      have hle : E ≤ P₁ := hall
      have := Subgroup.card_le_of_le hle
      rw [hE9, hP₁3] at this
      omega
    have hy1 : y ≠ 1 := fun h => hyP (h ▸ P₁.one_mem)
    obtain ⟨n, hn, hnp⟩ := c.exists_conj_eq_of_good hN₁2 hT₁ hN₁ (hED.trans hD₃N₁)
      (hED.trans (hD₃W.trans hWM)) hEel hE9 hEcore p (hP₁E p.2)
      (fun h => hp (Subtype.ext h)) y hyE hy1
    have hnpP : n * (p : G) * n⁻¹ ∈ P₁ :=
      hwc n hn.1 p p.2 (by rw [hnp]; exact hD₃W (hED hyE))
    rw [hnp] at hnpP
    exact hyP hnpP
  exact center3_of_cyclic_normal_mul27 c hWM hWp hWidx hD₃W hD₃N hD₃c hW₂W
    (hW₂B.trans inf_le_right) hC₂1 hC₂2 hT₂ hfacD hP₁D₃ hP₁3 hwc

theorem center3_of_cyclic27
    (hX : D1NoXBlock3 G) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K T) (S : Sylow 3 ↥(ffC M T))
    (hS : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    (hS0 : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype ≠ ⊥) : Center3Conclusion M := by
  have ctx := c.ctx
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := c.sylow
  have hNT := c.not_normalizer_le
  have hs := c.solvable
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M :=
    CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)
  · exact center3_of_thompson_cyclic27 c S hS hS0 hJ
  · set V := conjClosure (quasithinOmegaOneCenter T) M with hV
    obtain ⟨hU, -⟩ := B2_15 hF hT
    have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
      (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
    have hsAut : Group.IsSolvable ↥(autOn M V) := by
      have := hs
      exact Group.isSolvable_of_surjective (actOnAutOn_surjective hMN)
    have hFF : FFConclusion M T V := ffConclusion_of_solvable hF hsAut hT hV hJ
    obtain ⟨hU', hMN', I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFF
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3_free hN ffGroupStep3Free ctx hT hNT hU' I hMN'
      hcard hJM hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU' (baum T) ≤ autI hU' (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN' hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU' (hT.2.1.to_le (C1GN.baum_le T)))
    exact center3_of_pairData_cyclic27 c hMN' hI hcard hSylB hJM hperm rfl S hS hS0
      (ffSolvableInput G M T hF hT hcon S hS) hdat

end CFSG.LocalAnalysis.RankThreeTheoremC
