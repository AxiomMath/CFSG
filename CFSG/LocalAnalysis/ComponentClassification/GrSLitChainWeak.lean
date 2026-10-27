module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
public import CFSG.LocalAnalysis.ComponentClassification.GSLitChain
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem gsWeakCorr_map (φ : G ≃* G) {c b : G} {J L : Subgroup G} (h : GSWeakCorr c J b L) :
    GSWeakCorr (φ c) (J.map φ.toMonoidHom) (φ b) (L.map φ.toMonoidHom) := by
  obtain ⟨hc, hb, hcb, hJc, hJ, hLb, hL, hbJ, hJb, hfix⟩ := h
  obtain ⟨hJc', hJ'⟩ := isPComponent_map_centralizer φ hJc hJ
  obtain ⟨hLb', hL'⟩ := isPComponent_map_centralizer φ hLb hL
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hc, by rw [MulEquiv.orderOf_eq]; exact hb,
    by rw [← map_mul, ← map_mul, hcb], hJc', hJ', hLb', hL', ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    rw [mem_map_equiv, mem_map_equiv, map_mul, map_mul, map_inv, φ.symm_apply_apply]
    exact mem_normalizer_iff.mp hbJ _
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := mem_map.mp hj
    rw [← map_map_pPrimeCore]
    refine ⟨j'⁻¹ * b⁻¹ * j' * b, hJb j' hj', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  · rw [← map_gsFixedLayer]
    calc (gsFixedLayer J b).map φ.toMonoidHom ≤ (L ⊔ conjugate L c).map φ.toMonoidHom :=
          map_mono hfix
      _ = L.map φ.toMonoidHom ⊔ conjugate (L.map φ.toMonoidHom) (φ c) := by
          rw [Subgroup.map_sup, UnbalancedLayer.map_conjugate]
          rfl

theorem gsWeakCorr_conjugate {c b : G} {J L : Subgroup G} (h : GSWeakCorr c J b L) (g : G) :
    GSWeakCorr (g⁻¹ * c * g) (conjugate J g) (g⁻¹ * b * g) (conjugate L g) := by
  have h' := gsWeakCorr_map (MulAut.conj g⁻¹) h
  simp only [MulAut.conj_apply, inv_inv] at h'
  exact h'

theorem sup_conjugate_le_pLayer {s t : G} {M : Subgroup G} (hst : s * t = t * s)
    (htM : M ≤ centralizer ({t} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) :
    M ⊔ conjugate M s ≤
        (pLayer ↥(centralizer ({t} : Set G)) 2).map (centralizer ({t} : Set G)).subtype ∧
      (pLayer ↥(centralizer ({t} : Set G)) 2).map (centralizer ({t} : Set G)).subtype ≤
        normalizer ((M ⊔ conjugate M s : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set G) with hH
  set E := (pLayer ↥H 2).map H.subtype with hE
  have hφt : (MulAut.conj s⁻¹) t = t := by
    rw [MulAut.conj_apply, inv_inv]
    calc s⁻¹ * t * s = s⁻¹ * (t * s) := by group
      _ = s⁻¹ * (s * t) := by rw [hst]
      _ = t := by group
  obtain ⟨hMs1, hMs2⟩ := isPComponent_map_centralizer (MulAut.conj s⁻¹) htM hMp
  rw [hφt] at hMs1 hMs2
  have hEN : ∀ X : Subgroup H, IsPComponent 2 X → pLayer H 2 ≤ normalizer (X : Set H) := by
    intro X hX
    apply sSup_le
    intro M' hM'
    by_cases hMX : X = M'
    · rw [← hMX]
      exact le_normalizer
    · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two X M' hX
        hM').2 hMX).1
  have hENG : ∀ X : Subgroup G, X ≤ H → IsPComponent 2 (X.subgroupOf H) →
      E ≤ normalizer (X : Set G) := by
    intro X hXH hX y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    exact UnbalancedLayer.mem_normalizer_of_subgroupOf hXH (hEN _ hX hy')
  exact ⟨sup_le (le_map_pLayer_of_isPComponent htM hMp) (le_map_pLayer_of_isPComponent hMs1 hMs2),
    fun y hy => UnbalancedCorr.mem_normalizer_sup (hENG M htM hMp hy) (hENG _ hMs1 hMs2 hy)⟩

theorem gsIsoCorr_of_weakCorr_of_kernel_of_cover {s t : G} {M N : Subgroup G}
    (h : GSWeakCorr s M t N) (hsN : s ∈ coreActionKernel N)
    (hcover : gsFixedLayer M t ⊔ (pPrimeCore 2 N).map N.subtype = N) :
    GSIsoCorr s M t N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, ht, hst, hMs, hMp, hNt, hNp, htM, hMt, hfix⟩ := h
  obtain ⟨hMsub, -, hMq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMs).1 hMp
  obtain ⟨hNsub, -, hNq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 N _ hNt).1 hNp
  have hconj : conjugate N s = N :=
    conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp hsN).1
  have hjoin : N ⊔ conjugate N s = N := by rw [hconj, sup_idem]
  have hTN : gsFixedLayer M t ≤ N := hfix.trans hjoin.le
  have htK : t ∈ coreActionKernel M := mem_coreActionKernel.mpr ⟨htM, hMt⟩
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hs2 : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  have hTgen := fixedLayer_eq_closure hMq (zpowers_le.mpr htK) ht2
  have hXgen := fixedLayer_eq_closure hNq (zpowers_le.mpr hsN) hs2
  rw [fixedLayer_zpowers, centralizer_zpowers_eq] at hTgen hXgen
  have hTX : gsFixedLayer M t ≤ gsFixedLayer N s := by
    rw [hTgen, hXgen]
    apply Subgroup.closure_mono
    rintro x ⟨hx, hx2⟩
    have hxT : x ∈ gsFixedLayer M t := by rw [hTgen]; exact subset_closure ⟨hx, hx2⟩
    exact ⟨mem_inf.mpr ⟨hTN hxT, hMs (mem_inf.mp hx).1⟩, hx2⟩
  have hXcover := (fixedLayer_sup_pPrimeCore hNq (zpowers_le.mpr hsN) hs2).1
  rw [fixedLayer_zpowers] at hXcover
  have hTXcover := sup_pPrimeCore_of_le hTX hcover hXcover
  have hTp := gsFixedLayer_isPComponent hMs hMsub
    (mem_centralizer_singleton_iff.mpr hst.symm) ht htM hMq hMt
  have hXp := gsFixedLayer_isPComponent hNt hNsub
    (mem_centralizer_singleton_iff.mpr hst) hs (mem_coreActionKernel.mp hsN).1
    hNq (mem_coreActionKernel.mp hsN).2
  rw [inf_comm (centralizer ({t} : Set G))] at hXp
  have hTC : gsFixedLayer M t ≤ centralizer ({s} : Set G) ⊓ centralizer ({t} : Set G) :=
    le_inf ((gsFixedLayer_le_inf M t).trans (inf_le_left.trans hMs))
      ((gsFixedLayer_le_inf M t).trans inf_le_right)
  have hXC : gsFixedLayer N s ≤ centralizer ({s} : Set G) ⊓ centralizer ({t} : Set G) :=
    le_inf ((gsFixedLayer_le_inf N s).trans inf_le_right)
      ((gsFixedLayer_le_inf N s).trans (inf_le_left.trans hNt))
  have heq : gsFixedLayer M t = gsFixedLayer N s :=
    eq_of_isPComponent_cover hTC hTp hXC hXp
      (sup_eq_left.mpr (map_subtype_le _)) hTXcover
  exact gsIsoCorr_iff_sup.mpr ⟨⟨hs, ht, hst, hMs, hMp, hNt, hNp, htM, hMt,
    by rw [hjoin, heq]⟩, hjoin, hcover⟩

theorem diamond_target_weak {e s t z : G} {Le Lz M N : Subgroup G} (hez : GSIsoCorr e Le z Lz)
    (hC : GSWeakCorr s Le t M) (hzt : GSIsoCorr z Lz t N) (htz : z * t = t * z)
    (htLe : t ∈ coreActionKernel Le) (htLz : t ∈ coreActionKernel Lz) :
    N = M ∨ N = conjugate M s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hezC, hezK, -⟩ := gsIsoCorr_iff_sup.mp hez
  obtain ⟨hztC, hztK, hztsup⟩ := gsIsoCorr_iff_sup.mp hzt
  have hzLz : Lz ≤ centralizer ({z} : Set G) := hezC.2.2.2.2.2.1
  have hLzp := hezC.2.2.2.2.2.2.1
  have ht2 : orderOf t = 2 := hC.2.1
  have heK : t ∈ normalizer ((Lz ⊔ conjugate Lz e : Subgroup G) : Set G) := by
    rw [hezK]
    exact (mem_coreActionKernel.mp htLz).1
  have hKe : ∀ k ∈ Lz ⊔ conjugate Lz e, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
    rw [hezK]
    intro k hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hzLz hLzp
      ((mem_coreActionKernel.mp htLz).2 k hk)
  obtain ⟨hWTU, -, -, -, -, hWV, hncl⟩ := correspondence_nested_fixed_layer_normal_closure hezC
    ht2 htz (mem_coreActionKernel.mp htLe).1 heK (mem_coreActionKernel.mp htLe).2 hKe rfl rfl rfl
    rfl
  have hVeq : gsFixedLayer (Lz ⊔ conjugate Lz e) t = gsFixedLayer Lz t := by rw [hezK]
  have htN : N ≤ centralizer ({t} : Set G) := hztC.2.2.2.2.2.1
  have hNp := hztC.2.2.2.2.2.2.1
  have hVN : gsFixedLayer Lz t ≤ N := hztC.gsFixedLayer_le hztK
  obtain ⟨hs2, -, hst, -, -, htM, hMp, -, -, hUK₁⟩ := id hC
  obtain ⟨hK₁E, hEK₁⟩ := sup_conjugate_le_pLayer hst htM hMp
  set E := (pLayer ↥(centralizer ({t} : Set G)) 2).map (centralizer ({t} : Set G)).subtype
    with hEdef
  set K₁ := M ⊔ conjugate M s with hK₁def
  have hNE : N ≤ E := le_map_pLayer_of_isPComponent htN hNp
  have hV'K₁ : gsFixedLayer Lz t ≤ K₁ := by
    rw [← hVeq] at hVN ⊢
    exact le_of_normalClosure_eq_top hncl ((hVN.trans hNE).trans hEK₁)
      (hWTU.trans (inf_le_right.trans hUK₁))
  have hφt : (MulAut.conj s⁻¹) t = t := by
    rw [MulAut.conj_apply, inv_inv]
    calc s⁻¹ * t * s = s⁻¹ * (t * s) := by group
      _ = s⁻¹ * (s * t) := by rw [hst]
      _ = t := by group
  obtain ⟨hMs1, hMs2⟩ := isPComponent_map_centralizer (MulAut.conj s⁻¹) htM hMp
  rw [hφt] at hMs1 hMs2
  refine eq_or_eq_of_map_le_sup htN hNp htM hMp hMs1 hMs2 ?_
  rw [GSLit.map_mk_eq_of_sup_pPrimeCore htN hNp hztsup]
  exact map_mono fun x hx => mem_subgroupOf.mpr (hV'K₁ (mem_subgroupOf.mp hx))

theorem diamond_isoCorr_weak {e s t z : G} {Le Lz M N : Subgroup G}
    (hez : GSIsoCorr e Le z Lz) (hC : GSWeakCorr s Le t M)
    (hzt : GSIsoCorr z Lz t N) (hztcomm : z * t = t * z)
    (htLe : t ∈ coreActionKernel Le) (htLz : t ∈ coreActionKernel Lz)
    (hsz : s * z = z * s) : GSIsoCorr s Le t M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsLe : s ∈ coreActionKernel Le := mem_coreActionKernel_of_le_centralizer hC.2.2.2.1
  have hsLz : s ∈ coreActionKernel Lz :=
    ((kernel_iff_of_gsIsoCorr hez (mem_inf.mpr
      ⟨mem_centralizer_singleton_iff.mpr hsz, (mem_coreActionKernel.mp hsLe).1⟩)).2).mp hsLe
  have hsN : s ∈ coreActionKernel N :=
    ((kernel_iff_of_gsIsoCorr hzt (mem_inf.mpr
      ⟨mem_centralizer_singleton_iff.mpr hC.2.2.1,
        (mem_coreActionKernel.mp hsLz).1⟩)).2).mp hsLz
  have hMN : M = N := by
    rcases diamond_target_weak hez hC hzt hztcomm htLe htLz with hNM | hNM
    · exact hNM.symm
    · have hss : s * s = 1 := by
        simpa only [hC.1, pow_two] using pow_orderOf_eq_one s
      have hNM' := congrArg (fun X : Subgroup G => conjugate X s) hNM
      rw [conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp hsN).1,
        conjugate_conjugate, hss, conjugate_one] at hNM'
      exact hNM'.symm
  have hsM : s ∈ coreActionKernel M := hMN.symm ▸ hsN
  obtain ⟨hezC, hezK, hezcover⟩ := gsIsoCorr_iff_sup.mp hez
  obtain ⟨hztC, -, hztcover⟩ := gsIsoCorr_iff_sup.mp hzt
  have hzLz : Lz ≤ centralizer ({z} : Set G) := hezC.2.2.2.2.2.1
  have hLzp := hezC.2.2.2.2.2.2.1
  have heK : t ∈ normalizer ((Lz ⊔ conjugate Lz e : Subgroup G) : Set G) := by
    rw [hezK]
    exact (mem_coreActionKernel.mp htLz).1
  have hKe : ∀ k ∈ Lz ⊔ conjugate Lz e, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
    rw [hezK]
    intro k hk
    exact map_pPrimeCore_le_of_isPComponent hzLz hLzp
      ((mem_coreActionKernel.mp htLz).2 k hk)
  obtain ⟨hWTU, hWT, -, -, -, hWV, -⟩ :=
    correspondence_nested_fixed_layer_normal_closure hezC hC.2.1 hztcomm
      (mem_coreActionKernel.mp htLe).1 heK (mem_coreActionKernel.mp htLe).2 hKe rfl rfl rfl rfl
  rw [hezK] at hWV
  have hWLz := sup_pPrimeCore_trans hezcover hWT
  obtain ⟨-, -, hLzq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Lz _ hzLz).1 hLzp
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hC.2.1, pow_one])
  have hVLz := (fixedLayer_sup_pPrimeCore hLzq (zpowers_le.mpr htLz) ht2).1
  rw [fixedLayer_zpowers] at hVLz
  have hWVcover := sup_pPrimeCore_of_le hWV hWLz hVLz
  have hWN := sup_pPrimeCore_trans hztcover hWVcover
  have hconj : M ⊔ conjugate M s = M := by
    rw [conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp hsM).1, sup_idem]
  have hUM : gsFixedLayer Le t ≤ M := hC.2.2.2.2.2.2.2.2.2.trans hconj.le
  apply gsIsoCorr_of_weakCorr_of_kernel_of_cover hC hsM
  apply le_antisymm (sup_le hUM (map_subtype_le _))
  rw [← hMN] at hWN
  exact hWN.ge.trans (sup_le_sup (hWTU.trans inf_le_right) le_rfl)

theorem step_weak_with_iso {a : G} {J S : Subgroup G} (h : B2Setting a J S) {e : G}
    (he : orderOf e = 2)
    (heP : e ∈ S ⊓ coreActionKernel J) {Le : Subgroup G} (hLe : GSIsoCorr a J e Le)
    (hSG : SylowGood S (zpowers e) Le) {s t : G} {M : Subgroup G} (hC : GSWeakCorr s Le t M) :
    GSIsoCorr s Le t M ∧
      ∃ (t' : G) (L' : Subgroup G) (g : G), orderOf t' = 2 ∧ t' ∈ S ⊓ coreActionKernel J ∧
        GSIsoCorr a J t' L' ∧ M = conjugate L' g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSGe := B2Setting.sylow_of_sylowGood he hSG
  obtain ⟨hLeC, -, -⟩ := gsIsoCorr_iff_sup.mp hLe
  have hLe_e : Le ≤ centralizer ({e} : Set G) := hLeC.2.2.2.2.2.1
  have hCSe : S ⊓ centralizer ({e} : Set G) ≤ normalizer (Le : Set G) := fun x hx =>
    (kernel_iff_of_gsIsoCorr hLe (mem_inf.mpr ⟨(mem_inf.mp hx).2,
      (mem_inf.mp (h.le_H (mem_inf.mp hx).1)).2⟩)).1
  have hCS2 : IsPGroup 2 ↥(S ⊓ centralizer ({e} : Set G)) := h.isPGroup.to_le inf_le_left
  obtain ⟨R₀, hR₀⟩ := (hCS2.comap_subtype (K := normalizer (Le : Set G))).exists_le_sylow
  set R := (R₀ : Subgroup (normalizer (Le : Set G))).map (normalizer (Le : Set G)).subtype
    with hRdef
  have hRN : R ≤ normalizer (Le : Set G) := map_subtype_le _
  have hR2 : IsPGroup 2 R := R₀.isPGroup'.map _
  have hCSR : S ⊓ centralizer ({e} : Set G) ≤ R := fun x hx =>
    ⟨⟨x, hCSe hx⟩, hR₀ (show (⟨x, hCSe hx⟩ : normalizer (Le : Set G)) ∈
      (S ⊓ centralizer ({e} : Set G)).subgroupOf (normalizer (Le : Set G)) from hx), rfl⟩
  have hRsyl : ∃ P₀ : Sylow 2 ↥(normalizer (Le : Set G)),
      (P₀ : Subgroup _) = R.subgroupOf (normalizer (Le : Set G)) :=
    ⟨R₀, by rw [hRdef, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]⟩
  have hsK : s ∈ coreActionKernel Le := mem_coreActionKernel_of_le_centralizer hC.2.2.2.1
  have htK : t ∈ coreActionKernel Le :=
    mem_coreActionKernel.mpr ⟨hC.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1⟩
  have hE₀N : zpowers t ⊔ zpowers s ≤ normalizer (Le : Set G) :=
    sup_le (zpowers_le.mpr (mem_coreActionKernel.mp htK).1)
      (zpowers_le.mpr (mem_coreActionKernel.mp hsK).1)
  obtain ⟨y, hyN, hyR⟩ := exists_conjugate_le_of_sylow hRsyl hE₀N
    (isPGroup_two_sup_zpowers hC.1 hC.2.1 hC.2.2.1)
  have hCy := gsWeakCorr_conjugate hC y
  rw [conjugate_eq_of_mem_normalizer hyN] at hCy
  have ht₁R : y⁻¹ * t * y ∈ R := hyR (conj_mem_conjugate (mem_sup_left (mem_zpowers t)) y)
  have hs₁R : y⁻¹ * s * y ∈ R := hyR (conj_mem_conjugate (mem_sup_right (mem_zpowers s)) y)
  have ht₁K : y⁻¹ * t * y ∈ coreActionKernel Le := by
    have h1 := conj_mem_coreActionKernel_conjugate htK y
    rwa [conjugate_eq_of_mem_normalizer hyN] at h1
  have heR : e ∈ R :=
    hCSR (mem_inf.mpr ⟨(mem_inf.mp heP).1, mem_centralizer_singleton_iff.mpr rfl⟩)
  have heK : e ∈ coreActionKernel Le := mem_coreActionKernel_of_le_centralizer hLe_e
  have hne1 : e ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at he
    exact absurd he (by norm_num)
  have hRnorm : R ≤ normalizer ((R ⊓ coreActionKernel Le : Subgroup G) : Set G) := fun r hr =>
    normalizer_inf_mem (le_normalizer hr) (normalizer_le_normalizer_coreActionKernel Le (hRN hr))
  have hRKne : R ⊓ coreActionKernel Le ≠ ⊥ := fun hb => hne1 (by
    have h1 := mem_inf.mpr ⟨heR, heK⟩
    rw [hb, mem_bot] at h1
    exact h1)
  obtain ⟨z, hzRK, hz, hzc⟩ := exists_involution_mem_center hR2 inf_le_left hRnorm hRKne
  have hzR := (mem_inf.mp hzRK).1
  have hze : z ∈ centralizer ({e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hzc e heR).symm
  have hRe : R ⊓ centralizer ({e} : Set G) ≤ S ⊓ centralizer ({e} : Set G) :=
    le_of_sylow_of_le hSGe (le_inf hCSR inf_le_right) (fun x hx => mem_inf.mpr
      ⟨(mem_inf.mp hx).2, hRN (mem_inf.mp hx).1⟩) (hR2.to_le inf_le_left)
  have hzS : z ∈ S := (mem_inf.mp (hRe (mem_inf.mpr ⟨hzR, hze⟩))).1
  have hzA : z ∈ centralizer ({e} : Set G) ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨hze, (mem_inf.mp (h.le_H hzS)).2⟩
  have hzP : z ∈ S ⊓ coreActionKernel J :=
    mem_inf.mpr ⟨hzS, ((kernel_iff_of_gsIsoCorr hLe hzA).2).mpr (mem_inf.mp hzRK).2⟩
  obtain ⟨Lz, hLz⟩ := h.exists_isoTarget hz hzP
  have hez : GSIsoCorr e Le z Lz := h.gsIsoCorr_isoTarget he hz heP hzP
    (mem_centralizer_singleton_iff.mp hze).symm hLe hLz
  have hzt₁ : z * (y⁻¹ * t * y) = (y⁻¹ * t * y) * z := (hzc _ ht₁R).symm
  have ht₁A : y⁻¹ * t * y ∈ centralizer ({z} : Set G) ⊓ normalizer (Le : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hzt₁.symm, (mem_coreActionKernel.mp ht₁K).1⟩
  have ht₁Kz : y⁻¹ * t * y ∈ coreActionKernel Lz :=
    ((kernel_iff_of_gsIsoCorr hez ht₁A).2).mp ht₁K
  have ht₁Nz : y⁻¹ * t * y ∈ normalizer (Lz : Set G) := (kernel_iff_of_gsIsoCorr hez ht₁A).1
  set t₁ := y⁻¹ * t * y with ht₁def
  have hzpP : zpowers z ≤ S ⊓ coreActionKernel J := zpowers_le.mpr hzP
  have hzne : zpowers z ≠ ⊥ := by
    intro hb
    have h1 : z = 1 := zpowers_eq_bot.mp hb
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨x, hxP, hxcov, hxSG⟩ := h.exists_sylowGood hzpP hzne (GSIsoCorr.isCover hLz)
  rw [conjugate_zpowers] at hxP hxcov hxSG
  set z₂ := x⁻¹ * z * x with hz₂def
  have hz₂P : z₂ ∈ S ⊓ coreActionKernel J := hxP (mem_zpowers z₂)
  have hz₂ : orderOf z₂ = 2 := by rw [hz₂def, orderOf_conj_inv]; exact hz
  set Lz₂ := conjugate Lz x with hLz₂def
  have hLz₂ : GSIsoCorr a J z₂ Lz₂ := h.gsIsoCorr_of_isCover hz₂ hz₂P hxcov
  have hSGz := B2Setting.sylow_of_sylowGood hz₂ hxSG
  set t₂ := x⁻¹ * t₁ * x with ht₂def
  have ht₂C : t₂ ∈ centralizer ({z₂} : Set G) := by
    rw [mem_centralizer_singleton_iff, ht₂def, hz₂def]
    calc x⁻¹ * t₁ * x * (x⁻¹ * z * x) = x⁻¹ * (t₁ * z) * x := by group
      _ = x⁻¹ * (z * t₁) * x := by rw [hzt₁]
      _ = x⁻¹ * z * x * (x⁻¹ * t₁ * x) := by group
  have ht₂N : t₂ ∈ normalizer (Lz₂ : Set G) := by
    have h1 := conjugate_le_normalizer (zpowers_le.mpr ht₁Nz) x
    rw [conjugate_zpowers] at h1
    exact h1 (mem_zpowers t₂)
  have ht₂2 : IsPGroup 2 (zpowers t₂) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht₂def, orderOf_conj_inv, ht₁def, orderOf_conj_inv, hC.2.1, pow_one])
  obtain ⟨w, hwY, hwS⟩ := exists_conjugate_le_of_sylow hSGz
    (zpowers_le.mpr (mem_inf.mpr ⟨ht₂C, ht₂N⟩)) ht₂2
  rw [conjugate_zpowers] at hwS
  set t' := w⁻¹ * t₂ * w with ht'def
  have ht'S := hwS (mem_zpowers t')
  have hwz : w * z₂ = z₂ * w := mem_centralizer_singleton_iff.mp (mem_inf.mp hwY).1
  have hwN : w ∈ normalizer (Lz₂ : Set G) := (mem_inf.mp hwY).2
  have ht'Kz : t' ∈ coreActionKernel Lz₂ := by
    have h1 := conj_mem_coreActionKernel_conjugate
      (conj_mem_coreActionKernel_conjugate ht₁Kz x) w
    rwa [← hLz₂def, conjugate_eq_of_mem_normalizer hwN] at h1
  have ht'A : t' ∈ centralizer ({z₂} : Set G) ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨(mem_inf.mp ht'S).2, (mem_inf.mp (h.le_H (mem_inf.mp ht'S).1)).2⟩
  have ht'P : t' ∈ S ⊓ coreActionKernel J :=
    mem_inf.mpr ⟨(mem_inf.mp ht'S).1, ((kernel_iff_of_gsIsoCorr hLz₂ ht'A).2).mpr ht'Kz⟩
  have ht' : orderOf t' = 2 := by
    rw [ht'def, orderOf_conj_inv, ht₂def, orderOf_conj_inv, ht₁def, orderOf_conj_inv]
    exact hC.2.1
  obtain ⟨Lt, hLt⟩ := h.exists_isoTarget ht' ht'P
  have hz₂t' : z₂ * t' = t' * z₂ := (mem_centralizer_singleton_iff.mp (mem_inf.mp ht'S).2).symm
  have hzt' : GSIsoCorr z₂ Lz₂ t' Lt :=
    h.gsIsoCorr_isoTarget hz₂ ht' hz₂P ht'P hz₂t' hLz₂ hLt
  have hzg : (x * w)⁻¹ * z * (x * w) = z₂ := by
    rw [hz₂def]
    calc (x * w)⁻¹ * z * (x * w) = w⁻¹ * (x⁻¹ * z * x) * w := by group
      _ = w⁻¹ * (x⁻¹ * z * x * w) := by group
      _ = w⁻¹ * (w * (x⁻¹ * z * x)) := by rw [← hz₂def, hwz]
      _ = x⁻¹ * z * x := by group
  have hLzg : conjugate Lz (x * w) = Lz₂ := by
    rw [← conjugate_conjugate, ← hLz₂def, conjugate_eq_of_mem_normalizer hwN]
  have htg : (x * w)⁻¹ * t₁ * (x * w) = t' := by
    rw [ht'def, ht₂def]
    group
  have hez' := gsIsoCorr_conjugate hez (x * w)
  rw [hzg, hLzg] at hez'
  have hC' := gsWeakCorr_conjugate hCy (x * w)
  rw [htg] at hC'
  have ht'Le : t' ∈ coreActionKernel (conjugate Le (x * w)) := by
    have h1 := conj_mem_coreActionKernel_conjugate ht₁K (x * w)
    rwa [htg] at h1
  have hs'z : (x * w)⁻¹ * (y⁻¹ * s * y) * (x * w) * z₂ =
      z₂ * ((x * w)⁻¹ * (y⁻¹ * s * y) * (x * w)) := by
    rw [← hzg]
    calc (x * w)⁻¹ * (y⁻¹ * s * y) * (x * w) *
          ((x * w)⁻¹ * z * (x * w)) =
          (x * w)⁻¹ * ((y⁻¹ * s * y) * z) * (x * w) := by group
      _ = (x * w)⁻¹ * (z * (y⁻¹ * s * y)) * (x * w) := by rw [hzc _ hs₁R]
      _ = (x * w)⁻¹ * z * (x * w) *
          ((x * w)⁻¹ * (y⁻¹ * s * y) * (x * w)) := by group
  have hIso' := diamond_isoCorr_weak hez' hC' hzt' hz₂t' ht'Le ht'Kz hs'z
  rw [← htg] at hIso'
  have hIsoy := gsIsoCorr_conjugate hIso' (x * w)⁻¹
  rw [inv_inv, show (x * w) * ((x * w)⁻¹ * (y⁻¹ * s * y) * (x * w)) * (x * w)⁻¹ =
    y⁻¹ * s * y by group,
    show (x * w) * ((x * w)⁻¹ * t₁ * (x * w)) * (x * w)⁻¹ = t₁ by group,
    conjugate_conjugate_inv, conjugate_conjugate_inv] at hIsoy
  have hIso := gsIsoCorr_conjugate hIsoy y⁻¹
  rw [inv_inv, show y * (y⁻¹ * s * y) * y⁻¹ = s by group,
    show y * t₁ * y⁻¹ = t by rw [ht₁def]; group,
    conjugate_conjugate_inv, conjugate_eq_of_mem_normalizer (inv_mem hyN)] at hIso
  refine ⟨hIso, ?_⟩
  rcases diamond_target_weak hez' hC' hzt' hz₂t' ht'Le ht'Kz with h1 | h1
  · refine ⟨t', Lt, (y * (x * w))⁻¹, ht', ht'P, hLt, ?_⟩
    rw [h1]
    simp only [conjugate_conjugate]
    convert (conjugate_one M).symm using 2
    group
  · refine ⟨t', Lt, (y * (x * w) * ((x * w)⁻¹ * (y⁻¹ * s * y) * (x * w)))⁻¹, ht', ht'P, hLt,
      ?_⟩
    rw [h1]
    simp only [conjugate_conjugate]
    convert (conjugate_one M).symm using 2
    group

theorem step_weak {a : G} {J S : Subgroup G} (h : B2Setting a J S) {e : G} (he : orderOf e = 2)
    (heP : e ∈ S ⊓ coreActionKernel J) {Le : Subgroup G} (hLe : GSIsoCorr a J e Le)
    (hSG : SylowGood S (zpowers e) Le) {s t : G} {M : Subgroup G} (hC : GSWeakCorr s Le t M) :
    ∃ (t' : G) (L' : Subgroup G) (g : G), orderOf t' = 2 ∧ t' ∈ S ⊓ coreActionKernel J ∧
      GSIsoCorr a J t' L' ∧ M = conjugate L' g :=
  (step_weak_with_iso h he heP hLe hSG hC).2

theorem reach_conjugate_isoTarget_weak {a : G} {J S : Subgroup G} (h : B2Setting a J S)
    {M : Subgroup G} (hM : GSWeakReach J M) :
    ∃ (e : G) (L : Subgroup G) (g : G), orderOf e = 2 ∧ e ∈ S ⊓ coreActionKernel J ∧
      GSIsoCorr a J e L ∧ SylowGood S (zpowers e) L ∧ M = conjugate L g := by
  induction hM with
  | refl =>
    exact ⟨a, J, 1, h.orderOf_eq, mem_inf.mpr ⟨h.a_mem, h.a_mem_coreActionKernel⟩,
      gsIsoCorr_self h.orderOf_eq h.le_centralizer h.isPComponent, h.sylowGood_a,
      (conjugate_one J).symm⟩
  | @tail M N _ hst ih =>
    obtain ⟨e, L, g, he, heP, hL, hSG, rfl⟩ := ih
    obtain ⟨s, t, hC⟩ := hst
    have hC' := gsWeakCorr_conjugate hC g⁻¹
    rw [conjugate_conjugate_inv] at hC'
    obtain ⟨t', L', g', ht', ht'P, hL', hN⟩ := step_weak h he heP hL hSG hC'
    have hne : zpowers t' ≠ ⊥ := by
      intro hb
      have h1 : t' = 1 := zpowers_eq_bot.mp hb
      rw [h1, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    obtain ⟨x, hxP, hxcov, hxSG⟩ :=
      h.exists_sylowGood (zpowers_le.mpr ht'P) hne (GSIsoCorr.isCover hL')
    rw [conjugate_zpowers] at hxP hxcov hxSG
    have ht'2 : orderOf (x⁻¹ * t' * x) = 2 := by rw [orderOf_conj_inv]; exact ht'
    refine ⟨x⁻¹ * t' * x, conjugate L' x, x⁻¹ * g' * g, ht'2, hxP (mem_zpowers _),
      h.gsIsoCorr_of_isCover ht'2 (hxP (mem_zpowers _)) hxcov, hxSG, ?_⟩
    have h1 : N = conjugate (conjugate N g⁻¹) g := by
      have h2 := conjugate_conjugate_inv N g⁻¹
      rw [inv_inv] at h2
      exact h2.symm
    rw [h1, hN, conjugate_conjugate, conjugate_conjugate]
    congr 1
    group

theorem gsIsoCorr_of_weakReach_of_B2Setting {a : G} {J S : Subgroup G}
    (h : B2Setting a J S) :
    ∀ (s t : G) (M N : Subgroup G), GSWeakReach J M → GSWeakCorr s M t N →
      GSIsoCorr s M t N := by
  intro s t M N hM hC
  obtain ⟨e, L, g, he, heP, hL, hSG, rfl⟩ := reach_conjugate_isoTarget_weak h hM
  have hC' := gsWeakCorr_conjugate hC g⁻¹
  rw [conjugate_conjugate_inv] at hC'
  have hIso := (step_weak_with_iso h he heP hL hSG hC').1
  have hback := gsIsoCorr_conjugate hIso g
  rw [inv_inv, show g⁻¹ * (g * s * g⁻¹) * g = s by group,
    show g⁻¹ * (g * t * g⁻¹) * g = t by group,
    show conjugate (conjugate N g⁻¹) g = N from
      by simpa only [inv_inv] using conjugate_conjugate_inv N g⁻¹] at hback
  exact hback

theorem nonempty_fusionZStar_equiv_conjugate (L : Subgroup G) (g : G) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* conjugate L g ⧸ Open.fusionZStar (conjugate L g)) := by
  let e : L ≃* conjugate L g :=
    L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  refine GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.toMonoidHom e.surjective ?_
  rw [show e.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr e.injective, card_bot]
  norm_num

theorem zStar_equiv_of_weakReach {a : G} {J S : Subgroup G} (h : B2Setting a J S)
    {M : Subgroup G} (hM : GSWeakReach J M) :
    Nonempty (J ⧸ Open.fusionZStar J ≃* M ⧸ Open.fusionZStar M) := by
  obtain ⟨e, L, g, -, -, hL, -, rfl⟩ := reach_conjugate_isoTarget_weak h hM
  obtain ⟨-, -, -, -, -, -, hidx, -⟩ := isomorphic_correspondence_sylow_growth hL rfl rfl rfl rfl
  obtain ⟨e₁⟩ := GSCorr.zStar_of_index_eq hL.1 hidx
  obtain ⟨e₂⟩ := nonempty_fusionZStar_equiv_conjugate L g
  exact ⟨e₁.trans e₂⟩

theorem zStar_equiv_of_weakReach_of_B2 {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hiso : ∀ b : G, orderOf b = 2 → b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      ∃ K : Subgroup G, GSIsoCorr a J b K)
    (hcentral : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      GSIsoCorr a J b K →
      ∀ S : Subgroup G, S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
        (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
          (P : Subgroup _) =
            S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
        b ∈ S → (∀ s ∈ S, s * b = b * s) →
        S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
          ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
            (P : Subgroup _) =
              S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G)))
    {M : Subgroup G} (hM : GSWeakReach J M) :
    Nonempty (J ⧸ Open.fusionZStar J ≃* M ⧸ Open.fusionZStar M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
    inferInstance
  set H := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hH
  have hS : ∃ P : Sylow 2 ↥H, (P : Subgroup _) = ((P₀ : Subgroup H).map H.subtype).subgroupOf H :=
    ⟨P₀, by rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]⟩
  exact zStar_equiv_of_weakReach (B2Setting.mk ha hJa hJ (map_subtype_le _) hS hiso
    fun b K hb hbH hbJ hK hbS hbZ => hcentral b K hb hbH hbJ hK _ (map_subtype_le _) hS hbS hbZ)
    hM

end CFSG.ComponentClassification.GrSLit
