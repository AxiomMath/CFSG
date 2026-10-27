module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitSylowGood

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem map_pPrimeCore_le_of_isPComponent {Y L : Subgroup G} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) :
    (pPrimeCore 2 L).map L.subtype ≤ (pPrimeCore 2 Y).map Y.subtype := by
  have hle := map_pPrimeCore_subgroupOf_le hLY hL
  calc (pPrimeCore 2 L).map L.subtype
      = (((pPrimeCore 2 L).map L.subtype).subgroupOf Y).map Y.subtype :=
        (map_subgroupOf_eq_of_le ((map_subtype_le _).trans hLY)).symm
    _ ≤ (pPrimeCore 2 Y).map Y.subtype := map_mono hle

omit [Finite G] in
theorem le_map_pLayer_of_isPComponent {Y L : Subgroup G} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) : L ≤ (pLayer ↥Y 2).map Y.subtype := by
  calc L = (L.subgroupOf Y).map Y.subtype := (map_subgroupOf_eq_of_le hLY).symm
    _ ≤ (pLayer ↥Y 2).map Y.subtype :=
      map_mono (le_sSup (s := {M : Subgroup ↥Y | IsPComponent 2 M}) hL)

theorem eq_or_eq_of_map_le_sup {Y N M M' : Subgroup G} (hN : N ≤ Y)
    (hNp : IsPComponent 2 (N.subgroupOf Y)) (hM : M ≤ Y) (hMp : IsPComponent 2 (M.subgroupOf Y))
    (hM' : M' ≤ Y) (hM'p : IsPComponent 2 (M'.subgroupOf Y))
    (hle : (N.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 Y)) ≤
      ((M ⊔ M').subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 Y))) :
    N = M ∨ N = M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  set π := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  have hcomm : ∀ A : Subgroup G, A ≤ Y → IsPComponent 2 (A.subgroupOf Y) → N ≠ A →
      ⁅(N.subgroupOf Y).map π, (A.subgroupOf Y).map π⁆ = ⊥ := by
    intro A hA hAp hNA
    have hne' : N.subgroupOf Y ≠ A.subgroupOf Y := fun h => by
      rw [subgroupOf_inj, inf_of_le_left hN, inf_of_le_left hA] at h
      exact hNA h
    obtain ⟨-, -, hc, -⟩ :=
      (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hNp hAp).2
        hne'
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    obtain ⟨-, -, hs, -, -⟩ := id hNp
    refine hc.trans (inf_le_left.trans ?_)
    rw [map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  have hc1 := hcomm M hM hMp hne1
  have hc2 := hcomm M' hM' hM'p hne2
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hc1 hc2
  have hNle : (N.subgroupOf Y).map π ≤ (M.subgroupOf Y).map π ⊔ (M'.subgroupOf Y).map π := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup hM hM']
    exact hle
  have hab : (N.subgroupOf Y).map π ≤ centralizer ((N.subgroupOf Y).map π : Set _) :=
    hNle.trans (sup_le hc1 hc2)
  have hbot : ⁅(N.subgroupOf Y).map π, (N.subgroupOf Y).map π⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hab
  obtain ⟨Kc, hKc, -, hmap, -⟩ := id hNp
  rw [hmap, Subgroup.isPerfect_iff.mp hKc.1.1] at hbot
  subst hbot
  obtain ⟨x, y, hxy⟩ := hKc.1.2.2
  have h1 : ∀ z : ↥(⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)) ⧸
      center ↥(⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)), z = 1 := fun z => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    rw [Subsingleton.elim w 1]
    rfl
  exact hxy (by rw [h1 x, h1 y])

theorem gsIsoCorr_conjugate {a b : G} {J L : Subgroup G} (h : GSIsoCorr a J b L) (g : G) :
    GSIsoCorr (g⁻¹ * a * g) (conjugate J g) (g⁻¹ * b * g) (conjugate L g) := by
  rw [gsIsoCorr_iff_sup] at h ⊢
  obtain ⟨hC, hK, hsup⟩ := h
  refine ⟨gsCorr_conjugate hC g, ?_, ?_⟩
  · have h1 : conjugate (conjugate L g) (g⁻¹ * a * g) = conjugate (conjugate L a) g := by
      rw [conjugate_conjugate, conjugate_conjugate]
      congr 1
      group
    rw [h1]
    have h2 : conjugate L g ⊔ conjugate (conjugate L a) g = conjugate (L ⊔ conjugate L a) g := by
      unfold conjugate
      rw [Subgroup.map_sup]
    rw [h2, hK]
  · have h1 : gsFixedLayer (conjugate J g) (g⁻¹ * b * g) = conjugate (gsFixedLayer J b) g := by
      have h2 := map_gsFixedLayer (MulAut.conj g⁻¹) J b
      simp only [MulAut.conj_apply, inv_inv] at h2
      exact h2.symm
    rw [h1]
    exact conjugate_sup_pPrimeCore hsup g

omit [Finite G] in
theorem le_of_normalClosure_eq_top {V W X : Subgroup G}
    (hncl : normalClosure ((W.subgroupOf V : Subgroup V) : Set V) = ⊤)
    (hVX : V ≤ normalizer (X : Set G)) (hWX : W ≤ X) : V ≤ X := by
  have hnorm : (X.subgroupOf V).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hVX g.2) x).mp hx⟩
  have hle : normalClosure ((W.subgroupOf V : Subgroup V) : Set V) ≤ X.subgroupOf V :=
    normalClosure_le_normal fun x hx => mem_subgroupOf.mpr (hWX (mem_subgroupOf.mp hx))
  rw [hncl] at hle
  intro v hv
  exact mem_subgroupOf.mp (hle (mem_top (⟨v, hv⟩ : V)))

theorem sup_pPrimeCore_of_le {W X L : Subgroup G} (hWX : W ≤ X)
    (hW : W ⊔ (pPrimeCore 2 L).map L.subtype = L) (hX : X ⊔ (pPrimeCore 2 L).map L.subtype = L) :
    W ⊔ (pPrimeCore 2 X).map X.subtype = X := by
  have hXL : X ≤ L := le_sup_left.trans hX.le
  have hOX := map_pPrimeCore_eq_inf_of_sup_eq hX
  apply le_antisymm (sup_le hWX (map_subtype_le _))
  intro x hx
  have hmul := coe_sup_primeCore_eq_mul (hWX.trans hXL)
  rw [hW] at hmul
  have hx' : x ∈ ((W : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G)) := by
    rw [← hmul]
    exact hXL hx
  obtain ⟨w, hw, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have hoX : o ∈ X := by
    have h1 : o = w⁻¹ * (w * o) := by group
    rw [h1]
    exact mul_mem (inv_mem (hWX hw)) hx
  have hoOX : o ∈ (pPrimeCore 2 X).map X.subtype := by
    rw [hOX]
    exact mem_inf.mpr ⟨hoX, ho⟩
  exact mul_mem (mem_sup_left hw) (mem_sup_right hoOX)

omit [Finite G] in
theorem conjugate_zpowers (z g : G) : conjugate (zpowers z) g = zpowers (g⁻¹ * z * g) := by
  rw [conjugate, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

omit [Finite G] in
theorem conj_mem_coreActionKernel_conjugate {L : Subgroup G} {q : G}
    (hq : q ∈ coreActionKernel L) (g : G) : g⁻¹ * q * g ∈ coreActionKernel (conjugate L g) := by
  obtain ⟨hqN, hqL⟩ := mem_coreActionKernel.mp hq
  refine mem_coreActionKernel.mpr ⟨?_, fun l hl => ?_⟩
  · apply mem_normalizer_of_conjugate_eq
    rw [conjugate_conjugate, show g * (g⁻¹ * q * g) = q * g by group, ← conjugate_conjugate,
      conjugate_eq_of_mem_normalizer hqN]
  · rw [← conjugate_map_pPrimeCore, mem_conjugate_iff]
    rw [mem_conjugate_iff] at hl
    have h1 := hqL _ hl
    rwa [show g * (l⁻¹ * (g⁻¹ * q * g)⁻¹ * l * (g⁻¹ * q * g)) * g⁻¹ =
      (g * l * g⁻¹)⁻¹ * q⁻¹ * (g * l * g⁻¹) * q by group]

theorem gsIsoCorr_self {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) : GSIsoCorr a J a J := by
  have hJJ : conjugate J a = J := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJa
  have hk := mem_coreActionKernel.mp (mem_coreActionKernel_of_le_centralizer hJa)
  rw [gsIsoCorr_iff_sup]
  refine ⟨⟨ha, ha, rfl, hJa, hJ, hJa, hJ, hk.1, hk.2, ?_⟩, by rw [hJJ, sup_idem], ?_⟩
  · rw [hJJ, sup_idem]
  · rw [gsFixedLayer_eq_self hJa hJ]
    exact sup_eq_left.mpr (map_subtype_le _)

theorem kernel_iff_of_gsIsoCorr {c z : G} {M L : Subgroup G} (hL : GSIsoCorr c M z L) {g : G}
    (hg : g ∈ centralizer ({z} : Set G) ⊓ normalizer (M : Set G)) :
    g ∈ normalizer (L : Set G) ∧ (g ∈ coreActionKernel M ↔ g ∈ coreActionKernel L) := by
  obtain ⟨hNL, -, -, -, -, -, -, hker, -⟩ :=
    isomorphic_correspondence_sylow_growth hL rfl rfl rfl rfl
  refine ⟨hNL hg, ⟨fun hgM => ?_, fun hgL => ?_⟩⟩
  · have h1 : g ∈ {g | g ∈ centralizer ({z} : Set G) ⊓ normalizer (M : Set G) ∧
        ∀ j ∈ M, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 M).map M.subtype} :=
      ⟨hg, (mem_coreActionKernel.mp hgM).2⟩
    rw [hker] at h1
    exact mem_coreActionKernel.mpr ⟨hNL hg, h1.2⟩
  · have h1 : g ∈ {g | g ∈ centralizer ({z} : Set G) ⊓ normalizer (M : Set G) ∧
        ∀ l ∈ L, l⁻¹ * g⁻¹ * l * g ∈ (pPrimeCore 2 L).map L.subtype} :=
      ⟨hg, (mem_coreActionKernel.mp hgL).2⟩
    rw [← hker] at h1
    exact mem_coreActionKernel.mpr ⟨(mem_inf.mp hg).2, h1.2⟩

omit [Finite G] in
theorem le_of_sylow_of_le {Y Q X : Subgroup G}
    (hQ : ∃ P₀ : Sylow 2 ↥Y, (P₀ : Subgroup Y) = Q.subgroupOf Y) (hQX : Q ≤ X) (hXY : X ≤ Y)
    (hX : IsPGroup 2 X) : X ≤ Q := by
  obtain ⟨P₀, hP₀⟩ := hQ
  have hle : (P₀ : Subgroup Y) ≤ X.subgroupOf Y := by
    rw [hP₀]
    exact fun x hx => mem_subgroupOf.mpr (hQX (mem_subgroupOf.mp hx))
  have heq := P₀.is_maximal' (Q := X.subgroupOf Y) hX.comap_subtype hle
  intro x hx
  have h1 : (⟨x, hXY hx⟩ : Y) ∈ X.subgroupOf Y := hx
  rw [heq, hP₀] at h1
  exact mem_subgroupOf.mp h1

theorem diamond_target {e s t z : G} {Le Lz M N : Subgroup G} (hez : GSIsoCorr e Le z Lz)
    (hC : GSCorr s Le t M) (hzt : GSIsoCorr z Lz t N) (htz : z * t = t * z)
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
    exact map_pPrimeCore_le_of_isPComponent hzLz hLzp ((mem_coreActionKernel.mp htLz).2 k hk)
  obtain ⟨hWTU, -, -, -, -, hWV, hncl⟩ := correspondence_nested_fixed_layer_normal_closure hezC
    ht2 htz (mem_coreActionKernel.mp htLe).1 heK (mem_coreActionKernel.mp htLe).2 hKe rfl rfl rfl
    rfl
  have hVeq : gsFixedLayer (Lz ⊔ conjugate Lz e) t = gsFixedLayer Lz t := by rw [hezK]
  have htN : N ≤ centralizer ({t} : Set G) := hztC.2.2.2.2.2.1
  have hNp := hztC.2.2.2.2.2.2.1
  have hVN : gsFixedLayer Lz t ≤ N := hztC.gsFixedLayer_le hztK
  obtain ⟨hs2, -, hst, -, -, htM, hMp, -, -, hfix⟩ := id hC
  obtain ⟨hK₁E, hK₁n, -, -⟩ := correspondence_normal_closure hC rfl rfl rfl
  set E := (pLayer ↥(centralizer ({t} : Set G)) 2).map (centralizer ({t} : Set G)).subtype
    with hEdef
  set K₁ := M ⊔ conjugate M s with hK₁def
  have hUK₁ : gsFixedLayer Le t ≤ K₁ := by
    rw [hfix]
    exact (gsFixedLayer_le_inf _ s).trans inf_le_left
  have hEK₁ : E ≤ normalizer (K₁ : Set G) := (normal_subgroupOf_iff_le_normalizer hK₁E).mp hK₁n
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
  have hK₁t : K₁ ≤ centralizer ({t} : Set G) := sup_le htM hMs1
  refine eq_or_eq_of_map_le_sup htN hNp htM hMp hMs1 hMs2 ?_
  rw [map_mk_eq_of_sup_pPrimeCore htN hNp hztsup]
  exact map_mono fun x hx => mem_subgroupOf.mpr (hV'K₁ (mem_subgroupOf.mp hx))

omit [Finite G] in
theorem orderOf_conj_inv (z g : G) : orderOf (g⁻¹ * z * g) = orderOf z := by
  have h1 : g⁻¹ * z * g = (MulAut.conj g⁻¹) z := by
    rw [MulAut.conj_apply, inv_inv]
  rw [h1, MulEquiv.orderOf_eq]

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem gsIsoCorr_of_isCover (h : B2Setting a J S) {e : G} (he : orderOf e = 2)
    (heP : e ∈ S ⊓ coreActionKernel J) {K : Subgroup G} (hK : IsCover J (zpowers e) K) :
    GSIsoCorr a J e K := by
  obtain ⟨L, hL⟩ := h.exists_isoTarget he heP
  rw [hK.unique (GSIsoCorr.isCover hL)]
  exact hL

theorem sylow_of_sylowGood {e : G} (he : orderOf e = 2) {L : Subgroup G}
    (hSG : SylowGood S (zpowers e) L) :
    ∃ P₀ : Sylow 2 ↥(centralizer ({e} : Set G) ⊓ normalizer (L : Set G)),
      (P₀ : Subgroup _) = (S ⊓ centralizer ({e} : Set G)).subgroupOf
        (centralizer ({e} : Set G) ⊓ normalizer (L : Set G)) := by
  have hNe := LocalB.normalizer_zpowers_of_involution e he
  unfold SylowGood at hSG
  rw [hNe] at hSG
  exact hSG

theorem step (h : B2Setting a J S) {e : G} (he : orderOf e = 2)
    (heP : e ∈ S ⊓ coreActionKernel J) {Le : Subgroup G} (hLe : GSIsoCorr a J e Le)
    (hSG : SylowGood S (zpowers e) Le) {s t : G} {M : Subgroup G} (hC : GSCorr s Le t M) :
    ∃ (t' : G) (L' : Subgroup G) (g : G), orderOf t' = 2 ∧ t' ∈ S ⊓ coreActionKernel J ∧
      GSIsoCorr a J t' L' ∧ M = conjugate L' g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSGe := sylow_of_sylowGood he hSG
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
  have hCy := gsCorr_conjugate hC y
  rw [conjugate_eq_of_mem_normalizer hyN] at hCy
  have ht₁R : y⁻¹ * t * y ∈ R := hyR (conj_mem_conjugate (mem_sup_left (mem_zpowers t)) y)
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
  have hSGz := sylow_of_sylowGood hz₂ hxSG
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
  have hC' := gsCorr_conjugate hCy (x * w)
  rw [htg] at hC'
  have ht'Le : t' ∈ coreActionKernel (conjugate Le (x * w)) := by
    have h1 := conj_mem_coreActionKernel_conjugate ht₁K (x * w)
    rwa [htg] at h1
  rcases diamond_target hez' hC' hzt' hz₂t' ht'Le ht'Kz with h1 | h1
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

theorem sylowGood_a (h : B2Setting a J S) : SylowGood S (zpowers a) J := by
  unfold SylowGood
  rw [LocalB.normalizer_zpowers_of_involution a h.orderOf_eq,
    inf_eq_left.mpr (h.le_H.trans inf_le_left)]
  exact h.isSylow

theorem reach_conjugate_isoTarget (h : B2Setting a J S) {M : Subgroup G} (hM : GSReach J M) :
    ∃ (e : G) (L : Subgroup G) (g : G), orderOf e = 2 ∧ e ∈ S ⊓ coreActionKernel J ∧
      GSIsoCorr a J e L ∧ SylowGood S (zpowers e) L ∧ M = conjugate L g := by
  obtain ⟨-, hR⟩ := hM
  induction hR with
  | refl =>
    exact ⟨a, J, 1, h.orderOf_eq, mem_inf.mpr ⟨h.a_mem, h.a_mem_coreActionKernel⟩,
      gsIsoCorr_self h.orderOf_eq h.le_centralizer h.isPComponent, h.sylowGood_a,
      (conjugate_one J).symm⟩
  | @tail M N _ hst ih =>
    obtain ⟨e, L, g, he, heP, hL, hSG, rfl⟩ := ih
    obtain ⟨s, t, hC⟩ := hst
    have hC' := gsCorr_conjugate hC g⁻¹
    rw [conjugate_conjugate_inv] at hC'
    obtain ⟨t', L', g', ht', ht'P, hL', hN⟩ := h.step he heP hL hSG hC'
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

theorem gsMaximalComponent (h : B2Setting a J S) : GSMaximalComponent J := by
  refine gsMaximalComponent_of_index_le ⟨a, h.orderOf_eq, h.le_centralizer, h.isPComponent⟩
    fun M hM => ?_
  obtain ⟨e, L, g, -, -, hL, -, rfl⟩ := h.reach_conjugate_isoTarget hM
  rw [index_pPrimeCore_conjugate]
  obtain ⟨-, -, -, -, -, -, hidx, -⟩ := isomorphic_correspondence_sylow_growth hL rfl rfl rfl rfl
  exact hidx.symm.le

end B2Setting

theorem gsMaximalComponent_of_B2 {a : G} {J : Subgroup G} (ha : orderOf a = 2)
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
              S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G))) :
    GSMaximalComponent J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
    inferInstance
  set H := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hH
  have hS : ∃ P : Sylow 2 ↥H, (P : Subgroup _) = ((P₀ : Subgroup H).map H.subtype).subgroupOf H :=
    ⟨P₀, by rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]⟩
  exact (B2Setting.mk ha hJa hJ (map_subtype_le _) hS hiso fun b K hb hbH hbJ hK hbS hbZ =>
    hcentral b K hb hbH hbJ hK _ (map_subtype_le _) hS hbS hbZ).gsMaximalComponent

end CFSG.ComponentClassification.GSLit
