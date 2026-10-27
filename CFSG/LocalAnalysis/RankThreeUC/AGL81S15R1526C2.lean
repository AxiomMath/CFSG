module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526C1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L1
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section Row26FourB

variable {G : Type} [Group G] [Finite G]

theorem row1526_four_pair_aux_uOf_le_map {M T : Subgroup G} (L : Subgroup ↥M) :
    uOf M T L ≤ (gnV (T.subgroupOf M)).map M.subtype := by
  refine Subgroup.map_mono ?_
  rw [Subgroup.commutator_comm]
  exact commutator_gnV_le _ L

theorem row1526_four_pair_aux_uOf_le {M T : Subgroup G} (hX : GNSetting ↥M (T.subgroupOf M))
    (L : Subgroup ↥M) : uOf M T L ≤ T := by
  refine (row1526_four_pair_aux_uOf_le_map L).trans ?_
  have h := Subgroup.map_mono (f := M.subtype)
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.gnV_le (T.subgroupOf M) hX)
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.trans inf_le_left

theorem row1526_four_pair_aux_isElemAbelian {M T : Subgroup G}
    (hX : GNSetting ↥M (T.subgroupOf M)) (L : Subgroup ↥M) : IsElemAbelian 2 (uOf M T L) :=
  (((CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV (T.subgroupOf M) hX).map
    M.subtype).mono (row1526_four_pair_aux_uOf_le_map L))

theorem row1526_four_pair_aux_card_uOf {M T : Subgroup G} (L : Subgroup ↥M) :
    Nat.card (uOf M T L) = Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆ :=
  Subgroup.card_map_of_injective M.subtype_injective

theorem row1526_four_pair_aux_inter {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hpair : IsGNPair (T.subgroupOf M) T₁ T₂)
    (hcard : Set.ncard (CY (T.subgroupOf M) T₁ T₂) ≤ 3) {A : Subgroup G} (hAT : A ≤ T)
    (hA8 : 8 ≤ Nat.card A) {I : Subgroup ↥M} (hI : I ∈ CY (T.subgroupOf M) T₁ T₂) :
    A ⊓ Subgroup.normalizer ((uOf M T I : Subgroup G) : Set G) ≠ ⊥ := by
  classical
  have hAM : A ≤ M := hAT.trans hT.le
  set A' : Subgroup ↥M := A.subgroupOf M with hA'
  have hA'map : A'.map M.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAM]
  have hA'T : A' ≤ T.subgroupOf M := fun x hx => hAT hx
  have hA'2 : IsPGroup 2 A' := (hT.isPGroup.to_le hAT).comap_subtype
  have hrel := relIndex_normalizer_le_two hpair hcard hA'T hA'2 hI
  have hA'card : Nat.card A' = Nat.card A := by
    rw [← hA'map, Subgroup.card_map_of_injective M.subtype_injective]
  have hmul := Subgroup.relIndex_mul_card (A' ⊓ Subgroup.normalizer (I : Set ↥M)) A'
  rw [inf_eq_left.mpr (inf_le_left : A' ⊓ Subgroup.normalizer (I : Set ↥M) ≤ A')] at hmul
  have h4 : 4 ≤ Nat.card ↥(A' ⊓ Subgroup.normalizer (I : Set ↥M)) := by
    nlinarith [hmul, hrel, hA8, hA'card]
  have hne : A' ⊓ Subgroup.normalizer (I : Set ↥M) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨haA', haN⟩ := Subgroup.mem_inf.1 ha
  have haA : (a : G) ∈ A := haA'
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
  have hx : I.map (MulAut.conj a).toMonoidHom = I := mem_normalizer_iff_map_conj_eq.1 haN
  haveI : (gnV (T.subgroupOf M)).Normal := Subgroup.normalClosure_normal
  have hxU := mem_normalizer_commutator (V := gnV (T.subgroupOf M)) hx
  have hxU' : conjSub a ⁅I, gnV (T.subgroupOf M)⁆ = ⁅I, gnV (T.subgroupOf M)⁆ :=
    mem_normalizer_iff_map_conj_eq.1 hxU
  have hnorm : (a : G) ∈ Subgroup.normalizer ((uOf M T I : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have := map_subtype_conjSub ⁅I, gnV (T.subgroupOf M)⁆ a
    rw [hxU'] at this
    exact this.symm
  intro hbot
  have hmem : (a : G) ∈ A ⊓ Subgroup.normalizer ((uOf M T I : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨haA, hnorm⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ha1' hmem

theorem row1526_four_pair_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55)
    (hKSML3 : KSML3)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {L : Subgroup ↥M} (hL : L ∈ CY (T.subgroupOf M) T₁ T₂)
    (hmax : ∀ I ∈ CY (T.subgroupOf M) T₁ T₂,
      Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆ ≤ Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆)
    {g : G} (hgT : conjSub g (uOf M T L) ≤ T) {I : Subgroup ↥M}
    (hI : I ∈ CY (T.subgroupOf M) T₁ T₂) :
    conjSub g (uOf M T L) ⊔ uOf M T I ≤
      Subgroup.normalizer ((conjSub g (uOf M T L) : Subgroup G) : Set G) := by
  have hX := ctx.gn
  have hL0 := hL
  have hI0 := hI
  obtain ⟨Ls, hLs, hLL⟩ := hL0
  obtain ⟨Is, hIs, hII⟩ := hI0
  obtain ⟨N₁, N₂, hN1, hN12, -⟩ :=
    isNatSum_of_K55 hK55 hX hLs.1 (ctx.shape Ls hLs).1 (h25.2 Ls L hLs hLL) hLL
  have h8 : 8 ≤ Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆ := by
    have h1 : Nat.card N₁ = 2 ^ 3 := hN1.2.1
    have h2 : N₁ ≤ ⁅L, gnV (T.subgroupOf M)⁆ := hN12 ▸ le_sup_left
    have h3 := Subgroup.card_le_of_le h2
    omega
  have h3σ : 3 ∉ CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet G M := by
    change 3 ∉ sigmaM G M
    rw [h25.1]
    intro h
    have h37 : (3 : ℕ) = 7 := by simpa using h
    omega
  have hcard3 : Set.ncard (CY (T.subgroupOf M) T₁ T₂) ≤ 3 :=
    ncard_CY_le_three hKSML3 hX (ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h3σ)
      (fun Ls L hLs hL => h25.2 Ls L hLs hL)
  have hAcard : Nat.card (conjSub g (uOf M T L)) = Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆ := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, row1526_four_pair_aux_card_uOf]
  refine tiPair_normalizes ctx.sylow.isPGroup hgT (row1526_four_pair_aux_uOf_le hX I)
    ((row1526_four_pair_aux_isElemAbelian hX L).map (MulAut.conj g).toMonoidHom)
    (row1526_four_pair_aux_isElemAbelian hX I)
    (CFSG.RankThree.GF2n.isTI_conjSubgroup (row1526_three_gen hK55 ctx h20 h25 hLs hLL) g)
    (row1526_three_gen hK55 ctx h20 h25 hIs hII)
    (row1526_four_pair_aux_inter ctx.sylow ctx.pair hcard3 hgT (by omega) hI) ?_
  rw [hAcard, row1526_four_pair_aux_card_uOf]
  exact hmax I hI

theorem row1526_four_contra_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55)
    (hKSML3 : KSML3)
    (hKOut : KOut) (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {L : Subgroup ↥M} (hL : L ∈ CY (T.subgroupOf M) T₁ T₂) {g : G} (hg : g ∉ M)
    (hgT : conjSub g (uOf M T L) ≤ T) {I : Subgroup ↥M} (hI : I ∈ CY (T.subgroupOf M) T₁ T₂)
    (hpair : conjSub g (uOf M T L) ⊔ uOf M T I ≤
      Subgroup.normalizer ((conjSub g (uOf M T L) : Subgroup G) : Set G)) :
    ∀ a ∈ conjSub g (uOf M T L), ∀ b ∈ uOf M T I, a * b = b * a := by
  classical
  have hX := ctx.gn
  have hTM : T ≤ M := ctx.sylow.le
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have h3σ : 3 ∉ CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet G M := by
    change 3 ∉ sigmaM G M
    rw [h25.1]
    intro h
    have h37 : (3 : ℕ) = 7 := by simpa using h
    omega
  have h33 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h3σ
  have hI0 := hI
  obtain ⟨Ls, hLs, hLL⟩ := hL
  obtain ⟨Is, hIs, hII⟩ := hI
  intro a ha b hb
  by_contra hab
  have haT : a ∈ T := hgT ha
  have haM : a ∈ M := hTM haT
  have hI' : conjSub (⟨a, haM⟩ : ↥M) I ∈ CY (T.subgroupOf M) T₁ T₂ :=
    conj_mem_CY ctx.pair hI0 (t := ⟨a, haM⟩) haT
  obtain ⟨Is', hIs', hII'⟩ := hI'
  have h2 : 1 < CFSG.Open.pRank 7 (cMBar I) := (h20 7 h7 Is I hIs hII).2.1
  have hR := two_le_pRank_pElement_cMLStar hX hII (by norm_num) (by norm_num) h2
  obtain ⟨x, hx7, hxI, hxI'⟩ := exists_sevenElement_centralizing_gen hKOut hKSML3 hX
    (Or.inr (h33.trans (by norm_num))) (fun Ls L hLs hL => h25.2 Ls L hLs hL)
    hIs hII hIs' hII' hR
  have hxP : x ∈ pElementSubgroup 7 (cMLStar (T.subgroupOf M) Is) :=
    Subgroup.subset_closure ⟨hxI, 1, by simpa using hx7⟩
  have hxP' : x ∈ pElementSubgroup 7 (cMLStar (T.subgroupOf M) Is') :=
    Subgroup.subset_closure ⟨hxI', 1, by simpa using hx7⟩
  have hNI := isNatSum_of_K55 hK55 hX hIs.1 (ctx.shape Is hIs).1 (h25.2 Is I hIs hII) hII
  have hNI' := isNatSum_of_K55 hK55 hX hIs'.1 (ctx.shape Is' hIs').1
    (h25.2 Is' _ hIs' hII') hII'
  have hxc : ∀ u ∈ (⁅I, gnV (T.subgroupOf M)⁆ : Subgroup ↥M), u * x = x * u := fun u hu =>
    Subgroup.mem_centralizer_iff.1 (pElement_cMLStar_le_centralizer hX hIs.1 hII hNI hxP) u hu
  have hxc' : ∀ u ∈ (⁅conjSub (⟨a, haM⟩ : ↥M) I, gnV (T.subgroupOf M)⁆ : Subgroup ↥M),
      u * x = x * u := fun u hu =>
    Subgroup.mem_centralizer_iff.1 (pElement_cMLStar_le_centralizer hX hIs'.1 hII' hNI' hxP') u hu
  obtain ⟨b₀, hb₀, hbb⟩ := Subgroup.mem_map.1 hb
  have hc₀ : (⟨a, haM⟩ : ↥M) * b₀ * (⟨a, haM⟩ : ↥M)⁻¹ ∈
      (⁅conjSub (⟨a, haM⟩ : ↥M) I, gnV (T.subgroupOf M)⁆ : Subgroup ↥M) := by
    rw [← isNatSum_tiM_aux_conj_commutator (T := T.subgroupOf M) I ⟨a, haM⟩]
    exact Subgroup.mem_map.2 ⟨b₀, hb₀, by simp [MulAut.conj_apply]⟩
  have hc₁ : Commute ((⟨a, haM⟩ : ↥M) * b₀ * (⟨a, haM⟩ : ↥M)⁻¹) x := hxc' _ hc₀
  have hc₂ : Commute b₀ x := hxc b₀ hb₀
  have hd₀ : Commute (((⟨a, haM⟩ : ↥M) * b₀ * (⟨a, haM⟩ : ↥M)⁻¹) * b₀⁻¹) x :=
    hc₁.mul_left hc₂.inv_left
  have hdx : (x : G) * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * (x : G) := by
    have h := congrArg Subtype.val hd₀.eq
    rw [← hbb]
    simpa using h.symm
  have hbN : b ∈ Subgroup.normalizer ((conjSub g (uOf M T L) : Subgroup G) : Set G) :=
    hpair (Subgroup.mem_sup_right hb)
  have hdA : a * b * a⁻¹ * b⁻¹ ∈ conjSub g (uOf M T L) := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ conjSub g (uOf M T L) :=
      (Subgroup.mem_normalizer_iff.1 hbN a⁻¹).1 (Subgroup.inv_mem _ ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha h1
  have hd1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
    intro h
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  obtain ⟨u, hu, hud⟩ := Subgroup.mem_map.1 hdA
  have hud' : g * u * g⁻¹ = a * b * a⁻¹ * b⁻¹ := by simpa [MulAut.conj_apply] using hud
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hd1
    rw [← hud']
    simp
  obtain ⟨hCM, -⟩ := row1526_centralizer_gen hK55 ctx h20 h25 hLs hLL u hu hu1
  have hxg : g⁻¹ * (x : G) * g ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    calc u * (g⁻¹ * (x : G) * g) = g⁻¹ * ((g * u * g⁻¹) * (x : G)) * g := by group
      _ = g⁻¹ * ((x : G) * (g * u * g⁻¹)) * g := by rw [hud', hdx]
      _ = g⁻¹ * (x : G) * g * u := by group
  have hgxg : g⁻¹ * (x : G) * g ∈ M := hCM hxg
  have hx_conj : (x : G) ∈ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨g⁻¹ * (x : G) * g, hgxg, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hle : Subgroup.zpowers (x : G) ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨x.2, hx_conj⟩
  have hord : orderOf (x : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hx7
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hord] at hdvd
  exact (ctx.strong 7 h7).2.2 g hg hdvd

end Row26FourB

end CFSG.LocalAnalysis.RankThreeUC.S15
