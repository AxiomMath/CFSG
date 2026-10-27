module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bKGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

structure I264bHyp {G : Type} [Group G] [Finite G] (p : ℕ) (B L : Subgroup G) : Prop where
  elem : IsElemAbelian p B
  qs : CFSG.Open.IsQuasisimple (PQuot p L)
  kgroup : CFSG.Open.IsKGroup ↥L
  norm : B ≤ Subgroup.normalizer (L : Set G)
  card : p ^ 4 ≤ Nat.card B
  maxrank : IsMaxRankIn p B (L ⊔ B)
  cent : B ⊓ centModSubgroup p L ≠ ⊥
  chev : IsChevSimple 2 (PSimple p L)
  twogrp : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    ¬ T ≤ GLAPPrimeCoreOf p L

structure KHyp {Y : Type} [Group Y] [Finite Y] (p : ℕ) (K B : Subgroup Y) : Prop where
  normal : K.Normal
  qs : CFSG.Open.IsQuasisimple ↥K
  core : GLAPPrimeCore p ↥K = ⊥
  chev : IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)
  kgroup : CFSG.Open.IsKGroup Y
  elem : IsElemAbelian p B
  sup : K ⊔ B = ⊤
  card : p ^ 4 ≤ Nat.card B
  maxrank : IsMaxRankIn p B ⊤
  cent : B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥
  twogrp : ∃ T : Subgroup Y, T ≤ K ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set Y)

@[expose] def KConcl {Y : Type} [Group Y] [Finite Y] (p : ℕ) (K B : Subgroup Y) : Prop :=
  ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
    GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥

@[expose] def KD264bK (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B → KConcl p K B

@[expose] def I264bGenAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ B L : Subgroup G, I264bHyp p B L → IsGB p B L

section Transfer

variable {G : Type} [Group G] [Finite G]

private theorem isChevSimple_of_mulEquiv_held {r : ℕ} {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : IsChevSimple r S) : IsChevSimple r S' := by
  rcases h with h | h
  · exact Or.inl (ys03_catalogIs_of_mulEquiv e h)
  · exact Or.inr (ys03_catalogIs_of_mulEquiv e h)

private theorem barX_mono_held {p : ℕ} {M T L : Subgroup G} (h : T ≤ L) :
    barX p M T ≤ barX p M L :=
  Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem exists_kLevel_of_hyp {p : ℕ} (hp : p.Prime) {B L : Subgroup G} (h : I264bHyp p B L) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (K B' : Subgroup Y),
      KHyp p K B' ∧ Nat.card K ≤ Nat.card L ∧ (KConcl p K B' → IsGB p B L) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hBab := h.elem
  have hBN := h.norm
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBab
  set M : Subgroup G := L ⊔ B with hM
  have hLM : L ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  haveI hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMN
  have hsn : IsSubnormal L M := IsSubnormal.step hLM hLn (IsSubnormal.refl M)
  have hOL : GLAPPrimeCoreOf p M ≤ L := ys03_glaPPrimeCoreOf_sup_le hp hBp hBN
  have hOLM : GLAPPrimeCoreOf p L = GLAPPrimeCoreOf p M := by
    have h1 := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn
    rw [inf_eq_right.2 hOL] at h1
    exact h1.symm
  have eK : ↥(barX p M L) ≃* PQuot p L := (quotEquivBarX hp hLM hsn).symm
  have hKq : CFSG.Open.IsQuasisimple ↥(barX p M L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm h.qs
  have hKcore : GLAPPrimeCore p ↥(barX p M L) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p eK
    rw [ys03_glaPPrimeCore_quot_eq_bot hp ↥L] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).1 h1
  have hKn : (barX p M L).Normal := by
    show ((L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).Normal
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hBab' : IsElemAbelian p (barX p M B) := isElemAbelian_barX hBab
  have hsup : barX p M L ⊔ barX p M B = ⊤ := by
    show (L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) ⊔
      (B.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLM hBM]
    have htop : (L ⊔ B).subgroupOf M = ⊤ := by
      rw [← hM, Subgroup.subgroupOf_self]
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hpow : p ^ 4 ≤ Nat.card (barX p M B) := by
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    exact h.card
  have hcop : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hmaxY : IsMaxRankIn p (barX p M B) ⊤ := by
    intro E _ hE
    obtain ⟨S, hS, hSE, hSc⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥M) hcop hE
    have hS0 : IsElemAbelian p (S.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hS _
    have hle := h.maxrank (S.map M.subtype) (Subgroup.map_subtype_le S) hS0
    have hc1 : Nat.card (S.map M.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    have : Nat.card E = Nat.card S := hSc.symm
    omega
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.cent
  have hxB : x ∈ B := hxmem.1
  have hxcm : CentMod p L x := centMod_iff.2 hxmem.2
  have hxM : x ∈ M := hBM hxB
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hxbar_ne : ys03_qMap p M ⟨x, hxM⟩ ≠ 1 := by
    intro h1
    have hinj := injective_barX_comp hp hBp hBM
    have h2 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (B.subgroupOf M).subtype)
        ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxB⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (B.subgroupOf M).subtype) 1 := by
      show ys03_qMap p M ⟨x, hxM⟩ = ys03_qMap p M 1
      rw [h1, map_one]
    have h3 : (⟨x, hxM⟩ : ↥M) = 1 := congrArg Subtype.val (hinj h2)
    exact hx1' (congrArg Subtype.val h3)
  have hxC : ys03_qMap p M ⟨x, hxM⟩ ∈ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) :=
    (ys03_centMod_iff_qMap hp hLM hMN hsn hxM).1 hxcm
  have hxbar_mem : ys03_qMap p M ⟨x, hxM⟩ ∈ barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) :=
    ⟨Subgroup.mem_map.2 ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxB, rfl⟩, hxC⟩
  have hcent : barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) ≠ ⊥ := by
    intro hbot
    apply hxbar_ne
    have hmem := hxbar_mem
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hMK : CFSG.Open.IsKGroup ↥M := openIsKGroup_sup_pGroup hp h.kgroup hBp hBN
  have hKgrp : CFSG.Open.IsKGroup (PQuot p M) :=
    hMK.of_surjective (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) (QuotientGroup.mk'_surjective _)
  have hKchev : IsChevSimple 2 (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) :=
    isChevSimple_of_mulEquiv_held
      (QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).symm h.chev
  obtain ⟨T, hTL, hT2, hTB, hTO⟩ := h.twogrp
  have hTM : T ≤ M := hTL.trans hLM
  have hT2' : IsPGroup 2 ↥(barX p M T) := by
    have hTp : IsPGroup 2 ↥(T.subgroupOf M) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
    exact hTp.of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hTne : barX p M T ≠ ⊥ := by
    intro hbot
    apply hTO
    intro t ht
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨t, hTM ht⟩ ∈ barX p M T :=
      Subgroup.mem_map.2 ⟨⟨t, hTM ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : t ∈ GLAPPrimeCoreOf p M := (ys03_mem_primeCoreOf_iff_qMap (hTM ht)).2 h1
    rwa [hOLM]
  have hTnorm : barX p M B ≤ Subgroup.normalizer ((barX p M T : Subgroup (PQuot p M)) :
      Set (PQuot p M)) := barX_le_normalizer (C := M) hTB
  refine ⟨PQuot p M, inferInstance, inferInstance, barX p M L, barX p M B, ?_, ?_, ?_⟩
  · exact
      { normal := hKn, qs := hKq, core := hKcore, chev := hKchev, kgroup := hKgrp, elem := hBab',
        sup := hsup, card := hpow, maxrank := hmaxY, cent := hcent,
        twogrp := ⟨barX p M T, barX_mono_held hTL, hT2', hTne, hTnorm⟩ }
  ·
    have : Nat.card (barX p M L) ≤ Nat.card (L.subgroupOf M) :=
      Nat.card_le_card_of_surjective _
        (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (GLAPPrimeCore p ↥M))
          (L.subgroupOf M))
    exact this.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv).le
  · rintro ⟨E'', hE''B, _hE''ab, hE''card, hE''layer⟩
    obtain ⟨E, hEB, hEq, -⟩ := exists_le_barX_eq hp hBp hBM hE''B
    have hEM : E ≤ M := hEB.trans hBM
    have hEp : IsPGroup p E := hBp.to_le hEB
    have hEcard : Nat.card E = p ^ 3 := by
      rw [← ys03_card_barX_of_isPGroup hp hEp hEM, hEq]
      exact hE''card
    have hcE := ys03_barX_inf_centralizer_eq hp hLM hEM hEp hOL
    rw [hEq] at hcE
    obtain ⟨J', hJ', hJ'ne⟩ := ys03_exists_component_ne_bot hE''layer
    rw [← hcE] at hJ'
    obtain ⟨K₂, hK₂, hK₂J⟩ := exists_glaPComponent_map_eq hp (ys03_qMap p M)
      (ys03_coprime_inf_ker_qMap hp ((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M)) hJ'
    have hkerM : Nat.Coprime p (Nat.card ↥((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M ⊓
        M.subtype.ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have hK₂G := glaPComponent_map hp M.subtype hkerM hK₂
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (inf_le_left.trans hLM)] at hK₂G
    have hK₂ne : K₂ ≠ ⊥ := by
      rintro rfl
      apply hJ'ne
      rw [← hK₂J, Subgroup.map_bot]
    have hK₂G_ne : K₂.map M.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
      exact hK₂ne
    unfold IsGB
    refine ⟨E, hEB, isElemAbelian_mono hBab hEB, hEcard, hEB.trans hBN, ?_⟩
    intro hbot
    have hle : K₂.map M.subtype ≤ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) :=
      le_sSup hK₂G
    rw [hbot] at hle
    exact hK₂G_ne (le_bot_iff.1 hle)

end Transfer

theorem i264bGenAt_of_K {p : ℕ} (h : KD264bK p) (G : Type) [Group G] [Finite G] : I264bGenAt G p := by
  intro hp hp2 B L hL
  obtain ⟨Y, _, _, K, B', hKH, -, hconcl⟩ := exists_kLevel_of_hyp hp hL
  exact hconcl (h hp hp2 Y K B' hKH)

theorem i264bAt_of_gen {G : Type} [Group G] [Finite G] {p : ℕ} (h : I264bGenAt G p) : I264bAt G p := by
  unfold I264bAt
  intro hp hp2 B x L hBab hxB hx1 hL hKG hBN hpB hmax hlev hT
  refine h hp hp2 B L ⟨hBab, isQuasisimple_pQuot_of_glaPComponent hp hL, hKG, hBN, hpB, hmax, ?_,
    hlev, hT⟩
  intro hbot
  have hxc : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hL.1 hl) x (Set.mem_singleton x)).symm
  have hmem : x ∈ B ⊓ centModSubgroup p L := ⟨hxB, centMod_iff.1 (centMod_of_mem_centralizer hxc)⟩
  rw [hbot] at hmem
  exact hx1 (Subgroup.mem_bot.1 hmem)

theorem i264bAt_of_K {G : Type} [Group G] [Finite G] {p : ℕ} (h : KD264bK p) : I264bAt G p :=
  i264bAt_of_gen (i264bGenAt_of_K h G)

end CFSG.LocalAnalysis.GLTheoremA
