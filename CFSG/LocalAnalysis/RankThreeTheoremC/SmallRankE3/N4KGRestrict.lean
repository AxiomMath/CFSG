module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4KGPre
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStrong
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.GH74.Uniqueness.SU

variable {G : Type} [Group G] [Finite G]

theorem n4_normalizer_subgroupOf {Gs X : Subgroup G} (hX : X ≤ Gs) :
    normalizer ((X.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) =
      (normalizer (X : Set G)).subgroupOf Gs := by
  ext n
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.coe_mul,
    Subgroup.coe_inv]
  constructor
  · intro h g
    constructor
    · intro hg
      exact (h ⟨g, hX hg⟩).1 hg
    · intro hng
      have h1 : (n : G) * g * (n : G)⁻¹ ∈ Gs := hX hng
      have h2 : g ∈ Gs := by
        have h3 := Gs.mul_mem (Gs.mul_mem (Gs.inv_mem n.2) h1) n.2
        have h4 : (n : G)⁻¹ * ((n : G) * g * (n : G)⁻¹) * (n : G) = g := by group
        rwa [h4] at h3
      exact (h ⟨g, h2⟩).2 hng
  · intro h h'
    exact h (h' : G)

theorem n4_isSimpleSection_subgroupOf {Gs L D : Subgroup G} (hL : L ≤ Gs)
    (h : S622IsSimpleSection L D) :
    S622IsSimpleSection (L.subgroupOf Gs) (D.subgroupOf Gs) := by
  obtain ⟨hDL, hDn, hne, hmin, hnab⟩ := h
  have hDn' := (Subgroup.normal_subgroupOf_iff hDL).1 hDn
  have hD'L' : D.subgroupOf Gs ≤ L.subgroupOf Gs := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hDL hx
  refine ⟨hD'L', ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.normal_subgroupOf_iff hD'L']
    intro x y hx hy
    have hx' : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    exact Subgroup.mem_subgroupOf.mpr (hDn' (x : G) (y : G) hx' hy')
  ·
    intro heq
    apply hne
    apply le_antisymm hDL
    intro l hl
    have hx : (⟨l, hL hl⟩ : Gs) ∈ L.subgroupOf Gs := Subgroup.mem_subgroupOf.mpr hl
    rw [← heq, Subgroup.mem_subgroupOf] at hx
    exact hx
  ·
    intro N' hN'1 hN'2 hN'n
    have hDN : D ≤ N'.map Gs.subtype := by
      intro d hd
      have hdGs : d ∈ Gs := hL (hDL hd)
      have hdD : (⟨d, hdGs⟩ : Gs) ∈ D.subgroupOf Gs := Subgroup.mem_subgroupOf.mpr hd
      exact ⟨⟨d, hdGs⟩, hN'1 hdD, rfl⟩
    have hNL : N'.map Gs.subtype ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hN'2 hx)
    have hNn : ((N'.map Gs.subtype).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hNL]
      intro u g hu hg
      obtain ⟨x, hx, rfl⟩ := hu
      have hg' : (⟨g, hL hg⟩ : Gs) ∈ L.subgroupOf Gs := Subgroup.mem_subgroupOf.mpr hg
      have hconj := (Subgroup.normal_subgroupOf_iff hN'2).1 hN'n x ⟨g, hL hg⟩ hx hg'
      exact ⟨⟨g, hL hg⟩ * x * ⟨g, hL hg⟩⁻¹, hconj, rfl⟩
    have hcm := Subgroup.comap_map_eq_self_of_injective Gs.subtype_injective N'
    rcases hmin (N'.map Gs.subtype) hDN hNL hNn with h' | h'
    · left
      have h2 : (N'.map Gs.subtype).comap Gs.subtype = D.comap Gs.subtype := by rw [h']
      exact hcm.symm.trans h2
    · right
      have h2 : (N'.map Gs.subtype).comap Gs.subtype = L.comap Gs.subtype := by rw [h']
      exact hcm.symm.trans h2
  ·
    intro hall
    apply hnab
    intro a ha b hb
    have key := hall ⟨a, hL ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hL hb⟩
      (Subgroup.mem_subgroupOf.mpr hb)
    rw [Subgroup.mem_subgroupOf] at key
    simpa using key

theorem n4_characteristic_map {Gs S : Subgroup G} (hS : S ≤ Gs) {S₀ : Subgroup ↥Gs}
    (hS₀ : S₀ ≤ S.subgroupOf Gs) (h : (S₀.subgroupOf (S.subgroupOf Gs)).Characteristic) :
    ((S₀.map Gs.subtype).subgroupOf S).Characteristic := by
  clear hS₀
  set e : ↥(S.subgroupOf Gs) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS
  have key : ∀ y : ↥S, y ∈ (S₀.map Gs.subtype).subgroupOf S ↔
      e.symm y ∈ S₀.subgroupOf (S.subgroupOf Gs) := by
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hx' : x = (e.symm y).1 := Subtype.ext hxy
      rw [← hx']
      exact hx
    · intro hz
      exact ⟨(e.symm y).1, hz, rfl⟩
  refine ⟨fun ϕ => ?_⟩
  ext y
  set ψ : ↥(S.subgroupOf Gs) ≃* ↥(S.subgroupOf Gs) := e.trans (ϕ.trans e.symm) with hψdef
  have hψ := h.fixed ψ
  have hmem : ∀ x : ↥(S.subgroupOf Gs), ψ x ∈ S₀.subgroupOf (S.subgroupOf Gs) ↔
      x ∈ S₀.subgroupOf (S.subgroupOf Gs) := by
    intro x
    have hx : x ∈ (S₀.subgroupOf (S.subgroupOf Gs)).comap ψ.toMonoidHom ↔
        x ∈ S₀.subgroupOf (S.subgroupOf Gs) := by
      rw [hψ]
    exact hx
  have hψy : ψ (e.symm y) = e.symm (ϕ y) := by
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, key (ϕ y), key y, ← hψy]
  exact hmem (e.symm y)

theorem n4_isElemAbelian_subgroupOf {p : ℕ} {Gs B : Subgroup G} (hB : B ≤ Gs)
    (h : IsElemAbelian p B) : IsElemAbelian p (B.subgroupOf Gs) := by
  obtain ⟨hc, hp⟩ := SU1.isElemAbelian_iff.mp h
  refine SU1.isElemAbelian_iff.mpr ⟨fun a ha b hb => Subtype.ext (hc _ ha _ hb), fun a ha => ?_⟩
  exact Subtype.ext (by simpa using hp _ ha)

variable {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem KGData3Pre.restrict (d : KGData3Pre p H D S B L M z) {Gs : Subgroup G} (hGH : Gs ≤ H)
    (hD : D ≤ Gs) (hS : S ≤ Gs) (hB : B ≤ Gs) (hL : L ≤ Gs) :
    KGC.KGData3 p (⊤ : Subgroup ↥Gs) (D.subgroupOf Gs) (S.subgroupOf Gs) (B.subgroupOf Gs)
      (L.subgroupOf Gs) (M.subgroupOf Gs) ⟨z, hB d.z_mem_B⟩ := by
  have hp := d.prime
  have hHD : (⊤ : Subgroup ↥Gs) ≤ normalizer ((D.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro g _
    rw [n4_normalizer_subgroupOf hD]
    exact d.H_le_D (hGH g.2)
  have hD2 : IsPGroup 2 (D.subgroupOf Gs) :=
    d.D_two.of_equiv (Subgroup.subgroupOfEquivOfLe hD).symm
  have hS2 : IsPGroup 2 (S.subgroupOf Gs) :=
    d.S_two.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hDS : D.subgroupOf Gs < S.subgroupOf Gs := by
    refine lt_of_le_of_ne (fun x hx => d.D_lt_S.le hx) ?_
    intro heq
    obtain ⟨s, hsS, hsD⟩ := SetLike.exists_of_lt d.D_lt_S
    have hs' : (⟨s, hS hsS⟩ : ↥Gs) ∈ S.subgroupOf Gs := hsS
    rw [← heq] at hs'
    exact hsD hs'
  have hBc : Nat.card (B.subgroupOf Gs) = p ^ 2 := by
    rw [← d.B_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have hBS : B.subgroupOf Gs ≤ normalizer ((S.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro b hb
    rw [n4_normalizer_subgroupOf hS]
    exact d.B_le_S hb
  have hmax : ∀ S' : Subgroup ↥Gs, S' ≤ (⊤ : Subgroup ↥Gs) → IsPGroup 2 S' →
      B.subgroupOf Gs ≤ normalizer (S' : Set ↥Gs) → S.subgroupOf Gs ≤ S' →
      S' = S.subgroupOf Gs := by
    intro S' _ hS'2 hBS' hSS'
    have h1 : S'.map Gs.subtype ≤ H := by
      rintro _ ⟨y, _, rfl⟩
      exact hGH y.2
    have h2 : IsPGroup 2 (S'.map Gs.subtype) :=
      hS'2.of_equiv (S'.equivMapOfInjective Gs.subtype Gs.subtype_injective)
    have h3 : B ≤ normalizer ((S'.map Gs.subtype : Subgroup G) : Set G) := by
      intro b hb
      exact KGC.mem_normalizer_map_subtype
        (hBS' (show (⟨b, hB hb⟩ : ↥Gs) ∈ B.subgroupOf Gs from hb))
    have h4 : S ≤ S'.map Gs.subtype := by
      intro s hs
      exact ⟨⟨s, hS hs⟩, hSS' hs, rfl⟩
    have h5 := d.max_S _ h1 h2 h3 h4
    ext x
    constructor
    · intro hx
      have : (x : G) ∈ S'.map Gs.subtype := ⟨x, hx, rfl⟩
      rw [h5] at this
      exact this
    · intro hx
      exact hSS' hx
  have hcover : ∀ S₀ : Subgroup ↥Gs, D.subgroupOf Gs < S₀ → S₀ ≤ S.subgroupOf Gs →
      S.subgroupOf Gs ⊔ B.subgroupOf Gs ≤ normalizer (S₀ : Set ↥Gs) →
      normalizer (S₀ : Set ↥Gs) ≤ M.subgroupOf Gs := by
    intro S₀ hDS₀ hS₀S hSB g hg
    have hS₀G : S₀.map Gs.subtype ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact hS₀S hy
    have hDS₀G : D < S₀.map Gs.subtype := by
      refine lt_of_le_of_ne (fun x hx => ⟨⟨x, hD hx⟩, hDS₀.le hx, rfl⟩) ?_
      intro heq
      obtain ⟨y, hyS₀, hyD⟩ := SetLike.exists_of_lt hDS₀
      have : (y : G) ∈ S₀.map Gs.subtype := ⟨y, hyS₀, rfl⟩
      rw [← heq] at this
      exact hyD this
    have hSBN : S ⊔ B ≤ normalizer ((S₀.map Gs.subtype : Subgroup G) : Set G) := by
      refine sup_le (fun s hs => ?_) (fun b hb => ?_)
      · exact KGC.mem_normalizer_map_subtype (hSB (Subgroup.mem_sup_left (show (⟨s, hS hs⟩ : ↥Gs) ∈
          S.subgroupOf Gs from hs)))
      · exact KGC.mem_normalizer_map_subtype (hSB (Subgroup.mem_sup_right (show (⟨b, hB hb⟩ : ↥Gs) ∈
          B.subgroupOf Gs from hb)))
    exact d.cover _ hDS₀G hS₀G hSBN (KGC.mem_normalizer_map_subtype hg)
  have hcoverZ : normalizer ((zpowers (⟨z, hB d.z_mem_B⟩ : ↥Gs) : Subgroup ↥Gs) : Set ↥Gs) ≤
      M.subgroupOf Gs := fun g hg =>
    d.cover_Z (KGC.mem_normalizer_zpowers_coe hg)
  have hLnot : ¬ L.subgroupOf Gs ≤ M.subgroupOf Gs := fun h =>
    d.L_not_le fun l hl => h (show (⟨l, hL hl⟩ : ↥Gs) ∈ L.subgroupOf Gs from hl)
  have hML : M.subgroupOf Gs ⊓ (⊤ : Subgroup ↥Gs) ≤
      normalizer ((L.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro g hg
    rw [n4_normalizer_subgroupOf hL]
    exact d.M_le_L ⟨hg.1, hGH g.2⟩
  have hLrank : Open.pRank p (L.subgroupOf Gs) ≤ 1 :=
    (pRank_subgroupOf hp.one_lt hL).le.trans d.L_rank
  have hcharTwo : (⊤ : Subgroup ↥Gs) ⊓ centralizer ((D.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) ≤
      D.subgroupOf Gs := by
    intro g hg
    refine d.charTwo ⟨hGH g.2, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := mem_centralizer_iff.mp hg.2 (⟨x, hD hx⟩ : ↥Gs) hx
    exact congrArg Subtype.val this
  have hrankH : Open.pRank p (⊤ : Subgroup ↥Gs) ≤ 2 := by
    rw [← Subgroup.subgroupOf_self (H := Gs), pRank_subgroupOf hp.one_lt le_rfl]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hGH).trans d.rank_H
  have hcatalog : ∀ X : Subgroup ↥Gs, X ≤ (⊤ : Subgroup ↥Gs) →
      CFSG.AGLEmbedding.CatalogSimpleSections ↥X := fun X _ =>
    (d.catalog Gs hGH).subgroup X
  have hchar : ∀ S₀ : Subgroup ↥Gs, S₀ ≤ S.subgroupOf Gs → S₀ ≠ ⊥ →
      (S₀.subgroupOf (S.subgroupOf Gs)).Characteristic →
      normalizer (S₀ : Set ↥Gs) ≤ M.subgroupOf Gs := by
    intro S₀ hS₀ hne hcharS g hg
    have hS₀G : S₀.map Gs.subtype ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact hS₀ hy
    have hne' : S₀.map Gs.subtype ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro y hy
      have : (y : G) ∈ S₀.map Gs.subtype := ⟨y, hy, rfl⟩
      rw [h] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    exact d.char_le _ hS₀G hne' (n4_characteristic_map hS hS₀ hcharS)
      (KGC.mem_normalizer_map_subtype hg)
  exact ⟨⟨hp, d.five_le, le_top, hHD, hD2, fun x hx => d.D_le_M hx, hDS, le_top,
    fun x hx => d.S_le_M hx, hS2, le_top, fun x hx => d.B_le_M hx,
    n4_isElemAbelian_subgroupOf hB d.B_elem, hBc, d.z_mem_B, by
      rw [Subgroup.orderOf_mk]
      exact d.z_order, hBS, hmax, hcover, hcoverZ, n4_isSimpleSection_subgroupOf hL d.L_sec,
    le_top, d.z_mem_L, hLrank, hLnot, hML⟩, hcharTwo, hrankH, hcatalog, hchar⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
