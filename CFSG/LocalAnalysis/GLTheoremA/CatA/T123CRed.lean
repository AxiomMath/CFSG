module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Bookkeeping

variable {G : Type} [Group G] {H : Subgroup G}

theorem map_subgroupOf_inf_cs {L D : Subgroup G} (hL : L ≤ H) (hD : D ≤ H) :
    ((L.subgroupOf H) ⊓ cs (D.subgroupOf H)).map H.subtype = L ⊓ cs D := by
  ext g
  constructor
  · rintro ⟨k, ⟨hkL, hkC⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.1 hkL, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro d hd
    have hdH : d ∈ H := hD hd
    have h1 := Subgroup.mem_centralizer_iff.1 hkC ⟨d, hdH⟩ (Subgroup.mem_subgroupOf.2 hd)
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rintro ⟨hgL, hgC⟩
    refine ⟨⟨g, hL hgL⟩, ⟨Subgroup.mem_subgroupOf.2 hgL, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro k hk
    have hkD : (k : G) ∈ D := Subgroup.mem_subgroupOf.1 hk
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hgC) k hkD

theorem map_subgroupOf_inf_cx {L : Subgroup G} (hL : L ≤ H) (w : H) :
    ((L.subgroupOf H) ⊓ cx w).map H.subtype = L ⊓ cx (w : G) := by
  ext g
  constructor
  · rintro ⟨k, ⟨hkL, hkC⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.1 hkL, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    rw [hd]
    have h1 := Subgroup.mem_centralizer_iff.1 hkC (w : H) (Set.mem_singleton _)
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rintro ⟨hgL, hgC⟩
    refine ⟨⟨g, hL hgL⟩, ⟨Subgroup.mem_subgroupOf.2 hgL, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hgC) (w : G) (Set.mem_singleton _)

theorem map_zpowers_subtype (y : H) : (Subgroup.zpowers y).map H.subtype = Subgroup.zpowers (y : G) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem map_closure_pair (x y : H) :
    (Subgroup.closure ({x, y} : Set H)).map H.subtype = Subgroup.closure ({(x : G), (y : G)} : Set G) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

end Bookkeeping

theorem compl123_of_facts {G : Type} [Group G] [Finite G] {m p : ℕ} (hctx : S12Ctx G m p) (hin : Inputs122 G p)
    (hpar : ParityFact) (hblk : BlockFact) (h167 : I167Univ) : Compl123At G p := by
  intro B x L D K D₁ K₁ KE L₁ y hstar hrank hsplit hstd hE3 hKE hT172 hstd₁ hS hN hKy hc122
  have h : Cfg12 G m p B x L D K := ⟨hctx, ⟨hstar, hsplit⟩, hstd⟩
  have h₁ : Cfg12 G m p B x L D₁ K₁ := ⟨hctx, ⟨hstar, hsplit⟩, hstd₁⟩
  have hnb : NbrCfg G m p B x L D₁ K₁ y L₁ := ⟨h₁, hS, hN⟩
  have hcom := hin.l121.common
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := h.odd
  have hyB : y ∈ B := hnb.yB
  have hy1 : y ≠ 1 := hnb.y_ne_one
  have hL₁ : GLAPComponent p (cx y) L₁ := hnb.J_comp
  have hxB : x ∈ B := h.tri.mem
  have hx1 : x ≠ 1 := h.tri.ne_one
  have hBel : IsElemAbelian p B := h.tri.bmax.1
  have hcardBL : Nat.card ↥(B ⊓ cs L₁) = p := S12.card_B_inf_cs hnb
  have hBL : B ⊓ cs L₁ = Subgroup.zpowers y := S12.B_inf_cs_eq hnb
  have hcl : D₁ = Subgroup.closure ({x, y} : Set G) := hnb.nb.1
  have hD₁ : D₁ = B ⊓ cs K₁ := h₁.D_eq
  have hLnorm : B ≤ Subgroup.normalizer (L₁ : Set G) := hc122.norm
  have hK₁L₁ : K₁ ≤ L₁ := hKy.1.trans inf_le_left
  have hDB : D ≤ B := h.DB
  have hD₁B : D₁ ≤ B := h₁.DB
  set H : Subgroup G := L₁ ⊔ B with hH
  have hL₁H : L₁ ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hxH : x ∈ H := hBH hxB
  have hyH : y ∈ H := hBH hyB
  have hDH : D ≤ H := hDB.trans hBH
  have hD₁H : D₁ ≤ H := hD₁B.trans hBH
  have hK₁H : K₁ ≤ H := hK₁L₁.trans hL₁H
  have hHle : H ≤ Subgroup.normalizer (L₁ : Set G) := sup_le (fun g hg => Subgroup.le_normalizer hg) hLnorm
  have hι : Function.Injective H.subtype := Subgroup.subtype_injective H
  have hrankH : GLATwoLocalRank p ↥H ≤ CFSG.Open.pRank p B := S12.twoRank_L₁B_le hnb
  set S' : Subgroup H := L₁.subgroupOf H with hS'
  set B' : Subgroup H := B.subgroupOf H with hB'
  set K₁' : Subgroup H := K₁.subgroupOf H with hK₁'
  set D' : Subgroup H := D.subgroupOf H with hD'
  set D₁' : Subgroup H := D₁.subgroupOf H with hD₁'
  have hS'map : S'.map H.subtype = L₁ := Subgroup.map_subgroupOf_eq_of_le hL₁H
  have hB'map : B'.map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  have hK₁'map : K₁'.map H.subtype = K₁ := Subgroup.map_subgroupOf_eq_of_le hK₁H
  have hD'map : D'.map H.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDH
  have hD₁'map : D₁'.map H.subtype = D₁ := Subgroup.map_subgroupOf_eq_of_le hD₁H
  let x' : H := ⟨x, hxH⟩
  let y' : H := ⟨y, hyH⟩
  have hx'B' : x' ∈ B' := Subgroup.mem_subgroupOf.2 hxB
  have hy'B' : y' ∈ B' := Subgroup.mem_subgroupOf.2 hyB
  have hx'1 : x' ≠ 1 := fun e => hx1 (congrArg Subtype.val e)
  have hx'D' : x' ∈ D' := Subgroup.mem_subgroupOf.2 h.xD
  have hS'norm : S'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁H).2 hHle
  have hB'norm : B' ≤ Subgroup.normalizer (S' : Set H) := by
    intro b hb
    have hbL : (b : G) ∈ Subgroup.normalizer (L₁ : Set G) := hLnorm (Subgroup.mem_subgroupOf.1 hb)
    rw [Subgroup.mem_normalizer_iff] at hbL ⊢
    intro s
    have := hbL s.1
    simpa [hS', Subgroup.mem_subgroupOf] using this
  have E1 : (S' ⊓ cs D').map H.subtype = L₁ ⊓ cs D := by
    rw [hS', hD']; exact map_subgroupOf_inf_cs hL₁H hDH
  have E2 : ∀ w : H, (S' ⊓ cx w).map H.subtype = L₁ ⊓ cx (w : G) := fun w => by
    rw [hS']; exact map_subgroupOf_inf_cx hL₁H w
  have E3 : (B' ⊓ cs S').map H.subtype = B ⊓ cs L₁ := by
    rw [hB', hS']; exact map_subgroupOf_inf_cs hBH hL₁H
  have E4 : (B' ⊓ cs K₁').map H.subtype = B ⊓ cs K₁ := by
    rw [hB', hK₁']; exact map_subgroupOf_inf_cs hBH hK₁H
  have hzy : (Subgroup.zpowers y').map H.subtype = Subgroup.zpowers y := map_zpowers_subtype y'
  have hmapx : (Subgroup.zpowers x').map H.subtype = Subgroup.zpowers x := map_zpowers_subtype x'
  have hcl2 : (Subgroup.closure ({x', y'} : Set H)).map H.subtype = D₁ := by
    rw [map_closure_pair]; exact hcl.symm
  have hcs' : B' ⊓ cs S' = Subgroup.zpowers y' := by
    apply Subgroup.map_injective hι
    rw [E3, hzy, hBL]
  have hcard' : Nat.card (Subgroup.zpowers y') = p := by
    have e1 : Nat.card ↥((Subgroup.zpowers y').map H.subtype) = Nat.card ↥(Subgroup.zpowers y') :=
      Subgroup.card_map_of_injective hι
    rw [← e1, hzy, ← hBL]
    exact hcardBL
  have hD₁'' : B' ⊓ cs K₁' = D₁' := by
    apply Subgroup.map_injective hι
    rw [E4, hD₁'map, hD₁]
  have hcl' : Subgroup.closure ({x', y'} : Set H) = D₁' := by
    apply Subgroup.map_injective hι
    rw [hcl2, hD₁'map]
  have hcl'' : Subgroup.closure ({x', y'} : Set H) = B' ⊓ cs K₁' := hcl'.trans hD₁''.symm
  have hS'qs : CFSG.Open.IsQuasisimple ↥S' :=
    (isQuasisimple_map_iff hι S').1 (by rw [hS'map]; exact hc122.qs)
  have hS'chev : IsChevSimple 2 (PSimple p S') :=
    (isChevSimple_pSimple_map_iff hι 2 p S').1 (by rw [hS'map]; exact hc122.chev2)
  have hK₁'comp : GLAPComponent p (S' ⊓ cx x') K₁' := by
    refine (glaPComponent_map_iff hι p (S' ⊓ cx x') K₁').1 ?_
    rw [E2 x', hK₁'map]; exact hKy
  have hK₁'type : Type167J p K₁' :=
    (type167J_map_iff hι p K₁').1 (by rw [hK₁'map]; exact type167J_of_type172 hT172)
  have hB'el : IsElemAbelian p B' := hBel.subgroupOf H
  have hrank' : GLATwoLocalRank p ↥H ≤ CFSG.Open.pRank p B' := by
    have e := pRank_map_eq hι p B'
    rw [hB'map] at e
    rw [← e]
    exact hrankH
  have hSC' := hpar p H S' B' K₁' x' y' hp hp2 hS'norm hS'qs hS'chev hK₁'comp hK₁'type hB'el hB'norm
    hx'B' hx'1 hy'B' hcs' hcard' hcl'' hrank'
  have hSC_G : ∀ g ∈ L₁ ⊔ B, g ∈ Subgroup.centralizer (B : Set G) → orderOf g = p → g ∈ B := by
    intro g hgH hgC hord
    let g' : H := ⟨g, hgH⟩
    have hg'C : g' ∈ Subgroup.centralizer (B' : Set H) := Subgroup.mem_centralizer_iff.2 (fun b hb => by
      have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hgC) b hbB)
    have hord' : orderOf g' = p := (Subgroup.orderOf_coe g').symm.trans hord
    exact Subgroup.mem_subgroupOf.1 (hSC' g' hg'C hord')
  have hTypeL₁ : Type167 p L₁ K₁ :=
    h167 G p B L₁ D₁ K₁ hp hp2 hBel hc122.qs hc122.chev2 hc122.norm (S12.twoRank_L₁B_le hnb)
      (fun g hgX hg hord => hSC_G g hgX hg hord) (S12.card_B_inf_cs hnb) ⟨h₁.DB, h₁.elem, h₁.card_D⟩
      (S12.pcomp_cs_D₁ hnb hKy) h₁.D_eq (type167J_of_type172 hT172) (by
        rcases hc122.half.halfSplit16At_or_field with hh | hf
        · exact Or.inl hh
        · exact Or.inr ⟨x, h₁.xD, hf⟩)
  have hType' : Type167 p S' K₁' :=
    (type167_map_iff hι p S' K₁').1 (by rw [hS'map, hK₁'map]; exact hTypeL₁)
  have hD'B' : D' ≤ B' := fun d hd => Subgroup.mem_subgroupOf.2 (hDB (Subgroup.mem_subgroupOf.1 hd))
  have hD₁'B' : D₁' ≤ B' := fun d hd => Subgroup.mem_subgroupOf.2 (hD₁B (Subgroup.mem_subgroupOf.1 hd))
  have hcardsub : ∀ {E : Subgroup G}, E ≤ H → Nat.card (E.subgroupOf H) = Nat.card E := by
    intro E hE
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le hE]
    exact (Subgroup.card_map_of_injective hι).symm
  have hD'E2 : IsE2 p B' D' :=
    ⟨hD'B', h.elem.subgroupOf H, by rw [hcardsub hDH]; exact h.card_D⟩
  have hE3sub : (D ⊔ D₁).subgroupOf H = D' ⊔ D₁' := Subgroup.subgroupOf_sup hDH hD₁H
  have hE3' : IsE3 p B' (D' ⊔ D₁') := by
    refine ⟨sup_le hD'B' hD₁'B', ?_, ?_⟩
    · rw [← hE3sub]; exact hE3.2.1.subgroupOf H
    · rw [← hE3sub, hcardsub (sup_le hDH hD₁H)]; exact hE3.2.2
  obtain ⟨Pg, hPg⟩ := exists_pComponent_L₁_cs_D h h₁ hcom hKE hT172 hKy
  have hPgH : Pg ≤ H := (hPg.1.trans inf_le_left).trans hL₁H
  have hlayer' : GLAPLayer p (S' ⊓ cs D') ≠ ⊥ := by
    have hPg' : GLAPComponent p (S' ⊓ cs D') (Pg.subgroupOf H) := by
      refine (glaPComponent_map_iff hι p (S' ⊓ cs D') (Pg.subgroupOf H)).1 ?_
      rw [E1, Subgroup.map_subgroupOf_eq_of_le hPgH]
      exact hPg
    intro h0
    exact glaPComponent_ne_bot' hPg' (le_bot_iff.1 (h0 ▸ le_sSup hPg'))
  obtain ⟨w, hwD', hwx', P', M', hP', hM', hPM', hnc'⟩ :=
    hblk p H S' B' K₁' D₁' D' x' y' hp hp2 hS'norm hS'qs hType' hK₁'comp hB'el hB'norm hSC' hx'B' hx'1
      hy'B' hcs' hcard' hcl' hD₁'' hD'E2 hx'D' hE3' hlayer'
  have hwG : w.val ∈ D := Subgroup.mem_subgroupOf.1 hwD'
  have hwx : w.val ∉ Subgroup.zpowers x := by
    intro hm
    apply hwx'
    have hmem : w.val ∈ (Subgroup.zpowers x').map H.subtype := by rw [hmapx]; exact hm
    obtain ⟨z, hz, hzw⟩ := Subgroup.mem_map.1 hmem
    have hzw' : z = w := Subtype.ext hzw
    exact hzw' ▸ hz
  have hPG : GLAPComponent p (L₁ ⊓ cs D) (P'.map H.subtype) := by
    have := (glaPComponent_map_iff hι p (S' ⊓ cs D') P').2 hP'
    rw [E1] at this; exact this
  have hMG : GLAPComponent p (L₁ ⊓ cx (w : G)) (M'.map H.subtype) := by
    have := (glaPComponent_map_iff hι p (S' ⊓ cx w) M').2 hM'
    rw [E2 w] at this; exact this
  have hPMG : P'.map H.subtype ≤ M'.map H.subtype := Subgroup.map_mono hPM'
  have hncG : ¬ CentMod p (M'.map H.subtype) x := fun hc => hnc' ((centMod_map_iff hι p M' x').1 hc)
  have hPK : P'.map H.subtype ≤ K := S12.anchor_le_K h hcom hyB hL₁ hPG
  exact ⟨w.val, hwG, hwx, S12.not_centMod_of_layer h hcom hyB hy1 hwG hwx hL₁ hc122.qs hc122.norm hMG hPG hPK
    hPMG hncG⟩

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
