module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] {H : Subgroup G}

theorem map_inf_centralizer_subtype (X D : Subgroup ↥H) :
    (X ⊓ Subgroup.centralizer (D : Set ↥H)).map H.subtype =
      X.map H.subtype ⊓ Subgroup.centralizer ((D.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, Y10F.map_centralizer_subtype]
  refine le_antisymm (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (le_inf (inf_le_left.trans (Y10F.map_subtype_le X)) inf_le_right))

theorem glaStdSubPre_map_iff {p : ℕ} {B' L' D' K' : Subgroup ↥H} {x' : ↥H} :
    GLAStdSubPre p (B'.map H.subtype) (x' : G) (L'.map H.subtype) (D'.map H.subtype)
        (K'.map H.subtype) ↔ GLAStdSubPre p B' x' L' D' K' := by
  have hι : Function.Injective H.subtype := H.subtype_injective
  unfold GLAStdSubPre
  have e1 : D'.map H.subtype ≤ B'.map H.subtype ↔ D' ≤ B' :=
    Subgroup.map_le_map_iff_of_injective hι
  have e2 := Y10F.isElemAbelian_map_subtype_iff (p := p) D'
  have e3 : Nat.card (D'.map H.subtype) = p ^ 2 ↔ Nat.card D' = p ^ 2 := by
    rw [Y10F.card_map_subtype]
  have e4 : (x' : G) ∈ D'.map H.subtype ↔ x' ∈ D' := Subgroup.mem_map_iff_mem hι
  have hL : (L' ⊓ Subgroup.centralizer (D' : Set ↥H)).map H.subtype =
      L'.map H.subtype ⊓ Subgroup.centralizer ((D'.map H.subtype : Subgroup G) : Set G) :=
    map_inf_centralizer_subtype L' D'
  have e5 : K'.map H.subtype = GLALayer (L'.map H.subtype ⊓
        Subgroup.centralizer ((D'.map H.subtype : Subgroup G) : Set G)) ↔
      K' = GLALayer (L' ⊓ Subgroup.centralizer (D' : Set ↥H)) := by
    rw [← hL, Y10F.glaLayer_map hι]
    exact ⟨fun h => Subgroup.map_injective hι h, fun h => by rw [h]⟩
  have e6 : IsComponentOf (K'.map H.subtype) (L'.map H.subtype ⊓
        Subgroup.centralizer ((D'.map H.subtype : Subgroup G) : Set G)) ↔
      IsComponentOf K' (L' ⊓ Subgroup.centralizer (D' : Set ↥H)) := by
    rw [← hL]
    exact Y10F.isComponentOf_map_iff hι
  have hB : (B' ⊓ Subgroup.centralizer (K' : Set ↥H)).map H.subtype =
      B'.map H.subtype ⊓ Subgroup.centralizer ((K'.map H.subtype : Subgroup G) : Set G) :=
    map_inf_centralizer_subtype B' K'
  have e7 : D'.map H.subtype = B'.map H.subtype ⊓
        Subgroup.centralizer ((K'.map H.subtype : Subgroup G) : Set G) ↔
      D' = B' ⊓ Subgroup.centralizer (K' : Set ↥H) := by
    rw [← hB]
    exact ⟨fun h => Subgroup.map_injective hι h, fun h => by rw [h]⟩
  rw [e1, e2, e3, e4, e5, e6, e7]

theorem isE3_map_iff {p : ℕ} {B' E' : Subgroup ↥H} :
    IsE3 p (B'.map H.subtype) (E'.map H.subtype) ↔ IsE3 p B' E' := by
  unfold IsE3
  rw [Subgroup.map_le_map_iff_of_injective H.subtype_injective, Y10F.isElemAbelian_map_subtype_iff,
    Y10F.card_map_subtype]


theorem catalogIs_pSimple_map_iff [Finite G] {p : ℕ} (J' : Subgroup ↥H) (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple p (J'.map H.subtype)) Q ↔ catalogIs (PSimple p J') Q := by
  have hle : J'.map H.subtype ≤ H := Y10F.map_subtype_le J'
  obtain ⟨e⟩ := nonempty_pQuot_equiv_subgroupOf p hle
  rw [Y10F.map_subtype_subgroupOf] at e
  exact (catalogIs_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))).symm

theorem innerDiagMarking_subgroupOf {B L : Subgroup G} (hBH : B ≤ H) (hLH : L ≤ H)
    (h : InnerDiagMarking B L) : InnerDiagMarking (B.subgroupOf H) (L.subgroupOf H) := by
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  refine Y10F.glaMarking_congr e (P' := fun _ _ _ I _ θ =>
      B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hN, hb⟩ := hθ
  refine ⟨?_, ?_⟩
  · refine Y10F.le_normalizer_of_map_le ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hLH]
    exact hN
  · intro b' hb'
    have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    obtain ⟨φ, hφ, hind⟩ := hb (b' : G) hbB
    refine ⟨φ, hφ, ?_⟩
    intro l l' hll
    have hel : ∀ z : ↥(L.subgroupOf H), ((e z : ↥L) : G) = ((z : ↥H) : G) := fun z => rfl
    have hrel : ((e l' : ↥L) : G) = (b' : G)⁻¹ * ((e l : ↥L) : G) * (b' : G) := by
      rw [hel, hel]
      have := congrArg (fun z : ↥H => (z : G)) hll
      simpa using this
    have := hind (e l) (e l') hrel
    simpa [CFSG.StandardType.centerQuotCongr_mk] using this


theorem cent_eq_zpowers {p : ℕ} [Finite G] {B L : Subgroup G} {x : G} (hp : p.Prime)
    (hS : IsSStarMax p B x L) :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) ↔ b ∈ Subgroup.zpowers x := by
  have hxB : x ∈ B := (IsSStarMax.essential hS).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hS).2.1
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax hS).1
  have hxc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 ((IsSStarMax.component hS).1 hl)
  intro b hb
  constructor
  · intro hbc
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer (L : Set G) :=
      sup_le (Subgroup.zpowers_le.2 hxc) (Subgroup.zpowers_le.2 hbc)
    have hSB : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ B :=
      sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hb)
    have hSel : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers b) := isElemAbelian_mono hBel hSB
    have hcyc := IsSStarMax.cycMod hS _ (fun g hg => centMod_of_mem_centralizer (hle hg))
      (isPGroup_of_isElemAbelian hSel)
    have hcard := card_le_of_isCyclic_of_pow hp hcyc (fun d hd => hBel.2 d (hSB hd))
    exact mem_zpowers_of_card_sup_le hp (hBel.2 x hxB) hx1 hcard
  · intro hbx
    exact (Subgroup.zpowers_le.2 hxc) hbx

theorem mem_centralizer_subgroupOf_iff {L : Subgroup G} (hLH : L ≤ H) (b' : ↥H) :
    b' ∈ Subgroup.centralizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (b' : G) ∈ Subgroup.centralizer (L : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h l hl
    exact congrArg Subtype.val (h ⟨l, hLH hl⟩ hl)
  · intro h l hl
    exact Subtype.ext (h (l : G) hl)

theorem mem_zpowers_subtype_iff (x' b' : ↥H) :
    b' ∈ Subgroup.zpowers x' ↔ (b' : G) ∈ Subgroup.zpowers (x' : G) := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem e3_to_subgroupOf {p : ℕ} [Finite G] (hp : p.Prime) {B D K : Subgroup G} (hBH : B ≤ H)
    (hKH : K ≤ H)
    (h : ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (K ⊓ cs E) ≠ ⊥) :
    ∃ E' : Subgroup ↥H, IsE3 p (B.subgroupOf H) E' ∧ D.subgroupOf H ≤ E' ∧
      GLAPLayer p (K.subgroupOf H ⊓ cs E') ≠ ⊥ := by
  obtain ⟨E, hE3, hDE, hLay⟩ := h
  have hEH : E ≤ H := hE3.1.trans hBH
  refine ⟨E.subgroupOf H, ?_, fun d hd => hDE hd, fun hbot => hLay ?_⟩
  · refine isE3_map_iff.1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hEH]
    exact hE3
  · have h1 := Y10F.glaPLayer_map hp H.subtype_injective (K.subgroupOf H ⊓ cs (E.subgroupOf H))
    rw [map_inf_centralizer_subtype, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hEH, hbot, Subgroup.map_bot] at h1
    exact h1


theorem cfg172_of_field [Finite G] {p : ℕ} {B L D K : Subgroup G} {x : G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsSStarMax p B x L) (h4 : p ^ 4 ≤ Nat.card B) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hid : InnerDiagMarking B L) (hstd : GLAStdSubPre p B x L D K)
    (he3 : ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (K ⊓ cs E) ≠ ⊥)
    (hH : L ⊔ B = H) (x' : ↥H) (hx' : (x' : G) = x) :
    Cfg172 p (L.subgroupOf H) (B.subgroupOf H) (D.subgroupOf H) (K.subgroupOf H) x' := by
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hH ▸ le_sup_right
  have hDB : D ≤ B := hstd.1
  have hDH : D ≤ H := hDB.trans hBH
  have hKL : K ≤ L := by
    rw [hstd.2.2.2.2.1]
    exact (Y10F.glaLayer_le _).trans inf_le_left
  have hKH : K ≤ H := hKL.trans hLH
  have hxB : x ∈ B := (IsSStarMax.essential hS).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hS).2.1
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    hH ▸ sup_le Subgroup.le_normalizer (IsSStarMax.normalizes hS)
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax hS).1
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := (IsSStarMax.bmax hS).2.1
  haveI : Fact p.Prime := ⟨hp⟩
  refine
    { prime := hp
      odd := hp2
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
      qs := CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH) hq
      elem := (Y10F.isElemAbelian_subgroupOf_iff hBH).2 hBel
      top := ?_
      rank := ?_
      four := by rw [Y10F.card_subgroupOf hBH]; exact h4
      mem := Subgroup.mem_subgroupOf.2 (by rw [hx']; exact hxB)
      ne_one := fun h => hx1 (by rw [← hx', h]; rfl)
      cent := ?_
      idiag := innerDiagMarking_subgroupOf hBH hLH hid
      std := ?_
      e3 := ?_ }
  · have h1 : (L.subgroupOf H ⊔ B.subgroupOf H).map H.subtype = H := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_subgroupOf_eq_of_le hBH, hH]
    apply Subgroup.map_injective H.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  · rw [Y10F.card_subgroupOf hBH, hBcard]
    exact pow_le_pow_right₀ hp.one_lt.le (S11.twoLocalRank_le_top hp H)
  · intro b' hb'
    rw [mem_centralizer_subgroupOf_iff hLH, mem_zpowers_subtype_iff, hx']
    exact cent_eq_zpowers hp hS (b' : G) (Subgroup.mem_subgroupOf.1 hb')
  · have : GLAStdSubPre p ((B.subgroupOf H).map H.subtype) (x' : G) ((L.subgroupOf H).map H.subtype)
        ((D.subgroupOf H).map H.subtype) ((K.subgroupOf H).map H.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hLH,
        Subgroup.map_subgroupOf_eq_of_le hDH, Subgroup.map_subgroupOf_eq_of_le hKH, hx']
      exact hstd
    exact glaStdSubPre_map_iff.1 this
  · exact e3_to_subgroupOf hp hBH hKH he3


theorem catalogIs_pSimple_subgroupOf_iff [Finite G] {p : ℕ} {K : Subgroup G} (hKH : K ≤ H)
    (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple p (K.subgroupOf H)) Q ↔ catalogIs (PSimple p K) Q := by
  obtain ⟨e⟩ := nonempty_pQuot_equiv_subgroupOf p hKH
  exact catalogIs_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem lift_conclusion [Finite G] {p : ℕ} {B L D : Subgroup G} {x : G} (hBH : B ≤ H) (hLH : L ≤ H)
    (hDH : D ≤ H) (x' : ↥H) (hx' : (x' : G) = x) (D₁' K₁' : Subgroup ↥H)
    (hpre : GLAStdSubPre p (B.subgroupOf H) x' (L.subgroupOf H) D₁' K₁') :
    GLAStdSubPre p B x L (D₁'.map H.subtype) (K₁'.map H.subtype) ∧
      GLALayer (L ⊓ cs (D ⊔ D₁'.map H.subtype)) =
        (GLALayer (L.subgroupOf H ⊓ cs (D.subgroupOf H ⊔ D₁'))).map H.subtype := by
  have hDsup : (D.subgroupOf H ⊔ D₁').map H.subtype = D ⊔ D₁'.map H.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDH]
  refine ⟨?_, ?_⟩
  · have h := glaStdSubPre_map_iff.2 hpre
    rwa [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hLH, hx'] at h
  · rw [← Y10F.glaLayer_map H.subtype_injective, map_inf_centralizer_subtype,
      Subgroup.map_subgroupOf_eq_of_le hLH, hDsup]

theorem isE3_sup_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {B D D₁ : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hDB : D ≤ B) (hD₁B : D₁ ≤ B) (hD : Nat.card D = p ^ 2)
    (hD₁ : Nat.card D₁ = p ^ 2) (hxD : x ∈ D) (hxD₁ : x ∈ D₁) (hx1 : x ≠ 1) (hne : D ≠ D₁) :
    IsE3 p B (D ⊔ D₁) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsup : D ⊔ D₁ ≤ B := sup_le hDB hD₁B
  refine ⟨hsup, isElemAbelian_mono hB hsup, ?_⟩
  have hN : D₁ ≤ Subgroup.normalizer (D : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh =>
      isElemAbelian_commute hB (hDB hh) (hD₁B hd))
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  have hxp : orderOf x = p := orderOf_eq_prime (hB.2 x (hDB hxD)) hx1
  have hz : Subgroup.zpowers x ≤ D ⊓ D₁ := Subgroup.zpowers_le.2 ⟨hxD, hxD₁⟩
  have hpdvd : p ∣ Nat.card ↥(D ⊓ D₁) := by
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, hxp] at this
  have hdvd : Nat.card ↥(D ⊓ D₁) ∣ p ^ 2 := hD ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hi1 : i = 1 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [hi] at hpdvd
      simp at hpdvd
      exact absurd hpdvd hp.ne_one
    · rfl
    · exfalso
      apply hne
      have hM : D ⊓ D₁ = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hD, hi])
      have hM1 : D ⊓ D₁ = D₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hD₁, hi])
      rw [← hM, hM1]
  rw [hi1, pow_one] at hi
  rw [hi, hD, hD₁] at h1
  have hp0 : 0 < p := hp.pos
  have : Nat.card ↥(D ⊔ D₁) * p = p ^ 3 * p := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hp0 this

end CFSG.LocalAnalysis.GLTheoremA.S172

end
