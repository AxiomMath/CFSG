module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MainFact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Trans
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section MainTransport

variable {G : Type} [Group G] [Finite G]

theorem main_map_top (X : Subgroup G) : (⊤ : Subgroup X).map X.subtype = X := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem main_map_inf_cent {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X) :
    (L.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x, hx⟩ : X)} : Set X)).map X.subtype =
      L ⊓ Subgroup.centralizer ({x} : Set G) := by
  have hC : (Subgroup.centralizer ({(⟨x, hx⟩ : X)} : Set X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({x} : Set G) :=
    Y10F.map_centralizer_singleton_subtype ⟨x, hx⟩
  rw [Subgroup.map_inf _ _ _ X.subtype_injective, Y10F.subgroupOf_map_subtype_of_le hLX, hC]
  ext g
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hLX h.1, h.2⟩⟩

theorem main_subgroupOf_inf_cent {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X) :
    (L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf X =
      L.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x, hx⟩ : X)} : Set X) := by
  have hLC : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ X := inf_le_left.trans hLX
  apply Subgroup.map_injective X.subtype_injective
  rw [main_map_inf_cent hLX hx, Y10F.subgroupOf_map_subtype_of_le hLC]

theorem main_subgroupOf_zpowers {X : Subgroup G} {x : G} (hx : x ∈ X) :
    (Subgroup.zpowers x).subgroupOf X = Subgroup.zpowers (⟨x, hx⟩ : X) := by
  have h : (Subgroup.zpowers (⟨x, hx⟩ : X)).map X.subtype = Subgroup.zpowers x :=
    (MonoidHom.map_zpowers X.subtype _).trans rfl
  rw [← h, Y10F.map_subtype_subgroupOf]

theorem main_nonInnDiag_subgroupOf {p : ℕ} {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X)
    (h : NonInnDiag p x L) : NonInnDiag p (⟨x, hx⟩ : X) (L.subgroupOf X) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy := Subgroup.mem_normalizer_iff.1 h.1 (y : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hy
  · intro hin
    apply h.2
    have hin' : InnDiagOn p ((Subgroup.zpowers x).subgroupOf X) (L.subgroupOf X) := by
      rw [main_subgroupOf_zpowers hx]
      exact hin
    exact (T171.innDiagOn_subgroupOf_iff X (Subgroup.zpowers_le.2 hx) hLX).1 hin'

theorem main_fieldOn_subgroupOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X)
    (hxn : x ∈ Subgroup.normalizer (L : Set G)) (hF : FieldOn p x L) :
    FieldOn p (⟨x, hx⟩ : X) (L.subgroupOf X) := by
  have hz : (⟨x, hx⟩ : X) ∈ Subgroup.normalizer ((L.subgroupOf X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy := Subgroup.mem_normalizer_iff.1 hxn (y : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hy
  set e := T156.pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX) with he
  refine T156.fieldOn_to_Omega e.symm hz (fun q q' => ?_) hF
  have := T156.indRel_pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX) hz (e.symm q) (e.symm q')
  rw [← he] at this
  simpa using this

theorem main_card2_subgroupOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hLX : L ≤ X) :
    card2 p (L.subgroupOf X) = card2 p L := by
  unfold card2
  rw [Nat.card_congr (T156.pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX)).toEquiv]

theorem main_centCard2_subgroupOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X)
    (hxn : x ∈ Subgroup.normalizer (L : Set G)) :
    centCard2 p (L.subgroupOf X) (⟨x, hx⟩ : X) = centCard2 p L x := by
  have hz : (⟨x, hx⟩ : X) ∈ Subgroup.normalizer ((L.subgroupOf X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy := Subgroup.mem_normalizer_iff.1 hxn (y : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hy
  unfold centCard2
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquiv (T156.pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX)).toEquiv
    (fun q => (T156.indRel_pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX) hz q q).symm))

theorem main_fgOn_subgroupOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X)
    (h : FGOn p x L) : FGOn p (⟨x, hx⟩ : X) (L.subgroupOf X) := by
  rcases h with hF | ⟨h1, h2, h3⟩
  · exact Or.inl (main_fieldOn_subgroupOf hp hLX hx hF.1 hF)
  · refine Or.inr ⟨main_nonInnDiag_subgroupOf hLX hx h1, ?_, ?_⟩
    · rintro ⟨hp3, hT⟩
      exact h2 ⟨hp3, (T156.isTD4_congr hp3 (T156.pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLX))).1 hT⟩
    · rw [main_centCard2_subgroupOf hp hLX hx h1.1, main_card2_subgroupOf hp hLX]
      exact h3

theorem main_mem_centMod_subgroupOf {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X) (y : X) :
    y ∈ centModSubgroup p (K.subgroupOf X) ↔ (y : G) ∈ centModSubgroup p K := by
  rw [← centMod_iff, ← centMod_iff]
  have h := T123C.centMod_map_iff X.subtype_injective p (K.subgroupOf X) y
  rw [Y10F.subgroupOf_map_subtype_of_le hKX] at h
  exact h.symm

theorem main_map_inf_centModSubgroup {p : ℕ} {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) :
    (B.subgroupOf X ⊓ centModSubgroup p (K.subgroupOf X)).map X.subtype = B ⊓ centModSubgroup p K := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_inf] at hy
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hy.1, (main_mem_centMod_subgroupOf hKX y).1 hy.2⟩
  · intro hg
    rw [Subgroup.mem_inf] at hg
    exact ⟨⟨g, hBX hg.1⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hg.1,
      (main_mem_centMod_subgroupOf hKX ⟨g, hBX hg.1⟩).2 hg.2⟩, rfl⟩

theorem main_card_inf_centModSubgroup {p : ℕ} {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) :
    Nat.card ↥(B.subgroupOf X ⊓ centModSubgroup p (K.subgroupOf X)) =
      Nat.card ↥(B ⊓ centModSubgroup p K) := by
  rw [← main_map_inf_centModSubgroup hKX hBX]
  exact (Y10F.card_map_subtype _).symm

theorem main_disj_transport {k : ℕ} {Q1 Q2 Q3 : TauCeti.CFSGIndex → Prop} {X K L₁ B : Subgroup G} {x₂ : G}
    (hKX : K ≤ X) (hL₁X : L₁ ≤ X) (hBX : B ≤ X) (hx₂ : x₂ ∈ X)
    (h : catalogIs (PSimple 3 (K.subgroupOf X)) Q1 ∧ catalogIs (PSimple 3 (L₁.subgroupOf X)) Q2 ∧
      (∃ M : Subgroup X, GLAPComponent 3 (L₁.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x₂, hx₂⟩ : X)} : Set X)) M ∧
        catalogIs (PSimple 3 M) Q3) ∧
      Nat.card ↥(B.subgroupOf X) = 3 ^ k * Nat.card ↥(B.subgroupOf X ⊓ centModSubgroup 3 (K.subgroupOf X))) :
    catalogIs (PSimple 3 K) Q1 ∧ catalogIs (PSimple 3 L₁) Q2 ∧
      (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
        catalogIs (PSimple 3 M) Q3) ∧
      Nat.card ↥B = 3 ^ k * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
  obtain ⟨h1, h2, ⟨M', hM', hM'c⟩, hcard⟩ := h
  refine ⟨?_, ?_, ⟨M'.map X.subtype, ?_, ?_⟩, ?_⟩
  · have h1' := (T123C.catalogIs_pSimple_map_iff X.subtype_injective 3 (K.subgroupOf X) Q1).2 h1
    rwa [Y10F.subgroupOf_map_subtype_of_le hKX] at h1'
  · have h2' := (T123C.catalogIs_pSimple_map_iff X.subtype_injective 3 (L₁.subgroupOf X) Q2).2 h2
    rwa [Y10F.subgroupOf_map_subtype_of_le hL₁X] at h2'
  · rw [← main_map_inf_cent hL₁X hx₂]
    exact (T123C.glaPComponent_map_iff X.subtype_injective 3 _ _).2 hM'
  · exact (T123C.catalogIs_pSimple_map_iff X.subtype_injective 3 M' Q3).2 hM'c
  · rw [← Y10F.card_subgroupOf hBX, hcard, main_card_inf_centModSubgroup hKX hBX]

end MainTransport

theorem i158Main_of_fact {G : Type} [Group G] [Finite G] (h : T158MainFact) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G) (x₁ x₂ : G) (L₁ L₂ : Subgroup G),
      I158HypK p X K B x₁ x₂ L₁ L₂ → GLAPLayer p (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) ≠ ⊥ →
        p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧
          ((catalogIs (PSimple 3 K) (S10.isU6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isL2n (3 * n)) ∧
              (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
                catalogIs (PSimple 3 M) (S10.isL2n n)) ∧
              Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
            (catalogIs (PSimple 3 K) (S10.isTE6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isU3n (3 * n)) ∧
              (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
                catalogIs (PSimple 3 M) (S10.isU3n n)) ∧
              Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K))) ∧
          ∀ T : Subgroup G, T ≤ X → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
            (⁅T, B⁆ : Subgroup G) = ⊥ := by
  intro p hp hp2 X K B x₁ x₂ L₁ L₂ hI hne
  obtain ⟨⟨hKG, hK, hBel, hBX, hrk, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2⟩, hn12, hn21⟩ := hI
  have hx1X : x₁ ∈ X := hBX hx1B
  have hx2X : x₂ ∈ X := hBX hx2B
  have hKX : K ≤ X := hK.1
  have hKC1 : K ⊓ Subgroup.centralizer ({x₁} : Set G) ≤ X := inf_le_left.trans hKX
  have hKC2 : K ⊓ Subgroup.centralizer ({x₂} : Set G) ≤ X := inf_le_left.trans hKX
  have hL1X : L₁ ≤ X := hL1.1.trans hKC1
  have hL2X : L₂ ≤ X := hL2.1.trans hKC2
  have hTop : GLAPComponent p (⊤ : Subgroup X) (K.subgroupOf X) := by
    have h1 := T123C.glaPComponent_map_iff X.subtype_injective p (⊤ : Subgroup X) (K.subgroupOf X)
    rw [main_map_top X, Y10F.subgroupOf_map_subtype_of_le hKX] at h1
    exact h1.1 hK
  have hrk' : p ^ GLATwoLocalRank p ↥(⊤ : Subgroup X) ≤ Nat.card ↥(B.subgroupOf X) := by
    rw [Y10F.card_subgroupOf hBX]
    have hmono : GLATwoLocalRank p ↥(⊤ : Subgroup X) ≤ GLATwoLocalRank p ↥X :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp
        (⊤ : Subgroup X).subtype (⊤ : Subgroup X).subtype_injective
    exact (Nat.pow_le_pow_right hp.pos hmono).trans hrk
  have hx1' : (⟨x₁, hx1X⟩ : X) ≠ 1 := fun h0 => hx1 (congrArg Subtype.val h0)
  have hx2' : (⟨x₂, hx2X⟩ : X) ≠ 1 := fun h0 => hx2 (congrArg Subtype.val h0)
  have hL1' : GLAPComponent p (K.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x₁, hx1X⟩ : X)} : Set X))
      (L₁.subgroupOf X) := by
    rw [← main_subgroupOf_inf_cent hKX hx1X]
    have h1 := T123C.glaPComponent_map_iff X.subtype_injective p
      ((K ⊓ Subgroup.centralizer ({x₁} : Set G)).subgroupOf X) (L₁.subgroupOf X)
    rw [Y10F.subgroupOf_map_subtype_of_le hKC1, Y10F.subgroupOf_map_subtype_of_le hL1X] at h1
    exact h1.1 hL1
  have hL2' : GLAPComponent p (K.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x₂, hx2X⟩ : X)} : Set X))
      (L₂.subgroupOf X) := by
    rw [← main_subgroupOf_inf_cent hKX hx2X]
    have h1 := T123C.glaPComponent_map_iff X.subtype_injective p
      ((K ⊓ Subgroup.centralizer ({x₂} : Set G)).subgroupOf X) (L₂.subgroupOf X)
    rw [Y10F.subgroupOf_map_subtype_of_le hKC2, Y10F.subgroupOf_map_subtype_of_le hL2X] at h1
    exact h1.1 hL2
  have hc1' : IsChevSimple 2 (PSimple p (L₁.subgroupOf X)) := by
    refine (T123C.isChevSimple_pSimple_map_iff X.subtype_injective 2 p (L₁.subgroupOf X)).1 ?_
    rw [Y10F.subgroupOf_map_subtype_of_le hL1X]
    exact hc1
  have hc2' : IsChevSimple 2 (PSimple p (L₂.subgroupOf X)) := by
    refine (T123C.isChevSimple_pSimple_map_iff X.subtype_injective 2 p (L₂.subgroupOf X)).1 ?_
    rw [Y10F.subgroupOf_map_subtype_of_le hL2X]
    exact hc2
  have hn12' : FGOn p (⟨x₁, hx1X⟩ : X) (L₂.subgroupOf X) := main_fgOn_subgroupOf hp hL2X hx1X hn12
  have hn21' : FGOn p (⟨x₂, hx2X⟩ : X) (L₁.subgroupOf X) := main_fgOn_subgroupOf hp hL1X hx2X hn21
  have hI' : I158HypK p (⊤ : Subgroup X) (K.subgroupOf X) (B.subgroupOf X) ⟨x₁, hx1X⟩ ⟨x₂, hx2X⟩
      (L₁.subgroupOf X) (L₂.subgroupOf X) :=
    ⟨⟨hKG.subgroup ⊤, hTop, (Y10F.isElemAbelian_subgroupOf_iff hBX).2 hBel, le_top, hrk',
      Subgroup.mem_subgroupOf.2 hx1B, Subgroup.mem_subgroupOf.2 hx2B, hx1', hx2', hL1', hc1', hL2', hc2'⟩,
      hn12', hn21'⟩
  have hne' : GLAPLayer p (L₁.subgroupOf X ⊓ Subgroup.centralizer ({(⟨x₂, hx2X⟩ : X)} : Set X)) ≠ ⊥ := by
    intro h0
    apply hne
    rw [← main_map_inf_cent hL1X hx2X, Y10F.glaPLayer_map hp X.subtype_injective, h0, Subgroup.map_bot]
  obtain ⟨hp3, n, hodd, hn1, hD, hT⟩ :=
    h ↥X p hp hp2 (K.subgroupOf X) (B.subgroupOf X) ⟨x₁, hx1X⟩ ⟨x₂, hx2X⟩ (L₁.subgroupOf X) (L₂.subgroupOf X)
      hI' hne'
  refine ⟨hp3, n, hodd, hn1, ?_, ?_⟩
  · rcases hD with ⟨d1, d2, d3, d4⟩ | ⟨d1, d2, d3, d4⟩
    · exact Or.inl (main_disj_transport (k := 3) hKX hL1X hBX hx2X ⟨d1, d2, d3, d4⟩)
    · exact Or.inr (main_disj_transport (k := 4) hKX hL1X hBX hx2X ⟨d1, d2, d3, d4⟩)
  · intro T hTG hT2 hBT
    have hTX : T ≤ X := hTG
    have hB' : B.subgroupOf X ≤ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X) := by
      apply Y10F.le_normalizer_of_map_le
      rw [Y10F.subgroupOf_map_subtype_of_le hBX, Y10F.subgroupOf_map_subtype_of_le hTX]
      exact hBT
    have key := hT (T.subgroupOf X) le_top ((Y10F.isPGroup_subgroupOf_iff hTX).2 hT2) hB'
    have hcomm : (⁅T.subgroupOf X, B.subgroupOf X⁆ : Subgroup X).map X.subtype = ⁅T, B⁆ := by
      rw [Subgroup.map_commutator, Y10F.subgroupOf_map_subtype_of_le hTX,
        Y10F.subgroupOf_map_subtype_of_le hBX]
    rw [key, Subgroup.map_bot] at hcomm
    exact hcomm.symm

end CFSG.LocalAnalysis.GLTheoremA.T158

end
