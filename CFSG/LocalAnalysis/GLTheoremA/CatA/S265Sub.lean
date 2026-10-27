module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Trans
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem closureIn_eq_self_of_le {L B : Subgroup G} (h : B ≤ Subgroup.normalizer (L : Set G)) :
    closureIn L B = L := by
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    exact (Subgroup.mem_normalizer_iff.1 (h ha) z).1 hz
  · exact le_closureIn_self L B

theorem normal_subgroupOf {H L : Subgroup G} (hLH : L ≤ H) (hHN : H ≤ Subgroup.normalizer (L : Set G)) :
    (L.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN

theorem mem_normalizer_subgroupOf {H L : Subgroup G} (hLH : L ≤ H) (hHN : H ≤ Subgroup.normalizer (L : Set G))
    (h : ↥H) : h ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  haveI := normal_subgroupOf hLH hHN
  rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
  exact Subgroup.mem_top h

theorem sup3_subgroupOf {H L B T : Subgroup G} (h : L ⊔ B ⊔ T = H) :
    L.subgroupOf H ⊔ B.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
  have hLH : L ≤ H := h ▸ (le_sup_left.trans le_sup_left)
  have hBH : B ≤ H := h ▸ (le_sup_right.trans le_sup_left)
  have hTH : T ≤ H := h ▸ le_sup_right
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH,
    Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hTH, h, Subgroup.map_top,
    Subgroup.range_subtype]

theorem comm_subgroupOf_ne_bot {H B T : Subgroup G} (hBH : B ≤ H) (hTH : T ≤ H)
    (h : (⁅T, B⁆ : Subgroup G) ≠ ⊥) : (⁅T.subgroupOf H, B.subgroupOf H⁆ : Subgroup ↥H) ≠ ⊥ := by
  intro hbot
  apply h
  have := congrArg (Subgroup.map H.subtype) hbot
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_subgroupOf_eq_of_le hBH,
    Subgroup.map_bot] at this

theorem le_normalizer_subgroupOf {H B T : Subgroup G} (hBH : B ≤ H) (hTH : T ≤ H)
    (h : B ≤ Subgroup.normalizer (T : Set G)) :
    B.subgroupOf H ≤ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hb' := Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hb)) (g : G)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hb'

theorem isElemAbelian_subgroupOf' {p : ℕ} {B : Subgroup G} (H : Subgroup G) (hB : IsElemAbelian p B) :
    IsElemAbelian p (B.subgroupOf H) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact isElemAbelian_commute hB (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hB.2 _ (Subgroup.mem_subgroupOf.1 hx)

theorem card_subgroupOf' {B H : Subgroup G} (hBH : B ≤ H) : Nat.card (B.subgroupOf H) = Nat.card B :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv

theorem isPGroup_subgroupOf' {q : ℕ} {T H : Subgroup G} (hT : IsPGroup q T) (hTH : T ≤ H) :
    IsPGroup q (T.subgroupOf H) :=
  IsPGroup.of_injective hT (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTH).injective

end Basic

section PQuot

variable {G : Type} [Group G] [Finite G] {p : ℕ}

noncomputable def eL (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) :
    PQuot p (L.subgroupOf H) ≃* PQuot p L :=
  T156.pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLH)

theorem indRel_eL (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) (hHN : H ≤ Subgroup.normalizer (L : Set G))
    (g : ↥H) (q q' : PQuot p (L.subgroupOf H)) :
    indRel p L (g : G) (eL hp hLH q) (eL hp hLH q') ↔ indRel p (L.subgroupOf H) g q q' :=
  T156.indRel_pquotIsoOf hp (Subgroup.map_subgroupOf_eq_of_le hLH) (mem_normalizer_subgroupOf hLH hHN g) q q'

theorem fieldOn_subgroupOf (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) {b : G} (hb : b ∈ H) (hF : FieldOn p b L) :
    FieldOn p (⟨b, hb⟩ : ↥H) (L.subgroupOf H) := by
  refine T156.fieldOn_to_Omega (eL hp hLH).symm (mem_normalizer_subgroupOf hLH hHN _) (fun x x' => ?_) hF
  have := indRel_eL hp hLH hHN ⟨b, hb⟩ ((eL hp hLH).symm x) ((eL hp hLH).symm x')
  simpa using this

theorem fieldOn_of_subgroupOf (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) {b : G} (hb : b ∈ H)
    (hF : FieldOn p (⟨b, hb⟩ : ↥H) (L.subgroupOf H)) : FieldOn p b L :=
  T156.fieldOn_to_Omega (eL hp hLH) (hHN hb) (fun x x' => (indRel_eL hp hLH hHN ⟨b, hb⟩ x x').symm) hF

theorem innDiagOn_subgroupOf (hp : p.Prime) {H L A : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hAH : A ≤ H) (h : InnDiagOn p A L) :
    InnDiagOn p (A.subgroupOf H) (L.subgroupOf H) := by
  refine T156.innDiagOn_to_Omega (eL hp hLH).symm (fun a _ => mem_normalizer_subgroupOf hLH hHN a)
    (fun a' ha' => ⟨(a' : G), Subgroup.mem_subgroupOf.1 ha', fun x x' => ?_⟩) h
  have := indRel_eL hp hLH hHN a' ((eL hp hLH).symm x) ((eL hp hLH).symm x')
  simpa using this

theorem innDiagOn_of_subgroupOf (hp : p.Prime) {H L A : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hAH : A ≤ H)
    (h : InnDiagOn p (A.subgroupOf H) (L.subgroupOf H)) : InnDiagOn p A L := by
  refine T156.innDiagOn_of_Omega (eL hp hLH).symm (fun a ha => hHN (hAH ha)) (fun a ha => ?_) h
  refine ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.2 ha, fun x x' => ?_⟩
  have := indRel_eL hp hLH hHN ⟨a, hAH ha⟩ ((eL hp hLH).symm x) ((eL hp hLH).symm x')
  simpa using this

theorem card2_subgroupOf (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) :
    card2 p (L.subgroupOf H) = card2 p L := by
  unfold card2
  rw [Nat.card_congr (eL hp hLH).toEquiv]

theorem centCard2_subgroupOf (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (g : ↥H) :
    centCard2 p (L.subgroupOf H) g = centCard2 p L (g : G) := by
  unfold centCard2
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquiv (eL hp hLH).toEquiv
    (fun q => (indRel_eL hp hLH hHN g q q).symm))

theorem mem_centMod_subgroupOf_iff (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (g : ↥H) :
    g ∈ centModSubgroup p (L.subgroupOf H) ↔ (g : G) ∈ centModSubgroup p L := by
  have h := S267.mem_centModSubgroup_map_iff hp H.subtype (T156.not_dvd_card_ker_subtype hp H)
    (mem_normalizer_subgroupOf hLH hHN g)
  rw [Subgroup.map_subgroupOf_eq_of_le hLH] at h
  exact h

theorem centMod_subgroupOf_iff (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (g : ↥H) :
    CentMod p (L.subgroupOf H) g ↔ CentMod p L (g : G) := by
  rw [centMod_iff, centMod_iff]
  exact mem_centMod_subgroupOf_iff hp hLH hHN g

theorem cycModSylow_subgroupOf (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hcyc : CycModSylow p L) :
    CycModSylow p (L.subgroupOf H) := by
  intro P hP hPp
  have h1 : IsCyclic (P.map H.subtype) :=
    hcyc _ (fun g hg => by
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      exact (centMod_subgroupOf_iff hp hLH hHN g₀).1 (hP g₀ hg₀)) (hPp.map _)
  exact isCyclic_of_surjective (P.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
    (P.equivMapOfInjective H.subtype H.subtype_injective).symm.surjective

theorem twoLocalRank_subgroup (hp : p.Prime) (H : Subgroup G) :
    GLATwoLocalRank p ↥H ≤ GLATwoLocalRank p G :=
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp H.subtype
    H.subtype_injective

end PQuot

section Layers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem map_inf_cx_subgroupOf {H L : Subgroup G} (hLH : L ≤ H) {b : G} (hb : b ∈ H) :
    ((L.subgroupOf H) ⊓ Subgroup.centralizer ({(⟨b, hb⟩ : ↥H)} : Set ↥H) : Subgroup ↥H).map H.subtype =
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    have := congrArg Subtype.val hyC
    simpa using this
  · intro hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hLH hxL⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    apply Subtype.ext
    simpa using hxC

theorem map_inf_cs_subgroupOf {H L E : Subgroup G} (hLH : L ≤ H) (hEH : E ≤ H) :
    ((L.subgroupOf H) ⊓ Subgroup.centralizer ((E.subgroupOf H : Subgroup ↥H) : Set ↥H) : Subgroup ↥H).map
        H.subtype = L ⊓ Subgroup.centralizer (E : Set G) := by
  rw [S267.map_inf_centralizer_inj H.subtype H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hLH,
    Subgroup.map_subgroupOf_eq_of_le hEH]

theorem layer_cs_subgroupOf_ne_bot_iff (hp : p.Prime) {H L E : Subgroup G} (hLH : L ≤ H) (hEH : E ≤ H) :
    GLAPLayer p ((L.subgroupOf H) ⊓ Subgroup.centralizer ((E.subgroupOf H : Subgroup ↥H) : Set ↥H)) ≠ ⊥ ↔
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  have h := S267.glaPLayer_map_ne_bot_iff hp H.subtype (T156.not_dvd_card_ker_subtype hp H)
    ((L.subgroupOf H) ⊓ Subgroup.centralizer ((E.subgroupOf H : Subgroup ↥H) : Set ↥H))
  rw [map_inf_cs_subgroupOf hLH hEH] at h
  exact h.symm

theorem layer_cx_subgroupOf_ne_bot_iff (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {b : G} (hb : b ∈ H) :
    GLAPLayer p ((L.subgroupOf H) ⊓ Subgroup.centralizer ({(⟨b, hb⟩ : ↥H)} : Set ↥H)) ≠ ⊥ ↔
      GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set G)) ≠ ⊥ := by
  have h := S267.glaPLayer_map_ne_bot_iff hp H.subtype (T156.not_dvd_card_ker_subtype hp H)
    ((L.subgroupOf H) ⊓ Subgroup.centralizer ({(⟨b, hb⟩ : ↥H)} : Set ↥H))
  rw [map_inf_cx_subgroupOf hLH hb] at h
  exact h.symm

theorem layer_cs_map_ne_bot_iff (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) (E : Subgroup ↥H) :
    GLAPLayer p (L ⊓ Subgroup.centralizer ((E.map H.subtype : Subgroup G) : Set G)) ≠ ⊥ ↔
      GLAPLayer p ((L.subgroupOf H) ⊓ Subgroup.centralizer (E : Set ↥H)) ≠ ⊥ := by
  have h := S267.glaPLayer_map_ne_bot_iff hp H.subtype (T156.not_dvd_card_ker_subtype hp H)
    ((L.subgroupOf H) ⊓ Subgroup.centralizer (E : Set ↥H))
  rw [S267.map_inf_centralizer_inj H.subtype H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hLH] at h
  exact h

end Layers

section Zpowers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem mem_zpowers_subgroupOf_iff {H : Subgroup G} (a c : ↥H) :
    c ∈ Subgroup.zpowers a ↔ (c : G) ∈ Subgroup.zpowers (a : G) := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simp⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩

theorem centMod_iff_mem_zpowers (hp : p.Prime) {B L : Subgroup G} {x : G} (hB : IsElemAbelian p B)
    (hx : x ∈ B) (hx1 : x ≠ 1) (hxL : x ∈ centModSubgroup p L) (hcyc : CycModSylow p L) :
    ∀ c ∈ B, CentMod p L c ↔ c ∈ Subgroup.zpowers x := by
  intro c hc
  constructor
  · intro hcM
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤ centModSubgroup p L :=
      sup_le (Subgroup.zpowers_le.2 hxL) (Subgroup.zpowers_le.2 (centMod_iff.1 hcM))
    have hSB : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤ B :=
      sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hc)
    have hSel : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers c) := isElemAbelian_mono hB hSB
    have hcy := hcyc _ (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hSel)
    have hcard := card_le_of_isCyclic_of_pow hp hcy (fun d hd => hB.2 d (hSB hd))
    exact mem_zpowers_of_card_sup_le hp (hB.2 x hx) hx1 hcard
  · intro hcx
    exact centMod_iff.2 ((Subgroup.zpowers_le.2 hxL) hcx)

end Zpowers

end CFSG.LocalAnalysis.GLTheoremA.S265

end
