module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5N2Glue
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Syl3
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DC2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Out
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaBridgeEnd
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndAssembly
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsU62
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL64
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQFinal

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.EvenSmallLie.UnitarySix.YamadaSec3

section Inputs


@[expose] def Sec3DInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46,
      YamadaD.Hyp (sec3DData e t) ∧ YamadaD.HypB (sec3DData e t) ∧
        YamadaD.HypC (sec3DData e t) ∧ YamadaD.HypQ (sec3DData e t) ∧
        YamadaD.Hyp416 (sec3DData e t) ∧
        (YamadaD.HypNF (sec3DData e t) ∨ ∃ φ, YamadaD.HypF (sec3DData e t) φ)

@[expose] def Sec3Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ (t : G) (e : L ≃* T46),
      sS e ⊓ centralizer (sS e : Set G) = zpowers (sec3DData e t).z ∧
      (∀ X : Subgroup G, X ≤ sS e → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → Nat.card X = 2 ^ 9 →
        X = sA₂ e) ∧
      L ⊓ normalizer (sA₂ e : Set G) ≤ sK₂ e ⊔ sA₂ e ∧
      L ⊓ centralizer ({(sec3DData e t).z} : Set G) ≤ sK₁ e ⊔ sA₁ e

@[expose] def Y13CoordInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46,
      ∃ (θ : (sec3DData e t).K₁ ≃* YamadaPar.SU42b) (ιG : (Fin 8 → ZMod 2) → G),
        Y13Coords (sec3DData e t) θ ιG

@[expose] def N2Input (F : Type) [Field F] : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ (e : L ≃* T46) (P : Subgroup G),
      IsSylowOf 2 P (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁ (sec3DData e t).D₂) →
      Nat.card P = 2 ^ 30 → P ⊓ centralizer ({t} : Set G) = sS e → sS e ≤ P →
      (sec3DData e t).D₁ ≤ P → (sec3DData e t).D₂ ≤ P →
      (sec3DData e t).V₁ ≤ centralizer (P : Set G) → t ∈ normalizer (P : Set G) →
      ∃ N₂ : Subgroup G, N2Out F (sec3Data e t (sec3DData e t).V₁ (sec3DData e t).D₁
        (sec3DData e t).D₂ (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁
          (sec3DData e t).D₂) N₂ P)

end Inputs

section Inputs₂


@[expose] def Y14CoordInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46,
      ∃ (θ₂ : YamadaN2.SL3 →* G) (ιG : (Fin 9 → ZMod 2) → G), Y14Coords (sec3DData e t) θ₂ ιG ∧
        (∀ u ∈ YamadaN2.U3, θ₂ u ∈ sS e) ∧ θ₂ YamadaN2.s01 = sw e 0

@[expose] def N1PInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ (e : L ≃* T46) (θ : (sec3DData e t).K₁ ≃* YamadaPar.SU42b)
      (ιG : (Fin 8 → ZMod 2) → G), Y13Coords (sec3DData e t) θ ιG → ∀ P : Subgroup G,
      IsSylowOf 2 P (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁ (sec3DData e t).D₂) →
      Nat.card P = 2 ^ 30 → P ⊓ centralizer ({t} : Set G) = sS e → sS e ≤ P →
      (sec3DData e t).D₁ ≤ P → (sec3DData e t).D₂ ≤ P →
      (sec3DData e t).V₁ ≤ centralizer (P : Set G) → t ∈ normalizer (P : Set G) →
      P ≤ normalizer ((sec3DData e t).D₂ : Set G) ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂) ∧
      (∀ x ∈ P, x * x ∈ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂) ∧
      (∀ x ∈ P, x * t * x⁻¹ * t⁻¹ ∈ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂ →
        x ∈ sS e ⊔ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂) ∧
      ∃ j ∈ sK₂ e, j ∈ normalizer (P : Set G) ∧ j ^ 3 = 1 ∧
        ∀ x ∈ P, j * x * j⁻¹ * x⁻¹ ∈ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂ →
          x ∈ (sec3DData e t).D₁ ⊔ (sec3DData e t).D₂

end Inputs₂

section Inputs₃


@[expose] def HypAutInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46, YamadaSec3.HypAut (sec3DData e t)

@[expose] def CaseInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46,
      YamadaD.HypNF (sec3DData e t) ∨ ∃ φ, YamadaD.HypF (sec3DData e t) φ

@[expose] def Sec3LInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ (t : G) (e : L ≃* T46),
      (∀ X : Subgroup G, X ≤ sS e → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → Nat.card X = 2 ^ 9 →
        X = sA₂ e) ∧
      L ⊓ normalizer (sA₂ e : Set G) ≤ sK₂ e ⊔ sA₂ e ∧
      L ⊓ centralizer ({(sec3DData e t).z} : Set G) ≤ sK₁ e ⊔ sA₁ e

end Inputs₃

theorem nat_card_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact F4.card

theorem exists_involution_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) : ∃ t ∈ centralizer (L : Set G), orderOf t = 2 :=
  hset.standard.exists_involution_centralizer

theorem le_of_isSylowOf {G : Type} [Group G] {p : ℕ} {P K : Subgroup G} (h : IsSylowOf p P K) :
    P ≤ K := by
  obtain ⟨Q, rfl⟩ := h
  exact map_subtype_le _

theorem S_le_normalizer_D₂ {G : Type} [Group G] [Finite G] {d : YamadaD.Data G}
    (h : YamadaD.Hyp d) (hSL : d.S ≤ d.L) (hSA : d.S ≤ normalizer (d.A₂ : Set G))
    (hZS : d.S ⊓ centralizer (d.S : Set G) = zpowers d.z) :
    d.S ≤ normalizer (d.D₂ : Set G) := by
  intro x hx
  have hxt : x ∈ normalizer (zpowers d.t : Set G) :=
    YamadaPar.mem_normalizer_of_conj_eq fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right (show Commute x d.t from h.comm_of_mem_L (hSL hx)) k).eq,
        mul_inv_cancel_right]
  have hxz : x ∈ normalizer (zpowers d.z : Set G) := by
    have hz : d.z ∈ d.S ⊓ centralizer (d.S : Set G) := hZS ▸ mem_zpowers d.z
    exact YamadaPar.mem_normalizer_of_conj_eq fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right (show Commute x d.z from
        (mem_centralizer_iff.mp hz.2 x hx)) k).eq, mul_inv_cancel_right]
  have hxC := h.C₂_normal (YamadaD.mem_normalizer_sup (hSA hx) hxt)
  have hxV := h.X_le_normalizer_V₁ (YamadaD.mem_normalizer_sup hxz hxt)
  exact YamadaD.Hyp.mem_normalizer_inf hxC
    (YamadaD.mem_normalizer_of_conj_mem fun _ hn => YamadaD.conj_mem_centralizer hxV hn)

theorem normalizer_le_of_unique {G : Type} [Group G] [Finite G] {S A : Subgroup G}
    (hJ : ∀ X : Subgroup G, X ≤ S → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → Nat.card X = 2 ^ 9 →
      X = A) (hAS : A ≤ S) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA : Nat.card A = 2 ^ 9) :
    normalizer (S : Set G) ≤ normalizer (A : Set G) := by
  intro x hx
  have hX : A.map (MulAut.conj x).toMonoidHom = A := by
    refine hJ _ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (mem_normalizer_iff.mp hx a).mp (hAS ha)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
        _ = x * (b * a) * x⁻¹ := by rw [hAc a ha b hb]
        _ = x * b * x⁻¹ * (x * a * x⁻¹) := by group
    · rw [card_map_of_injective (MulEquiv.injective _), hA]
  exact YamadaD.mem_normalizer_of_conj_mem fun a ha => hX ▸ ⟨a, ha, rfl⟩

section Reduce


theorem sec3DInput_of
    (hA : HypAutInput) (hc : CaseInput) : Sec3DInput := by
  intro G _ _ L hset hZ hQ t htL ht e
  have hA' := hA hset hZ hQ htL ht e
  exact ⟨hyp_sec3DData' hset hZ hQ htL ht e hA', hypB_sec3DData hA', hypC_sec3DData,
    hypQ_sec3DData hA'.NZ₂S, hyp416_sec3DData, hc hset hZ hQ htL ht e⟩

theorem sec3Input_of (hL : Sec3LInput) : Sec3Input := by
  intro G _ _ L hset hZ hQ t e
  obtain ⟨h2, h3, h4⟩ := hL hset hZ hQ t e
  exact ⟨d_center_S, h2, h3, h4⟩

end Reduce

section Assembly

theorem childU6Centerless_of_n2 (h3 : Sec3DInput) (hX : Sec3Input)
    (hY : Y13CoordInput) (hN2 : N2Input F4) : ChildU6Centerless := by
  intro G _ _ L hset hZ hQ
  have : IsSimpleGroup G := hset.simple
  obtain ⟨t, htL, ht⟩ := exists_involution_of_standard hset
  obtain ⟨e₀⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hQ
  let e : L ≃* T46 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀
  obtain ⟨hH, hB, hC, hQq, h416, hcase⟩ := h3 hset hZ hQ htL ht e
  obtain ⟨hZS, hJ, -, hNL₁⟩ := hX hset hZ hQ t e
  obtain ⟨θ, ιG, hco⟩ := hY hset hZ hQ htL ht e
  have hV : ∀ v ∈ (sec3DData e t).V₁, v * v = 1 :=
    fun v hv => hH.V₁_sq hset.nonab hset.kProper hv
  have hN := hH.yamada_4_16_3 hB hC hV hQq h416 hcase
  have s0 := section3Out hset hZ hQ htL ht F4 nat_card_F4 e ⊥ ⊥ ⊥ ⊥ ⊥ ⊥
  have hY13 := y13Hyp_of hH hB hC hV h416 hco s0.K₁_A₁ hN
  have hSL : sS e ≤ L := le_of_isSylowOf s0.sylow
  have hSA : sS e ≤ normalizer (sA₂ e : Set G) :=
    le_normalizer.trans (normalizer_le_of_unique hJ s0.A₂_le hH.A₂_comm hH.card_A₂)
  have hzS : (sec3DData e t).z ∈ sS e ⊓ centralizer (sS e : Set G) := hZS ▸ mem_zpowers _
  have hSK : sS e ≤ sK₁ e ⊔ sA₁ e := fun s hs => hNL₁ (mem_inf.mpr ⟨hSL hs,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzS.2 s hs)⟩)
  obtain ⟨P, hPN, hPs, hPc, hPH, hSP, hD₁P, hD₂P, hV₁P, htP⟩ :=
    hY13.exists_sylow s0.sylow s0.K₁_le s0.A₁_le hSK (S_le_normalizer_D₂ hH hSL hSA hZS)
  obtain ⟨N₂, hN₂⟩ := hN2 hset hZ hQ htL ht e P hPs hPc hPH hSP hD₁P hD₂P hV₁P htP
  have s3 := section3Out hset hZ hQ htL ht F4 nat_card_F4 e (sec3DData e t).V₁
    (sec3DData e t).D₁ (sec3DData e t).D₂
    (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁ (sec3DData e t).D₂) N₂ P
  have s4 := YamadaD.section4Out hH hB hset.nonab hset.kProper hSL hZS
    (sec3Data e t (sec3DData e t).V₁ (sec3DData e t).D₁ (sec3DData e t).D₂
      (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁ (sec3DData e t).D₂) N₂ P)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hY13.main F4 nat_card_F4
  obtain ⟨χ, hχ₂, hχ₃, hχS⟩ := s3.K₁_model
  obtain ⟨c2, c3⟩ := hY13.card_inf_conjR_w YamadaInputs.l44Input F4 nat_card_F4 χ hχ₂ hχ₃
    (fun A hA => (mem_inf.mp (hχS A hA)).1) hPs hSP hD₁P
  have hX₂ : sX₂ e ≤ sS e := s3.S_b.symm.le.trans (inf_le_left.trans inf_le_left)
  have hX₃ : sX₃ e ≤ sS e := s3.S_c.symm.le.trans (inf_le_left.trans inf_le_left)
  have hKg : sK₁ e = sX₂ e ⊔ sX₃ e ⊔ zpowers (sw e 1) ⊔ zpowers (sw e 2) := s3.K₁_gen
  have hw₂ : sw e 1 ∈ sK₁ e := by
    rw [hKg]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
  have hw₃ : sw e 2 ∈ sK₁ e := by
    rw [hKg]; exact mem_sup_right (mem_zpowers _)
  have hK₁ : sK₁ e ≤ sS e ⊔ zpowers (sw e 1) ⊔ zpowers (sw e 2) := by
    rw [hKg]
    exact sup_le (sup_le (sup_le (hX₂.trans (le_sup_left.trans le_sup_left))
      (hX₃.trans (le_sup_left.trans le_sup_left))) (le_sup_right.trans le_sup_left)) le_sup_right
  have h4 : YamadaSection4 F4 (sec3Data e t (sec3DData e t).V₁ (sec3DData e t).D₁
      (sec3DData e t).D₂ (YamadaPar.nOne (sec3DData e t).D₁ (sec3DData e t).K₁
        (sec3DData e t).D₂) N₂ P) :=
    { s3, s4, hN₂ with
      D₁_le := m1
      N₁_norm := m2
      t_N₁ := m3
      centralizer₁ := m4
      N₁_H := m5
      type₁ := m6
      t_D₁ := hH.t_mem_normalizer_D₁
      t_D₂ := hH.t_mem_normalizer_D₂
      P_le₁ := hPN
      sylow_P₁ := hPs
      card_P := hPc
      P_H := hPH
      D₁_le_P := hD₁P
      D₂_le_P := hD₂P
      V₁_center := hV₁P
      t_P := htP
      card_P_w₂ := c2
      card_P_w₃ := c3
      N₁_gen := YamadaPar.nOne_eq_sup hw₂ hw₃ hK₁ hPN hSP hD₁P hD₂P }
  exact h4.false_of_yamada_endgame YamadaInputs.l44Input YamadaInputs.l64CentralizerInput
      YamadaInputs.l64TransferInput YamadaInputs.u62RankInput


theorem n2Input_of (h3 : Sec3DInput) (hX : Sec3Input) (hY : Y13CoordInput)
    (hY₂ : Y14CoordInput) (hP₁ : N1PInput) : N2Input F4 := by
  intro G _ _ L hset hZ hQ t htL ht e P hPs hPc hPH hSP hD₁P hD₂P hV₁P htP
  have : IsSimpleGroup G := hset.simple
  obtain ⟨hH, hB, hC, hQq, h416, hcase⟩ := h3 hset hZ hQ htL ht e
  obtain ⟨hZS, hJ, hNL, hNL₁⟩ := hX hset hZ hQ t e
  obtain ⟨θ, ιG, hco⟩ := hY hset hZ hQ htL ht e
  obtain ⟨θ₂, ιG₂, hco₂, hU, hw₁⟩ := hY₂ hset hZ hQ htL ht e
  have hV : ∀ v ∈ (sec3DData e t).V₁, v * v = 1 :=
    fun v hv => hH.V₁_sq hset.nonab hset.kProper hv
  have hN := hH.yamada_4_16_3 hB hC hV hQq h416 hcase
  have s0 := section3Out hset hZ hQ htL ht F4 nat_card_F4 e ⊥ ⊥ ⊥ ⊥ ⊥ ⊥
  have hNA := normalizer_le_of_unique hJ s0.A₂_le hH.A₂_comm hH.card_A₂
  have hSA : sS e ≤ normalizer (sA₂ e : Set G) := le_normalizer.trans hNA
  have hSL : sS e ≤ L := le_of_isSylowOf s0.sylow
  have hY14 := y14Hyp_of hH hB hC hV hco hco₂ s0.K₂_A₂ hN
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hY14.main F4 nat_card_F4
  obtain ⟨q1, q2, q3, q4, j, hj, hjP, hj3, hjfix⟩ :=
    hP₁ hset hZ hQ htL ht e θ ιG hco P hPs hPc hPH hSP hD₁P hD₂P hV₁P htP
  have hX₁ : sX₁ e ≤ sS e := s0.S_a.symm.le.trans (inf_le_left.trans inf_le_left)
  have hX₂ : sX₂ e ≤ sS e := s0.S_b.symm.le.trans (inf_le_left.trans inf_le_left)
  have hK₂g : sK₂ e = sX₁ e ⊔ sX₂ e ⊔ zpowers (sw e 0) ⊔ zpowers (sw e 1) := s0.K₂_gen
  have hPD₁ : P ≤ normalizer ((sec3DData e t).D₁ : Set G) :=
    (le_of_isSylowOf hPs).trans (nOne_le_normalizer_D₁ hH hN.1)
  obtain ⟨p1, p2, p3, p4⟩ := hY14.P_fields (g1 hH hB hV) (g2 hH s0.sylow hSA s0.A₂_le hNL)
    (nS hH hB hZS hNA hNL) (fun s hs => hNL (mem_inf.mpr ⟨hSL hs, hSA hs⟩)) hK₂g hX₁ hX₂ hU hw₁
    YamadaN2.card_U3_inf_s01 hPc hSP hD₁P hD₂P htP hPD₁ q1 q2 q3 q4 hj hjP hj3 hjfix
  exact ⟨YamadaN2.nTwo (sec3DData e t).D₂ (sec3DData e t).K₂ (sec3DData e t).D₁,
    { D₂_le := m1
      N₂_norm := m2
      N₂_H := m5
      t_N₂ := m3
      normalizer_S := normalizer_S_le hH hB hV hZS hNA hNL hNL₁
      centralizer₂ := m4
      type₂ := m6
      P_le₂ := p1
      sylow_P₂ := p2
      card_P_w₁ := p3
      N₂_gen := p4 }⟩

theorem childU6Centerless_of_inputs' (h3 : Sec3DInput) (hX : Sec3Input) (hY : Y13CoordInput)
    (hY₂ : Y14CoordInput) (hP₁ : N1PInput) : ChildU6Centerless :=
  childU6Centerless_of_n2 h3 hX hY (n2Input_of h3 hX hY hY₂ hP₁)

theorem childU6Centerless_of_inputs
    (hA : HypAutInput)
    (hcase : CaseInput) (hL : Sec3LInput) (hY : Y13CoordInput) (hY₂ : Y14CoordInput)
    (hP₁ : N1PInput) : ChildU6Centerless :=
  childU6Centerless_of_inputs' (sec3DInput_of hA hcase) (sec3Input_of hL) hY hY₂ hP₁

end Assembly

end CFSG.EvenSmallLie.UnitarySix.Child5
