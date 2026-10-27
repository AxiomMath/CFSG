module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_sup_eq_of_isPGroup {p : ℕ} (hp : p.Prime) {L P : Subgroup G}
    (hP : IsPGroup p P) (hPL : P ≤ centModSubgroup p L) :
    (L ⊓ Subgroup.centralizer (P : Set G)) ⊔ GLAPPrimeCoreOf p L = L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  apply le_antisymm (sup_le inf_le_left (Subgroup.map_subtype_le _))
  intro l hl
  have hmem : ∀ g ∈ P, ∀ o ∈ O, l⁻¹ * (g * (l * o) * g⁻¹) ∈ O := by
    intro g hg o ho
    have hgC := hPL hg
    have h1 : ⁅l⁻¹, g⁆ ∈ O := hgC.2 _ (L.inv_mem hl)
    have h2 : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hgC.1) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact O.mul_mem h1 h2
  letI act : MulAction P O :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : P) : G) * (l * (o : G)) *
          ((1 : P) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : P) : G) * (l * (o : G)) *
          ((g * h : P) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  obtain ⟨o, ho⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card O hOp
  have hcomm : ∀ g ∈ P, g * (l * (o : G)) = (l * (o : G)) * g := by
    intro g hg
    have hfg : l⁻¹ * (g * (l * (o : G)) * g⁻¹) = o :=
      congrArg Subtype.val (ho ⟨g, hg⟩)
    have hy : g * (l * (o : G)) * g⁻¹ = l * o := by
      calc g * (l * (o : G)) * g⁻¹ = l * (l⁻¹ * (g * (l * (o : G)) * g⁻¹)) := by group
        _ = l * o := by rw [hfg]
    calc g * (l * (o : G)) = (g * (l * (o : G)) * g⁻¹) * g := by group
      _ = (l * o) * g := by rw [hy]
  have hyL : l * (o : G) ∈ L := L.mul_mem hl (Subgroup.map_subtype_le _ o.2)
  have hyC : l * (o : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun g hg => hcomm g hg
  have hl' : l = (l * (o : G)) * (o : G)⁻¹ := by group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyL, hyC⟩)
    (Subgroup.mem_sup_right (O.inv_mem o.2))

private theorem pgc_inf_centralizer_quot_facts {p : ℕ} (hp : p.Prime) {L P : Subgroup G}
    (hP : IsPGroup p P) (hPL : P ≤ centModSubgroup p L) :
    Nonempty ((↥(L ⊓ Subgroup.centralizer (P : Set G)) ⧸
      GLAPPrimeCore p ↥(L ⊓ Subgroup.centralizer (P : Set G))) ≃* PQuot p L) ∧
    GLAPPrimeCoreOf p (L ⊓ Subgroup.centralizer (P : Set G)) ≤ GLAPPrimeCoreOf p L := by
  obtain ⟨h1, h2⟩ := cover_facts hp inf_le_left (inf_centralizer_sup_eq_of_isPGroup hp hP hPL)
  exact ⟨h2, h1 ▸ inf_le_right⟩

private theorem pgc_isQuasisimple_quot_inf_centralizer {p : ℕ} (hp : p.Prime)
    {L P : Subgroup G} (hL : CFSG.Open.IsQuasisimple (PQuot p L)) (hP : IsPGroup p P)
    (hPL : P ≤ centModSubgroup p L) :
    CFSG.Open.IsQuasisimple (↥(L ⊓ Subgroup.centralizer (P : Set G)) ⧸
      GLAPPrimeCore p ↥(L ⊓ Subgroup.centralizer (P : Set G))) := by
  obtain ⟨⟨e⟩, -⟩ := pgc_inf_centralizer_quot_facts hp hP hPL
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hL

theorem glaPLayer_inf_centralizer_of_isPGroup {p : ℕ} (hp : p.Prime) {X L P : Subgroup G}
    (hL : GLAPComponent p X L) (hP : IsPGroup p P) (hPL : P ≤ centModSubgroup p L) :
    GLAPComponent p (L ⊓ Subgroup.centralizer (P : Set G))
        (GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G))) ∧
      (∀ J : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer (P : Set G)) J →
        J = GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G))) ∧
      L ⊓ Subgroup.centralizer (P : Set G) ≤
        Subgroup.normalizer (GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G)) : Set G) ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G)) ⊔ GLAPPrimeCoreOf p L = L ∧
      Nonempty (PQuot p (GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G))) ≃* PQuot p L) := by
  set Y := L ⊓ Subgroup.centralizer (P : Set G) with hY
  set I := GLAPLayer p Y with hI
  have hLq := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hYq := pgc_isQuasisimple_quot_inf_centralizer hp hLq hP hPL
  obtain ⟨⟨e⟩, hOY⟩ := pgc_inf_centralizer_quot_facts hp hP hPL
  obtain ⟨hIc, hall, hIbar⟩ := glaPLayer_of_isQuasisimple hYq
  have hIY : I ≤ Y := hIc.1
  have hsupY : I ⊔ GLAPPrimeCoreOf p Y = Y := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hIY hIbar
  have hnorm := le_normalizer_of_unique_glaPComponent hIc hall
  have hsupL : Y ⊔ GLAPPrimeCoreOf p L = L := inf_centralizer_sup_eq_of_isPGroup hp hP hPL
  refine ⟨hIc, hall, hnorm, ?_, ?_⟩
  · apply le_antisymm (sup_le (hIY.trans inf_le_left) (Subgroup.map_subtype_le _))
    calc L = Y ⊔ GLAPPrimeCoreOf p L := hsupL.symm
      _ = (I ⊔ GLAPPrimeCoreOf p Y) ⊔ GLAPPrimeCoreOf p L := by rw [hsupY]
      _ ≤ I ⊔ GLAPPrimeCoreOf p L := sup_le (sup_le le_sup_left (hOY.trans le_sup_right))
          le_sup_right
  · have e1 : PQuot p I ≃* ↥(barX p Y I) := quotEquivBarX hp hIY hIc.2.1
    rw [hIbar] at e1
    exact ⟨(e1.trans Subgroup.topEquiv).trans e⟩

theorem glaPLayer_le_of_isSubnormal {p : ℕ} (hp : p.Prime) {Y X : Subgroup G}
    (h : IsSubnormal Y X) : GLAPLayer p Y ≤ GLAPLayer p X := by
  unfold GLAPLayer
  refine sSup_le fun K hK => le_sSup ?_
  exact glaPComponent_of_isSubnormal' hp h hK

private theorem pgc_eq_bot_of_commutator_eq_self {p : ℕ} (hp : p.Prime)
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup p Q) (H : Subgroup Q)
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  by_contra hne
  have h := Group.IsSolvable.commutator_lt_of_ne_bot hne
  rw [hH] at h
  exact lt_irrefl _ h

private theorem pgc_isPGroup_quotient_sup {p : ℕ} {X P : Subgroup G}
    [(X.subgroupOf (X ⊔ P)).Normal] (hP : IsPGroup p P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) :
    IsPGroup p (↥(X ⊔ P) ⧸ X.subgroupOf (X ⊔ P)) := by
  set φ : ↥P →* (↥(X ⊔ P) ⧸ X.subgroupOf (X ⊔ P)) :=
    (QuotientGroup.mk' (X.subgroupOf (X ⊔ P))).comp (Subgroup.inclusion le_sup_right) with hφ
  refine hP.of_surjective φ ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    have ha : (a : G) ∈ ((P ⊔ X : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact a.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P X hPX] at ha
    obtain ⟨p', hp', x', hx', hpx⟩ := Set.mem_mul.mp ha
    refine ⟨⟨p', hp'⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show p'⁻¹ * (a : G) ∈ X
    rw [← hpx, inv_mul_cancel_left]
    exact hx'

private theorem pgc_le_of_glaPComponent_sup {p : ℕ} (hp : p.Prime) {X P K : Subgroup G}
    (hP : IsPGroup p P) (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hK : GLAPComponent p (X ⊔ P) K) : K ≤ X := by
  haveI : (X.subgroupOf (X ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hPX)
  have hQ : IsPGroup p (↥(X ⊔ P) ⧸ X.subgroupOf (X ⊔ P)) := pgc_isPGroup_quotient_sup hP hPX
  have hKa : ⁅K.subgroupOf (X ⊔ P), K.subgroupOf (X ⊔ P)⁆ = K.subgroupOf (X ⊔ P) := by
    rw [← CFSG.LocalAnalysis.GLTheoremB.subgroupOf_commutator hK.1 hK.1, glaPComponent_perfect hK]
  have hbot : (K.subgroupOf (X ⊔ P)).map (QuotientGroup.mk' (X.subgroupOf (X ⊔ P))) = ⊥ := by
    apply pgc_eq_bot_of_commutator_eq_self hp hQ
    rw [← Subgroup.map_commutator, hKa]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  have hkA : (⟨k, hK.1 hk⟩ : ↥(X ⊔ P)) ∈ K.subgroupOf (X ⊔ P) := Subgroup.mem_subgroupOf.2 hk
  exact Subgroup.mem_subgroupOf.1 (hbot hkA)

theorem glaPComponent_of_sup_isPGroup {p : ℕ} (hp : p.Prime) {X P K : Subgroup G}
    (hP : IsPGroup p P) (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hK : GLAPComponent p (X ⊔ P) K) : GLAPComponent p X K := by
  exact glaPComponent_of_le hp hK (pgc_le_of_glaPComponent_sup hp hP hPX hK) le_sup_left

private theorem pgc_conj_mem_centralizer {P : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) (hc : c ∈ Subgroup.centralizer (P : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hg hc ⊢
  intro s hs
  have hs1 : s * g = g * s := hg s hs
  have hs2 : s * c = c * s := hc s hs
  have h1 : g⁻¹ * s = s * g⁻¹ := by
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [hs1]
      _ = s * g⁻¹ := by group
  calc s * (g * c * g⁻¹) = (s * g) * c * g⁻¹ := by group
    _ = (g * s) * c * g⁻¹ := by rw [hs1]
    _ = g * (s * c) * g⁻¹ := by group
    _ = g * (c * s) * g⁻¹ := by rw [hs2]
    _ = (g * c) * (s * g⁻¹) := by group
    _ = (g * c) * (g⁻¹ * s) := by rw [h1]
    _ = (g * c * g⁻¹) * s := by group

private theorem pgc_isSubnormal_inf_centralizer {P X : Subgroup G}
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) :
    IsSubnormal (X ⊓ Subgroup.centralizer (P : Set G))
      ((X ⊔ P) ⊓ Subgroup.centralizer (P : Set G)) := by
  have hle : X ⊓ Subgroup.centralizer (P : Set G) ≤ (X ⊔ P) ⊓ Subgroup.centralizer (P : Set G) :=
    inf_le_inf_right _ le_sup_left
  have key : ∀ x ∈ (X ⊔ P) ⊓ Subgroup.centralizer (P : Set G),
      ∀ h ∈ X ⊓ Subgroup.centralizer (P : Set G),
        x * h * x⁻¹ ∈ X ⊓ Subgroup.centralizer (P : Set G) := by
    intro x hx h hh
    exact ⟨(Subgroup.mem_normalizer_iff.1 (sup_le Subgroup.le_normalizer hPX hx.1) h).1 hh.1,
      pgc_conj_mem_centralizer hx.2 hh.2⟩
  refine IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_)
    (IsSubnormal.refl _)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hgh => ?_⟩
  have h2 := key g⁻¹ (Subgroup.inv_mem _ hg) _ hgh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at h2
  exact h2

theorem glaPLayer_inf_centralizer_le {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt G p)
    {X P : Subgroup G} (hK : CFSG.Open.IsKGroup ↥(X ⊔ P)) (hP : IsPGroup p P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) :
    GLAPLayer p (X ⊓ Subgroup.centralizer (P : Set G)) ≤ GLAPLayer p X := by
  have hYX : GLAPLayer p (X ⊔ P) ≤ GLAPLayer p X := by
    unfold GLAPLayer
    refine sSup_le fun K hK' => le_sSup ?_
    exact glaPComponent_of_sup_isPGroup hp hP hPX hK'
  exact (glaPLayer_le_of_isSubnormal hp (pgc_isSubnormal_inf_centralizer hPX)).trans
    ((hLB (X ⊔ P) P hK le_sup_right hP).trans hYX)

end CFSG.LocalAnalysis.GLTheoremA
