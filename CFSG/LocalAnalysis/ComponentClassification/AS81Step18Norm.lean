module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fusion
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_closureIn_eq_top {A N : Subgroup G} (hAN : A ≤ N)
    (hA : commutator ↥A = ⊤) : commutator ↥(closureIn A N) = ⊤ := by
  let eA : ↥(A.subgroupOf N) ≃* ↥A := subgroupOfEquivOfLe hAN
  let eL : ↥(closureIn A N) ≃* ↥(rankTwoX (A.subgroupOf N)) :=
    ((rankTwoX _).equivMapOfInjective _ N.subtype_injective).symm
  exact commutator_eq_top_of_mulEquiv eL.symm
    (commutator_rankTwoX_eq_top (commutator_eq_top_of_mulEquiv eA.symm hA))

omit [Finite G] in
theorem closureIn_cases {A N : Subgroup G} (h : L34Conclusion (A.subgroupOf N)) :
    (Nonempty (↥(closureIn A N) ⧸ center ↥(closureIn A N) ≃* Blueprint.NativeSporadic.Suz) ∧
        Nat.card (center ↥(closureIn A N)) ∣ 3) ∨
      Nonempty (↥(closureIn A N) ≃* Blueprint.NativeSporadic.He) := by
  let eL : ↥(closureIn A N) ≃* ↥(rankTwoX (A.subgroupOf N)) :=
    ((rankTwoX _).equivMapOfInjective _ N.subtype_injective).symm
  rcases h with ⟨⟨eSuz⟩, hZ3⟩ | ⟨-, ⟨eHe⟩⟩
  · refine Or.inl ⟨⟨(QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eSuz⟩, ?_⟩
    rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv]
    exact hZ3
  · exact Or.inr ⟨eL.trans eHe⟩

omit [Finite G] in
theorem exists_mul_ne_of_isQuasisimple {A : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A) :
    ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hZ : center ↥A = ⊤ := eq_top_iff.mpr fun x _ =>
    mem_center_iff.mpr fun y => Subtype.ext (hcon y y.2 x x.2)
  have : Nontrivial (↥A ⧸ center ↥A) := hq.2.toNontrivial
  obtain ⟨u, hu⟩ := exists_ne (1 : ↥A ⧸ center ↥A)
  apply hu
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
  rw [QuotientGroup.eq_one_iff, hZ]
  exact mem_top a

omit [Finite G] in
theorem isQuasisimple_closureIn
    {A N : Subgroup G} (hAN : A ≤ N) (hq : CFSG.Open.IsQuasisimple ↥A)
    (h : L34Conclusion (A.subgroupOf N)) : CFSG.Open.IsQuasisimple ↥(closureIn A N) := by
  refine ⟨commutator_closureIn_eq_top hAN hq.1, ?_⟩
  rcases closureIn_cases h with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Suz.isSimpleGroup_Suz e
  · have hs : IsSimpleGroup ↥(closureIn A N) :=
      @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He e
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_ne_of_isQuasisimple hq
    have hZ : center ↥(closureIn A N) = ⊥ :=
      RankThree.PartTwo.Sec21.center_eq_bot_of_simple ⟨⟨a, le_closureIn hAN ha⟩,
        ⟨b, le_closureIn hAN hb⟩, fun h => hab (congrArg Subtype.val h)⟩
    exact @MulEquiv.isSimpleGroup _ _ _ _ hs
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

omit [Finite G] in
theorem le_of_normal_of_isQuasisimple {L K : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hKL : K ≤ L) (hn : L ≤ normalizer (K : Set G)) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a * b ≠ b * a) : L ≤ K := by
  have hKn : (K.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr hn
  rcases quasisimple_normal_le_center_or_eq_top hq hKn with h | h
  · exfalso
    have hz : (⟨a, hKL ha⟩ : ↥L) ∈ center ↥L := h (mem_subgroupOf.mpr ha)
    exact hab (congrArg Subtype.val (mem_center_iff.mp hz ⟨b, hKL hb⟩)).symm
  · exact subgroupOf_eq_top.mp h

omit [Finite G] in
theorem card_eq_of_suz {L : Subgroup G}
    (e : ↥L ⧸ center ↥L ≃* Blueprint.NativeSporadic.Suz) :
    Nat.card L = 448345497600 * Nat.card (centerIn L) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), Nat.card_congr e.toEquiv,
    Sporadic.Suz.card_Suz, centerIn_eq_map_center', card_map_of_injective L.subtype_injective]

theorem closureIn_eq_of_le
    {A N₁ N₂ : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A) (hA₁ : A ≤ N₁) (hA₂ : A ≤ N₂)
    (hle : closureIn A N₂ ≤ N₁) (h₁ : L34Conclusion (A.subgroupOf N₁))
    (h₂ : L34Conclusion (A.subgroupOf N₂)) : closureIn A N₂ = closureIn A N₁ := by
  set L₁ := closureIn A N₁ with hL₁
  set L₂ := closureIn A N₂ with hL₂
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_ne_of_isQuasisimple hq
  have hAL₁ : A ≤ L₁ := le_closureIn hA₁
  have hAL₂ : A ≤ L₂ := le_closureIn hA₂
  have hq₁ := isQuasisimple_closureIn hA₁ hq h₁
  have hq₂ := isQuasisimple_closureIn hA₂ hq h₂
  have hL₂N : L₂ ≤ normalizer (L₁ : Set G) := hle.trans (le_normalizer_closureIn A N₁)
  have h21 : L₂ ≤ L₁ := by
    have hn : L₂ ≤ normalizer ((L₁ ⊓ L₂ : Subgroup G) : Set G) := fun x hx => by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hL₂N hx) y,
        mem_normalizer_iff.mp (le_normalizer hx) y]
    have h := le_of_normal_of_isQuasisimple hq₂ (inf_le_right : L₁ ⊓ L₂ ≤ L₂) hn
      ⟨hAL₁ ha, hAL₂ ha⟩ ⟨hAL₁ hb, hAL₂ hb⟩ hab
    exact h.trans inf_le_left
  have hdvd := Subgroup.card_dvd_of_le h21
  rcases closureIn_cases h₁ with ⟨⟨e₁⟩, hZ₁⟩ | ⟨⟨e₁⟩⟩ <;>
    rcases closureIn_cases h₂ with ⟨⟨e₂⟩, hZ₂⟩ | ⟨⟨e₂⟩⟩
  ·
    have hc₁ := card_eq_of_suz e₁
    have hc₂ := card_eq_of_suz e₂
    set Z := centerIn L₁ with hZ
    have hZC : Z ≤ centralizer (L₂ : Set G) := fun x hx =>
      mem_centralizer_iff.mpr fun y hy => mem_centralizer_iff.mp hx.2 y (h21 hy)
    have hZN : Z ≤ normalizer (L₂ : Set G) := hZC.trans (centralizer_le_normalizer _)
    have hprod := card_sup_mul_card_inf hZN
    have hinf : L₂ ⊓ Z ≤ centerIn L₂ := fun x hx =>
      ⟨hx.1, mem_centralizer_iff.mpr fun y hy => (mem_centralizer_iff.mp (hZC hx.2) y hy)⟩
    have hle₁ : Nat.card ↥(L₂ ⊓ Z) ≤ Nat.card (centerIn L₂) := card_le_of_le hinf
    have hsup : L₂ ⊔ Z ≤ L₁ := sup_le h21 inf_le_left
    have hpos : 0 < Nat.card (centerIn L₂) := Nat.card_pos
    have hge : Nat.card L₁ ≤ Nat.card ↥(L₂ ⊔ Z) := by
      have h3 : Nat.card ↥(L₂ ⊔ Z) * Nat.card (centerIn L₂) ≥
          Nat.card L₁ * Nat.card (centerIn L₂) := by
        calc Nat.card ↥(L₂ ⊔ Z) * Nat.card (centerIn L₂)
            ≥ Nat.card ↥(L₂ ⊔ Z) * Nat.card ↥(L₂ ⊓ Z) := Nat.mul_le_mul_left _ hle₁
          _ = Nat.card L₂ * Nat.card Z := hprod
          _ = Nat.card L₁ * Nat.card (centerIn L₂) := by rw [hc₁, hc₂]; ring
      exact Nat.le_of_mul_le_mul_right h3 hpos
    have heq : L₂ ⊔ Z = L₁ := eq_of_le_of_card_ge hsup hge
    have hL₁N : L₁ ≤ normalizer (L₂ : Set G) := heq ▸ sup_le le_normalizer hZN
    exact le_antisymm h21 (le_of_normal_of_isQuasisimple hq₁ h21 hL₁N (hAL₂ ha) (hAL₂ hb) hab)
  ·
    exfalso
    rw [card_eq_of_suz e₁, Nat.card_congr e₂.toEquiv, Sporadic.He.card_He] at hdvd
    have h3 : Nat.card (centerIn L₁) ∣ 3 := by
      rwa [centerIn_eq_map_center', card_map_of_injective L₁.subtype_injective]
    have hle3 := Nat.le_of_dvd (by norm_num) h3
    have hpos : 0 < Nat.card (centerIn L₁) := Nat.card_pos
    interval_cases (Nat.card (centerIn L₁)) <;> norm_num at hdvd
  ·
    exfalso
    rw [card_eq_of_suz e₂, Nat.card_congr e₁.toEquiv, Sporadic.He.card_He] at hdvd
    exact absurd ((Dvd.intro _ rfl).trans hdvd) (by norm_num)
  ·
    refine eq_of_le_of_card_ge h21 ?_
    rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem normalizer_le_normalizer_closureIn (h4 : AS76b.Asc75Theorem4)
    (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hbelow : L34GeneralBelow (Nat.card G)) {z : G} (hzE : z ∈ E)
    (hW : AS76b.oddCoreIn (centralizer ({z} : Set G)) ≠ ⊥)
    (hLW : L34Conclusion
      (A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)))) :
    normalizer (A : Set G) ≤ normalizer
      (closureIn A (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)) : Set G) := by
  have hstd := hF.base.hyp.standard
  set K := centralizer (A : Set G) with hKdef
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  set X := AS76b.oddCoreIn K with hXdef
  obtain ⟨hWX, hX⟩ := oddCoreIn_centralizer_le_of_frame h4 h34 hF hL hzE
  have hX1 : X ≠ ⊥ := fun h => hW (le_bot_iff.mp (h ▸ hWX))
  obtain ⟨-, hAX, hLX⟩ := step17_of h4 h34 hE16 G A R g E F hF hL hbelow X hX hX1
  have hACX : A ≤ centralizer (X : Set G) := le_centralizer_iff.mp (AS76b.oddCoreIn_le K)
  have hAW : A ≤ normalizer (W : Set G) :=
    (hACX.trans (centralizer_le hWX)).trans (centralizer_le_normalizer _)
  have hle : closureIn A (normalizer (X : Set G)) ≤ normalizer (W : Set G) :=
    ((closureIn_le_centralizer hACX).trans (centralizer_le hWX)).trans
      (centralizer_le_normalizer _)
  have heq := closureIn_eq_of_le hstd.1 hAW hAX hle hLW hLX
  rw [← heq]
  intro n hn
  refine le_normalizer_closureIn A _ (AS76b.normalizer_le_normalizer_oddCoreIn K ?_)
  rw [AS76b.normalizer_centralizer_eq hstd]
  exact hn

end CFSG.ComponentClassification.AS81
