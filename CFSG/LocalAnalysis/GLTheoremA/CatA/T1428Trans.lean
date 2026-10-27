module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem glaIsBmax_iff {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} :
    GLAIsBmax p B ↔ IsElemAbelian p B ∧ Nat.card B = p ^ GLATwoLocalRank p G ∧
      ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) :=
  Iff.rfl

section Generic

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isElemAbelian_subgroupOf_of {p : ℕ} {X E : Subgroup Γ} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact isElemAbelian_commute hE (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 _ (Subgroup.mem_subgroupOf.1 hx)

theorem card_subgroupOf_of_le {X E : Subgroup Γ} (hE : E ≤ X) :
    Nat.card (E.subgroupOf X) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv

theorem isPGroup_subgroupOf_of {p : ℕ} {X U : Subgroup Γ} (hU : IsPGroup p U) (hUX : U ≤ X) :
    IsPGroup p (U.subgroupOf X) :=
  IsPGroup.of_injective hU (Subgroup.subgroupOfEquivOfLe hUX).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hUX).injective

theorem isElemAbelian_map_of_injective {A : Type} [Group A] [Finite A] {p : ℕ} {f : A →* Γ}
    (hf : Function.Injective f) {E : Subgroup A} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, isElemAbelian_commute hE ha hb]
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    show f a ^ p = 1
    rw [← map_pow, hE.2 a ha, map_one]

theorem pRank_subgroupOf_eq {p : ℕ} {X B : Subgroup Γ} (hBX : B ≤ X) :
    CFSG.Open.pRank p (B.subgroupOf X) = CFSG.Open.pRank p B := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨E, hE, hel, hcard⟩
    refine ⟨E.map X.subtype, ?_, isElemAbelian_map_of_injective X.subtype_injective hel, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_subgroupOf.1 (hE he)
    · rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact hcard
  · rintro ⟨E, hE, hel, hcard⟩
    refine ⟨E.subgroupOf X, ?_, isElemAbelian_subgroupOf_of hel, ?_⟩
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hE (Subgroup.mem_subgroupOf.1 hx))
    · rw [card_subgroupOf_of_le (hE.trans hBX)]
      exact hcard

theorem mem_normalizer_subgroupOf_iff {X K : Subgroup Γ} (hK : K ≤ X) {b : Γ} (hb : b ∈ X) :
    (⟨b, hb⟩ : ↥X) ∈ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      b ∈ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ X
    · have h' := h ⟨g, hg⟩
      simpa [Subgroup.mem_subgroupOf] using h'
    · constructor
      · intro hgK
        exact absurd (hK hgK) hg
      · intro hbK
        exfalso
        apply hg
        have h1 : b⁻¹ * (b * g * b⁻¹) * b ∈ X :=
          X.mul_mem (X.mul_mem (X.inv_mem hb) (hK hbK)) hb
        have e : b⁻¹ * (b * g * b⁻¹) * b = g := by group
        rw [e] at h1
        exact h1
  · intro h g
    have h' := h g.1
    simpa [Subgroup.mem_subgroupOf] using h'

theorem le_normalizer_subgroupOf_iff {X B K : Subgroup Γ} (hB : B ≤ X) (hK : K ≤ X) :
    B.subgroupOf X ≤ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      B ≤ Subgroup.normalizer (K : Set Γ) := by
  constructor
  · intro h b hb
    have hb' : (⟨b, hB hb⟩ : ↥X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.2 hb
    exact (mem_normalizer_subgroupOf_iff hK (hB hb)).1 (h hb')
  · intro h x hx
    exact (mem_normalizer_subgroupOf_iff hK x.2).2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem glaIsBmax_subgroupOf {p : ℕ} {X B : Subgroup Γ} (h : S10.IsBmaxIn p X B) :
    GLAIsBmax p (B.subgroupOf X) := by
  obtain ⟨hBX, hel, hcard, U, hUX, hU0, hU2, hBU⟩ := h
  refine glaIsBmax_iff.2 ⟨isElemAbelian_subgroupOf_of hel, ?_, U.subgroupOf X, ?_,
    isPGroup_subgroupOf_of hU2 hUX, ?_⟩
  · rw [card_subgroupOf_of_le hBX]
    exact hcard
  · intro hbot
    apply hU0
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hUX] at hbot
    exact hbot
  · intro g hg
    exact (mem_normalizer_subgroupOf_iff hUX g.2).2 (hBU (Subgroup.mem_subgroupOf.1 hg))

theorem glaPComponent_top_of {p : ℕ} (hp : p.Prime) {X K : Subgroup Γ} (hK : GLAPComponent p X K) :
    GLAPComponent p (⊤ : Subgroup ↥X) (K.subgroupOf X) := by
  have h := glaPComponent_subgroupOf hp (le_refl X) hK
  rwa [Subgroup.subgroupOf_self] at h

theorem glaPComponent_inf_centralizer_subgroupOf {p : ℕ} (hp : p.Prime) {X K M : Subgroup Γ} {y : Γ}
    (hyX : y ∈ X) (hKX : K ≤ X) (hM : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Γ)) M) :
    GLAPComponent p (K.subgroupOf X ⊓ Subgroup.centralizer ({(⟨y, hyX⟩ : ↥X)} : Set ↥X))
      (M.subgroupOf X) := by
  have hXH : K ⊓ Subgroup.centralizer ({y} : Set Γ) ≤ X := inf_le_left.trans hKX
  have h := glaPComponent_subgroupOf hp hXH hM
  rwa [subgroupOf_inf_centralizer hyX] at h

theorem twoLocalRank_le_subgroup {p : ℕ} (hp : p.Prime) (X : Subgroup Γ) :
    GLATwoLocalRank p ↥X ≤ GLATwoLocalRank p Γ :=
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp X.subtype
    (Subgroup.subtype_injective X)

theorem isChevSimple_congr {r : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    IsChevSimple r S ↔ IsChevSimple r S' := by
  simp only [IsChevSimple, catalogIs_congr e]

theorem nonempty_centerQuot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem nonempty_pSimple_subgroupOf (p : ℕ) {X K : Subgroup Γ} (hK : K ≤ X) :
    Nonempty (PSimple p (K.subgroupOf X) ≃* PSimple p K) := by
  obtain ⟨e⟩ := nonempty_pQuot_equiv_subgroupOf p hK
  exact nonempty_centerQuot_of_equiv e

theorem glaMarking_congr_const {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (Q : CFSG.Assembly.LargeEvenLabel → Prop) :
    GLAMarking L (fun lab _ _ _ _ _ => Q lab) ↔ GLAMarking L' (fun lab _ _ _ _ _ => Q lab) := by
  have key : ∀ {A B : Type} [Group A] [Group B] (f : A ≃* B), commutator A = ⊤ → commutator B = ⊤ := by
    intro A B _ _ f h
    have hmap : (commutator A).map f.toMonoidHom = commutator B := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ f.surjective]
    rw [← hmap, h, Subgroup.map_top_of_surjective _ f.surjective]
  obtain ⟨ε⟩ := nonempty_centerQuot_of_equiv e
  have hθ : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R],
      (∃ _ : L ⧸ Subgroup.center L ≃* R, Q lab) ↔ (∃ _ : L' ⧸ Subgroup.center L' ≃* R, Q lab) := by
    intro lab R _
    constructor
    · rintro ⟨θ, hq⟩
      exact ⟨ε.symm.trans θ, hq⟩
    · rintro ⟨θ, hq⟩
      exact ⟨ε.trans θ, hq⟩
  have hraw : ∀ lab : CFSG.Assembly.LargeEvenLabel,
      CFSG.Assembly.LargeEvenRawDatum lab (fun R _ _ _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ _ : L ⧸ Subgroup.center L ≃* R, Q lab) ↔
      CFSG.Assembly.LargeEvenRawDatum lab (fun R _ _ _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ _ : L' ⧸ Subgroup.center L' ≃* R, Q lab) := by
    intro lab
    have hF : (fun (R : Type) [Group R] (_ _ : Set (MulAut R)) => IsSimpleGroup R ∧
        (∃ a b : R, a * b ≠ b * a) ∧ ∃ _ : L ⧸ Subgroup.center L ≃* R, Q lab) =
        (fun (R : Type) [Group R] (_ _ : Set (MulAut R)) => IsSimpleGroup R ∧
        (∃ a b : R, a * b ≠ b * a) ∧ ∃ _ : L' ⧸ Subgroup.center L' ≃* R, Q lab) := by
      funext R _ I F
      exact propext (and_congr Iff.rfl (and_congr Iff.rfl (hθ lab R)))
    rw [hF]
  constructor
  · rintro ⟨hc, lab, hl, hr⟩
    exact ⟨key e hc, lab, hl, (hraw lab).1 hr⟩
  · rintro ⟨hc, lab, hl, hr⟩
    exact ⟨key e.symm hc, lab, hl, (hraw lab).2 hr⟩

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
