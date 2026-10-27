module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4X1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SH2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Y6bPData (c : Ctx5 G L) (P : Subgroup G) : Prop :=
  y6bT3 c ≤ P ∧ P ≤ y6bX c ∧ Nat.card ↥P = 2 * Nat.card ↥(y6bT3 c) ∧
    Nat.card ↥(y6bT3 c) = 2 ^ 11

theorem y6b_normal_of_card {P T : Subgroup G} (hTP : T ≤ P) (hP : Nat.card ↥P = 2 * Nat.card ↥T) :
    ∀ x ∈ P, ∀ y ∈ T, x * y * x⁻¹ ∈ T := by
  let T' : Subgroup ↥P := T.subgroupOf P
  haveI : Nonempty ↥T' := Set.nonempty_coe_sort.mpr (Subgroup.coe_nonempty T')
  have hcard : Nat.card ↥T' = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  have hindex : T'.index = 2 := by
    have h : Nat.card ↥T' * T'.index = Nat.card ↥T' * 2 := by
      calc Nat.card ↥T' * T'.index = Nat.card ↥P := Subgroup.card_mul_index T'
        _ = 2 * Nat.card ↥T := hP
        _ = Nat.card ↥T * 2 := Nat.mul_comm _ _
        _ = Nat.card ↥T' * 2 := by rw [hcard]
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥T')) h
  have hnormal : T'.Normal := Subgroup.normal_of_index_eq_two hindex
  intro x hx y hy
  have hmem : (⟨x, hx⟩ : ↥P) * ⟨y, hTP hy⟩ * (⟨x, hx⟩ : ↥P)⁻¹ ∈ T' :=
    hnormal.conj_mem ⟨y, hTP hy⟩ (show (⟨y, hTP hy⟩ : ↥P) ∈ T' from hy) ⟨x, hx⟩
  exact hmem

theorem y6b_card_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) :
    Nat.card ↥(y6bX c) = 16 * Nat.card ↥(y6bX c ⊓ c.s.H) := by
  letI : MulAction ↥(y6bX c) G :=
    { smul := fun x g => (x : G) * g * (x : G)⁻¹
      mul_smul := by
        intro x y g
        change (↑(x * y) : G) * g * (↑(x * y))⁻¹
          = (↑x : G) * ((↑y : G) * g * (↑y : G)⁻¹) * (↑x : G)⁻¹
        rw [Subgroup.coe_mul]
        group
      one_smul := by
        intro g
        change (↑(1 : ↥(y6bX c)) : G) * g * (↑(1 : ↥(y6bX c)) : G)⁻¹ = g
        simp }
  have hsmul : ∀ (x : ↥(y6bX c)) (g : G), x • g = (x : G) * g * (x : G)⁻¹ :=
    fun _ _ => rfl
  have horb_eq : MulAction.orbit ↥(y6bX c) c.s.t =
      (fun e : G => e * c.s.t) '' ((y6bE16 c : Subgroup G) : Set G) := by
    ext g
    constructor
    · intro hg
      rw [MulAction.mem_orbit_iff] at hg
      obtain ⟨x, hx⟩ := hg
      obtain ⟨e, he, heq⟩ := y6b_X_conj_t c hH hF hRT x x.2
      exact ⟨e, he, by rw [← hx, hsmul x c.s.t]; exact heq.symm⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, hxX, hx⟩ := y6b_conj_t_surj c hH hF hRT h1 e he
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨x, hxX⟩, by rw [hsmul ⟨x, hxX⟩ c.s.t]; exact hx⟩
  have horb_card : (MulAction.orbit ↥(y6bX c) c.s.t).ncard = 16 := by
    rw [horb_eq, Set.ncard_image_of_injective _ (mul_left_injective c.s.t),
      ← Nat.card_coe_set_eq]
    exact y6b_card_E16 c hH hRT
  have hstab : MulAction.stabilizer ↥(y6bX c) c.s.t =
      (y6bX c ⊓ c.s.H).subgroupOf (y6bX c) := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hx' : (x : G) * c.s.t * (x : G)⁻¹ = c.s.t := by
        simpa only [hsmul x c.s.t] using hx
      have hxt : (x : G) * c.s.t = c.s.t * (x : G) := by
        calc (x : G) * c.s.t = (x : G) * c.s.t * (x : G)⁻¹ * (x : G) := by group
          _ = c.s.t * (x : G) := by rw [hx']
      exact hxt.symm
    · rintro ⟨-, hxH⟩
      have hxt : c.s.t * (x : G) = (x : G) * c.s.t :=
        Subgroup.mem_centralizer_iff.mp hxH c.s.t (Set.mem_singleton c.s.t)
      show (x : G) * c.s.t * (x : G)⁻¹ = c.s.t
      rw [← hxt]
      group
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥(y6bX c) c.s.t) =
      Nat.card ↥(y6bX c ⊓ c.s.H) := by
    rw [hstab]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : y6bX c ⊓ c.s.H ≤ y6bX c)).toEquiv
  have hidx : (MulAction.stabilizer ↥(y6bX c) c.s.t).index = 16 := by
    rw [MulAction.index_stabilizer (G := ↥(y6bX c)) (X := G), horb_card]
  have hmul := Subgroup.index_mul_card (H := MulAction.stabilizer ↥(y6bX c) c.s.t)
  rw [hidx, hstabcard] at hmul
  exact hmul.symm

theorem y6b_exists_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) (hT3c : Nat.card ↥(y6bT3 c) = 2 ^ 11) :
    ∃ P : Subgroup G, Y6bPData c P := by
  have hT_le_X : c.s.T ≤ y6bX c := y6b_T_le_X c hH hRT
  have hT_le_H : c.s.T ≤ c.s.H := c.s.sylow_T.1
  have hT_le_Q : c.s.T ≤ y6bX c ⊓ c.s.H := by
    intro x hx
    exact ⟨hT_le_X hx, hT_le_H hx⟩
  have hTcard : Nat.card ↥c.s.T = 256 := (y6_card_T hH).2 hRT
  have hrelmul := Subgroup.relIndex_mul_relIndex (H := c.s.T) (K := y6bX c ⊓ c.s.H)
    (L := c.s.H) hT_le_Q inf_le_right
  have hnotdvd : ¬ 2 ∣ c.s.T.relIndex (y6bX c ⊓ c.s.H) := by
    intro h2
    have hdvd : 2 ∣ c.s.T.relIndex (y6bX c ⊓ c.s.H) *
        (y6bX c ⊓ c.s.H).relIndex c.s.H := dvd_mul_of_dvd_left h2 _
    rw [hrelmul] at hdvd
    exact c.s.sylow_T.2.2 hdvd
  have hQcard : Nat.card ↥(y6bX c ⊓ c.s.H) =
      c.s.T.relIndex (y6bX c ⊓ c.s.H) * 256 := by
    have h := Subgroup.relIndex_mul_card (H := c.s.T) (K := y6bX c ⊓ c.s.H)
    rw [inf_of_le_left hT_le_Q, hTcard] at h
    exact h.symm
  haveI : Nonempty ↥(y6bX c ⊓ c.s.H) :=
    Set.nonempty_coe_sort.mpr (Subgroup.coe_nonempty _)
  have hrel_ne : c.s.T.relIndex (y6bX c ⊓ c.s.H) ≠ 0 := by
    intro h0
    have hpos : 0 < Nat.card ↥(y6bX c ⊓ c.s.H) := Nat.card_pos
    rw [hQcard, h0, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hXcard : Nat.card ↥(y6bX c) = 2 ^ 12 * c.s.T.relIndex (y6bX c ⊓ c.s.H) := by
    rw [y6b_card_X c hH hF hRT h1, hQcard]
    ring
  have hfact : Nat.factorization (Nat.card ↥(y6bX c)) 2 = 12 := by
    rw [hXcard, Nat.factorization_mul (pow_ne_zero 12 (by norm_num)) hrel_ne]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self (p := 2) (n := 12) (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]
  let T3X : Subgroup ↥(y6bX c) := (y6bT3 c).subgroupOf (y6bX c)
  have hT3_le_X : y6bT3 c ≤ y6bX c := y6b_T3_le_X c hH hF hRT
  have hT3X_card : Nat.card ↥T3X = 2 ^ 11 := by
    change Nat.card ↥((y6bT3 c).subgroupOf (y6bX c)) = 2 ^ 11
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT3_le_X).toEquiv]
    exact hT3c
  have hT3X_P : IsPGroup 2 ↥T3X := IsPGroup.of_card (p := 2) (n := 11) hT3X_card
  obtain ⟨P', hT3X_le_P'⟩ := hT3X_P.exists_le_sylow
  have hP'card : Nat.card P' = 2 ^ 12 := by
    rw [Sylow.card_eq_multiplicity (P := P'), hfact]
  refine ⟨(P' : Subgroup ↥(y6bX c)).map (y6bX c).subtype, ?_, ?_, ?_, hT3c⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hT3_le_X]
    exact Subgroup.map_mono hT3X_le_P'
  · exact Subgroup.map_subtype_le (P' : Subgroup ↥(y6bX c))
  · have hcard := Subgroup.card_subtype (y6bX c) (P' : Subgroup ↥(y6bX c))
    rw [hcard, hP'card, hT3c]
    norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
