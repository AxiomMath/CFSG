module

public import CFSG.LargeExtraspecial.BridgeConclusion
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LargeExtraspecial.S3Basic
import CFSG.Adapters.WholeGroupLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Bridge

open Subgroup CFSG.Open

theorem generalizedFitting_eq_timmesfeldFStar (H : Type*) [Group H] :
    CFSG.generalizedFitting H = timmesfeldFStar H :=
  (CFSG.Adapters.timmesfeldFStar_eq_foundations H).symm

section Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem Q_eq_timmesfeldFStar : S.Q = timmesfeldFStar S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CFSG.IsCharacteristicP 2 S.M := by
    change centralizer (CFSG.pCore 2 S.M : Set S.M) ≤ CFSG.pCore 2 S.M
    rw [← S.Q_eq_pCore]
    exact S.centralizer_le
  rw [S.Q_eq_pCore, ← (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore S.M 2).mp hchar,
    generalizedFitting_eq_timmesfeldFStar]

theorem timmesfeldIsExtraspecial_fstar :
    timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({S.z} : Set G))) := by
  rw [← Q_eq_timmesfeldFStar S]
  exact (timmesfeldIsExtraspecial_iff _).mpr S.extraspecial

theorem card_fstar :
    Nat.card (timmesfeldFStar (centralizer ({S.z} : Set G))) = 2 ^ (1 + 2 * S.width) := by
  rw [← Q_eq_timmesfeldFStar S]
  exact S.card_Q_eq

theorem width_eq_of_card {w : ℕ}
    (hw : Nat.card (timmesfeldFStar (centralizer ({S.z} : Set G))) = 2 ^ (1 + 2 * w)) :
    S.width = w := by
  rw [← Q_eq_timmesfeldFStar S] at hw
  exact S.width_eq hw

theorem quotientIso_Mbar :
    timmesfeldQuotientIso (timmesfeldFStar (centralizer ({S.z} : Set G))) S.Mbar := by
  rw [← Q_eq_timmesfeldFStar S, quotientIso_iff]
  exact ⟨S.quotientEquivMbar⟩

theorem nonempty_mulEquiv_Mbar {X : Type*} [Group X]
    (h : timmesfeldQuotientIso (timmesfeldFStar (centralizer ({S.z} : Set G))) X) :
    Nonempty (S.Mbar ≃* X) := by
  rw [← Q_eq_timmesfeldFStar S, quotientIso_iff] at h
  obtain ⟨f⟩ := h
  exact ⟨S.quotientEquivMbar.symm.trans f⟩

theorem finite_Mbar : Finite S.Mbar :=
  Finite.of_equiv _ S.quotientEquivMbar.toEquiv

theorem card_Mbar_lt : Nat.card S.Mbar < Nat.card G := by
  have h1 : Nat.card S.Mbar = Nat.card (S.M ⧸ S.Q) :=
    Nat.card_congr S.quotientEquivMbar.symm.toEquiv
  have h2 := S.Q.card_eq_card_quotient_mul_card_subgroup
  have h3 : 1 < Nat.card S.Q := by
    rw [S.card_Q_eq]
    exact Nat.one_lt_two_pow (by omega)
  have h4 : Nat.card S.M ≤ Nat.card G := Subgroup.card_le_card_group _
  have h5 : 0 < Nat.card (S.M ⧸ S.Q) := Nat.card_pos
  rw [h1]
  nlinarith

theorem card_lt_of_card_le_Mbar {X : Type*} (h : Nat.card X ≤ Nat.card S.Mbar) :
    Nat.card X < Nat.card G :=
  lt_of_le_of_lt h (card_Mbar_lt S)

theorem card_subgroup_Mbar_lt (K : Subgroup S.Mbar) : Nat.card K < Nat.card G := by
  have := finite_Mbar S
  exact card_lt_of_card_le_Mbar S (Subgroup.card_le_card_group K)

theorem card_quotient_lt (K : Subgroup S.Mbar) (N : Subgroup K) :
    Nat.card (K ⧸ N) < Nat.card G := by
  have := finite_Mbar S
  refine lt_of_le_of_lt ?_ (card_subgroup_Mbar_lt S K)
  rw [N.card_eq_card_quotient_mul_card_subgroup (α := K)]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem TimmesfeldAlt8.of_setting {Mbar : Type*} [Group Mbar] [Finite Mbar] {w : ℕ}
    (hs : IsSimpleGroup Mbar) (T : Setting Mbar)
    (h : (w = 16 ∧ T.width = 8 ∧
        Nonempty (T.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
      (w = 28 ∧ T.width = 16 ∧ Nonempty (T.Mbar ≃* timmesfeldOmegaPlus 6))) :
    TimmesfeldAlt8 w Mbar := by
  refine ⟨hs, T.z, T.orderOf_z, timmesfeldIsExtraspecial_fstar T, ?_⟩
  rcases h with ⟨h16, hT, ⟨f⟩⟩ | ⟨h28, hT, ⟨f⟩⟩
  · exact Or.inl ⟨h16, by rw [card_fstar T, hT], quotientIso_congr_right (quotientIso_Mbar T) f⟩
  · exact Or.inr ⟨h28, by rw [card_fstar T, hT], quotientIso_congr_right (quotientIso_Mbar T) f⟩

end Setting

section OfFStar

variable {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
  (hext : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G))))

theorem width_ofFStar {w : ℕ}
    (hw : Nat.card (timmesfeldFStar (centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w)) :
    (Setting.ofFStar z hz hext).width = w :=
  width_eq_of_card _ hw

theorem nonempty_mulEquiv_Mbar_ofFStar {Mbar : Type*} [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (centralizer ({z} : Set G))) Mbar) :
    Nonempty ((Setting.ofFStar z hz hext).Mbar ≃* Mbar) :=
  nonempty_mulEquiv_Mbar _ hMbar

end OfFStar

theorem mainFor_iff (G : Type) [Group G] [Finite G] :
    MainFor G ↔ ((∃ a b : G, a * b ≠ b * a) →
      ∀ S : Setting G, TimmesfeldConclusion G S.width S.Mbar) := by
  constructor
  · intro h hnonab S
    exact h hnonab S.z S.orderOf_z (timmesfeldIsExtraspecial_fstar S) S.width (card_fstar S)
      S.Mbar (quotientIso_Mbar S)
  · intro h hnonab z hz hext w hw Mbar _ hMbar
    let S := Setting.ofFStar z hz hext
    have hS := h hnonab S
    rw [width_eq_of_card S hw] at hS
    obtain ⟨e⟩ := nonempty_mulEquiv_Mbar S hMbar
    exact hS.of_mulEquiv_quotient e

theorem orderMainFor_iff (G : Type) [Group G] [Finite G] :
    OrderMainFor G ↔ ((∃ a b : G, a * b ≠ b * a) →
      ∀ S : Setting G, TimmesfeldOrderConclusion G S.width S.Mbar) := by
  constructor
  · intro h hnonab S
    exact h hnonab S.z S.orderOf_z (timmesfeldIsExtraspecial_fstar S) S.width (card_fstar S)
      S.Mbar (quotientIso_Mbar S)
  · intro h hnonab z hz hext w hw Mbar _ hMbar
    let S := Setting.ofFStar z hz hext
    have hS := h hnonab S
    rw [width_eq_of_card S hw] at hS
    obtain ⟨e⟩ := nonempty_mulEquiv_Mbar S hMbar
    exact hS.of_mulEquiv_quotient e

theorem mainStatement_of_setting
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ S : Setting G, TimmesfeldConclusion G S.width S.Mbar) :
    MainStatement :=
  fun G _ _ _ => (mainFor_iff G).mpr (h G)

theorem mainStatement_of_step
    (step : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], Nat.card H < Nat.card G →
        MainFor H) → MainFor G) :
    MainStatement := by
  suffices h : ∀ (n : ℕ) (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      Nat.card G = n → MainFor G from
    fun G _ _ _ => h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn
    exact step G fun H _ _ _ hlt => ih _ (hn ▸ hlt) H rfl

theorem mainStatement_of_setting_step
    (step : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], Nat.card H < Nat.card G →
        (∃ a b : H, a * b ≠ b * a) → ∀ T : Setting H, TimmesfeldConclusion H T.width T.Mbar) →
      (∃ a b : G, a * b ≠ b * a) → ∀ S : Setting G, TimmesfeldConclusion G S.width S.Mbar) :
    MainStatement :=
  mainStatement_of_step fun G _ _ _ ih =>
    (mainFor_iff G).mpr (step G fun H _ _ _ hlt => (mainFor_iff H).mp (ih H hlt))

section Sections

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem ih_subgroup {P : ∀ (H : Type) [Group H], Prop}
    (ih : ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], Nat.card H < Nat.card G → P H)
    (K : Subgroup S.Mbar) [IsSimpleGroup K] : P K := by
  have := finite_Mbar S
  exact ih K (card_subgroup_Mbar_lt S K)

theorem ih_quotient {P : ∀ (H : Type) [Group H], Prop}
    (ih : ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], Nat.card H < Nat.card G → P H)
    (K : Subgroup S.Mbar) (N : Subgroup K) [N.Normal] [IsSimpleGroup (K ⧸ N)] : P (K ⧸ N) := by
  have := finite_Mbar S
  exact ih (K ⧸ N) (card_quotient_lt S K N)

end Sections

end CFSG.LargeExtraspecial.Bridge
