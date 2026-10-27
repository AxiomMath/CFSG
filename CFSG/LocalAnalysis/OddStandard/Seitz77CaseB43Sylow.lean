module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Diag
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Main

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section RadInAlg

variable {G : Type} [Group G] {k : Type} [Field k] {A₁ : Subgroup G} {e : ↥A₁ ≃* ↥(unipAll k)}

theorem radIn_sup (E F : Subgroup ↥(unipAll k)) :
    radIn A₁ e (E ⊔ F) = radIn A₁ e E ⊔ radIn A₁ e F :=
  Subgroup.map_sup _ _ _

theorem radIn_top : radIn A₁ e ⊤ = A₁ := by
  ext x
  constructor
  · exact fun hx => radIn_le hx
  · intro hx
    exact mem_radIn.mpr ⟨⟨x, hx⟩, trivial, rfl⟩

end RadInAlg

namespace SwapPair

variable {G : Type} [Group G] {A B : Subgroup G} {t : G} (P : SwapPair A B t)

include P

theorem B_eq : B = cs t A := by
  refine le_antisymm (fun y hy => ?_) (P.cs_le le_rfl)
  rw [mem_cs, P.t_inv]
  have := P.swap₂ y hy
  rwa [P.t_inv] at this

end SwapPair

section Sylow43

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {d : Datum A}
  {c : CaseB A R d.t} {R' M₁ M₂ S A₁ B₁ : Subgroup G} {k : Type} [Field k]
  {e : ↥A₁ ≃* ↥(unipAll k)}

theorem SylowB.swapPair (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) : SwapPair A₁ B₁ d.t where
  t_sq := c.t_mul_self
  comm := Sy.comm
  inf_eq := Sy.inf_eq
  swap₁ := Sy.swap₁
  swap₂ := Sy.swap₂

theorem SylowB.S_eq_sup (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) :
    S = (radIn A₁ e (radOne k) ⊔ cs d.t (radIn A₁ e (radOne k))) ⊔
      (radIn A₁ e (radTwo k) ⊔ cs d.t (radIn A₁ e (radTwo k))) := by
  have P := Sy.swapPair
  have h1 : radIn A₁ e (radOne k) ⊔ radIn A₁ e (radTwo k) = A₁ := by
    rw [← radIn_sup, radOne_sup_radTwo, radIn_top]
  have h2 : cs d.t (radIn A₁ e (radOne k)) ⊔ cs d.t (radIn A₁ e (radTwo k)) = B₁ := by
    rw [← cs_sup, ← radIn_sup, radOne_sup_radTwo, radIn_top, P.B_eq]
  rw [Sy.prod, sup_sup_sup_comm, h1, h2]

theorem SylowB.W_eq_of_diag (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) {R'' : Subgroup G}
    (c'' : CaseB A R'' d.t) {E₀ : Subgroup ↥(unipAll k)} (hE : E₀ = radOne k ∨ E₀ = radTwo k)
    (hdiag : ∀ v, v ∈ R'' ↔ ∃ a : ↥A₁, e a ∈ E₀ ∧ v = (a : G) * (d.t * a * d.t⁻¹)) :
    c''.W = radIn A₁ e E₀ ⊔ cs d.t (radIn A₁ e E₀) := by
  have hk := Sy.card_k
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨hsq, hcomm, hcard⟩ := rad_facts hk hE
  have P := Sy.swapPair
  have hXA : radIn A₁ e E₀ ≤ A₁ := radIn_le
  have hXe : IsElemAbelian 2 (radIn A₁ e E₀) :=
    isElemAbelian_of_forall_two (fun x hx y hy => radIn_comm hcomm hx hy)
      (fun x hx => radIn_mul_self hsq hx)
  have hR : ∀ v, v ∈ R'' ↔ ∃ a ∈ radIn A₁ e E₀, v = a * (d.t * a * d.t⁻¹) := by
    intro v
    rw [hdiag v]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, mem_radIn.mpr ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨a', ha', rfl⟩ := mem_radIn.mp ha
      exact ⟨a', ha', rfl⟩
  obtain ⟨hDe, hDcard, -, hDC, hDt, hDcomm⟩ := P.diag_facts hXA hXe hR
  have hXcard : Nat.card (radIn A₁ e E₀) = 16 := by rw [card_radIn, hcard]
  have hD8 : Nat.card ↥(radIn A₁ e E₀ ⊔ cs d.t (radIn A₁ e E₀)) = 2 ^ 8 := by
    rw [hDcard, hXcard]
    norm_num
  exact (c''.H.eq_W_of_elem hDC hDe hD8 hDt hDcomm).symm

theorem SylowB.hdiag_R (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) (hRV : R ≤ d.V) (v : G) :
    v ∈ R ↔ ∃ a : ↥A₁, e a ∈ radOne k ∧ v = (a : G) * (d.t * a * d.t⁻¹) := by
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := (Sy.V_diag v).mp (hRV hv)
    exact ⟨⟨a, ha⟩, (Sy.R_coord ⟨a, ha⟩).mp hv, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (Sy.R_coord a).mpr ha

theorem SylowB.hdiag_R' (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) (hR'V : R' ≤ d.V) (v : G) :
    v ∈ R' ↔ ∃ a : ↥A₁, e a ∈ radTwo k ∧ v = (a : G) * (d.t * a * d.t⁻¹) := by
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := (Sy.V_diag v).mp (hR'V hv)
    exact ⟨⟨a, ha⟩, (Sy.R'_coord ⟨a, ha⟩).mp hv, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (Sy.R'_coord a).mpr ha

theorem SylowB.S_eq_W_sup (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) (hRV : R ≤ d.V) (hR'V : R' ≤ d.V)
    (c' : CaseB A R' d.t) : S = c.W ⊔ c'.W := by
  rw [Sy.S_eq_sup, ← Sy.W_eq_of_diag c (Or.inl rfl) (Sy.hdiag_R hRV),
    ← Sy.W_eq_of_diag c' (Or.inr rfl) (Sy.hdiag_R' hR'V)]

theorem SylowB.W_eq (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) (hRV : R ≤ d.V) :
    c.W = radIn A₁ e (radOne k) ⊔ cs d.t (radIn A₁ e (radOne k)) :=
  Sy.W_eq_of_diag c (Or.inl rfl) (Sy.hdiag_R hRV)

theorem SylowB.W'_eq (Sy : SylowB c R' M₁ M₂ S A₁ B₁ e) (hR'V : R' ≤ d.V)
    (c' : CaseB A R' d.t) :
    c'.W = radIn A₁ e (radTwo k) ⊔ cs d.t (radIn A₁ e (radTwo k)) :=
  Sy.W_eq_of_diag c' (Or.inr rfl) (Sy.hdiag_R' hR'V)

end Sylow43

theorem sylowB_eq_of_two {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
    {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t}
    {M₁ M₂ S A₁ B₁ N₁ N₂ S' A₁' B₁' : Subgroup G} {k k' : Type} [Field k] [Field k']
    {e : ↥A₁ ≃* ↥(unipAll k)} {e' : ↥A₁' ≃* ↥(unipAll k')}
    (Sy : SylowB c₁ V₂ M₁ M₂ S A₁ B₁ e) (Sy' : SylowB c₂ V₁ N₁ N₂ S' A₁' B₁' e')
    (hV₁ : V₁ ≤ d.V) (hV₂ : V₂ ≤ d.V) : S = S' := by
  rw [Sy.S_eq_W_sup hV₁ hV₂ c₂, Sy'.S_eq_W_sup hV₂ hV₁ c₁, sup_comm]

end CFSG.OddStandard.Seitz77
