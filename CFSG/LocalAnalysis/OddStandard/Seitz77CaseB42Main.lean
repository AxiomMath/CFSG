module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Sylow
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42A1
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Torus

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem Radicals.symm_B42 {G : Type*} [Group G] {V V₁ V₂ : Subgroup G} (h : Radicals V V₁ V₂) :
    Radicals V V₂ V₁ where
  le₁ := h.le₂
  le₂ := h.le₁
  normal₁ := h.normal₂
  normal₂ := h.normal₁
  elem₁ := h.elem₂
  elem₂ := h.elem₁
  card₁ := h.card₂
  card₂ := h.card₁
  inf_eq := by rw [inf_comm]; exact h.inf_eq
  sup_eq := by rw [sup_comm]; exact h.sup_eq
  card_center := h.card_center
  le_of_elem := fun E hE he => (h.le_of_elem E hE he).symm
  eq_of_card := fun E hE he hc => (h.eq_of_card E hE he hc).symm
  le_of_sq := fun x hx hx2 => (h.le_of_sq x hx hx2).symm

structure SylowB {G : Type} [Group G] [Finite G] {A R : Subgroup G} {d : Datum A}
    (c : CaseB A R d.t) (R' M₁ M₂ S₀ A₁ B₁ : Subgroup G) {k : Type} [Field k]
    (e : ↥A₁ ≃* ↥(unipAll k)) : Prop where
  card_k : Nat.card k = 4
  S₀_sylow : IsSylowOf 2 S₀ c.Ninf
  V_le : d.V ≤ S₀
  W_le : c.W ≤ S₀
  A₁_eq : A₁ = S₀ ⊓ M₁
  B₁_eq : B₁ = S₀ ⊓ M₂
  prod : S₀ = A₁ ⊔ B₁
  inf_eq : A₁ ⊓ B₁ = ⊥
  comm : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a
  swap₁ : ∀ x ∈ A₁, d.t * x * d.t⁻¹ ∈ B₁
  swap₂ : ∀ x ∈ B₁, d.t * x * d.t⁻¹ ∈ A₁
  V_eq : d.V = S₀ ⊓ centralizer ({d.t} : Set G)
  V_diag : ∀ v : G, v ∈ d.V ↔ ∃ a ∈ A₁, v = a * (d.t * a * d.t⁻¹)
  W_coord : ∀ a : ↥A₁, (a : G) ∈ c.W ↔ e a ∈ radOne k
  R_coord : ∀ a : ↥A₁, (a : G) * (d.t * a * d.t⁻¹) ∈ R ↔ e a ∈ radOne k
  R'_coord : ∀ a : ↥A₁, (a : G) * (d.t * a * d.t⁻¹) ∈ R' ↔ e a ∈ radTwo k
  A1 : ∀ s ∈ S₀, ¬ IsConj d.t s
  torus : ∃ x : G, x ∈ M₁ ∧ Odd (orderOf x) ∧ x ∉ centralizer (c.W : Set G) ∧
    x ^ 3 ∈ centralizer (c.W : Set G) ∧ (∀ a ∈ A₁, x * a * x⁻¹ ∈ A₁) ∧
    (c.OddCoreCentral → ∀ m ∈ M₂, x * m = m * x) ∧
    ∃ μ : k, μ ≠ 0 ∧ μ ≠ 1 ∧ ∀ a a' : ↥A₁, (a' : G) = x * a * x⁻¹ →
      coordA (e a') = μ * coordA (e a) ∧ coordB (e a') = μ * coordB (e a)

section Seitz

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G}

theorem CaseB.exists_sylowB
    (h : Hyp G A) (d : Datum A) {R' : Subgroup G} (hR : Radicals d.V R R')
    (c : CaseB A R d.t) :
    ∃ (M₁ M₂ S₀ A₁ B₁ : Subgroup G) (k : Type) (_ : Field k) (e : ↥A₁ ≃* ↥(unipAll k)),
      c.Factors M₁ M₂ ∧ SylowB c R' M₁ M₂ S₀ A₁ B₁ e := by
  obtain ⟨M₁, M₂, F⟩ := c.exists_factors
  obtain ⟨S, P⟩ := c.exists_prod2 h d hR F
  obtain ⟨k, hkF, hkfin, hk, e, hW, hR1, hR2⟩ := c.exists_coord h d hR F P
  refine ⟨M₁, M₂, S, S ⊓ M₁, S ⊓ M₂, k, hkF, e, F, ?_⟩
  exact
    { card_k := hk
      S₀_sylow := by rw [F.ninf_eq]; exact P.sylow
      V_le := P.V_le
      W_le := c.W_le_S F P
      A₁_eq := rfl
      B₁_eq := rfl
      prod := P.S_eq
      inf_eq := P.inf_AB
      comm := fun a ha b hb => P.comm_AB ha hb
      swap₁ := fun x hx => P.swap_A hx
      swap₂ := fun x hx => P.swap_B hx
      V_eq := P.V_eq
      V_diag := fun v => ⟨fun hv => P.exists_diag_V hv, fun ⟨a, ha, hva⟩ => hva ▸ P.diag_mem_V ha⟩
      W_coord := hW
      R_coord := hR1
      R'_coord := hR2
      A1 := fun s hs => not_isConj_of_mem_prod hk h d hR (fun a ha b hb => P.comm_AB ha hb)
        P.inf_AB (fun x hx => P.swap_A hx) (fun x hx => P.swap_B hx) e
        (by rw [← P.S_eq]; exact hs)
      torus := by
        obtain ⟨x, hxM, hxodd, hx1, hx3, hxA, μ, hμ0, hμ1, hμ⟩ := c.exists_torus F P hk e hW
        refine ⟨x, hxM, hxodd, hx1, hx3, hxA, fun hZ m hm => ?_, μ, hμ0, hμ1, hμ⟩
        have hxc : x ∈ centralizer (M₂ : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp (F.comm_eq_bot hZ) hxM
        exact (mem_centralizer_iff.mp hxc m hm).symm }

end Seitz

end CFSG.OddStandard.Seitz77
