module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Mod
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBDefs

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section AbstractFac

variable {G : Type} [Group G] {K W F₁ F₂ H₁ H₂ : Subgroup G} {t : G}

namespace FacSetup

variable (S : FacSetup K W F₁ F₂ H₁ H₂ t)

include S

theorem exists_conj_M₁ {y : G} (hy : y ∈ H₁) :
    ∃ m ∈ perfectResidualOf H₁, ∀ f ∈ F₁, y * f * y⁻¹ = m * f * m⁻¹ := by
  obtain ⟨k, hk, m, hm, rfl⟩ := S.perf₁ y hy
  refine ⟨m, hm, fun f hf => ?_⟩
  have hmf : m * f * m⁻¹ ∈ F₁ := S.normF₁ m (mem_sup_left (prOf_le H₁ hm)) f hf
  have hcomm : m * f * m⁻¹ * k = k * (m * f * m⁻¹) := S.W_central _ (S.F₁_le hmf) k hk
  calc k * m * f * (k * m)⁻¹ = k * (m * f * m⁻¹) * k⁻¹ := by group
    _ = m * f * m⁻¹ * k * k⁻¹ := by rw [← hcomm]
    _ = m * f * m⁻¹ := by group

theorem invariant_M₁ {U : Subgroup G} (hU : U ≤ F₁)
    (hinv : ∀ m ∈ perfectResidualOf H₁, ∀ u ∈ U, m * u * m⁻¹ ∈ U) :
    ∀ y ∈ H₁, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
  intro y hy u hu
  obtain ⟨m, hm, h⟩ := S.exists_conj_M₁ hy
  rw [h u (hU hu)]
  exact hinv m hm u hu

end FacSetup

end AbstractFac

section Seitz

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}

@[expose] def CaseB.OddCoreCentral (c : CaseB A R t) : Prop := CentralOddCore c.Ninf

structure CaseB.Factors (c : CaseB A R t) (M₁ M₂ : Subgroup G) : Prop where
  ninf_eq : c.Ninf = M₁ ⊔ M₂
  perfect₁ : ⁅M₁, M₁⁆ = M₁
  perfect₂ : ⁅M₂, M₂⁆ = M₂
  norm₁ : ∀ x ∈ c.Ninf, ∀ m ∈ M₁, x * m * x⁻¹ ∈ M₁
  norm₂ : ∀ x ∈ c.Ninf, ∀ m ∈ M₂, x * m * x⁻¹ ∈ M₂
  odd_inf : Odd (Nat.card ↥(M₁ ⊓ M₂))
  comm_eq_bot : c.OddCoreCentral → ⁅M₁, M₂⁆ = ⊥
  swap₁ : ∀ x ∈ M₁, t * x * t⁻¹ ∈ M₂
  swap₂ : ∀ x ∈ M₂, t * x * t⁻¹ ∈ M₁
  W_le : c.W ≤ c.Ninf
  card₁ : Nat.card ↥(c.W ⊓ M₁) = 16
  card₂ : Nat.card ↥(c.W ⊓ M₂) = 16
  W_eq : (c.W ⊓ M₁) ⊔ (c.W ⊓ M₂) = c.W
  W_disj : (c.W ⊓ M₁) ⊓ (c.W ⊓ M₂) = ⊥
  W₂_cent : c.W ⊓ M₂ ≤ centralizer (M₁ : Set G)
  W₁_cent : c.W ⊓ M₁ ≤ centralizer (M₂ : Set G)
  irr₁ : ∀ U : Subgroup G, U ≤ c.W ⊓ M₁ → (∀ m ∈ M₁, ∀ u ∈ U, m * u * m⁻¹ ∈ U) →
    U = ⊥ ∨ U = c.W ⊓ M₁
  irr₂ : ∀ U : Subgroup G, U ≤ c.W ⊓ M₂ → (∀ m ∈ M₂, ∀ u ∈ U, m * u * m⁻¹ ∈ U) →
    U = ⊥ ∨ U = c.W ⊓ M₂
  faithful₁ : ∀ m ∈ M₁, (∀ w ∈ c.W ⊓ M₁, m * w * m⁻¹ = w) → m ∈ centralizer (c.W : Set G)
  faithful₂ : ∀ m ∈ M₂, (∀ w ∈ c.W ⊓ M₂, m * w * m⁻¹ = w) → m ∈ centralizer (c.W : Set G)
  fpf₁ : ∀ m ∈ M₁, m ∉ centralizer (c.W : Set G) → m ^ 3 ∈ centralizer (c.W : Set G) →
    ∀ w ∈ c.W ⊓ M₁, m * w * m⁻¹ = w → w = 1
  fpf₂ : ∀ m ∈ M₂, m ∉ centralizer (c.W : Set G) → m ^ 3 ∈ centralizer (c.W : Set G) →
    ∀ w ∈ c.W ⊓ M₂, m * w * m⁻¹ = w → w = 1
  a5₁ : ∃ π : ↥M₁ →* alternatingGroup (Fin 5), Function.Surjective π ∧
    ∀ m : ↥M₁, π m = 1 ↔ (m : G) ∈ centralizer (c.W : Set G)
  a5₂ : ∃ π : ↥M₂ →* alternatingGroup (Fin 5), Function.Surjective π ∧
    ∀ m : ↥M₂, π m = 1 ↔ (m : G) ∈ centralizer (c.W : Set G)
  card_M₁ : Nat.card ↥M₁ = Nat.card ↥(M₁ ⊓ centralizer (c.W : Set G)) * 60
  card_M₂ : Nat.card ↥M₂ = Nat.card ↥(M₂ ⊓ centralizer (c.W : Set G)) * 60
  sylow_card₁ : ∀ T : Subgroup G, IsSylowOf 2 T M₁ → Nat.card ↥T = 64
  sylow_card₂ : ∀ T : Subgroup G, IsSylowOf 2 T M₂ → Nat.card ↥T = 64
  sylow_W₁ : IsSylowOf 2 (c.W ⊓ M₁) (M₁ ⊓ centralizer (c.W : Set G))
  sylow_W₂ : IsSylowOf 2 (c.W ⊓ M₂) (M₂ ⊓ centralizer (c.W : Set G))
  two_elem : ∀ x ∈ centralizer (c.W : Set G), (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ c.W
  exists_O₁ : ∃ O₁ : Subgroup G, O₁ ≤ centralizer (c.W : Set G) ∧ Odd (Nat.card ↥O₁) ∧
    c.W ⊓ O₁ = ⊥ ∧ (∀ k ∈ centralizer (c.W : Set G), ∃ w ∈ c.W, ∃ o ∈ O₁, k = w * o) ∧
    (∀ x ∈ c.Ninf, ∀ o ∈ O₁, x * o * x⁻¹ ∈ O₁) ∧
    (∀ x ∈ centralizer (c.W : Set G), Odd (orderOf x) → x ∈ O₁)

theorem CaseB.exists_factors (c : CaseB A R t) :
    ∃ M₁ M₂ : Subgroup G, c.Factors M₁ M₂ := by
  obtain ⟨S₁, S₂, hF⟩ := c.H.exists_facSit c.B
  obtain ⟨F₁, F₂, H₁, H₂, S, E, hH₁, hH₂⟩ := Setup27.exists_facSetup hF
  have hsup_le : H₁ ⊔ H₂ ≤ c.N := sup_le hH₁ hH₂
  have hninf : c.Ninf = perfectResidualOf H₁ ⊔ perfectResidualOf H₂ := by
    rw [← S.prOf_sup]
    refine le_antisymm ?_ ?_
    · exact le_prOf c.Ninf_perfect (E.perf_le c.Ninf (prOf_le c.N) c.Ninf_perfect)
    · exact le_prOf (prOf_perfect _) (le_trans (prOf_le _) hsup_le)
  have hNH : c.Ninf ≤ H₁ ⊔ H₂ := by
    rw [hninf]
    exact sup_le_sup (prOf_le H₁) (prOf_le H₂)
  have hW₁ : c.W ⊓ perfectResidualOf H₁ = F₁ := S.inf_M₁_eq
  have hW₂ : c.W ⊓ perfectResidualOf H₂ = F₂ := S.inf_M₂_eq
  refine ⟨perfectResidualOf H₁, perfectResidualOf H₂, ?_⟩
  exact
    { ninf_eq := hninf
      perfect₁ := prOf_perfect H₁
      perfect₂ := prOf_perfect H₂
      norm₁ := fun x hx m hm => S.normM₁ (hNH hx) hm
      norm₂ := fun x hx m hm => S.normM₂ (hNH hx) hm
      odd_inf := S.odd_card_inf_M
      comm_eq_bot := fun hZ => S.comm_eq_bot (by rw [← hninf]; exact hZ)
      swap₁ := fun x hx => S.swap_M₁ hx
      swap₂ := fun x hx => S.swap_M₂ hx
      W_le := by
        rw [hninf]
        exact (S.F_sup.symm.le.trans (sup_le_sup S.F₁_le_M₁ S.symm.F₁_le_M₁))
      card₁ := by rw [hW₁]; exact E.card₁
      card₂ := by rw [hW₂]; exact E.card₂
      W_eq := by rw [hW₁, hW₂]; exact S.F_sup
      W_disj := by rw [hW₁, hW₂]; exact S.F_disj
      W₂_cent := by
        rw [hW₂]
        intro f hf
        rw [mem_centralizer_iff]
        intro m hm
        have h := S.cent₁ m (prOf_le H₁ hm) f hf
        calc m * f = m * f * m⁻¹ * m := by group
          _ = f * m := by rw [h]
      W₁_cent := by
        rw [hW₁]
        intro f hf
        rw [mem_centralizer_iff]
        intro m hm
        have h := S.cent₂ m (prOf_le H₂ hm) f hf
        calc m * f = m * f * m⁻¹ * m := by group
          _ = f * m := by rw [h]
      irr₁ := fun U hU hinv => by
        rw [hW₁] at hU ⊢
        exact E.irr₁ U hU (S.invariant_M₁ hU hinv)
      irr₂ := fun U hU hinv => by
        rw [hW₂] at hU ⊢
        exact E.irr₂ U hU (S.symm.invariant_M₁ hU hinv)
      faithful₁ := fun m hm h =>
        E.faithful₁ m (prOf_le H₁ hm) (fun f hf => h f (by rw [hW₁]; exact hf))
      faithful₂ := fun m hm h =>
        E.faithful₂ m (prOf_le H₂ hm) (fun f hf => h f (by rw [hW₂]; exact hf))
      fpf₁ := fun m hm h1 h3 w hw hfix =>
        E.fpf₁ m (prOf_le H₁ hm) h1 h3 w (by rw [← hW₁]; exact hw) hfix
      fpf₂ := fun m hm h1 h3 w hw hfix =>
        E.fpf₂ m (prOf_le H₂ hm) h1 h3 w (by rw [← hW₂]; exact hw) hfix
      a5₁ := E.a5₁
      a5₂ := E.a5₂
      card_M₁ := by rw [S.card_M₁, E.idx₁]
      card_M₂ := by rw [S.symm.card_M₁, E.idx₂]
      sylow_card₁ := fun T hT => S.card_sylow_M₁ hT E.idx₁ E.card₁
      sylow_card₂ := fun T hT => S.symm.card_sylow_M₁ hT E.idx₂ E.card₂
      sylow_W₁ := by rw [hW₁]; exact S.isSylowOf_F₁_inf_K
      sylow_W₂ := by rw [hW₂]; exact S.symm.isSylowOf_F₁_inf_K
      two_elem := fun x hx h2 => S.mem_W_of_two_power hx h2
      exists_O₁ := by
        obtain ⟨O₁, h1, h2, h3, h4, h5, h6⟩ := S.exists_O₁
        exact ⟨O₁, h1, h2, h3, h4, fun x hx o ho => h5 x (hNH hx) o ho, h6⟩ }

theorem CaseB.Factors.comm_elem {c : CaseB A R t} {M₁ M₂ : Subgroup G} (F : c.Factors M₁ M₂)
    (hZ : c.OddCoreCentral) {a b : G} (ha : a ∈ M₁) (hb : b ∈ M₂) : a * b = b * a := by
  have hc : a ∈ centralizer (M₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (F.comm_eq_bot hZ) ha
  exact (mem_centralizer_iff.mp hc b hb).symm

theorem CaseB.Factors.inf_central {c : CaseB A R t} {M₁ M₂ : Subgroup G} (F : c.Factors M₁ M₂)
    (hZ : c.OddCoreCentral) {z n : G} (hz : z ∈ M₁ ⊓ M₂) (hn : n ∈ c.Ninf) :
    z * n = n * z := by
  rw [F.ninf_eq] at hn
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_comm (fun x hx y hy => F.comm_elem hZ hx hy) hn
  have h1 : a * z = z * a := F.comm_elem hZ ha hz.2
  have h2 : z * b = b * z := F.comm_elem hZ hz.1 hb
  calc z * (a * b) = (z * a) * b := by group
    _ = (a * z) * b := by rw [h1]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by group

end Seitz

end CFSG.OddStandard.Seitz77
