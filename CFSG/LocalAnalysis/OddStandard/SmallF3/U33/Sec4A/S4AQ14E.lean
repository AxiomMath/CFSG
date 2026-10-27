module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q14E

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q14_Q_le_M (t x₁ x₂ rho : G) : l41Q t x₁ x₂ rho ≤ l41M t x₁ x₂ rho :=
  pCoreOf_two_le _

theorem q14_Q_isPGroup (t x₁ x₂ rho : G) : IsPGroup 2 (l41Q t x₁ x₂ rho) :=
  pCoreOf_two_isPGroup _

theorem q14_conj_Q {g : G} (hg : g ∈ l41M t x₁ x₂ rho) {q : G} (hq : q ∈ l41Q t x₁ x₂ rho) :
    g * q * g⁻¹ ∈ l41Q t x₁ x₂ rho :=
  pCoreOf_two_conj_mem hg hq

theorem q14_mem_normalizer_Q {g : G} (hg : g ∈ l41M t x₁ x₂ rho) :
    g ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hq => q14_conj_Q hg hq

theorem q14_mem_normalizer_F {g : G} (hg : g ∈ l41M t x₁ x₂ rho) :
    g ∈ normalizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) := hg

theorem q14_mem_normalizer_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ l41M t x₁ x₂ rho) :
    g ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun y hy => (m13_normal_Y h).2 g hg y hy

theorem q14_F_le_Q (h : L41GPh8 t L S x₁ x₂ lam rho) : l41F t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho :=
  le_pCoreOf_two (q14_F_le_M t x₁ x₂ rho) (fun _ hn _ hq => q14_conj_F hn hq)
    (q14_F_isPGroup h)

theorem q14_t_mem_Q (h : L41GPh8 t L S x₁ x₂ lam rho) : t ∈ l41Q t x₁ x₂ rho :=
  q14_F_le_Q h (q14_t_mem_F t x₁ x₂ rho)

theorem q14_R_le_Q (h : L41GPh8 t L S x₁ x₂ lam rho) : l41R t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho :=
  le_sup_left.trans (q14_F_le_Q h)

theorem q14_Y_le_Q (h : L41GPh10 t L S x₁ x₂ lam rho) : l41Y t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho :=
  (m13_Y_le_R t x₁ x₂ rho).trans (q14_R_le_Q h.toL41GPh8)

theorem q14_W_le_Q (h : L41GPh8 t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ l41Q t x₁ x₂ rho :=
  (m13_W_le_F h).trans (q14_F_le_Q h)

theorem q14_normal_YQ (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal :=
  q14_normal_subgroupOf fun _ hq _ hn => (m13_normal_Y h).2 _ (q14_Q_le_M t x₁ x₂ rho hq) _ hn

theorem q14_normal_FQ (t x₁ x₂ rho : G) :
    ((l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal :=
  q14_normal_subgroupOf fun _ hq _ hn => q14_conj_F (q14_Q_le_M t x₁ x₂ rho hq) hn

theorem q14_inf_K_Q (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Q t x₁ x₂ rho ⊓ closure {rho, lam} = ⊥ := by
  obtain ⟨e⟩ := h.basic.sigma3
  exact q14_inf_eq_bot_of_sigma3 e (q14_Q_isPGroup t x₁ x₂ rho)
    fun k hk d hd => q14_conj_Q (q14_K_le_M h.toL41GPh8 hk) hd

theorem q14_card_Q (h : L41GPh10 t L S x₁ x₂ lam rho) : Nat.card (l41Q t x₁ x₂ rho) = 512 := by
  have hM := q14_card_M h
  have hmul := m11_card_mul_le_sup (q14_inf_K_Q h)
  rw [q14_card_K h.toL41GPh1] at hmul
  have hsup : Nat.card ↥(l41Q t x₁ x₂ rho ⊔ closure {rho, lam}) ≤
      Nat.card (l41M t x₁ x₂ rho) :=
    Subgroup.card_le_of_le (sup_le (q14_Q_le_M t x₁ x₂ rho) (q14_K_le_M h.toL41GPh8))
  have key : Nat.card (l41M t x₁ x₂ rho) = 3 * Nat.card (l41Q t x₁ x₂ rho) ∨
      Nat.card (l41M t x₁ x₂ rho) = 6 * Nat.card (l41Q t x₁ x₂ rho) :=
    q14_card_pCore (e := 10) (by omega)
  omega

theorem q14_M_eq (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41M t x₁ x₂ rho = l41Q t x₁ x₂ rho ⊔ closure {rho, lam} := by
  have hmul := m11_card_mul_le_sup (q14_inf_K_Q h)
  rw [q14_card_Q h, q14_card_K h.toL41GPh1] at hmul
  have hle : l41Q t x₁ x₂ rho ⊔ closure {rho, lam} ≤ l41M t x₁ x₂ rho :=
    sup_le (q14_Q_le_M t x₁ x₂ rho) (q14_K_le_M h.toL41GPh8)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [q14_card_M h]; omega)).symm

theorem q14_F_lt_Q (h : L41GPh10 t L S x₁ x₂ lam rho) : l41F t x₁ x₂ rho < l41Q t x₁ x₂ rho := by
  refine lt_of_le_of_ne (q14_F_le_Q h.toL41GPh8) fun heq => ?_
  have h1 := m13_card_F h.toL41GPh8
  have h2 := q14_card_Q h
  rw [heq] at h1
  omega

theorem q14_cent_Q_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Q t x₁ x₂ rho ⊓ invCent t = ctxW t x₁ x₂ := by
  have hWQ : ctxW t x₁ x₂ ≤ l41Q t x₁ x₂ rho ⊓ invCent t :=
    le_inf (q14_W_le_Q h.toL41GPh8) (m13_W_le_invCent h.toL41GPh5)
  refine (Subgroup.eq_of_le_of_card_ge hWQ ?_).symm
  have hDK : (l41Q t x₁ x₂ rho ⊓ invCent t) ⊓ closure {rho, lam} = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans (q14_inf_K_Q h).le)
  have hmul := m11_card_mul_le_sup hDK
  rw [q14_card_K h.toL41GPh1] at hmul
  have hKc : closure {rho, lam} ≤ invCent t :=
    (le_sup_right.trans (m13_cent_M_t h).symm.le).trans inf_le_left
  have hsup : (l41Q t x₁ x₂ rho ⊓ invCent t) ⊔ closure {rho, lam} ≤
      l41M t x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
    sup_le (le_inf (inf_le_left.trans (q14_Q_le_M t x₁ x₂ rho)) inf_le_right)
      (le_inf (q14_K_le_M h.toL41GPh8) hKc)
  have hc := Subgroup.card_le_of_le hsup
  rw [q14_card_cent_M_t h] at hc
  rw [q14_card_W h.toL41GPh5]
  omega

theorem q14_orbit_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    conjIn (l41Q t x₁ x₂ rho) t =
      {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1} := by
  have hsub : conjIn (l41Q t x₁ x₂ rho) t ⊆
      {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1} := by
    rintro u ⟨q, hq, rfl⟩
    exact m13_conj_mem_X h (q14_Q_le_M t x₁ x₂ rho hq)
  have h1 := m13_card_conjIn_mul (l41Q t x₁ x₂ rho) t
  have h2 : Nat.card ↥(l41Q t x₁ x₂ rho ⊓ centralizer ({t} : Set G)) = 32 := by
    have e : l41Q t x₁ x₂ rho ⊓ centralizer ({t} : Set G) = ctxW t x₁ x₂ := q14_cent_Q_t h
    rw [e]
    exact q14_card_W h.toL41GPh5
  rw [q14_card_Q h, h2] at h1
  have h3 : (conjIn (l41Q t x₁ x₂ rho) t).ncard = 16 := by omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [h3, m13_card_X h]) (Set.toFinite _)

end Q14E

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
