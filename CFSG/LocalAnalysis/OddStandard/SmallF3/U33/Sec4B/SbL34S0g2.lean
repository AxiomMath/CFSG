module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0g1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

section Gen

variable {G : Type*} [Group G] [Finite G]

private theorem card_sup_le_aux {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B h
  let f : A × B → (A ⊔ B : Subgroup G) := fun q => ⟨q.1 * q.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ ((A : Set G) * (B : Set G)) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(A ⊔ B) ≤ Nat.card (A × B) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

private theorem card_mul_le_aux {A B : Subgroup G} (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : A × B => (⟨(p.1 : G) * (p.2 : G), mul_mem (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
  have h2 : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h1]
      _ = (b' : G) * (b : G)⁻¹ := by group
  have hmem : (a' : G)⁻¹ * (a : G) ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    rw [h2]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [h, Subgroup.mem_bot] at hmem
  have hb : (b' : G) * (b : G)⁻¹ = 1 := h2.symm.trans hmem
  have ha : (a : G) = (a' : G) := (inv_mul_eq_one.mp hmem).symm
  have hb' : (b : G) = (b' : G) := (mul_inv_eq_one.mp hb).symm
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb')

theorem card_sup_eq_mul_of_normalizes {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B :=
  le_antisymm (card_sup_le_aux hB) (card_mul_le_aux h)

end Gen

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem mem_zpowers_eq_one_or_eq_aux {z g : G} (hz : z * z = 1)
    (hg : g ∈ zpowers z) : g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

section E

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem t_ne_tau : t ≠ tau := by
  intro h
  apply hc.tau_not_mem
  rw [← h]
  exact Subgroup.mem_sup_left hc.hyp.mem_twoCore

theorem card_T : Nat.card ↥(closure ({t, tau} : Set G)) = 4 :=
  card_closure_pair hc.t_mul_self hc.tau_mul_self hc.t_comm_tau hc.t_ne_one hc.tau_ne_one
    (t_ne_tau hc)

theorem E_eq : closure ({t, tau, lam} : Set G) = closure ({t, tau} : Set G) ⊔ zpowers lam := by
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  tauto

theorem zpowers_lam_le_normalizer_T :
    zpowers lam ≤ normalizer ((closure ({t, tau} : Set G) : Subgroup G) : Set G) := by
  have hmem : lam ∈ centralizer ((closure ({t, tau} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases (mem_T_iff hc).mp hx with rfl | rfl | rfl | rfl
    · simp
    · exact t_comm_lam hc
    · exact (lam_comm_tau hc).symm
    · calc (t * tau) * lam = t * (tau * lam) := by group
        _ = t * (lam * tau) := by rw [← lam_comm_tau hc]
        _ = (t * lam) * tau := by group
        _ = (lam * t) * tau := by rw [t_comm_lam hc]
        _ = lam * (t * tau) := by group
  exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hmem)

theorem T_inf_zpowers_lam : closure ({t, tau} : Set G) ⊓ zpowers lam = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases mem_zpowers_eq_one_or_eq_aux (lam_mul_self hc) hx.2 with rfl | rfl
  · rfl
  · exact absurd (T_le_O hc hx.1) (lam_not_mem_O hc)

theorem card_E : Nat.card ↥(closure ({t, tau, lam} : Set G)) = 8 := by
  have hz : Nat.card (zpowers lam) = 2 := by
    rw [Nat.card_zpowers, hc.wreath.ord_lam]
  rw [E_eq hc, card_sup_eq_mul_of_normalizes (zpowers_lam_le_normalizer_T hc)
    (T_inf_zpowers_lam hc), card_T hc, hz]

theorem E_le_centralizer_q :
    closure ({t, tau, lam} : Set G) ≤ centralizer ({t * lam} : Set G) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  change g ∈ Subgroup.centralizer ({t * lam} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hg with hg | hg | hg
  · rw [hg]
    calc t * (t * lam) = (t * t) * lam := by group
      _ = lam := by rw [hc.t_mul_self, one_mul]
      _ = (t * lam) * t := by
          rw [mul_assoc, ← t_comm_lam hc, ← mul_assoc, hc.t_mul_self, one_mul]
  · rw [hg]
    exact (q_comm_tau hc).symm
  · rw [hg]
    calc lam * (t * lam) = (lam * t) * lam := by group
      _ = (t * lam) * lam := by rw [← t_comm_lam hc]

theorem E_le_U : closure ({t, tau, lam} : Set G) ≤ ctxU t tau x₁ x₂ lam := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact O_le_U hc hc.t_mem_O
  · exact O_le_U hc hc.tau_mem_O
  · exact lam_mem_U hc

theorem mem_E_iff {e : G} : e ∈ closure ({t, tau, lam} : Set G) ↔
    e ∈ closure ({t, tau} : Set G) ∨ ∃ s ∈ closure ({t, tau} : Set G), e = s * lam := by
  have hTE : closure ({t, tau} : Set G) ≤ closure ({t, tau, lam} : Set G) :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  have hlamE : lam ∈ closure ({t, tau, lam} : Set G) := Subgroup.subset_closure (by simp)
  have hset : (closure ({t, tau, lam} : Set G) : Set G) =
      (closure ({t, tau} : Set G) : Set G) * (zpowers lam : Set G) := by
    rw [E_eq hc]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ (zpowers_lam_le_normalizer_T hc)
  constructor
  · intro he
    have he' : e ∈ (closure ({t, tau} : Set G) : Set G) * (zpowers lam : Set G) := by
      rw [← hset]; exact he
    obtain ⟨s, hs, c, hcmem, hsc⟩ := Set.mem_mul.mp he'
    rcases mem_zpowers_eq_one_or_eq_aux (lam_mul_self hc) hcmem with rfl | rfl
    · left
      rw [mul_one] at hsc
      exact hsc ▸ hs
    · exact Or.inr ⟨s, hs, hsc.symm⟩
  · rintro (he | ⟨s, hs, rfl⟩)
    · exact hTE he
    · exact mul_mem (hTE hs) hlamE

theorem CQ_inf_E : (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) ⊓
    closure ({t, tau, lam} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases (mem_E_iff hc).mp hx.2 with hxT | ⟨s, hs, hxs⟩
  · have hmem : x ∈ ctxQ t tau x₁ x₂ rho ⊓ closure ({t, tau} : Set G) := ⟨hx.1.1, hxT⟩
    rwa [Q_inf_T hc, Subgroup.mem_bot] at hmem
  · exfalso
    exact lam_not_mem_O hc (by
      rw [show lam = s⁻¹ * x by rw [hxs]; group]
      exact mul_mem (inv_mem (T_le_O hc hs)) (hc.Q_le_O hx.1.1))

theorem E_le_normalizer_CQ : closure ({t, tau, lam} : Set G) ≤
    normalizer ((ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G) : Subgroup G) : Set G) := by
  intro e he
  refine Subgroup.mem_normalizer_fintype (fun c hc' => ?_)
  have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := hc'.1
  have hcent : c ∈ centralizer ({t * lam} : Set G) := hc'.2
  refine ⟨hc.normal_Q.2 e (U_le_M hc (E_le_U hc he)) c hcQ, ?_⟩
  change e * c * e⁻¹ ∈ centralizer ({t * lam} : Set G)
  exact mul_mem (mul_mem (E_le_centralizer_q hc he) hcent) (inv_mem (E_le_centralizer_q hc he))

theorem CU_tl : ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) =
    (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) ⊔ closure ({t, tau, lam} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro u hu
    rcases U_decomp hc hu.1 with huO | ⟨a, haO, rfl⟩
    · obtain ⟨b, hbQ, s, hsT, rfl⟩ := O_decomp hc huO
      have hsE : s ∈ closure ({t, tau, lam} : Set G) := by
        rw [E_eq hc]
        exact Subgroup.mem_sup_left hsT
      have hse : s ∈ centralizer ({t * lam} : Set G) := E_le_centralizer_q hc hsE
      have hbq : b ∈ centralizer ({t * lam} : Set G) := by
        rw [show b = (b * s) * s⁻¹ by group]
        exact mul_mem hu.2 (inv_mem hse)
      exact Subgroup.mul_mem_sup ⟨hbQ, hbq⟩ hsE
    · obtain ⟨b, hbQ, s, hsT, rfl⟩ := O_decomp hc haO
      have heE : s * lam ∈ closure ({t, tau, lam} : Set G) :=
        (mem_E_iff hc).mpr (Or.inr ⟨s, hsT, rfl⟩)
      have hee : s * lam ∈ centralizer ({t * lam} : Set G) := E_le_centralizer_q hc heE
      have hbq : b ∈ centralizer ({t * lam} : Set G) := by
        rw [show b = ((b * s) * lam) * (s * lam)⁻¹ by group]
        exact mul_mem hu.2 (inv_mem hee)
      rw [mul_assoc]
      exact Subgroup.mul_mem_sup ⟨hbQ, hbq⟩ heE
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨O_le_U hc (hc.Q_le_O hx.1), hx.2⟩
    · intro e he
      exact ⟨E_le_U hc he, E_le_centralizer_q hc he⟩

theorem card_CU_tl (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) = 2 ^ 6 := by
  rw [CU_tl hc, card_sup_eq_mul_of_normalizes (E_le_normalizer_CQ hc) (CQ_inf_E hc),
    card_CQ_tl hc hs, card_E hc]
  norm_num

end E

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
