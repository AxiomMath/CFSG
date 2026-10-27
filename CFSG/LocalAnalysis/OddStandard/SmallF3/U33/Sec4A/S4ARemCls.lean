module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma ht2_of (h : Ctx t L S x₁ x₂ lam rho tau) : t * t = 1 := t_mul_self h.hyp

private lemma htau2_of (h44 : tau ^ 2 = 1) : tau * tau = 1 := by
  simpa [pow_two] using h44

private lemma tau_mem_invCent (h : Ctx t L S x₁ x₂ lam rho tau) : tau ∈ invCent t :=
  h.le_invCent h.tau_mem

private lemma ht_comm_tau_of (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    t * tau = tau * t := by
  exact (mem_invCent_iff.mp (tau_mem_invCent h)).symm

private lemma tau_ne_one_of (h : Ctx t L S x₁ x₂ lam rho tau) : tau ≠ 1 := by
  intro h1
  exact h.tau_not_mem (by rw [h1]; exact Subgroup.one_mem _)

private lemma tau_not_mem_L_of (h : Ctx t L S x₁ x₂ lam rho tau) : tau ∉ L := by
  intro hl
  exact h.tau_not_mem (Subgroup.mem_sup_right hl)

private lemma t_mul_tau_not_mem_PL (h : Ctx t L S x₁ x₂ lam rho tau) :
    t * tau ∉ twoCore t ⊔ L := by
  intro hmem
  apply h.tau_not_mem
  have h1 : t * (t * tau) = tau := by rw [← mul_assoc, ht2_of h, one_mul]
  rw [← h1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.hyp.mem_twoCore) hmem

private lemma t_mul_tau_not_mem_L (h : Ctx t L S x₁ x₂ lam rho tau) : t * tau ∉ L := by
  intro hl
  exact t_mul_tau_not_mem_PL h (Subgroup.mem_sup_right hl)

private lemma t_ne_tau_of (h : Ctx t L S x₁ x₂ lam rho tau) : t ≠ tau := by
  intro heq
  apply h.tau_not_mem
  rw [← heq]
  exact Subgroup.mem_sup_left h.hyp.mem_twoCore

private lemma t_mul_tau_ne_one (h : Ctx t L S x₁ x₂ lam rho tau) : t * tau ≠ 1 := by
  intro h1
  apply t_ne_tau_of h
  have h2 : tau = t := by
    calc tau = t * (t * tau) := by rw [← mul_assoc, ht2_of h, one_mul]
      _ = t * 1 := by rw [h1]
      _ = t := mul_one t
  exact h2.symm

private lemma t_mul_tau_ne_t (h : Ctx t L S x₁ x₂ lam rho tau) : t * tau ≠ t := by
  intro h1
  exact tau_ne_one_of h (mul_left_cancel (a := t) (by rw [h1, mul_one]))

private lemma t_mul_tau_ne_tau (h : Ctx t L S x₁ x₂ lam rho tau) : t * tau ≠ tau := by
  intro h1
  exact t_ne_one h.hyp (mul_right_cancel (by rw [h1, one_mul]))

private lemma twoCore_eq_one_or_eq_t (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {a : G} (ha : a ∈ twoCore t) : a = 1 ∨ a = t := by
  have ha' : a ∈ zpowers t := h43 ▸ ha
  have hdvd : orderOf a ∣ orderOf t := orderOf_dvd_of_mem_zpowers ha'
  have ha2 : a ^ 2 = 1 := by
    have h2 : orderOf a ∣ 2 := by rw [← h.hyp.ord_t]; exact hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact h.hyp.eq_one_or_eq a ha ha2

private lemma mem_PL_or_mul_tau_mem (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ invCent t) : g ∈ twoCore t ⊔ L ∨ g * tau ∈ twoCore t ⊔ L := by
  have hPLH : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  rcases mem_or_mem_or_mul_mem_of_relIndex_two (S := invCent t) (K := twoCore t ⊔ L)
      hPLH h.relIndex_two hg (tau_mem_invCent h) with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.tau_not_mem
  · exact Or.inr h1

private lemma mem_sup_iff_mem_L_or (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {x : G} :
    x ∈ twoCore t ⊔ L ↔ x ∈ L ∨ t * x ∈ L := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hx
    rcases twoCore_eq_one_or_eq_t h h43 ha with ha1 | ha1
    · subst a
      exact Or.inl (by simpa using hb)
    · subst a
      exact Or.inr (by rw [← mul_assoc, ht2_of h, one_mul]; exact hb)
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_right hx
    · have hx' : x = t * (t * x) := by rw [← mul_assoc, ht2_of h, one_mul]
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.hyp.mem_twoCore)
        (Subgroup.mem_sup_right hx)

private lemma conj_mem_L (h : Ctx t L S x₁ x₂ lam rho tau) {g x : G}
    (hg : g ∈ invCent t) (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h.hyp hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.hyp.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private lemma conj_mem_PL (h : Ctx t L S x₁ x₂ lam rho tau) {g x : G}
    (hg : g ∈ invCent t) (hx : x ∈ twoCore t ⊔ L) : g * x * g⁻¹ ∈ twoCore t ⊔ L := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hx
  have hcP : g * a * g⁻¹ ∈ twoCore t := twoCore_conj_mem t hg ha
  have hcL : g * b * g⁻¹ ∈ L := conj_mem_L h hg hb
  have heq : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcP) (Subgroup.mem_sup_right hcL)

private lemma mem_Q_iff (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} :
    g ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} ↔ g ∈ L ∧ g * tau = tau * g := by
  rw [← h.cent_L_tau, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgC⟩
    exact ⟨hgL, (Subgroup.mem_centralizer_iff.mp hgC tau (Set.mem_singleton tau)).symm⟩
  · rintro ⟨hgL, hgtau⟩
    exact ⟨hgL, Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgtau.symm)⟩

private lemma conj_eq_of_mem_twoCore (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {a x : G} (ha : a ∈ twoCore t) (hx : x ∈ invCent t) :
    a * x * a⁻¹ = x := by
  rcases twoCore_eq_one_or_eq_t h h43 ha with ha1 | ha1
  · subst a
    rw [one_mul, inv_one, mul_one]
  · subst a
    rw [(mem_invCent_iff.mp hx).symm, mul_assoc, mul_inv_cancel, mul_one]

private lemma conj_t_self (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ invCent t) : g * t * g⁻¹ = t := by
  rw [mem_invCent_iff.mp hg, mul_assoc, mul_inv_cancel, mul_one]

private lemma commute_closure_pair {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) {x y : G} (hx : x ∈ closure {a, b}) (hy : y ∈ closure {a, b}) :
    x * y = y * x := by
  haveI : IsMulCommutative (closure {a, b}) :=
    Subgroup.isMulCommutative_closure (by
      apply Set.Pairwise.of_forall₂
      intro p hp q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · rw [hp, hq]
      · rw [hp, hq]; exact hab
      · rw [hp, hq]; exact hab.symm
      · rw [hp, hq])
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (closure {a, b}))
      ⟨x, hx⟩ ⟨y, hy⟩)

private lemma E4_comm (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) {a b : G}
    (ha : a ∈ closure {t, tau}) (hb : b ∈ closure {t, tau}) : a * b = b * a :=
  commute_closure_pair (ht_comm_tau_of h h44) (ht2_of h) (htau2_of h44) ha hb

private lemma E4_sq_mul (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) {x : G}
    (hx : x ∈ closure {t, tau}) : x * x = 1 := by
  have ht2 := ht2_of h
  have htau2 := htau2_of h44
  have hcomm := ht_comm_tau_of h h44
  rcases mem_closure_pair_cases hcomm ht2 htau2 hx with hx1 | hx1 | hx1 | hx1
  · subst x; rw [one_mul]
  · subst x; exact ht2
  · subst x; exact htau2
  · subst x
    calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [hcomm.symm]
      _ = (t * t) * (tau * tau) := by group
      _ = 1 := by rw [ht2, htau2, mul_one]

private lemma E4_isElemAbelian (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (closure {t, tau} : Subgroup G) := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.isMulCommutative_closure (by
      apply Set.Pairwise.of_forall₂
      intro p hp q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · rw [hp, hq]
      · rw [hp, hq]; exact ht_comm_tau_of h h44
      · rw [hp, hq]; exact (ht_comm_tau_of h h44).symm
      · rw [hp, hq])
  · intro x hx
    rw [pow_two]
    exact E4_sq_mul h h44 hx

private lemma E4_card (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    Nat.card (closure {t, tau} : Subgroup G) = 4 := by
  have ht2 := ht2_of h
  have htau2 := htau2_of h44
  have hcomm := ht_comm_tau_of h h44
  have hset : (closure {t, tau} : Set G) = {1, t, tau, t * tau} := by
    ext x
    constructor
    · intro hx
      rcases mem_closure_pair_cases hcomm ht2 htau2 hx with hx1 | hx1 | hx1 | hx1 <;>
        (subst x <;> simp)
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with hx1 | hx1 | hx1 | hx1
      · subst x; exact Subgroup.one_mem _
      · subst x; exact Subgroup.subset_closure (by simp)
      · subst x; exact Subgroup.subset_closure (by simp)
      · subst x; exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  change (closure {t, tau} : Set G).ncard = 4
  rw [hset, Set.ncard_eq_four]
  exact ⟨1, t, tau, t * tau, (t_ne_one h.hyp).symm, (tau_ne_one_of h).symm,
    (t_mul_tau_ne_one h).symm, t_ne_tau_of h, (t_mul_tau_ne_t h).symm,
    (t_mul_tau_ne_tau h).symm, rfl⟩

private lemma E4_inf_Q_eq_bot (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    closure {t, tau} ⊓ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} = (⊥ : Subgroup G) := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hgE : g ∈ closure {t, tau} := hg.1
  have hgL : g ∈ L := (mem_Q_iff h).mp hg.2 |>.1
  have ht2 := ht2_of h
  have htau2 := htau2_of h44
  have hcomm := ht_comm_tau_of h h44
  rcases mem_closure_pair_cases hcomm ht2 htau2 hgE with hg1 | hg1 | hg1 | hg1
  · subst g; rfl
  · subst g; exact absurd hgL (t_not_mem_L h.hyp)
  · subst g; exact absurd hgL (tau_not_mem_L_of h)
  · subst g; exact absurd hgL (t_mul_tau_not_mem_L h)

private lemma commute_E4_Q (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {a b : G}
    (ha : a ∈ closure {t, tau}) (hb : b ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam}) :
    a * b = b * a := by
  obtain ⟨hbL, hbtau⟩ := (mem_Q_iff h).mp hb
  have hbH : b ∈ invCent t := L_le_invCent h.hyp hbL
  have hbt : b * t = t * b := mem_invCent_iff.mp hbH
  have ht2 := ht2_of h
  have htau2 := htau2_of h44
  have hcomm := ht_comm_tau_of h h44
  rcases mem_closure_pair_cases hcomm ht2 htau2 ha with ha1 | ha1 | ha1 | ha1
  · subst a; rw [one_mul, mul_one]
  · subst a; exact hbt.symm
  · subst a; exact hbtau.symm
  · subst a
    calc (t * tau) * b = t * (tau * b) := by group
      _ = t * (b * tau) := by rw [hbtau.symm]
      _ = (t * b) * tau := by group
      _ = (b * t) * tau := by rw [hbt.symm]
      _ = b * (t * tau) := by group

private lemma sup_le_centralizer (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} ≤
      centralizer ((closure {t, tau} : Subgroup G) : Set G) := by
  apply sup_le
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact E4_comm h h44 hb ha
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact commute_E4_Q h h43 h44 ha hb

private lemma mem_sup_of_mem_PL (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {g : G} (hgH : g ∈ invCent t)
    (hgPL : g ∈ twoCore t ⊔ L) (hgtau : g * tau = tau * g) :
    g ∈ closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} := by
  rcases (mem_sup_iff_mem_L_or h h43).mp hgPL with hgL | htgL
  · exact Subgroup.mem_sup_right ((mem_Q_iff h).mpr ⟨hgL, hgtau⟩)
  · have hb_tau : (t * g) * tau = tau * (t * g) := by
      calc (t * g) * tau = t * (g * tau) := by group
        _ = t * (tau * g) := by rw [hgtau]
        _ = (t * tau) * g := by group
        _ = (tau * t) * g := by rw [ht_comm_tau_of h h44]
        _ = tau * (t * g) := by group
    have hbQ : t * g ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} :=
      (mem_Q_iff h).mpr ⟨htgL, hb_tau⟩
    have hg_eq : g = t * (t * g) := by rw [← mul_assoc, ht2_of h, one_mul]
    rw [hg_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
      (Subgroup.mem_sup_right hbQ)

private lemma centralizer_le_sup (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    centralizer ((closure {t, tau} : Subgroup G) : Set G) ≤
      closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} := by
  intro g hg
  have htE : t ∈ closure {t, tau} := Subgroup.subset_closure (by simp)
  have htauE : tau ∈ closure {t, tau} := Subgroup.subset_closure (by simp)
  have hgt : g * t = t * g := (Subgroup.mem_centralizer_iff.mp hg t htE).symm
  have hgtau : g * tau = tau * g := (Subgroup.mem_centralizer_iff.mp hg tau htauE).symm
  have hgH : g ∈ invCent t := mem_invCent_iff.mpr hgt
  by_cases hgPL : g ∈ twoCore t ⊔ L
  · exact mem_sup_of_mem_PL h h43 h44 hgH hgPL hgtau
  · have hxPL : g * tau ∈ twoCore t ⊔ L := (mem_PL_or_mul_tau_mem h hgH).resolve_left hgPL
    have hxH : g * tau ∈ invCent t := (invCent t).mul_mem hgH (tau_mem_invCent h)
    have hxt : (g * tau) * t = t * (g * tau) := by
      calc (g * tau) * t = g * (tau * t) := by group
        _ = g * (t * tau) := by rw [(ht_comm_tau_of h h44).symm]
        _ = (g * t) * tau := by group
        _ = (t * g) * tau := by rw [hgt]
        _ = t * (g * tau) := by group
    have hxtau : (g * tau) * tau = tau * (g * tau) := by
      have hval : tau * (g * tau) = g := by
        calc tau * (g * tau) = (tau * g) * tau := by group
          _ = (g * tau) * tau := by rw [← hgtau]
          _ = g * (tau * tau) := by group
          _ = g := by rw [htau2_of h44, mul_one]
      calc (g * tau) * tau = g * (tau * tau) := by group
        _ = g := by rw [htau2_of h44, mul_one]
        _ = tau * (g * tau) := hval.symm
    have hx := mem_sup_of_mem_PL h h43 h44 hxH hxPL hxtau
    have hg_eq : g = (g * tau) * tau := by rw [mul_assoc, htau2_of h44, mul_one]
    rw [hg_eq]
    exact Subgroup.mul_mem _ hx (Subgroup.mem_sup_left htauE)

private lemma eps_mem_twoCore (h : Ctx t L S x₁ x₂ lam rho tau) {eps : G}
    (heps : eps = 1 ∨ eps = t) : eps ∈ twoCore t := by
  rcases heps with rfl | rfl
  · exact Subgroup.one_mem _
  · exact h.hyp.mem_twoCore

private lemma eps_tau_comm (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) {eps : G}
    (heps : eps = 1 ∨ eps = t) : eps * tau = tau * eps := by
  rcases heps with rfl | rfl
  · rw [one_mul, mul_one]
  · exact ht_comm_tau_of h h44

private lemma tau_coset_caseA (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {eps : G}
    (heps : eps = 1 ∨ eps = t) {u : G} (hu : u ∈ L)
    {g₀ : G} (hg₀H : g₀ ∈ invCent t) (hg₀PL : g₀ ∈ twoCore t ⊔ L)
    {p : G} (hp : p ∈ twoCore t)
    (hconj : g₀ * (eps * tau * u) * g₀⁻¹ = p * tau) :
    ∃ c ∈ L, c * (eps * tau) * c⁻¹ = eps * tau * u := by
  have htau2 := htau2_of h44
  have hepsP := eps_mem_twoCore h heps
  have hepsH : eps ∈ invCent t := twoCore_le_invCent t hepsP
  have heps_tau := eps_tau_comm h h44 heps
  have hγH : eps * tau * u ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).mul_mem hepsH (tau_mem_invCent h))
      (L_le_invCent h.hyp hu)
  obtain ⟨a, ha, l, hl, hg₀_eq⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hg₀PL
  have ha_cases := twoCore_eq_one_or_eq_t h h43 ha
  have hconj_al : g₀ * (eps * tau * u) * g₀⁻¹ = l * (eps * tau * u) * l⁻¹ := by
    rw [hg₀_eq]
    rcases ha_cases with ha1 | ha1
    · subst a; group
    · subst a
      have hxH : l * (eps * tau * u) * l⁻¹ ∈ invCent t :=
        (invCent t).mul_mem ((invCent t).mul_mem (L_le_invCent h.hyp hl) hγH)
          ((invCent t).inv_mem (L_le_invCent h.hyp hl))
      have htc : t * (l * (eps * tau * u) * l⁻¹) * t⁻¹ = l * (eps * tau * u) * l⁻¹ := by
        rw [(mem_invCent_iff.mp hxH).symm, mul_assoc, mul_inv_cancel, mul_one]
      calc (t * l) * (eps * tau * u) * (t * l)⁻¹
          = t * (l * (eps * tau * u) * l⁻¹) * t⁻¹ := by group
        _ = l * (eps * tau * u) * l⁻¹ := htc
  have heps_comm_l : eps * l = l * eps := twoCore_commute h.hyp eps hepsP l hl
  have hlγ : l * (eps * tau * u) * l⁻¹ = eps * tau * ((tau⁻¹ * l * tau) * u * l⁻¹) := by
    calc l * (eps * tau * u) * l⁻¹
        = (l * eps) * tau * u * l⁻¹ := by group
      _ = (eps * l) * tau * u * l⁻¹ := by rw [heps_comm_l.symm]
      _ = eps * tau * ((tau⁻¹ * l * tau) * u * l⁻¹) := by group
  have hl''L : (tau⁻¹ * l * tau) * u * l⁻¹ ∈ L := by
    have h1 : tau⁻¹ * l * tau ∈ L := by
      have h2 := conj_mem_L h ((invCent t).inv_mem (tau_mem_invCent h)) hl
      simpa using h2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 hu) (Subgroup.inv_mem _ hl)
  have hptau : p * tau = eps * tau * ((tau⁻¹ * l * tau) * u * l⁻¹) := by
    rw [← hconj, hconj_al, hlγ]
  have hp_tau : p * tau = tau * p := by
    rcases twoCore_eq_one_or_eq_t h h43 hp with hp1 | hp1
    · subst p; rw [one_mul, mul_one]
    · subst p; exact ht_comm_tau_of h h44
  have hp_eq : p = eps * ((tau⁻¹ * l * tau) * u * l⁻¹) := by
    calc p = tau⁻¹ * (p * tau) := by rw [hp_tau]; group
      _ = tau⁻¹ * (eps * tau * ((tau⁻¹ * l * tau) * u * l⁻¹)) := by rw [hptau]
      _ = eps * ((tau⁻¹ * l * tau) * u * l⁻¹) := by
            rw [show tau⁻¹ * (eps * tau * ((tau⁻¹ * l * tau) * u * l⁻¹))
                  = (tau⁻¹ * (eps * tau)) * ((tau⁻¹ * l * tau) * u * l⁻¹) from by group,
              show tau⁻¹ * (eps * tau) = eps from by
                rw [heps_tau, ← mul_assoc, inv_mul_cancel, one_mul]]
  have hl''_eq : (tau⁻¹ * l * tau) * u * l⁻¹ = eps⁻¹ * p := by
    rw [hp_eq]
    group
  have hl''P : (tau⁻¹ * l * tau) * u * l⁻¹ ∈ twoCore t := by
    rw [hl''_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hepsP) hp
  have hl''one : (tau⁻¹ * l * tau) * u * l⁻¹ = 1 := by
    have hmem : (tau⁻¹ * l * tau) * u * l⁻¹ ∈ twoCore t ⊓ L := ⟨hl''P, hl''L⟩
    rw [h.hyp.twoCore_inf] at hmem
    simpa using hmem
  have hlγ_eps : l * (eps * tau * u) * l⁻¹ = eps * tau := by
    rw [hlγ, hl''one, mul_one]
  refine ⟨l⁻¹, Subgroup.inv_mem _ hl, ?_⟩
  have hmain : l⁻¹ * (eps * tau) * l = eps * tau * u := by
    calc l⁻¹ * (eps * tau) * l = l⁻¹ * (l * (eps * tau * u) * l⁻¹) * l := by rw [hlγ_eps]
      _ = eps * tau * u := by group
  simpa using hmain

private lemma tau_coset_of_eps (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {eps : G}
    (heps : eps = 1 ∨ eps = t) :
    ∀ u ∈ L, (eps * tau * u) * (eps * tau * u) = 1 →
      ∃ c ∈ L, c * (eps * tau) * c⁻¹ = eps * tau * u := by
  intro u hu hγ2
  have htau2 := htau2_of h44
  have hepsP := eps_mem_twoCore h heps
  have hepsH : eps ∈ invCent t := twoCore_le_invCent t hepsP
  have heps_tau := eps_tau_comm h h44 heps
  have hγH : eps * tau * u ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).mul_mem hepsH (tau_mem_invCent h))
      (L_le_invCent h.hyp hu)
  have hγPL : eps * tau * u ∉ twoCore t ⊔ L := by
    intro hmem
    apply h.tau_not_mem
    have h1 : tau = eps⁻¹ * (eps * tau * u) * u⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hepsP)) hmem)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu))
  have hγ2P : (eps * tau * u) ^ 2 ∈ twoCore t := by
    rw [pow_two, hγ2]
    exact Subgroup.one_mem _
  obtain ⟨g₀, hg₀H, p, hp, hconj⟩ := h.invol_outer (eps * tau * u) hγH hγPL hγ2P
  rcases mem_PL_or_mul_tau_mem h hg₀H with hg₀PL | hg₁PL
  · exact tau_coset_caseA h h43 h44 heps hu hg₀H hg₀PL hp hconj
  · have hg₁H : g₀ * tau ∈ invCent t := (invCent t).mul_mem hg₀H (tau_mem_invCent h)
    have hg₀_eq : g₀ = (g₀ * tau) * tau := by rw [mul_assoc, htau2, mul_one]
    have hu'L : tau * u * tau⁻¹ ∈ L := conj_mem_L h (tau_mem_invCent h) hu
    have hγ'_eq : tau * (eps * tau * u) * tau⁻¹ = eps * tau * (tau * u * tau⁻¹) := by
      calc tau * (eps * tau * u) * tau⁻¹
          = (tau * eps) * (tau * u) * tau⁻¹ := by group
        _ = (eps * tau) * (tau * u) * tau⁻¹ := by rw [heps_tau.symm]
        _ = eps * tau * (tau * u * tau⁻¹) := by group
    have hγ'2 : (eps * tau * (tau * u * tau⁻¹)) * (eps * tau * (tau * u * tau⁻¹)) = 1 := by
      rw [← hγ'_eq]
      calc (tau * (eps * tau * u) * tau⁻¹) * (tau * (eps * tau * u) * tau⁻¹)
          = tau * ((eps * tau * u) * (eps * tau * u)) * tau⁻¹ := by group
        _ = tau * 1 * tau⁻¹ := by rw [hγ2]
        _ = 1 := by group
    have hconj' : (g₀ * tau) * (eps * tau * (tau * u * tau⁻¹)) * (g₀ * tau)⁻¹ = p * tau := by
      rw [← hγ'_eq]
      calc (g₀ * tau) * (tau * (eps * tau * u) * tau⁻¹) * (g₀ * tau)⁻¹
          = ((g₀ * tau) * tau) * (eps * tau * u) * ((g₀ * tau) * tau)⁻¹ := by group
        _ = g₀ * (eps * tau * u) * g₀⁻¹ := by rw [← hg₀_eq]
        _ = p * tau := hconj
    obtain ⟨c', hc'L, hc'⟩ :=
      tau_coset_caseA h h43 h44 heps hu'L hg₁H hg₁PL hp hconj'
    refine ⟨tau⁻¹ * c' * tau, ?_, ?_⟩
    · simpa using conj_mem_L h ((invCent t).inv_mem (tau_mem_invCent h)) hc'L
    · have hmiddle : tau * (eps * tau) * tau⁻¹ = eps * tau := by
        calc tau * (eps * tau) * tau⁻¹ = (tau * eps) * tau * tau⁻¹ := by group
          _ = (eps * tau) * tau * tau⁻¹ := by rw [heps_tau.symm]
          _ = eps * tau := by group
      have htauinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
      have hfinal : tau⁻¹ * c' * tau * (eps * tau) * (tau⁻¹ * c' * tau)⁻¹
          = eps * tau * u := by
        rw [show tau⁻¹ * c' * tau * (eps * tau) * (tau⁻¹ * c' * tau)⁻¹
              = tau⁻¹ * c' * (tau * (eps * tau) * tau⁻¹) * c'⁻¹ * tau from by group,
            hmiddle]
        rw [show tau⁻¹ * c' * (eps * tau) * c'⁻¹ * tau
              = tau⁻¹ * (c' * (eps * tau) * c'⁻¹) * tau from by group, hc']
        rw [show tau⁻¹ * (eps * tau * (tau * u * tau⁻¹)) * tau = eps * tau * u from by
          rw [htauinv]
          calc tau * (eps * tau * (tau * u * tau)) * tau
              = (tau * eps) * (tau * tau) * u * (tau * tau) := by group
            _ = (tau * eps) * 1 * u * 1 := by rw [htau2]
            _ = tau * eps * u := by rw [mul_one, mul_one]
            _ = eps * tau * u := by rw [heps_tau.symm]]
      simpa using hfinal

private lemma conj_tau_of_mem_PL_ne (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {g : G}
    (hgPL : g ∈ twoCore t ⊔ L) : g * tau * g⁻¹ ≠ t * tau := by
  obtain ⟨a, ha, l, hl, hg_eq⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hgPL
  have hconj_l : g * tau * g⁻¹ = l * tau * l⁻¹ := by
    rw [hg_eq]
    calc (a * l) * tau * (a * l)⁻¹ = a * (l * tau * l⁻¹) * a⁻¹ := by group
      _ = l * tau * l⁻¹ := conj_eq_of_mem_twoCore h h43 ha
        ((invCent t).mul_mem ((invCent t).mul_mem (L_le_invCent h.hyp hl) (tau_mem_invCent h))
          ((invCent t).inv_mem (L_le_invCent h.hyp hl)))
  have hmain : g * tau * g⁻¹ = tau * ((tau⁻¹ * l * tau) * l⁻¹) := by
    rw [hconj_l]
    group
  intro heq
  have hm_L : (tau⁻¹ * l * tau) * l⁻¹ ∈ L := by
    have h1 : tau⁻¹ * l * tau ∈ L := by
      have h2 := conj_mem_L h ((invCent t).inv_mem (tau_mem_invCent h)) hl
      simpa using h2
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hl)
  have hm_t : (tau⁻¹ * l * tau) * l⁻¹ = t := by
    have h1 : tau * ((tau⁻¹ * l * tau) * l⁻¹) = t * tau := by rw [← hmain, heq]
    have h2 : (tau⁻¹ * l * tau) * l⁻¹ = tau⁻¹ * (t * tau) := by
      calc (tau⁻¹ * l * tau) * l⁻¹
          = tau⁻¹ * (tau * ((tau⁻¹ * l * tau) * l⁻¹)) := by group
        _ = tau⁻¹ * (t * tau) := by rw [h1]
    rw [h2, ht_comm_tau_of h h44, ← mul_assoc, inv_mul_cancel, one_mul]
  exact t_not_mem_L h.hyp (hm_t ▸ hm_L)

private lemma conj_tau_ne_t_mul_tau (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    ∀ g ∈ invCent t, g * tau * g⁻¹ ≠ t * tau := by
  intro g hgH
  rcases mem_PL_or_mul_tau_mem h hgH with hgPL | hgPL
  · exact conj_tau_of_mem_PL_ne h h43 h44 hgPL
  · have hg_eq : g = (g * tau) * tau := by rw [mul_assoc, htau2_of h44, mul_one]
    have hginv : g⁻¹ = tau * (g * tau)⁻¹ := by
      conv_lhs => rw [hg_eq]
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (htau2_of h44)]
    have hconj_eq : g * tau * g⁻¹ = (g * tau) * tau * (g * tau)⁻¹ := by
      rw [hginv]
      group
    rw [hconj_eq]
    exact conj_tau_of_mem_PL_ne h h43 h44 hgPL

theorem centralizer_t_tau_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    centralizer ((closure {t, tau} : Subgroup G) : Set G) =
      closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} ∧
    CFSG.Open.IsElemAbelian 2 (closure {t, tau} : Subgroup G) ∧
    Nat.card (closure {t, tau} : Subgroup G) = 4 ∧
    closure {t, tau} ⊓ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} = (⊥ : Subgroup G) ∧
    (∀ a ∈ (closure {t, tau} : Subgroup G),
      ∀ b ∈ (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Subgroup G), a * b = b * a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_antisymm (centralizer_le_sup h h43 h44) (sup_le_centralizer h h43 h44)
  · exact E4_isElemAbelian h h44
  · exact E4_card h h44
  · exact E4_inf_Q_eq_bot h h43 h44
  · intro a ha b hb
    exact commute_E4_Q h h43 h44 ha hb

theorem five_classes_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    (∀ g ∈ invCent t, g * g = 1 → g ≠ 1 → ∃ h ∈ invCent t,
      h * g * h⁻¹ = t ∨ h * g * h⁻¹ = (x₁ * x₂) ^ 2 ∨ h * g * h⁻¹ = tau ∨
      h * g * h⁻¹ = t * (x₁ * x₂) ^ 2 ∨ h * g * h⁻¹ = t * tau) ∧
    List.Pairwise (fun a b : G => ∀ h ∈ invCent t, h * a * h⁻¹ ≠ b)
      [t, (x₁ * x₂) ^ 2, tau, t * (x₁ * x₂) ^ 2, t * tau] := by
  constructor
  · intro g hgH hg2 hg1
    by_cases hgPL : g ∈ twoCore t ⊔ L
    · obtain ⟨k, hkH, hkconj⟩ := h.invol_PL g hgPL hg2 hg1
      refine ⟨k, hkH, ?_⟩
      rcases hkconj with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · have hg2P : g ^ 2 ∈ twoCore t := by
        rw [pow_two, hg2]
        exact Subgroup.one_mem _
      obtain ⟨k, hkH, p, hp, hkconj⟩ := h.invol_outer g hgH hgPL hg2P
      refine ⟨k, hkH, ?_⟩
      rcases twoCore_eq_one_or_eq_t h h43 hp with hp1 | hp1
      · subst p
        refine Or.inr (Or.inr (Or.inl ?_))
        rwa [one_mul] at hkconj
      · subst p
        exact Or.inr (Or.inr (Or.inr (Or.inr hkconj)))
  · have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h.toCtx0).2
    have hzPL : (x₁ * x₂) ^ 2 ∈ twoCore t ⊔ L := Subgroup.mem_sup_right hzL
    have htzPL : t * (x₁ * x₂) ^ 2 ∈ twoCore t ⊔ L :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left h.hyp.mem_twoCore) hzPL
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))))
    · intro b hb
      rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton] at hb
      rcases hb with hb1 | hb1 | hb1 | hb1
      · subst b; exact h.invol_PL_distinct.1
      · subst b
        intro g gg
        rw [conj_t_self h gg]
        exact t_ne_tau_of h
      · subst b; exact h.invol_PL_distinct.2.1
      · subst b
        intro g gg
        rw [conj_t_self h gg]
        exact (t_mul_tau_ne_t h).symm
    · intro b hb
      rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hb
      rcases hb with hb1 | hb1 | hb1
      · subst b
        intro g gg heq
        apply h.tau_not_mem
        rw [← heq]
        exact conj_mem_PL h gg hzPL
      · subst b; exact h.invol_PL_distinct.2.2
      · subst b
        intro g gg heq
        apply t_mul_tau_not_mem_PL h
        rw [← heq]
        exact conj_mem_PL h gg hzPL
    · intro b hb
      rw [List.mem_cons, List.mem_singleton] at hb
      rcases hb with hb1 | hb1
      · subst b
        intro g gg heq
        apply h.tau_not_mem
        have h1 : tau = g⁻¹ * (t * (x₁ * x₂) ^ 2) * g := by
          calc tau = g⁻¹ * (g * tau * g⁻¹) * g := by group
            _ = g⁻¹ * (t * (x₁ * x₂) ^ 2) * g := by rw [heq]
        rw [h1]
        simpa using conj_mem_PL h ((invCent t).inv_mem gg) htzPL
      · subst b; exact conj_tau_ne_t_mul_tau h h43 h44
    · intro b hb
      rw [List.mem_singleton] at hb
      subst b
      intro g gg heq
      apply t_mul_tau_not_mem_PL h
      rw [← heq]
      exact conj_mem_PL h gg htzPL
    · intro b hb
      exact absurd hb (by simp)

theorem involutions_tau_coset_of (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    (∀ u ∈ L, (tau * u) * (tau * u) = 1 → ∃ c ∈ L, c * tau * c⁻¹ = tau * u) ∧
    (∀ u ∈ L, (t * tau * u) * (t * tau * u) = 1 → ∃ c ∈ L, c * (t * tau) * c⁻¹ = t * tau * u) := by
  constructor
  · intro u hu h2
    have h1 := tau_coset_of_eps h h43 h44 (eps := (1 : G)) (Or.inl rfl)
    have h3 := h1 u hu (by simpa using h2)
    simpa using h3
  · intro u hu h2
    have h1 := tau_coset_of_eps h h43 h44 (eps := t) (Or.inr rfl)
    exact h1 u hu h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
