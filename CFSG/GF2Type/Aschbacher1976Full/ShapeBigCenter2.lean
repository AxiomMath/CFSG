module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeBigCenter
public import CFSG.GF2Type.Aschbacher1976Full.ShapeSmall
public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm CFSG.Blueprint Subgroup
open scoped commutatorElement

theorem commutator_mul_mul {P : Type*} [Group P] {a b c d : P} (hac : Commute a c)
    (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    (a * c) * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (c * d * c⁻¹ * d⁻¹) := by
  have h1 : Commute a⁻¹ (c * d * c⁻¹) :=
    ((hac.mul_right had).mul_right hac.inv_right).inv_left
  have h2 : Commute b⁻¹ (c * d * c⁻¹ * d⁻¹) :=
    (((hbc.mul_right hbd).mul_right hbc.inv_right).mul_right hbd.inv_right).inv_left
  calc (a * c) * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hbc.symm.eq]
    _ = a * b * ((c * d * c⁻¹) * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * (c * d * c⁻¹)) * d⁻¹ * b⁻¹ := by rw [← h1.eq]
    _ = a * b * a⁻¹ * ((c * d * c⁻¹ * d⁻¹) * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (c * d * c⁻¹ * d⁻¹)) := by rw [← h2.eq]
    _ = (a * b * a⁻¹ * b⁻¹) * (c * d * c⁻¹ * d⁻¹) := by group

section Frattini

variable {P : Type*} [Group P] [Finite P] {D E R : Subgroup P} {z : P}

theorem four_lt_index_frattini (hP : IsPGroup 2 P) (c : CritData D E R z)
    (hk8 : 8 ≤ Nat.card (Zof D)) {w : ℕ} (hw : 1 ≤ w) (hEcard : Nat.card E = 2 ^ (1 + 2 * w))
    (hER : E ⊓ R = zpowers z) : 4 < (frattini P).index := by
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  haveI := c.R_normal
  haveI : Fact (IsPGroup 2 ↥R) := ⟨hP.to_subgroup R⟩
  obtain ⟨a, k, hag⟩ := exists_gen hP c
  have hk : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hag.card] at this
    omega
  set N : Subgroup P := (frattini ↥R).map R.subtype with hN
  have hNR : N ≤ R := Subgroup.map_subtype_le _
  have hZR : Zof D ≤ R := c.RZ.symm.le.trans inf_le_left
  have hsqR : ∀ r ∈ R, r ^ 2 ∈ N := fun r hr =>
    Subgroup.mem_map.mpr
      ⟨(⟨r, hr⟩ : ↥R) ^ 2, pth_power_mem_frattini_of_isPGroup (R := ↥R) (p := 2) ⟨r, hr⟩, rfl⟩
  have hzN : z ∈ N := by
    rw [hag.z_eq c (by omega)]
    have hb : a ^ 2 ^ (k - 2) ∈ R := hZR (pow_mem hag.mem _)
    have h2 : (a ^ 2 ^ (k - 2)) ^ 2 = a ^ 2 ^ (k - 1) := by
      rw [← pow_mul, ← pow_succ]
      congr 2
      omega
    rw [← h2]
    exact hsqR _ hb
  have hzpN : zpowers z ≤ N := zpowers_le.mpr hzN
  have hsq : ∀ x : P, x ^ 2 ∈ N := by
    intro x
    have hx : x ∈ E ⊔ R := by rw [c.ER]; exact mem_top x
    obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hx
    have hcr : Commute e r := c.E_R_comm he hr
    rw [hcr.mul_pow]
    exact mul_mem (hzpN (c.E_sq e he)) (hsqR r hr)
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ N := by
    intro x y
    have hx : x ∈ E ⊔ R := by rw [c.ER]; exact mem_top x
    have hy : y ∈ E ⊔ R := by rw [c.ER]; exact mem_top y
    obtain ⟨e₁, he₁, r₁, hr₁, rfl⟩ := mem_sup_of_normal_right.mp hx
    obtain ⟨e₂, he₂, r₂, hr₂, rfl⟩ := mem_sup_of_normal_right.mp hy
    have h := commutator_mul_mul (c.E_R_comm he₁ hr₁ : Commute e₁ r₁) (c.E_R_comm he₁ hr₂)
      (c.E_R_comm he₂ hr₁) (c.E_R_comm he₂ hr₂)
    rw [commutatorElement_def, h]
    refine mul_mem (hzpN (c.E_comm e₁ he₁ e₂ he₂)) ?_
    have h1 : (⁅(⟨r₁, hr₁⟩ : ↥R), ⟨r₂, hr₂⟩⁆ : ↥R) ∈ frattini ↥R :=
      commutator_le_frattini_of_isPGroup (p := 2) (by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have hΦ : frattini P ≤ N := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro g (hg | ⟨x, rfl⟩)
    · have : commutator P ≤ N := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        exact hcomm x y
      exact this hg
    · exact hsq x
  have hRidx : 4 ≤ R.index := by
    have h1 : R.relIndex (E ⊔ R) = R.relIndex E := Subgroup.relIndex_sup_right E R
    rw [c.ER, Subgroup.relIndex_top_right] at h1
    have h2 : Nat.card (R.subgroupOf E) * (R.subgroupOf E).index = Nat.card E :=
      Subgroup.card_mul_index _
    have h3 : Nat.card (R.subgroupOf E) = 2 := by
      have h7 : Nat.card ((R.subgroupOf E).map E.subtype) = Nat.card (R.subgroupOf E) :=
        Subgroup.card_map_of_injective E.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_comm, hER, Nat.card_zpowers, c.z_ord] at h7
      exact h7.symm
    have h4 : R.relIndex E = (R.subgroupOf E).index := rfl
    rw [h3, hEcard] at h2
    rw [h1, h4]
    have h5 : 2 ^ (1 + 2 * w) = 2 * 2 ^ (2 * w) := by rw [pow_add, pow_one]
    have h6 : 2 ^ 2 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrel : N.relIndex R = (frattini ↥R).index := by
    have : N.subgroupOf R = frattini ↥R :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    exact congrArg Subgroup.index this
  have hfr : 2 ≤ (frattini ↥R).index := by
    have hne : (frattini ↥R).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      have h1 : (⊥ : Subgroup ↥R) = ⊤ := lemma_1_7_a (p := 2) ⊥ (by rw [bot_sup_eq]; exact h)
      have h2 : (⟨z, hZR c.z_mem⟩ : ↥R) ∈ (⊥ : Subgroup ↥R) := h1 ▸ mem_top _
      have h3 : z = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp h2)
      have := c.z_ord
      rw [h3, orderOf_one] at this
      omega
    have := Subgroup.index_ne_zero_of_finite (H := frattini ↥R)
    omega
  have hNidx : 8 ≤ N.index := by
    have := Subgroup.relIndex_mul_index hNR
    rw [hrel] at this
    calc 8 = 2 * 4 := by norm_num
      _ ≤ (frattini ↥R).index * R.index := Nat.mul_le_mul hfr hRidx
      _ = N.index := this
  have hdvd : N.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hΦ
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  omega

end Frattini

section NotTwoGen

variable {G : Type} [Group G] [Finite G] {z : G}

theorem not_two_generated (hsymp : CFSG.Open.GLASymplecticType (Fz z))
    {D E R : Subgroup ↥(Fz z)} {zz : ↥(Fz z)} (c : CritData D E R zz)
    (hk8 : 8 ≤ Nat.card (Zof D)) {w : ℕ} (hw : 1 ≤ w) (hEcard : Nat.card E = 2 ^ (1 + 2 * w))
    (hER : E ⊓ R = zpowers zz) :
    ¬ ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = Fz z := by
  rintro ⟨s, hs2, hs⟩
  have hrank : Group.rank ↥(Fz z) ≤ 2 := by
    rw [← hs]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs2
  obtain ⟨d, hd, hcard, -, -⟩ :=
    Aschbacher1976Common.frattini_quotient_elementary_of_rank_le_two hsymp.1 hrank
  have h4 := four_lt_index_frattini hsymp.1 c hk8 hw hEcard hER
  have h5 : (frattini ↥(Fz z)).index = 2 ^ d := hcard
  have h6 : 2 ^ d ≤ 4 := calc 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
    _ = 4 := by norm_num
  omega

end NotTwoGen

section BigCenter

variable {G : Type} [Group G] [Finite G] {z : G}

theorem shape_big_center {z : G} (hsymp : CFSG.Open.GLASymplecticType (Fz z))
    {D E R : Subgroup ↥(Fz z)} {zz : ↥(Fz z)} (c : CritData D E R zz) (hzz : zz = zF z)
    (hmax : ∀ D' : Subgroup ↥(Fz z), ThompsonCritical D' → Nat.card D' ≤ Nat.card D)
    (hk8 : 8 ≤ Nat.card (Zof D)) {w : ℕ} (hw : 1 ≤ w) (hEcard : Nat.card E = 2 ^ (1 + 2 * w))
    (hER : E ⊓ R = zpowers zz) : Asc76Shape z := by
  haveI := c.char
  haveI : D.Characteristic := c.crit.1
  refine Asc76Shape.bigCenter ⟨lift (Zof D), lift (Q4 c), isCyclic_lift c.cyc, ?_, ?_, lift_le _,
    ?_, lift_le _, ?_, ?_, ?_, ?_⟩
  · rw [card_lift]
    exact hk8
  · have h1 : (zF z) ∈ Zof D := hzz ▸ c.z_mem
    exact mem_lift.mpr h1
  · exact fun h hh =>
      conjugate_eq_of_invariant (K := Hz z) (fun h hh x hx => char_conj_mem hh hx) hh
  · exact fun h hh => conjugate_eq_of_invariant (K := Hz z) (fun h hh x hx => Q4_conj c hh hx) hh
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have h4 : q ^ 4 = 1 := (mem_Q4.mp hq).2
    change (q : G) ^ 4 = 1
    rw [← Subgroup.coe_pow, h4]
    rfl
  · exact fun h hh hc => cent_Q4_le hsymp c hmax hk8 hh hc
  · exact not_two_generated hsymp c hk8 hw hEcard hER

end BigCenter

end CFSG.GF2Type.Aschbacher1976Full.Shape
