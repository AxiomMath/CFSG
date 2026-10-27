module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq mem_normalizer_inf
  mem_normalizer_sup)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

@[expose] def miyamotoC0 (M E A : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (M : Set G) ∧ g ∈ normalizer (E : Set G) ∧
    g ∈ normalizer (A : Set G) ∧ ∀ w ∈ A, g * w * g⁻¹ * w⁻¹ ∈ E}
  mul_mem' := by
    rintro g k ⟨hgM, hgE, hgA, hg⟩ ⟨hkM, hkE, hkA, hk⟩
    refine ⟨mul_mem hgM hkM, mul_mem hgE hkE, mul_mem hgA hkA, fun w hw => ?_⟩
    rw [show g * k * w * (g * k)⁻¹ * w⁻¹ = g * (k * w * k⁻¹ * w⁻¹) * g⁻¹ * (g * w * g⁻¹ * w⁻¹) by
      group]
    exact mul_mem ((mem_normalizer_iff.1 hgE _).1 (hk w hw)) (hg w hw)
  one_mem' := ⟨one_mem _, one_mem _, one_mem _, fun w _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro g ⟨hgM, hgE, hgA, hg⟩
    refine ⟨inv_mem hgM, inv_mem hgE, inv_mem hgA, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hgA) w).1 hw
      rwa [inv_inv] at this
    have := inv_mem (hg _ hw')
    rw [show (g * (g⁻¹ * w * g) * g⁻¹ * (g⁻¹ * w * g)⁻¹)⁻¹ = g⁻¹ * w * g * w⁻¹ by group] at this
    rwa [inv_inv]

theorem le_normalizer_miyamotoC0 [Finite G] {M E A : Subgroup G} {x : G}
    (hxM : x ∈ normalizer (M : Set G)) (hxE : x ∈ normalizer (E : Set G))
    (hxA : x ∈ normalizer (A : Set G)) : x ∈ normalizer (miyamotoC0 M E A : Set G) := by
  refine mem_normalizer_fintype fun g hg => ?_
  obtain ⟨hgM, hgE, hgA, hgw⟩ := hg
  refine ⟨mul_mem (mul_mem hxM hgM) (inv_mem hxM), mul_mem (mul_mem hxE hgE) (inv_mem hxE),
    mul_mem (mul_mem hxA hgA) (inv_mem hxA), fun w hw => ?_⟩
  have hw' : x⁻¹ * w * x ∈ A := by
    have := (mem_normalizer_iff.1 (inv_mem hxA) w).1 hw
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.1 hxE _).1 (hgw _ hw')
  rwa [show x * (g * (x⁻¹ * w * x) * g⁻¹ * (x⁻¹ * w * x)⁻¹) * x⁻¹ =
    x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ * w⁻¹ by group] at h1

end Generic

section Generic2

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer' {N H : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ H) :
    ∃ n ∈ N, ∃ k ∈ H, x = n * k := by
  have : x ∈ ((N ⊔ H : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N H hHN] at this
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.1 this
  exact ⟨n, hn, k, hk, rfl⟩

end Generic2

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem E_comm_A2 (hS : Setting h L η t Q T) {e a : G} (he : e ∈ miyamotoEG h L η Q)
    (ha : a ∈ miyamotoA2G h L η) : e * a = a * e :=
  hS.E_comm_PG he (hS.A2G_le_PG ha)

theorem t_mem_M (hS : Setting h L η t Q T) : t ∈ miyamotoM0 Q :=
  hS.B2_le_M (mem_sup_left (mem_zpowers t))

theorem A2_le_M (hS : Setting h L η t Q T) : miyamotoA2G h L η ≤ miyamotoM0 Q :=
  le_sup_right.trans hS.B2_le_M

theorem E_le_M (hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoM0 Q :=
  hS.E_le_Y.trans hS.Y_le_M

theorem EA2_le_M (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊔ miyamotoA2G h L η ≤ miyamotoM0 Q :=
  sup_le hS.E_le_M hS.A2_le_M

theorem t_mem_normalizer_E (hS : Setting h L η t Q T) :
    t ∈ normalizer (miyamotoEG h L η Q : Set G) :=
  hS.H_le_normalizer_E (hS.M_le_H hS.t_mem_M)

theorem t_not_mem_EA2 (hS : Setting h L η t Q T) :
    t ∉ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := by
  intro ht
  obtain ⟨e, he, a, ha, hea⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he a ha => hS.E_comm_A2 he ha) ht
  have hat : a * t = t * a :=
    mem_centralizer_singleton_iff.1 (hS.PG_le_C (hS.A2G_le_PG ha))
  have he' : e = t * a⁻¹ := by rw [hea]; group
  have het : e * t = t * e := by
    rw [he', mul_assoc, ← (Commute.inv_left hat).eq, ← mul_assoc]
  have heZ : e ∈ miyamotoZG h L η := by
    refine (hS.crossed_eq_one_iff_E he).1 ?_
    rw [mul_assoc e⁻¹, ← het, inv_mul_cancel_left, hS.t_mul_t]
  have : t ∈ L := by
    rw [hea]
    exact mul_mem (miyamotoPull_le h L η _ heZ) (miyamotoPull_le h L η _ ha)
  exact hS.t_not_mem_L this

theorem mem_EA2_or_of_mem_M (hS : Setting h L η t Q T) {m : G} (hm : m ∈ miyamotoM0 Q) :
    m ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η ∨
      t⁻¹ * m ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := by
  rw [← hS.sec3_3.2.2.1] at hm
  have hB2E : miyamotoB2 h L η t ≤ normalizer (miyamotoEG h L η Q : Set G) :=
    hS.B2_le_M.trans (hS.M_le_H.trans hS.H_le_normalizer_E)
  obtain ⟨e, he, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hB2E hm
  obtain ⟨u, hu, a, ha, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _)) hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  rcases hS.zpow_t_eq k with h1 | h1
  · left
    rw [h1, one_mul]
    exact mul_mem (mem_sup_left he) (mem_sup_right ha)
  · right
    rw [h1]
    have hte : t⁻¹ * e * t ∈ miyamotoEG h L η Q := by
      have := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_E) e).1 he
      rwa [inv_inv] at this
    rw [show t⁻¹ * (e * (t * a)) = (t⁻¹ * e * t) * a by group]
    exact mul_mem (mem_sup_left hte) (mem_sup_right ha)

theorem conj_t_mem_EA2 (hS : Setting h L η t Q T) {g : G}
    (hgM : g ∈ normalizer (miyamotoM0 Q : Set G))
    (hgA : g ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G)) :
    t⁻¹ * (g * t * g⁻¹) ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := by
  rcases hS.mem_EA2_or_of_mem_M ((mem_normalizer_iff.1 hgM t).1 hS.t_mem_M) with h1 | h1
  · exact absurd ((mem_normalizer_iff.1 hgA t).2 h1) hS.t_not_mem_EA2
  · exact h1

theorem H_le_normalizer_EA2 (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤
      normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_sup (hS.H_le_normalizer_E hg) (hS.H_le_normalizer_A2 hg)

theorem H_le_normalizers (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer (CFSG.centerIn Q : Set G)) :
    g ∈ normalizer (miyamotoM0 Q : Set G) ∧ g ∈ normalizer (miyamotoEG h L η Q : Set G) ∧
      g ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) :=
  ⟨hS.H_le_normalizer_M hg, hS.H_le_normalizer_E hg, hS.H_le_normalizer_EA2 hg⟩

theorem E_le_EA2 (_hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := le_sup_left

theorem normal_E_subgroupOf_EA2 (hS : Setting h L η t Q T) :
    ((miyamotoEG h L η Q).subgroupOf (miyamotoEG h L η Q ⊔ miyamotoA2G h L η)).Normal := by
  refine (normal_subgroupOf_iff_le_normalizer hS.E_le_EA2).2 (sup_le le_normalizer fun a ha => ?_)
  exact mem_normalizer_fintype fun e he => by
    rw [← hS.E_comm_A2 he ha, mul_inv_cancel_right]
    exact he

theorem exists_card_C0_eq (hS : Setting h L η t Q T)
    (hsurj : ∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η, ∃ g ∈ miyamotoC0 (miyamotoM0 Q)
      (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η),
      w⁻¹ * (t⁻¹ * (g * t * g⁻¹)) ∈ miyamotoEG h L η Q) :
    ∃ K₀ : Subgroup G, K₀ ≤ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ∧
      (∀ g ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η),
        t⁻¹ * (g * t * g⁻¹) ∈ miyamotoEG h L η Q → g ∈ K₀) ∧
      Nat.card (miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η)) = (2 ^ f) ^ 4 * Nat.card K₀ := by
  set E := miyamotoEG h L η Q with hE
  set EA := miyamotoEG h L η Q ⊔ miyamotoA2G h L η with hEA
  set C₀ := miyamotoC0 (miyamotoM0 Q) E EA with hC₀
  have := hS.normal_E_subgroupOf_EA2
  have hx : ∀ g ∈ C₀, t⁻¹ * (g * t * g⁻¹) ∈ EA := fun g hg => hS.conj_t_mem_EA2 hg.1 hg.2.2.1
  let φ : C₀ →* EA ⧸ E.subgroupOf EA :=
    MonoidHom.mk' (fun g => QuotientGroup.mk (⟨t⁻¹ * ((g : G) * t * (g : G)⁻¹), hx g g.2⟩ : EA))
      fun g k => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have hk := hx k k.2
        have := g.2.2.2.2 _ (inv_mem hk)
        simp only [coe_mul, coe_inv]
        rw [show (t⁻¹ * ((g : G) * (k : G) * t * ((g : G) * (k : G))⁻¹))⁻¹ *
            (t⁻¹ * ((g : G) * t * (g : G)⁻¹) * (t⁻¹ * ((k : G) * t * (k : G)⁻¹))) =
          (g : G) * (t⁻¹ * ((k : G) * t * (k : G)⁻¹))⁻¹ * (g : G)⁻¹ *
            (t⁻¹ * ((k : G) * t * (k : G)⁻¹))⁻¹⁻¹ by group]
        exact this
  have hφ : ∀ g : C₀, φ g = QuotientGroup.mk
      (⟨t⁻¹ * ((g : G) * t * (g : G)⁻¹), hx g g.2⟩ : EA) := fun _ => rfl
  have hrange : φ.range = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    induction w using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨g, hg, hgw⟩ := hsurj w w.2
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [hφ, QuotientGroup.eq, mem_subgroupOf]
    have := inv_mem hgw
    rw [mul_inv_rev, inv_inv] at this
    exact this
  refine ⟨φ.ker.map C₀.subtype, fun _ ⟨g, _, e⟩ => e ▸ g.2, fun g hg hgE => ⟨⟨g, hg⟩, ?_, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hgE
  · rw [Subgroup.card_map_of_injective C₀.subtype_injective]
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf EA)
    have hE' : Nat.card (E.subgroupOf EA) = Nat.card E :=
      Nat.card_congr (subgroupOfEquivOfLe hS.E_le_EA2).toEquiv
    rw [hE', hS.card_E_sup_A2, hS.card_E] at h2
    have hq : Nat.card (EA ⧸ E.subgroupOf EA) = (2 ^ f) ^ 4 := by
      have : (2 ^ f) ^ 4 * (2 ^ f) ^ 2 = Nat.card (EA ⧸ E.subgroupOf EA) * (2 ^ f) ^ 2 := by
        rw [← h2]; ring
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
    rw [← h1, hq, mul_comm]

theorem Z2_le_A2 (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoZ2 h) ≤ miyamotoA2G h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoZ2_le_A2 h)

theorem F_le_C0 (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ≤ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) := by
  intro x hx
  have hxF := hS.F_le_F1 hx
  have hxE : x ∈ normalizer (miyamotoEG h L η Q : Set G) :=
    mem_normalizer_fintype fun e he => hS.conj_mem_E_of_mem_F1 hxF he
  have hxA := hS.conj_EA2_eq hx
  refine ⟨mem_normalizer_fintype fun m hm => ?_, hxE, hxA, fun w hw => ?_⟩
  · rcases hS.mem_EA2_or_of_mem_M hm with h1 | h1
    · exact hS.EA2_le_M ((mem_normalizer_iff.1 hxA m).1 h1)
    · have hδ := hS.crossed_mem_Z2_of_mem_F (inv_mem hx)
      have hxt : x * t * x⁻¹ = (x⁻¹⁻¹ * t * x⁻¹ * t) * t := by
        rw [inv_inv, mul_assoc _ t t, hS.t_mul_t, mul_one]
      rw [show x * m * x⁻¹ = (x * t * x⁻¹) * (x * (t⁻¹ * m) * x⁻¹) by group, hxt]
      exact mul_mem (mul_mem (hS.A2_le_M (hS.Z2_le_A2 hδ)) hS.t_mem_M)
        (hS.EA2_le_M ((mem_normalizer_iff.1 hxA _).1 h1))
  · obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun e he a ha => hS.E_comm_A2 he ha) hw
    have h1 := hS.commutator_F_A2_mem_E hx ha
    have h2 := hS.conj_mem_E_of_mem_F1 hxF he
    rw [show x * (e * a) * x⁻¹ * (e * a)⁻¹ = (x * e * x⁻¹) * (x * a * x⁻¹ * a⁻¹) * e⁻¹ by
      group]
    exact mul_mem (mul_mem h2 h1) (inv_mem he)

theorem conj_t_eq_crossed (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoF1G h L η t) :
    t⁻¹ * (x * t * x⁻¹) = x⁻¹⁻¹ * t * x⁻¹ * t := by
  have hδ := hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 (inv_mem hx))
  have hc : (x⁻¹⁻¹ * t * x⁻¹ * t) * t = t * (x⁻¹⁻¹ * t * x⁻¹ * t) :=
    (mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t hδ))
  rw [inv_inv] at hc ⊢
  calc t⁻¹ * (x * t * x⁻¹) = t⁻¹ * ((x * t * x⁻¹ * t) * t) := by
        rw [mul_assoc (x * t * x⁻¹) t t, hS.t_mul_t, mul_one]
    _ = t⁻¹ * (t * (x * t * x⁻¹ * t)) := by rw [hc]
    _ = x * t * x⁻¹ * t := by group

theorem exists_C0_conj_eq_of_mem_Z2 (hS : Setting h L η t Q T) {z : G}
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    ∃ g ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η),
      t⁻¹ * (g * t * g⁻¹) = z := by
  obtain ⟨x, hx, hxz⟩ := hS.exists_F_crossed_eq hz
  refine ⟨x⁻¹, hS.F_le_C0 (inv_mem hx), ?_⟩
  rw [hS.conj_t_eq_crossed (inv_mem (hS.F_le_F1 hx)), inv_inv, inv_inv]
  exact hxz

theorem R2G_facts (hS : Setting h L η t Q T) :
    miyamotoR2G h L η ∈ normalizer (miyamotoM0 Q : Set G) ∧
      miyamotoR2G h L η ∈ normalizer (miyamotoEG h L η Q : Set G) ∧
      miyamotoR2G h L η ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) :
        Set G) ∧
      miyamotoR2G h L η * t = t * miyamotoR2G h L η := by
  have hH := hS.K0_le_H hS.R2G_mem_K0
  exact ⟨hS.H_le_normalizer_M hH, hS.H_le_normalizer_E hH, hS.H_le_normalizer_EA2 hH,
    mem_centralizer_singleton_iff.1 (hS.L_le_centralizer (η.symm _).2)⟩

theorem exists_C0_conj_eq_of_mem_rootA (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h)) :
    ∃ g ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η),
      t⁻¹ * (g * t * g⁻¹) = u := by
  have : CharP K 2 := h.charP
  obtain ⟨gu, ⟨a, hga⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  have hcS : miyamotoXGL h 0 0 a 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootC_le_SU ⟨a, rfl⟩
  set R : gramSU h (miyamotoJ4 K) := ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ with hR
  have hc : ((η.symm ⟨_, hcS⟩ : L) : G) ∈ miyamotoPull h L η (miyamotoZ2 h) :=
    hS.rootC_le_Z2 ((symm_mem_miyamotoPull_iff h L η).2 ⟨a, rfl⟩)
  obtain ⟨g₀, hg₀, hg₀c⟩ := hS.exists_C0_conj_eq_of_mem_Z2 hc
  obtain ⟨hrM, hrE, hrA, hrt⟩ := hS.R2G_facts
  set r := miyamotoR2G h L η with hr
  have hrC0 := le_normalizer_miyamotoC0 (inv_mem hrM) (inv_mem hrE) (inv_mem hrA)
  refine ⟨r⁻¹ * g₀ * r⁻¹⁻¹, (mem_normalizer_iff.1 hrC0 g₀).1 hg₀, ?_⟩
  have e1 : t⁻¹ * (r⁻¹ * g₀ * r⁻¹⁻¹ * t * (r⁻¹ * g₀ * r⁻¹⁻¹)⁻¹) =
      r⁻¹ * (t⁻¹ * (g₀ * t * g₀⁻¹)) * r := by
    calc t⁻¹ * (r⁻¹ * g₀ * r⁻¹⁻¹ * t * (r⁻¹ * g₀ * r⁻¹⁻¹)⁻¹)
        = t⁻¹ * r⁻¹ * g₀ * (r * t * r⁻¹) * g₀⁻¹ * r := by group
      _ = t⁻¹ * r⁻¹ * g₀ * t * g₀⁻¹ * r := by rw [hrt, mul_inv_cancel_right]
      _ = (r * t)⁻¹ * g₀ * t * g₀⁻¹ * r := by group
      _ = (t * r)⁻¹ * g₀ * t * g₀⁻¹ * r := by rw [hrt]
      _ = r⁻¹ * (t⁻¹ * (g₀ * t * g₀⁻¹)) * r := by group
  rw [e1, hg₀c, hr, miyamotoR2G]
  rw [← coe_symm_conj_inv h L η]
  congr 2
  apply Subtype.ext
  simp only [coe_mul, coe_inv]
  rw [hga]
  exact miyamotoR2_conj_rootC h a

theorem C0_surj (hS : Setting h L η t Q T) :
    ∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η, ∃ g ∈ miyamotoC0 (miyamotoM0 Q)
      (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η),
      w⁻¹ * (t⁻¹ * (g * t * g⁻¹)) ∈ miyamotoEG h L η Q := by
  have : CharP K 2 := h.charP
  intro w hw
  obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he a ha => hS.E_comm_A2 he ha) hw
  obtain ⟨z, hz, u, hu, rfl⟩ := exists_mul_of_mem_miyamotoPull h L η
    ((miyamotoZ2_le_A1 h).trans ((miyamotoA1_le_P h).trans (miyamotoUnipotent_le_SU h false false)))
    hS.rootA_le_SU (miyamotoZ2_mul_rootA h) ha
  obtain ⟨gz, hgz, hgzz⟩ := hS.exists_C0_conj_eq_of_mem_Z2 hz
  obtain ⟨gu, hgu, hguu⟩ := hS.exists_C0_conj_eq_of_mem_rootA hu
  refine ⟨gz * gu, mul_mem hgz hgu, ?_⟩
  have e1 : t⁻¹ * (gz * gu * t * (gz * gu)⁻¹) =
      (t⁻¹ * (gz * t * gz⁻¹)) * (gz * (t⁻¹ * (gu * t * gu⁻¹)) * gz⁻¹) := by group
  rw [e1, hgzz, hguu]
  have huEA : u ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η :=
    mem_sup_right (hS.rootA_le_A2G hu)
  set c := gz * u * gz⁻¹ * u⁻¹ with hc
  have hcE : c ∈ miyamotoEG h L η Q := hgz.2.2.2 u huEA
  have hzP := hS.A1G_le_PG (hS.Z2_le_A1 hz)
  have huP := hS.A2G_le_PG (hS.rootA_le_A2G hu)
  have hX : e⁻¹ * c ∈ miyamotoEG h L η Q := mul_mem (inv_mem he) hcE
  have hzX : z * (e⁻¹ * c) = (e⁻¹ * c) * z := (hS.E_comm_PG hX hzP).symm
  have huX : u * (e⁻¹ * c) = (e⁻¹ * c) * u := (hS.E_comm_PG hX huP).symm
  have hze : z * e⁻¹ = e⁻¹ * z := (hS.E_comm_PG (inv_mem he) hzP).symm
  have e2 : (e * (z * u))⁻¹ * (z * (gz * u * gz⁻¹)) = e⁻¹ * c := by
    have hgu' : gz * u * gz⁻¹ = c * u := by rw [hc]; group
    rw [hgu']
    calc (e * (z * u))⁻¹ * (z * (c * u)) = u⁻¹ * (z⁻¹ * (e⁻¹ * z) * c) * u := by group
      _ = u⁻¹ * (z⁻¹ * (z * e⁻¹) * c) * u := by rw [hze]
      _ = u⁻¹ * (e⁻¹ * c) * u := by group
      _ = e⁻¹ * c := by rw [mul_assoc, ← huX, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e2]
  exact hX

theorem ET_le_H (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊔ T ≤ normalizer (CFSG.centerIn Q : Set G) := by
  refine sup_le (hS.E_le_M.trans hS.M_le_H) fun x hx => ?_
  have hxQ : x ∈ normalizer (Q : Set G) := hS.normalizer_T_le_normalizer_Q (le_normalizer hx)
  exact normalizer_le_normalizer_centerIn Q hxQ

theorem T_le_normalizer_E (hS : Setting h L η t Q T) :
    T ≤ normalizer (miyamotoEG h L η Q : Set G) := fun _ hx =>
  hS.H_le_normalizer_E (hS.ET_le_H (mem_sup_right hx))

theorem card_ET (hS : Setting h L η t Q T) :
    Nat.card (miyamotoEG h L η Q ⊔ T : Subgroup G) = 2 ^ f * Nat.card T := by
  have : CharP K 2 := h.charP
  have hinf : miyamotoEG h L η Q ⊓ T = miyamotoZG h L η := by
    refine le_antisymm (fun e he => (hS.crossed_eq_one_iff_E he.1).1 ?_) (le_inf hS.ZP_le_E
      ((miyamotoPull_mono h L η (miyamotoZ_le_P h)).trans (hS.P_le_Q.trans hS.Q_le_T)))
    have het : e * t = t * e := mem_centralizer_singleton_iff.1 (hS.T_le (mem_inf.1 he).2)
    rw [mul_assoc e⁻¹, ← het, inv_mul_cancel_left, hS.t_mul_t]
  have key := card_sup_mul_card_inf_eq hS.T_le_normalizer_E
  rw [hinf, hS.card_E, hS.card_ZP] at key
  have : Nat.card (miyamotoEG h L η Q ⊔ T : Subgroup G) * 2 ^ f = 2 ^ f * Nat.card T * 2 ^ f := by
    rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem card_T1 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF1G h L η t ⊔ T : Subgroup G) = (2 ^ f) ^ 4 * Nat.card T := by
  have hinf : miyamotoF1G h L η t ⊓ T = miyamotoA1G h L η := by
    refine le_antisymm (fun x hx => ?_) (le_inf hS.A1_le_F1 (le_sup_right.trans hS.B1_le_T))
    obtain ⟨hxF, hxT⟩ := mem_inf.1 hx
    rw [← hS.F1_inf_B1]
    refine ⟨hxF, ?_⟩
    rw [← hS.D1_inf_C]
    exact ⟨hS.F1_le_D1 hxF, hS.T_le hxT⟩
  have hTF : T ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1
  have key := card_sup_mul_card_inf_eq hTF
  rw [hinf, hS.card_F1, card_miyamotoA1G] at key
  have : Nat.card (miyamotoF1G h L η t ⊔ T : Subgroup G) * (2 ^ f) ^ 4 =
      (2 ^ f) ^ 4 * Nat.card T * (2 ^ f) ^ 4 := by rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem exists_two_subgroup_card_gt_T1 (hS : Setting h L η t Q T) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧
      Nat.card (miyamotoF1G h L η t ⊔ T : Subgroup G) < Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₀ := miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
    (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) with hC₀
  set ET := miyamotoEG h L η Q ⊔ T with hET
  obtain ⟨K₀, hK₀C, hK₀, hcard⟩ := hS.exists_card_C0_eq hS.C0_surj
  have hETN : ET ≤ normalizer (C₀ : Set G) := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hS.H_le_normalizers (hS.ET_le_H hx)
    exact le_normalizer_miyamotoC0 h1 h2 h3
  have hinfK : C₀ ⊓ ET ≤ K₀ := fun g hg => by
    obtain ⟨hgC, hgET⟩ := mem_inf.1 hg
    refine hK₀ g hgC ?_
    have hH := hS.ET_le_H hgET
    have h1 := hS.crossed_mem_ZP (inv_mem hH)
    rw [inv_inv] at h1
    have hzt : (g * t * g⁻¹ * t) * t = t * (g * t * g⁻¹ * t) :=
      mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t h1)
    have e1 : t⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * t := by
      calc t⁻¹ * (g * t * g⁻¹) = t⁻¹ * ((g * t * g⁻¹ * t) * t) := by
            rw [mul_assoc (g * t * g⁻¹) t t, hS.t_mul_t, mul_one]
        _ = t⁻¹ * (t * (g * t * g⁻¹ * t)) := by rw [hzt]
        _ = g * t * g⁻¹ * t := by group
    rw [e1]
    exact hS.ZP_le_E h1
  have key := card_sup_mul_card_inf_eq hETN
  rw [hcard] at key
  have hrel := Subgroup.relIndex_mul_card (C₀ ⊓ ET) K₀
  rw [inf_of_le_left hinfK] at hrel
  have hpos : 0 < Nat.card (C₀ ⊓ ET : Subgroup G) := Nat.card_pos
  have hsup : Nat.card (C₀ ⊔ ET : Subgroup G) =
      (2 ^ f) ^ 4 * ((C₀ ⊓ ET).relIndex K₀ * Nat.card ET) := by
    have : Nat.card (C₀ ⊔ ET : Subgroup G) * Nat.card (C₀ ⊓ ET : Subgroup G) =
        (2 ^ f) ^ 4 * ((C₀ ⊓ ET).relIndex K₀ * Nat.card ET) * Nat.card (C₀ ⊓ ET : Subgroup G) := by
      rw [key, ← hrel]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hS.isPGroup_T
  have hETcard : Nat.card ET = 2 ^ (f + m) := by rw [hET, hS.card_ET, hm, pow_add]
  have hdvd : 2 ^ (4 * f + (f + m)) ∣ Nat.card (C₀ ⊔ ET : Subgroup G) :=
    ⟨(C₀ ⊓ ET).relIndex K₀, by rw [hsup, hETcard]; ring⟩
  obtain ⟨S', hS'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨S'.map (C₀ ⊔ ET).subtype, IsPGroup.of_card (n := 4 * f + (f + m)) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (C₀ ⊔ ET).subtype_injective, hS']
  · rw [Subgroup.card_map_of_injective (C₀ ⊔ ET).subtype_injective, hS', hS.card_T1, hm]
    have h1 : (2 ^ f) ^ 4 * 2 ^ m = 2 ^ (4 * f + m) := by
      rw [← pow_mul, mul_comm f 4, ← pow_add]
    rw [h1]
    exact Nat.pow_lt_pow_right (by norm_num) (by have := hS.two_le; omega)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
