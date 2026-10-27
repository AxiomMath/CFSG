module

public import CFSG.LocalAnalysis.EvenBN.U4.RootD1

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (CosetData mem_of_mem_commutator_sup_of_fixed
  card_sup_mul_card_inf_eq mem_normalizer_inf mem_normalizer_sup)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem crossed_mul_of_commute {t x x' : G} (htt : t * t = 1)
    (hc : (x⁻¹ * t * x * t) * x' = x' * (x⁻¹ * t * x * t)) :
    (x * x')⁻¹ * t * (x * x') * t = (x⁻¹ * t * x * t) * (x'⁻¹ * t * x' * t) := by
  have hc' : x'⁻¹ * (x⁻¹ * t * x * t) = (x⁻¹ * t * x * t) * x'⁻¹ :=
    ((Commute.inv_right (show Commute (x⁻¹ * t * x * t) x' from hc)).eq).symm
  calc (x * x')⁻¹ * t * (x * x') * t = x'⁻¹ * (x⁻¹ * t * x * (t * t)) * x' * t := by
        rw [htt]; group
    _ = (x'⁻¹ * (x⁻¹ * t * x * t)) * (t * x' * t) := by group
    _ = ((x⁻¹ * t * x * t) * x'⁻¹) * (t * x' * t) := by rw [hc']
    _ = (x⁻¹ * t * x * t) * (x'⁻¹ * t * x' * t) := by group

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, mem_normalizer_iff_map_conj_eq.1 hH,
    mem_normalizer_iff_map_conj_eq.1 hK]

end Generic

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem odd_card_miyamotoI1 : Odd (Nat.card (miyamotoI1 h)) := by
  have : Finite K := h.finite
  have : Finite h.fixedField := Subtype.finite
  have hd := Subgroup.card_range_dvd
    ((miyamotoI1Hom (K := K)).comp (Units.map h.fixedField.subtype.toMonoidHom))
  rw [Nat.card_units, UnitaryFieldData.card_fixedField h] at hd
  refine Odd.of_dvd_nat ?_ hd
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩
  exact Nat.Even.sub_odd h1 h2 odd_one

end ModelFacts

section Pull

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem I1G_commute_N1G {x y : G} (hx : x ∈ miyamotoI1G h L η) (hy : y ∈ miyamotoN1G h L η) :
    x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
  have e : g * k = k * g := Subtype.ext (miyamotoI1_commute_N1 h hg hk)
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]

end Pull

@[expose] noncomputable def miyamotoF1G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G) :
    Subgroup G :=
  ⁅miyamotoI1G h L η, miyamotoD1 h L η t⁆ ⊔ miyamotoA1G h L η

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem I1_le_L_inf_normalizer_A1 (_hS : Setting h L η t Q T) :
    miyamotoI1G h L η ≤ L ⊓ normalizer (miyamotoA1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  rw [normalizer_miyamotoA1G]
  exact le_sup_left.trans le_sup_right

theorem I1_le_C (hS : Setting h L η t Q T) : miyamotoI1G h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem I1_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoI1G h L η ≤ normalizer (miyamotoB1 h L η t : Set G) := fun _ hi =>
  mem_normalizer_sup (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1
    (hS.I1_le_C hi))) (hS.I1_le_L_inf_normalizer_A1 hi).2

theorem odd_card_I1 (_hS : Setting h L η t Q T) : Odd (Nat.card (miyamotoI1G h L η)) := by
  rw [card_miyamotoPull h L η (miyamotoI1_le_SU h)]
  exact odd_card_miyamotoI1 h

theorem exists_I1_fpf_A1 (hS : Setting h L η t Q T) : ∃ i ∈ miyamotoI1G h L η,
    ∀ a ∈ miyamotoA1G h L η, i * a * i⁻¹ = a → a = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨s, hs, hs2⟩ := exists_fixed_unit_sq_ne_one h hS.two_le
  have hDI : miyamotoIHom h (s, s) ∈ miyamotoI1 h := (mem_miyamotoI1 h).2 ⟨s, hs, rfl⟩
  have hDS : miyamotoIHom h (s, s) ∈ gramSU h (miyamotoJ4 K) := miyamotoI1_le_SU h hDI
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨_, hDS⟩)).2 hDI, fun a ha e => ?_⟩
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  obtain ⟨b, c, d, hb, hd, hgd⟩ := (mem_A1 h).1 hg
  have e' : (⟨_, hDS⟩ : gramSU h (miyamotoJ4 K)) * g * (⟨_, hDS⟩)⁻¹ = g := by
    apply η.symm.injective
    apply Subtype.ext
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using e
  have e2 : (miyamotoIHom h (s, s))⁻¹ * (g : GL (Fin 4) K) * miyamotoIHom h (s, s) = g := by
    have := congrArg Subtype.val e'
    simp only [coe_mul, coe_inv] at this
    calc (miyamotoIHom h (s, s))⁻¹ * (g : GL (Fin 4) K) * miyamotoIHom h (s, s) =
        (miyamotoIHom h (s, s))⁻¹ * (miyamotoIHom h (s, s) * g * (miyamotoIHom h (s, s))⁻¹) *
          miyamotoIHom h (s, s) := by rw [this]
      _ = g := by group
  rw [hgd, miyamotoI1_conj h hs, miyamotoXGL_inj] at e2
  obtain ⟨-, eb, ec, ed⟩ := e2
  have hz : ∀ x : K, (s : K) ^ 2 * x = x → x = 0 := fun x ex => by
    have : ((s : K) ^ 2 - 1) * x = 0 := by linear_combination ex
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs2)
  have : g = 1 := Subtype.ext (by
    rw [hgd, hz _ eb, hz _ ec, hz _ ed, miyamotoXGL_zero, OneMemClass.coe_one])
  rw [this, map_one, OneMemClass.coe_one]

theorem crossed_mem_A1_of_mem_D1 (hS : Setting h L η t Q T) {d : G}
    (hd : d ∈ miyamotoD1 h L η t) : d⁻¹ * t * d * t ∈ miyamotoA1G h L η :=
  hS.cosetData_B1.crossed_mem d (hS.D1_le_normalizer_B1 hd)

theorem crossed_mul_D1 (hS : Setting h L η t Q T) {x x' : G} (hx : x ∈ miyamotoD1 h L η t)
    (hx' : x' ∈ miyamotoD1 h L η t) :
    (x * x')⁻¹ * t * (x * x') * t = (x⁻¹ * t * x * t) * (x'⁻¹ * t * x' * t) :=
  crossed_mul_of_commute hS.t_mul_t (mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hx') _
    (hS.crossed_mem_A1_of_mem_D1 hx))

theorem crossed_inv_D1 (hS : Setting h L η t Q T) {d : G} (hd : d ∈ miyamotoD1 h L η t) :
    d⁻¹⁻¹ * t * d⁻¹ * t = (d⁻¹ * t * d * t)⁻¹ := by
  have h3 := hS.crossed_mul_D1 hd (inv_mem hd)
  rw [mul_inv_cancel] at h3
  have e1 : (1 : G)⁻¹ * t * 1 * t = 1 := by rw [inv_one, one_mul, mul_one, hS.t_mul_t]
  rw [e1] at h3
  exact eq_inv_of_mul_eq_one_right h3.symm

theorem mem_B1_of_crossed_eq_one (hS : Setting h L η t Q T) {d : G}
    (hd : d ∈ miyamotoD1 h L η t) (h1 : d⁻¹ * t * d * t = 1) : d ∈ miyamotoB1 h L η t := by
  rw [← hS.D1_inf_C]
  refine ⟨hd, mem_centralizer_singleton_iff.2 ?_⟩
  have e2 : d⁻¹ * t * d = t := by
    have := eq_inv_of_mul_eq_one_left h1
    rwa [hS.t_inv] at this
  calc d * t = d * (d⁻¹ * t * d) := by rw [e2]
    _ = t * d := by group

theorem mul_self_mem_A1_of_mem_D1 (hS : Setting h L η t Q T) {d : G}
    (hd : d ∈ miyamotoD1 h L η t) : d * d ∈ miyamotoA1G h L η := by
  have hAe := isElementaryAbelian_miyamotoA1G h L η
  have hBe := hS.isElementaryAbelian_B1
  have hsqA : ∀ a ∈ miyamotoA1G h L η, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hsqB : ∀ b ∈ miyamotoB1 h L η t, b * b = 1 := fun b hb => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian b hb
  have hdd : d * d ∈ miyamotoB1 h L η t := by
    refine hS.mem_B1_of_crossed_eq_one (mul_mem hd hd) ?_
    rw [hS.crossed_mul_D1 hd hd, hsqA _ (hS.crossed_mem_A1_of_mem_D1 hd)]
  rcases hS.mem_A1_or_of_mem_B1 hdd with h1 | ⟨a, ha, e⟩
  · exact h1
  · exfalso
    obtain ⟨d', hd', hdt⟩ := hS.D1_transitive ha
    have hyd : d' * d * d'⁻¹ ∈ miyamotoD1 h L η t :=
      (mem_normalizer_iff.1 (hS.normalizer_B1_le_normalizer_D1 (hS.D1_le_normalizer_B1 hd')) d).1
        hd
    have hsq : (d' * d * d'⁻¹) * (d' * d * d'⁻¹) = t := by
      calc (d' * d * d'⁻¹) * (d' * d * d'⁻¹) = d' * (d * d) * d'⁻¹ := by group
        _ = d' * (t * a) * d'⁻¹ := by rw [e]
        _ = d' * (d'⁻¹ * t * d') * d'⁻¹ := by rw [hdt]
        _ = t := by group
    have hcomm : (d' * d * d'⁻¹) * t = t * (d' * d * d'⁻¹) := by
      rw [← hsq]
      group
    have hB : d' * d * d'⁻¹ ∈ miyamotoB1 h L η t := by
      rw [← hS.D1_inf_C]
      exact ⟨hyd, mem_centralizer_singleton_iff.2 hcomm⟩
    rw [hsqB _ hB] at hsq
    exact hS.t_ne_one hsq.symm

theorem commutator_mem_A1_of_mem_D1 (hS : Setting h L η t Q T) {d d' : G}
    (hd : d ∈ miyamotoD1 h L η t) (hd' : d' ∈ miyamotoD1 h L η t) :
    d * d' * d⁻¹ * d'⁻¹ ∈ miyamotoA1G h L η := by
  have e : d * d' * d⁻¹ * d'⁻¹ = (d * d) * ((d⁻¹ * d') * (d⁻¹ * d')) * (d' * d')⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (hS.mul_self_mem_A1_of_mem_D1 hd)
    (hS.mul_self_mem_A1_of_mem_D1 (mul_mem (inv_mem hd) hd')))
    (inv_mem (hS.mul_self_mem_A1_of_mem_D1 hd'))

theorem A1_le_D1 (hS : Setting h L η t Q T) : miyamotoA1G h L η ≤ miyamotoD1 h L η t :=
  le_sup_right.trans hS.B1_le_D1

theorem t_mem_D1 (hS : Setting h L η t Q T) : t ∈ miyamotoD1 h L η t :=
  hS.B1_le_D1 (mem_sup_left (mem_zpowers t))

theorem I1_le_normalizer_D1 (hS : Setting h L η t Q T) :
    miyamotoI1G h L η ≤ normalizer (miyamotoD1 h L η t : Set G) :=
  fun _ hi => hS.normalizer_B1_le_normalizer_D1 (hS.I1_le_normalizer_B1 hi)

theorem F1_le_D1 (hS : Setting h L η t Q T) : miyamotoF1G h L η t ≤ miyamotoD1 h L η t := by
  refine sup_le (commutator_le.2 fun i hi d hd => ?_) hS.A1_le_D1
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (hS.I1_le_normalizer_D1 hi) d).1 hd) (inv_mem hd)

theorem A1_le_F1 (_hS : Setting h L η t Q T) : miyamotoA1G h L η ≤ miyamotoF1G h L η t :=
  le_sup_right

theorem commutator_mem_F1 (_hS : Setting h L η t Q T) {i d : G} (hi : i ∈ miyamotoI1G h L η)
    (hd : d ∈ miyamotoD1 h L η t) : i * d * i⁻¹ * d⁻¹ ∈ miyamotoF1G h L η t := by
  have := commutator_mem_commutator hi hd
  rw [commutatorElement_def] at this
  exact mem_sup_left this

theorem t_not_mem_F1 (hS : Setting h L η t Q T) : t ∉ miyamotoF1G h L η t := by
  intro htF
  refine hS.t_not_mem_A1 (mem_of_mem_commutator_sup_of_fixed hS.A1_le_D1
    (fun d hd d' hd' => hS.commutator_mem_A1_of_mem_D1 hd hd') hS.I1_le_normalizer_D1
    (fun i hi => (hS.I1_le_L_inf_normalizer_A1 hi).2)
    (coprime_of_odd_of_isPGroup hS.odd_card_I1 hS.isPGroup_D1) htF fun i hi => ?_)
  have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.I1_le_C hi)
  rw [hit, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem exists_F1_crossed_eq (hS : Setting h L η t Q T) {a : G}
    (ha : a ∈ miyamotoA1G h L η) : ∃ e ∈ miyamotoF1G h L η t, e⁻¹ * t * e * t = a := by
  have hAe := isElementaryAbelian_miyamotoA1G h L η
  obtain ⟨i, hi, hfpf⟩ := hS.exists_I1_fpf_A1
  have hiA := (hS.I1_le_L_inf_normalizer_A1 hi).2
  set ψ : miyamotoA1G h L η → miyamotoA1G h L η := fun z' =>
    ⟨i * z' * i⁻¹ * (z' : G)⁻¹, mul_mem ((mem_normalizer_iff.1 hiA z').1 z'.2) (inv_mem z'.2)⟩
  have hcomm : ∀ a ∈ miyamotoA1G h L η, ∀ b ∈ miyamotoA1G h L η, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : miyamotoA1G h L η) ⟨b, hb⟩)
  have hinj : Function.Injective ψ := by
    intro z₁ z₂ e
    have e' : i * (z₁ : G) * i⁻¹ * (z₁ : G)⁻¹ = i * z₂ * i⁻¹ * (z₂ : G)⁻¹ := congrArg Subtype.val e
    have hw : (z₂ : G)⁻¹ * z₁ ∈ miyamotoA1G h L η := mul_mem (inv_mem z₂.2) z₁.2
    have h1 : i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (z₂ : G)⁻¹ * z₁ := by
      calc i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (i * z₂ * i⁻¹)⁻¹ * (i * z₁ * i⁻¹) := by group
        _ = (i * z₂ * i⁻¹)⁻¹ * (i * z₂ * i⁻¹ * (z₂ : G)⁻¹ * z₁) := by
            rw [show i * (z₁ : G) * i⁻¹ = i * z₁ * i⁻¹ * (z₁ : G)⁻¹ * z₁ by group, e']
        _ = (z₂ : G)⁻¹ * z₁ := by group
    have := hfpf _ hw h1
    exact Subtype.ext (by rw [← mul_left_cancel_iff (a := (z₂ : G)⁻¹), this, inv_mul_cancel])
  obtain ⟨z', hz'⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨a, ha⟩
  have hz'v : i * (z' : G) * i⁻¹ * (z' : G)⁻¹ = a := congrArg Subtype.val hz'
  obtain ⟨d, hd, hdz⟩ := hS.sec3_4.2.2.2.2.2.1 z' z'.2
  refine ⟨i * d * i⁻¹ * d⁻¹, hS.commutator_mem_F1 hi hd, ?_⟩
  have hid : i * d * i⁻¹ ∈ miyamotoD1 h L η t :=
    (mem_normalizer_iff.1 (hS.I1_le_normalizer_D1 hi) d).1 hd
  have h1 := hS.crossed_mul_D1 hid (inv_mem hd)
  have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.I1_le_C hi)
  have h2 := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := d) hit
  rw [h1, h2, hS.crossed_inv_D1 hd, hdz, hz'v]

theorem mem_F1_or_of_mem_D1 (hS : Setting h L η t Q T) {d : G} (hd : d ∈ miyamotoD1 h L η t) :
    d ∈ miyamotoF1G h L η t ∨ ∃ e ∈ miyamotoF1G h L η t, d = e * t := by
  obtain ⟨e, he, hed⟩ := hS.exists_F1_crossed_eq (hS.crossed_mem_A1_of_mem_D1 hd)
  have heD := hS.F1_le_D1 he
  have h1 := hS.crossed_mul_D1 (inv_mem heD) hd
  rw [hS.crossed_inv_D1 heD, hed, inv_mul_cancel] at h1
  have hw := hS.mem_B1_of_crossed_eq_one (mul_mem (inv_mem heD) hd) h1
  rcases hS.mem_A1_or_of_mem_B1 hw with h2 | ⟨a, ha, e2⟩
  · left
    rw [show d = e * (e⁻¹ * d) by group]
    exact mul_mem he (hS.A1_le_F1 h2)
  · right
    refine ⟨e * a, mul_mem he (hS.A1_le_F1 ha), ?_⟩
    have hta : t * a = a * t :=
      (mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t ha)).symm
    calc d = e * (e⁻¹ * d) := by group
      _ = e * (t * a) := by rw [e2]
      _ = e * a * t := by rw [hta, mul_assoc]

theorem F1_sup_zpowers (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ zpowers t = miyamotoD1 h L η t := by
  refine le_antisymm (sup_le hS.F1_le_D1 (zpowers_le.2 hS.t_mem_D1)) fun d hd => ?_
  rcases hS.mem_F1_or_of_mem_D1 hd with h1 | ⟨e, he, rfl⟩
  · exact mem_sup_left h1
  · exact mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers t))

theorem F1_inf_B1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ miyamotoB1 h L η t = miyamotoA1G h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.A1_le_F1 le_sup_right)
  obtain ⟨hxF, hxB⟩ := mem_inf.1 hx
  rcases hS.mem_A1_or_of_mem_B1 hxB with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply hS.t_not_mem_F1
    have := mul_mem hxF (inv_mem (hS.A1_le_F1 ha))
    rwa [mul_inv_cancel_right] at this

theorem card_F1 (hS : Setting h L η t Q T) : Nat.card (miyamotoF1G h L η t) = (2 ^ f) ^ 8 := by
  have hle : miyamotoF1G h L η t ≤ normalizer (miyamotoB1 h L η t : Set G) :=
    hS.F1_le_D1.trans hS.D1_le_normalizer_B1
  have e := card_sup_mul_card_inf_eq hle
  have hsup : miyamotoB1 h L η t ⊔ miyamotoF1G h L η t = miyamotoD1 h L η t := by
    refine le_antisymm (sup_le hS.B1_le_D1 hS.F1_le_D1) ?_
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_right (zpowers_le.2 (mem_sup_left (mem_sup_left (mem_zpowers t))))
  rw [hsup, inf_comm, hS.F1_inf_B1, hS.card_D1, card_miyamotoA1G, hS.card_B1] at e
  have e' : (2 * (2 ^ f) ^ 4) * Nat.card (miyamotoF1G h L η t) =
      (2 * (2 ^ f) ^ 4) * (2 ^ f) ^ 8 := by
    rw [← e]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) e'

theorem commutator_mem_F1_of_mem_normalizer (hS : Setting h L η t Q T) {x d : G}
    (hxD : x ∈ normalizer (miyamotoD1 h L η t : Set G))
    (hxF : x ∈ normalizer (miyamotoF1G h L η t : Set G)) (hd : d ∈ miyamotoD1 h L η t) :
    x * d * x⁻¹ * d⁻¹ ∈ miyamotoF1G h L η t := by
  rcases hS.mem_F1_or_of_mem_D1 hd with h1 | ⟨e, he, rfl⟩
  · exact mul_mem ((mem_normalizer_iff.1 hxF _).1 h1) (inv_mem h1)
  · have hxd : x * (e * t) * x⁻¹ ∈ miyamotoD1 h L η t := (mem_normalizer_iff.1 hxD _).1 hd
    rcases hS.mem_F1_or_of_mem_D1 hxd with h2 | ⟨e', he', e2⟩
    · exfalso
      apply hS.t_not_mem_F1
      have := mul_mem (inv_mem he) ((mem_normalizer_iff.1 hxF (e * t)).2 h2)
      rwa [inv_mul_cancel_left] at this
    · rw [e2, show e' * t * (e * t)⁻¹ = e' * e⁻¹ by group]
      exact mul_mem he' (inv_mem he)

theorem D1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t ≤ normalizer (miyamotoF1G h L η t : Set G) := fun d hd =>
  mem_normalizer_fintype fun x hx => by
    rw [show d * x * d⁻¹ = (d * x * d⁻¹ * x⁻¹) * x by group]
    exact mul_mem (hS.A1_le_F1 (hS.commutator_mem_A1_of_mem_D1 hd (hS.F1_le_D1 hx))) hx

theorem A1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.A1_le_D1.trans hS.D1_le_normalizer_F1

theorem I1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoI1G h L η ≤ normalizer (miyamotoF1G h L η t : Set G) := fun _ hi =>
  mem_normalizer_sup (mem_normalizer_commutator (le_normalizer hi) (hS.I1_le_normalizer_D1 hi))
    (hS.I1_le_L_inf_normalizer_A1 hi).2

theorem N1_le_normalizer_D1 (hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ normalizer (miyamotoD1 h L η t : Set G) := fun _ hn =>
  hS.normalizer_B1_le_normalizer_D1 (hS.N1G_le_normalizer_B1 hn).1

theorem N1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ normalizer (miyamotoF1G h L η t : Set G) := by
  intro n hn
  have hnB := (hS.N1G_le_normalizer_B1 hn).1
  refine mem_normalizer_sup (mem_normalizer_commutator ?_ (hS.N1_le_normalizer_D1 hn))
    (hS.normalizer_B1_le_normalizer_A1 hnB)
  exact mem_normalizer_fintype fun i hi => by
    rw [← I1G_commute_N1G h L η hi hn, mul_inv_cancel_right]
    exact hi

theorem normalizer_B1_inf_C_le_normalizer_F1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (miyamotoF1G h L η t : Set G) := by
  have : CharP K 2 := h.charP
  intro c hc
  have hcD := hS.normalizer_B1_le_normalizer_D1 hc.1
  have hcA := hS.normalizer_B1_le_normalizer_A1 hc.1
  have hcL : c ∈ normalizer (L : Set G) := hS.centralizer_le_normalizer hc.2
  have hX : ∀ i ∈ miyamotoI1G h L η, c * i * c⁻¹ ∈ normalizer (miyamotoD1 h L η t : Set G) ⊓
      normalizer (miyamotoF1G h L η t : Set G) := by
    intro i hi
    have hmem : c * i * c⁻¹ ∈ L ⊓ normalizer (miyamotoA1G h L η : Set G) :=
      mem_inf.2 ⟨(mem_normalizer_iff.1 hcL i).1 (miyamotoPull_le h L η _ hi),
        mul_mem (mul_mem hcA (mem_inf.1 (hS.I1_le_L_inf_normalizer_A1 hi)).2) (inv_mem hcA)⟩
    rw [normalizer_miyamotoA1G] at hmem
    exact (sup_le (le_inf (hS.A1_le_D1.trans le_normalizer) hS.A1_le_normalizer_F1)
      (sup_le (le_inf hS.I1_le_normalizer_D1 hS.I1_le_normalizer_F1)
        (le_inf hS.N1_le_normalizer_D1 hS.N1_le_normalizer_F1))) hmem
  have key : miyamotoF1G h L η t ≤ (miyamotoF1G h L η t).comap (MulAut.conj c).toMonoidHom := by
    refine sup_le (commutator_le.2 fun i hi d hd => ?_) fun a ha => ?_
    · change c * ⁅i, d⁆ * c⁻¹ ∈ miyamotoF1G h L η t
      obtain ⟨hxD, hxF⟩ := hX i hi
      rw [commutatorElement_def, show c * (i * d * i⁻¹ * d⁻¹) * c⁻¹ =
        (c * i * c⁻¹) * (c * d * c⁻¹) * (c * i * c⁻¹)⁻¹ * (c * d * c⁻¹)⁻¹ by group]
      exact hS.commutator_mem_F1_of_mem_normalizer hxD hxF ((mem_normalizer_iff.1 hcD d).1 hd)
    · change c * a * c⁻¹ ∈ miyamotoF1G h L η t
      exact hS.A1_le_F1 ((mem_normalizer_iff.1 hcA a).1 ha)
  exact mem_normalizer_fintype fun x hx => key hx

theorem normalizer_B1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ≤ normalizer (miyamotoF1G h L η t : Set G) := by
  intro g hg
  obtain ⟨c, hc, d, hd, rfl⟩ := hS.normalizer_B1_eq_mul hg
  exact mul_mem (hS.normalizer_B1_inf_C_le_normalizer_F1 hc) (hS.D1_le_normalizer_F1 hd)

theorem D1_eq (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t =
      normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer (miyamotoA1G h L η : Set G) := by
  refine le_antisymm (le_inf hS.D1_le_normalizer_B1 hS.D1_le_centralizer_A1) fun g hg => ?_
  obtain ⟨hg1, hg2⟩ := mem_inf.1 hg
  obtain ⟨c, hc, d, hd, rfl⟩ := hS.normalizer_B1_eq_mul hg1
  have hcA : c ∈ centralizer (miyamotoA1G h L η : Set G) := by
    have := mul_mem hg2 (inv_mem (hS.D1_le_centralizer_A1 hd))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (hS.B1_le_D1 (hS.centralizer_A1_inf_C_le_B1 ⟨hcA, hc.2⟩)) hd

theorem crossed_eq_one_iff_F1 (hS : Setting h L η t Q T) {e : G}
    (he : e ∈ miyamotoF1G h L η t) : e⁻¹ * t * e * t = 1 ↔ e ∈ miyamotoA1G h L η := by
  refine ⟨fun h1 => ?_, fun ha => ?_⟩
  · rw [← hS.F1_inf_B1]
    exact ⟨he, hS.mem_B1_of_crossed_eq_one (hS.F1_le_D1 he) h1⟩
  · have hat : e * t = t * e := mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t ha)
    rw [mul_assoc e⁻¹, ← hat, inv_mul_cancel_left, hS.t_mul_t]

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
