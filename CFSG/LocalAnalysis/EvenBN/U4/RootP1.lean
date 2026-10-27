module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF1Elem
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Pairing

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq mem_normalizer_sup)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem mem_ZG_of_mem_A1_of_commute (hS : Setting h L η t Q T) {a : G}
    (ha : a ∈ miyamotoA1G h L η) (hap : ∀ p ∈ miyamotoPG h L η, a * p = p * a) :
    a ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  show a ∈ miyamotoPull h L η (miyamotoZ h)
  rw [← centerIn_miyamotoPG]
  exact mem_inf.2 ⟨hS.A1G_le_PG ha, mem_centralizer_iff.2 fun p hp => (hap p hp).symm⟩

theorem mem_E_of_mem_F1_of_commute (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t) (hP : ∀ p ∈ miyamotoPG h L η, x * p = p * x) :
    x ∈ miyamotoEG h L η Q := by
  have hxD := hS.F1_le_D1 hx
  have hc : x⁻¹ * t * x * t ∈ miyamotoZG h L η := by
    refine hS.mem_ZG_of_mem_A1_of_commute (hS.crossed_mem_A1_of_mem_D1 hxD) fun p hp => ?_
    have hpt : p * t = t * p := mem_centralizer_singleton_iff.1 (hS.PG_le_C hp)
    have hxp := hP p hp
    have hxp' : x⁻¹ * p = p * x⁻¹ := by
      calc x⁻¹ * p = x⁻¹ * (p * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * p) * x⁻¹ := by rw [hxp]
        _ = p * x⁻¹ := by group
    calc x⁻¹ * t * x * t * p = x⁻¹ * t * x * (t * p) := by group
      _ = x⁻¹ * t * x * (p * t) := by rw [hpt]
      _ = x⁻¹ * t * (x * p) * t := by group
      _ = x⁻¹ * t * (p * x) * t := by rw [hxp]
      _ = x⁻¹ * (t * p) * x * t := by group
      _ = x⁻¹ * (p * t) * x * t := by rw [hpt]
      _ = (x⁻¹ * p) * t * x * t := by group
      _ = (p * x⁻¹) * t * x * t := by rw [hxp']
      _ = p * (x⁻¹ * t * x * t) := by group
  obtain ⟨e, he, hec⟩ := hS.exists_E_crossed_eq hc
  have heF := hS.E_le_F1 he
  have heD := hS.F1_le_D1 heF
  have h1 : (x * e⁻¹)⁻¹ * t * (x * e⁻¹) * t = 1 := by
    rw [hS.crossed_mul_D1 hxD (inv_mem heD), hS.crossed_inv_D1 heD, hec, mul_inv_cancel]
  have hA : x * e⁻¹ ∈ miyamotoA1G h L η :=
    (hS.crossed_eq_one_iff_F1 (mul_mem hx (inv_mem heF))).1 h1
  have hZ := hS.mem_ZG_of_mem_A1_of_commute hA fun p hp => by
    have hep := hS.E_comm_PG he hp
    have hep' : e⁻¹ * p = p * e⁻¹ := by
      calc e⁻¹ * p = e⁻¹ * (p * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * p) * e⁻¹ := by rw [hep]
        _ = p * e⁻¹ := by group
    calc x * e⁻¹ * p = x * (e⁻¹ * p) := by group
      _ = x * (p * e⁻¹) := by rw [hep']
      _ = (x * p) * e⁻¹ := by group
      _ = (p * x) * e⁻¹ := by rw [hP p hp]
      _ = p * (x * e⁻¹) := by group
  have := mul_mem (hS.ZP_le_E hZ) he
  rwa [inv_mul_cancel_right] at this

theorem mem_A1_of_mem_PG_of_commute (hS : Setting h L η t Q T) {p : G}
    (hp : p ∈ miyamotoPG h L η) (hA : ∀ a ∈ miyamotoA1G h L η, p * a = a * p) :
    p ∈ miyamotoA1G h L η := by
  by_contra hpA
  have h1 := hS.card_A1_inf_centralizer_le_of_mem_P hp hpA
  have h2 : miyamotoA1G h L η ⊓ centralizer ({p} : Set G) = miyamotoA1G h L η :=
    inf_eq_left.2 fun a ha => mem_centralizer_singleton_iff.2 (hA a ha).symm
  rw [h2, card_miyamotoA1G] at h1
  have : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 :=
    Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by have := hS.two_le; omega)) (by norm_num)
  omega

theorem centerIn_P1 (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoF1G h L η t ⊔ miyamotoPG h L η) = miyamotoEG h L η Q := by
  refine le_antisymm (fun x hx => ?_) fun e he => ?_
  · obtain ⟨hxP1, hxC⟩ := mem_inf.1 hx
    obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hxP1
    have hpA : p ∈ miyamotoA1G h L η := hS.mem_A1_of_mem_PG_of_commute hp fun a ha => by
      have h1 : a * (f₀ * p) = f₀ * p * a :=
        mem_centralizer_iff.1 hxC a (mem_sup_left (hS.A1_le_F1 ha))
      have h2 : a * f₀ = f₀ * a := hS.F1_comm (hS.A1_le_F1 ha) hf₀
      calc p * a = f₀⁻¹ * ((f₀ * p) * a) := by group
        _ = f₀⁻¹ * (a * (f₀ * p)) := by rw [← h1]
        _ = f₀⁻¹ * ((a * f₀) * p) := by group
        _ = f₀⁻¹ * ((f₀ * a) * p) := by rw [h2]
        _ = a * p := by group
    exact hS.mem_E_of_mem_F1_of_commute (mul_mem hf₀ (hS.A1_le_F1 hpA)) fun p' hp' =>
      (mem_centralizer_iff.1 hxC p' (mem_sup_right hp')).symm
  · have heF := hS.E_le_F1 he
    refine mem_inf.2 ⟨mem_sup_left heF, mem_centralizer_sup
      (mem_centralizer_iff.2 fun x hx => hS.F1_comm hx heF)
      (mem_centralizer_iff.2 fun p hp => (hS.E_comm_PG he hp).symm)⟩

theorem mem_normalizer_F1_of_le (hS : Setting h L η t Q T) {X : Subgroup G}
    (hFX : miyamotoF1G h L η t ≤ X) (hXT : X ≤ miyamotoF1G h L η t ⊔ T) {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer (miyamotoF1G h L η t : Set G) := by
  have hB := hS.eq_F1_of_commute (B := (miyamotoF1G h L η t).map (MulAut.conj g).toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hXT ((mem_normalizer_iff.1 hg x).1 (hFX hx)))
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        _ = g * (y * x) * g⁻¹ := by rw [hS.F1_comm hx hy]
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group)
    (le_of_eq (by
      rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
        hS.card_F1]))
  exact mem_normalizer_fintype fun x hx => by
    rw [← hB]
    exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

theorem D1_le_T1 (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ T := by
  rw [← hS.F1_sup_zpowers]
  exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_T))

theorem normalizer_D1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoD1 h L η t : Set G) ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  fun _ hg => hS.mem_normalizer_F1_of_le hS.F1_le_D1 hS.D1_le_T1 hg

theorem mem_A1_of_mul_t_mul_self (hS : Setting h L η t Q T) {e : G}
    (he : e ∈ miyamotoF1G h L η t) (hee : e * t * (e * t) = 1) : e ∈ miyamotoA1G h L η := by
  refine hS.mem_A1_of_conj_mul_eq_one he ?_
  calc t * e * t⁻¹ * e = e⁻¹ * (e * t * (e * t)) * e := by rw [hS.t_inv]; group
    _ = 1 := by rw [hee]; group

theorem normalizer_D1_eq (hS : Setting h L η t Q T) :
    normalizer (miyamotoD1 h L η t : Set G) = normalizer (miyamotoB1 h L η t : Set G) := by
  refine le_antisymm (fun g hg => ?_) hS.normalizer_B1_le_normalizer_D1
  have hgF := hS.normalizer_D1_le_normalizer_F1 hg
  have hBe := hS.isElementaryAbelian_B1
  refine mem_normalizer_fintype fun b hb => ?_
  have hbD : g * b * g⁻¹ ∈ miyamotoD1 h L η t := (mem_normalizer_iff.1 hg b).1 (hS.B1_le_D1 hb)
  rcases hS.mem_A1_or_of_mem_B1 hb with hbA | ⟨a, ha, rfl⟩
  ·
    have : g * b * g⁻¹ ∈ CFSG.centerIn (miyamotoD1 h L η t) := by
      refine mem_inf.2 ⟨hbD, mem_centralizer_iff.2 fun d hd => ?_⟩
      have hd' : g⁻¹ * d * g⁻¹⁻¹ ∈ miyamotoD1 h L η t := (mem_normalizer_iff.1 (inv_mem hg) d).1 hd
      have hc : b * (g⁻¹ * d * g⁻¹⁻¹) = (g⁻¹ * d * g⁻¹⁻¹) * b :=
        mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hd') b hbA
      calc d * (g * b * g⁻¹) = g * ((g⁻¹ * d * g⁻¹⁻¹) * b) * g⁻¹ := by group
        _ = g * (b * (g⁻¹ * d * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
        _ = g * b * g⁻¹ * d := by group
    rw [hS.centerIn_D1] at this
    exact mem_sup_right this
  ·
    have hnF : g * (t * a) * g⁻¹ ∉ miyamotoF1G h L η t := fun hF => by
      have h1 := (mem_normalizer_iff.1 hgF (t * a)).2 hF
      exact hS.t_not_mem_F1 (by
        have := mul_mem h1 (inv_mem (hS.A1_le_F1 ha))
        rwa [mul_inv_cancel_right] at this)
    rcases hS.mem_F1_or_of_mem_D1 hbD with hF | ⟨e, he, hee⟩
    · exact absurd hF hnF
    rw [hee]
    have hsq : e * t * (e * t) = 1 := by
      rw [← hee]
      have hb2 : t * a * (t * a) = 1 := by
        rw [← sq]
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hb
      calc g * (t * a) * g⁻¹ * (g * (t * a) * g⁻¹) = g * (t * a * (t * a)) * g⁻¹ := by group
        _ = 1 := by rw [hb2, mul_one, mul_inv_cancel]
    exact mul_mem (mem_sup_right (hS.mem_A1_of_mul_t_mul_self he hsq)) hS.t_mem_B1

theorem exists_mul_of_mem_normalizer_Q1_inf_B1 (hS : Setting h L η t Q T) {g : G}
    (hgQ : g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))
    (hgB : g ∈ normalizer (miyamotoB1 h L η t : Set G)) :
    ∃ c ∈ normalizer (Q : Set G) ⊓ centralizer ({t} : Set G), ∃ d ∈ miyamotoD1 h L η t,
      g = c * d := by
  obtain ⟨c, hc, d, hd, rfl⟩ := hS.normalizer_B1_eq_mul hgB
  have hcC := (mem_inf.1 hc).2
  have hDQ : miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ Q := by
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_Q))
  have hcN : c ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := by
    have := mul_mem hgQ (inv_mem (le_normalizer (hDQ hd)))
    rwa [mul_inv_cancel_right] at this
  have hLtC : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le hS.L_le_centralizer (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hQLt : Q ≤ L ⊔ zpowers t := by
    rw [hS.Q_eq]
    exact sup_le_sup_right (miyamotoPull_le h L η _) _
  have hcLt : c ∈ normalizer ((L ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup (hS.centralizer_le_normalizer hcC)
      (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 hcC))
  have hQF : Q ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.Q_le_T.trans (hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1)
  refine ⟨c, mem_inf.2 ⟨mem_normalizer_fintype fun y hy => ?_, hcC⟩, d, hd, rfl⟩
  have h1 : c * y * c⁻¹ ∈ miyamotoF1G h L η t ⊔ Q :=
    (mem_normalizer_iff.1 hcN y).1 (mem_sup_right hy)
  have h2 : c * y * c⁻¹ ∈ L ⊔ zpowers t := (mem_normalizer_iff.1 hcLt y).1 (hQLt hy)
  obtain ⟨f₀, hf₀, q, hq, hfq⟩ := exists_mul_of_mem_sup_of_le_normalizer' hQF h1
  have hf₀C : f₀ ∈ miyamotoF1G h L η t ⊓ miyamotoB1 h L η t := by
    refine mem_inf.2 ⟨hf₀, ?_⟩
    rw [← hS.D1_inf_C]
    refine mem_inf.2 ⟨hS.F1_le_D1 hf₀, hLtC ?_⟩
    have := mul_mem h2 (inv_mem (hQLt hq))
    rwa [hfq, mul_inv_cancel_right] at this
  rw [hS.F1_inf_B1] at hf₀C
  rw [hfq]
  exact mul_mem ((hS.A1G_le_PG.trans hS.P_le_Q) hf₀C) hq

theorem A1_sup_A2 (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ⊔ miyamotoA2G h L η = miyamotoPG h L η := by
  have : CharP K 2 := h.charP
  refine eq_of_le_of_card_ge (sup_le hS.A1G_le_PG hS.A2G_le_PG) ?_
  have key := card_sup_mul_card_inf_eq (hS.A2G_le_PG.trans hS.PG_le_normalizer_A1)
  rw [miyamotoA1G_inf_miyamotoA2G, card_miyamotoPull h L η (miyamotoUnipotent_le_SU h true true),
    card_miyamotoZ2, card_miyamotoA1G, card_miyamotoA2G] at key
  rw [card_miyamotoPG]
  have : Nat.card (miyamotoA1G h L η ⊔ miyamotoA2G h L η : Subgroup G) * (2 ^ f) ^ 3 =
      (2 ^ f) ^ 6 * (2 ^ f) ^ 3 := by
    rw [key]
    ring
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).ge

theorem commutator_F_PG_mem_E (hS : Setting h L η t Q T) {x p : G}
    (hx : x ∈ miyamotoFG h L η t Q) (hp : p ∈ miyamotoPG h L η) :
    x * p * x⁻¹ * p⁻¹ ∈ miyamotoEG h L η Q := by
  rw [← hS.A1_sup_A2] at hp
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' (hS.A2G_le_PG.trans hS.PG_le_normalizer_A1) hp
  have hc : x * a₁ = a₁ * x := hS.F1_comm (hS.F_le_F1 hx) (hS.A1_le_F1 ha₁)
  have hw := hS.commutator_F_A2_mem_E hx ha₂
  have hcw : a₁ * (x * a₂ * x⁻¹ * a₂⁻¹) = (x * a₂ * x⁻¹ * a₂⁻¹) * a₁ :=
    hS.F1_comm (hS.A1_le_F1 ha₁) (hS.E_le_F1 hw)
  have : x * (a₁ * a₂) * x⁻¹ * (a₁ * a₂)⁻¹ = x * a₂ * x⁻¹ * a₂⁻¹ := by
    calc x * (a₁ * a₂) * x⁻¹ * (a₁ * a₂)⁻¹ = (x * a₁) * a₂ * x⁻¹ * a₂⁻¹ * a₁⁻¹ := by group
      _ = (a₁ * x) * a₂ * x⁻¹ * a₂⁻¹ * a₁⁻¹ := by rw [hc]
      _ = a₁ * (x * a₂ * x⁻¹ * a₂⁻¹) * a₁⁻¹ := by group
      _ = (x * a₂ * x⁻¹ * a₂⁻¹) * a₁ * a₁⁻¹ := by rw [hcw]
      _ = x * a₂ * x⁻¹ * a₂⁻¹ := by group
  rw [this]
  exact hw

theorem commutator_F_P1_mem_E (hS : Setting h L η t Q T) {x y : G}
    (hx : x ∈ miyamotoFG h L η t Q) (hy : y ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    x * y * x⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q := by
  obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hy
  have hc : x * f₀ = f₀ * x := hS.F1_comm (hS.F_le_F1 hx) hf₀
  have hw := hS.commutator_F_PG_mem_E hx hp
  have hcw : f₀ * (x * p * x⁻¹ * p⁻¹) = (x * p * x⁻¹ * p⁻¹) * f₀ :=
    hS.F1_comm hf₀ (hS.E_le_F1 hw)
  have : x * (f₀ * p) * x⁻¹ * (f₀ * p)⁻¹ = x * p * x⁻¹ * p⁻¹ := by
    calc x * (f₀ * p) * x⁻¹ * (f₀ * p)⁻¹ = (x * f₀) * p * x⁻¹ * p⁻¹ * f₀⁻¹ := by group
      _ = (f₀ * x) * p * x⁻¹ * p⁻¹ * f₀⁻¹ := by rw [hc]
      _ = f₀ * (x * p * x⁻¹ * p⁻¹) * f₀⁻¹ := by group
      _ = (x * p * x⁻¹ * p⁻¹) * f₀ * f₀⁻¹ := by rw [hcw]
      _ = x * p * x⁻¹ * p⁻¹ := by group
  rw [this]
  exact hw

theorem mem_A1_of_commutator_mem_ZP (_hS : Setting h L η t Q T) {p : G}
    (hp : p ∈ miyamotoPG h L η)
    (hc : ∀ a ∈ miyamotoA1G h L η, p * a * p⁻¹ * a⁻¹ ∈ miyamotoZG h L η) :
    p ∈ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  obtain ⟨a, b, c, d, hb, hd, hgx⟩ := (mem_P h).1 hg
  have hyA : miyamotoXGL h 0 1 0 0 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_one _, map_zero _⟩
  set y : gramSU h (miyamotoJ4 K) := ⟨_, miyamotoUnipotent_le_SU h true false hyA⟩ with hy
  have h2 : ((η.symm (g * y * g⁻¹ * y⁻¹) : L) : G) ∈ miyamotoZG h L η := by
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using
      hc _ ((symm_mem_miyamotoPull_iff h L η).2 hyA)
  have hw := (symm_mem_miyamotoPull_iff h L η).1 h2
  simp only [coe_mul, coe_inv] at hw
  set w := (g : GL (Fin 4) K) * y * (g : GL (Fin 4) K)⁻¹ * (y : GL (Fin 4) K)⁻¹ with hwdef
  have hwc : (g : GL (Fin 4) K) * y * w⁻¹ = w⁻¹ * (g * y) := by
    have hcen : w⁻¹ ∈ CFSG.centerIn (miyamotoP h) := by
      rw [centerIn_miyamotoP]
      exact inv_mem hw
    exact mem_centralizer_iff.1 (mem_inf.1 hcen).2 _ (mul_mem hg (miyamotoA1_le_P h hyA))
  have e : miyamotoXGL h 0 1 0 0 * miyamotoXGL h a b c d =
      miyamotoXGL h a b c d * miyamotoXGL h 0 1 0 0 * w⁻¹ := by
    rw [← hgx]
    calc (y : GL (Fin 4) K) * g = w⁻¹ * (w * (y * g)) := by group
      _ = w⁻¹ * (g * y) := by rw [hwdef]; group
      _ = g * y * w⁻¹ := hwc.symm
  have ha := eq_zero_of_rootB_mul_eq h hb (inv_mem hw) e
  refine (symm_mem_miyamotoPull_iff h L η).2 ?_
  rw [hgx, miyamotoXGL_mem_A1]
  subst ha
  refine ⟨rfl, hb, (add_bar_eq_zero_iff h).1 ?_⟩
  simpa using hd

theorem mem_Z2_of_commutator_mem_ZP (_hS : Setting h L η t Q T) {a : G}
    (ha : a ∈ miyamotoA1G h L η)
    (hc : ∀ g ∈ miyamotoPG h L η, a * g * a⁻¹ * g⁻¹ ∈ miyamotoZG h L η) :
    a ∈ miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  obtain ⟨x, hx, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  obtain ⟨b, c, d, hb, hd, hxa⟩ := (mem_A1 h).1 hx
  have huP : miyamotoXGL h 1 0 0 0 ∈ miyamotoP h :=
    (miyamotoXGL_mem_P h).2 ⟨map_zero _, by simp⟩
  set u : gramSU h (miyamotoJ4 K) := ⟨_, miyamotoUnipotent_le_SU h false false huP⟩ with hu
  have h2 : ((η.symm (x * u * x⁻¹ * u⁻¹) : L) : G) ∈ miyamotoZG h L η := by
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using
      hc _ ((symm_mem_miyamotoPull_iff h L η).2 huP)
  have hw := (symm_mem_miyamotoPull_iff h L η).1 h2
  simp only [coe_mul, coe_inv] at hw
  set w := (x : GL (Fin 4) K) * u * (x : GL (Fin 4) K)⁻¹ * (u : GL (Fin 4) K)⁻¹ with hwdef
  have hwc : (u : GL (Fin 4) K) * x * w = w * (u * x) := by
    have hcen : w ∈ CFSG.centerIn (miyamotoP h) := by
      rw [centerIn_miyamotoP]
      exact hw
    exact mem_centralizer_iff.1 (mem_inf.1 hcen).2 _ (mul_mem huP (miyamotoA1_le_P h hx))
  have e : miyamotoXGL h 0 b c d * miyamotoXGL h 1 0 0 0 =
      miyamotoXGL h 1 0 0 0 * miyamotoXGL h 0 b c d * w := by
    rw [← hxa]
    calc (x : GL (Fin 4) K) * u = w * (u * x) := by rw [hwdef]; group
      _ = u * x * w := hwc.symm
  have hb0 := eq_zero_of_mul_rootA_eq h hb hw e
  refine (symm_mem_miyamotoPull_iff h L η).2 ?_
  rw [hxa, miyamotoXGL_mem_Z2]
  exact ⟨rfl, hb0, hd⟩

theorem mem_F_of_commutator_mem_E (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η)
    (hc : ∀ y ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η, x * y * x⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q) :
    x ∈ miyamotoFG h L η t Q := by
  obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hx
  have hpA : p ∈ miyamotoA1G h L η := hS.mem_A1_of_commutator_mem_ZP hp fun a ha => by
    have haF := hS.A1_le_F1 ha
    have hpa : p * a * p⁻¹ ∈ miyamotoA1G h L η :=
      (mem_normalizer_iff.1 (hS.PG_le_normalizer_A1 hp) a).1 ha
    have h1 := hc a (mem_sup_left haF)
    have hcomm : f₀ * (p * a * p⁻¹) = (p * a * p⁻¹) * f₀ := hS.F1_comm hf₀ (hS.A1_le_F1 hpa)
    have h2 : f₀ * p * a * (f₀ * p)⁻¹ * a⁻¹ = p * a * p⁻¹ * a⁻¹ := by
      calc f₀ * p * a * (f₀ * p)⁻¹ * a⁻¹ = f₀ * (p * a * p⁻¹) * f₀⁻¹ * a⁻¹ := by group
        _ = (p * a * p⁻¹) * f₀ * f₀⁻¹ * a⁻¹ := by rw [hcomm]
        _ = p * a * p⁻¹ * a⁻¹ := by group
    rw [h2] at h1
    rw [← hS.E_inf_A1]
    exact mem_inf.2 ⟨h1, mul_mem hpa (inv_mem ha)⟩
  set x := f₀ * p with hxdef
  have hxF : x ∈ miyamotoF1G h L η t := mul_mem hf₀ (hS.A1_le_F1 hpA)
  have hxD := hS.F1_le_D1 hxF
  have hcross : ∀ {z g : G}, z ∈ miyamotoD1 h L η t → g * t = t * g →
      g * z * g⁻¹ ∈ miyamotoD1 h L η t →
      (g * z * g⁻¹)⁻¹ * t * (g * z * g⁻¹) * t = g * (z⁻¹ * t * z * t) * g⁻¹ := by
    intro z g _ hgt _
    have hgt' : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
        _ = t * g⁻¹ := by group
    calc (g * z * g⁻¹)⁻¹ * t * (g * z * g⁻¹) * t = g * z⁻¹ * (g⁻¹ * t) * g * z * g⁻¹ * t := by
          group
      _ = g * z⁻¹ * (t * g⁻¹) * g * z * g⁻¹ * t := by rw [hgt']
      _ = g * z⁻¹ * t * z * (g⁻¹ * t) := by group
      _ = g * z⁻¹ * t * z * (t * g⁻¹) := by rw [hgt']
      _ = g * (z⁻¹ * t * z * t) * g⁻¹ := by group
  have hZ2 : x⁻¹ * t * x * t ∈ miyamotoPull h L η (miyamotoZ2 h) := by
    refine hS.mem_Z2_of_commutator_mem_ZP (hS.crossed_mem_A1_of_mem_D1 hxD) fun g hg => ?_
    have hgt : g * t = t * g := mem_centralizer_singleton_iff.1 (hS.PG_le_C hg)
    have hgxD : g * x⁻¹ * g⁻¹ ∈ miyamotoD1 h L η t :=
      hS.F1_le_D1 ((mem_normalizer_iff.1 (hS.PG_le_normalizer_F1 hg) _).1 (inv_mem hxF))
    have hwE := hc g (mem_sup_right hg)
    have hwD : x * g * x⁻¹ * g⁻¹ ∈ miyamotoD1 h L η t := by
      have : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
      rw [this]
      exact mul_mem hxD hgxD
    have h1 := hS.sec3_3.2.2.2.2.2.1 _ hwE
    have h2 : (x * g * x⁻¹ * g⁻¹)⁻¹ * t * (x * g * x⁻¹ * g⁻¹) * t =
        (x⁻¹ * t * x * t) * g * (x⁻¹ * t * x * t)⁻¹ * g⁻¹ := by
      have e1 : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
      rw [e1, hS.crossed_mul_D1 hxD hgxD, hcross (inv_mem hxD) hgt hgxD,
        hS.crossed_inv_D1 hxD]
      group
    rw [h2] at h1
    exact h1
  obtain ⟨y, hy, hyx⟩ := hS.exists_F_crossed_eq hZ2
  have hyF := hS.F_le_F1 hy
  have hyD := hS.F1_le_D1 hyF
  have hxyA : x * y⁻¹ ∈ miyamotoA1G h L η := by
    refine (hS.crossed_eq_one_iff_F1 (mul_mem hxF (inv_mem hyF))).1 ?_
    rw [hS.crossed_mul_D1 hxD (inv_mem hyD), hS.crossed_inv_D1 hyD, hyx, mul_inv_cancel]
  have hxyZ := hS.mem_Z2_of_commutator_mem_ZP hxyA fun g hg => by
    have h1 := hc g (mem_sup_right hg)
    have h2 := hS.commutator_F_PG_mem_E (inv_mem hy) hg
    have hcomm : x * (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) = (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) * x :=
      hS.F1_comm hxF (hS.E_le_F1 h2)
    have e : x * y⁻¹ * g * (x * y⁻¹)⁻¹ * g⁻¹ =
        (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) * (x * g * x⁻¹ * g⁻¹) := by
      calc x * y⁻¹ * g * (x * y⁻¹)⁻¹ * g⁻¹
          = x * (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) * g * x⁻¹ * g⁻¹ := by group
        _ = (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) * x * g * x⁻¹ * g⁻¹ := by rw [hcomm]
        _ = _ := by group
    rw [← hS.E_inf_A1]
    refine mem_inf.2 ⟨by rw [e]; exact mul_mem h2 h1, ?_⟩
    have hgA : g * (x * y⁻¹)⁻¹ * g⁻¹ ∈ miyamotoA1G h L η :=
      (mem_normalizer_iff.1 (hS.PG_le_normalizer_A1 hg) _).1 (inv_mem hxyA)
    have : x * y⁻¹ * g * (x * y⁻¹)⁻¹ * g⁻¹ = (x * y⁻¹) * (g * (x * y⁻¹)⁻¹ * g⁻¹) := by group
    rw [this]
    exact mul_mem hxyA hgA
  have := mul_mem (hS.Z2_le_F hxyZ) hy
  rwa [inv_mul_cancel_right] at this

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
