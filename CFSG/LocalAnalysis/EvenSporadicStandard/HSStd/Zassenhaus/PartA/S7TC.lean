module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7K1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Sigma

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup Open

section Abstract

variable {T : Type} [Group T]

theorem s7tc_card_closure27 {y c c' : T} (hy : y ^ 3 = 1) (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1)
    (hy1 : y ≠ 1) (hc1 : c ≠ 1) (hc'1 : c' ≠ 1) (hyc : Commute y c) (hyc' : Commute y c')
    (hcc' : Commute c c')
    (hind : ∀ i j l : ℤ, y ^ i * c ^ j * c' ^ l = 1 → y ^ i = 1 ∧ c ^ j = 1 ∧ c' ^ l = 1) :
    Nat.card ↥(closure ({y, c, c'} : Set T)) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hoy : orderOf y = 3 := orderOf_eq_prime hy hy1
  have hoc : orderOf c = 3 := orderOf_eq_prime hc hc1
  have hoc' : orderOf c' = 3 := orderOf_eq_prime hc' hc'1
  have hcast : ∀ n : ℤ, (((n % 3).toNat : ℕ) : ℤ) = n % 3 := fun n =>
    Int.toNat_of_nonneg (by omega)
  let g : Fin 3 × Fin 3 × Fin 3 → ↥(closure ({y, c, c'} : Set T)) := fun p =>
    ⟨wd y c c' (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ), wd_mem_closure _ _ _⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨i, j, l, rfl⟩ := mem_closure_wd hyc hyc' hcc' hx
    refine ⟨(⟨(i % 3).toNat, by omega⟩, ⟨(j % 3).toNat, by omega⟩, ⟨(l % 3).toNat, by omega⟩), ?_⟩
    apply Subtype.ext
    show wd y c c' (((i % 3).toNat : ℕ) : ℤ) (((j % 3).toNat : ℕ) : ℤ) (((l % 3).toNat : ℕ) : ℤ) =
      wd y c c' i j l
    simp only [hcast]
    exact (wd_mod hy hc hc' i j l).symm
  have hinj : Function.Injective g := by
    intro p q hpq
    have h : wd y c c' (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ) =
        wd y c c' (q.1 : ℕ) (q.2.1 : ℕ) (q.2.2 : ℕ) := congrArg Subtype.val hpq
    have h1 : wd y c c' (((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ)) (((p.2.1 : ℕ) : ℤ) - ((q.2.1 : ℕ) : ℤ))
        (((p.2.2 : ℕ) : ℤ) - ((q.2.2 : ℕ) : ℤ)) = 1 := by
      have h2 : wd y c c' (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ) *
          (wd y c c' (q.1 : ℕ) (q.2.1 : ℕ) (q.2.2 : ℕ))⁻¹ = 1 := by
        rw [h, mul_inv_cancel]
      rw [wd_inv hyc hyc' hcc', wd_mul hyc hyc' hcc'] at h2
      simpa only [sub_eq_add_neg] using h2
    obtain ⟨e1, e2, e3⟩ := hind _ _ _ h1
    have d1 := orderOf_dvd_iff_zpow_eq_one.2 e1
    have d2 := orderOf_dvd_iff_zpow_eq_one.2 e2
    have d3 := orderOf_dvd_iff_zpow_eq_one.2 e3
    rw [hoy] at d1
    rw [hoc] at d2
    rw [hoc'] at d3
    have := p.1.2
    have := p.2.1.2
    have := p.2.2.2
    have := q.1.2
    have := q.2.1.2
    have := q.2.2.2
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> omega
  have hbij : Function.Bijective g := ⟨hinj, hsurj⟩
  rw [← Nat.card_eq_of_bijective g hbij]
  simp [Nat.card_eq_fintype_card]

end Abstract

section Facts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.s7_yT_ord (hb : PAB G L t E W z) (a : PA5 L t E z) : orderOf (a.s7_yT hb) = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact a.y_ord

theorem PA5.s7tc_mem_N₁ (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G}
    (hub : g * a.ub = a.ub * g) (hu₁ : a.dcase = DCase.d8 → g * a.u₁ = a.u₁ * g) :
    g ∈ a.s7_N₁ := by
  rw [a.s7_mem_N₁]
  refine ⟨fun f => ?_, hub⟩
  have hcomm : ∀ f ∈ a.F₀, g * f * g⁻¹ = f := by
    intro f hf
    have h : g * f = f * g := by
      rcases (a.s7_mem_F₀_iff hb f).1 hf with h | h | ⟨hd, h | h⟩
      · rw [h, one_mul, mul_one]
      · rw [h]; exact hub
      · rw [h]; exact hu₁ hd
      · rw [h]
        calc g * (a.ub * a.u₁) = (g * a.ub) * a.u₁ := (mul_assoc _ _ _).symm
          _ = a.ub * (g * a.u₁) := by rw [hub, mul_assoc]
          _ = a.ub * (a.u₁ * g) := by rw [hu₁ hd]
          _ = a.ub * a.u₁ * g := (mul_assoc _ _ _).symm
    rw [mul_inv_eq_iff_eq_mul]; exact h
  constructor
  · intro hf; rw [hcomm f hf]; exact hf
  · intro hf
    have h : g⁻¹ * (g * f * g⁻¹) * g = f := by group
    have hf' := hcomm _ hf
    have : g * f * g⁻¹ = g * (g * f * g⁻¹) * g⁻¹ := by rw [hf']
    have h2 : f = g * f * g⁻¹ := by
      have := congrArg (fun x => g⁻¹ * x * g) this
      simpa [mul_assoc] using this
    rw [h2]; exact hf

theorem PA5.s7tc_hind (a : PA5 L t E z) {c : G} (hcK : c ∈ a.K₁) (i j l : ℤ)
    (h : a.y ^ i * c ^ j * (t * c * t⁻¹) ^ l = 1) :
    a.y ^ i = 1 ∧ c ^ j = 1 ∧ (t * c * t⁻¹) ^ l = 1 := by
  have hc' : t * c * t⁻¹ ∈ conjSub t a.K₁ := mem_conjSub.2 ⟨c, hcK, rfl⟩
  have hcj : c ^ j ∈ a.K₁ := zpow_mem hcK j
  have hcl : (t * c * t⁻¹) ^ l ∈ conjSub t a.K₁ := zpow_mem hc' l
  have hyi : a.y ^ i ∈ fusionOddCoreOf (Cen a.y) := zpow_mem a.y_O i
  have h1 : a.y ^ i = 1 := by
    have hm : a.y ^ i ∈ fusionOddCoreOf (Cen a.y) ⊓ (a.K₁ ⊔ conjSub t a.K₁) := by
      refine ⟨hyi, ?_⟩
      have : a.y ^ i = (c ^ j * (t * c * t⁻¹) ^ l)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← mul_assoc]; exact h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (mem_sup_left hcj) (mem_sup_right hcl))
    rw [a.O_inf] at hm
    exact Subgroup.mem_bot.1 hm
  rw [h1, one_mul] at h
  have h2 : c ^ j = 1 := by
    have hm : c ^ j ∈ a.K₁ ⊓ conjSub t a.K₁ := by
      refine ⟨hcj, ?_⟩
      have : c ^ j = ((t * c * t⁻¹) ^ l)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact Subgroup.inv_mem _ hcl
    rw [a.K₁_inf] at hm
    exact Subgroup.mem_bot.1 hm
  rw [h2, one_mul] at h
  exact ⟨h1, h2, h⟩

theorem PA5.s7_exists_ckT (hb : PAB G L t E W z) (a : PA5 L t E z)
    (hinv : ∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, a.s7_tT hb * x * (a.s7_tT hb)⁻¹ = x⁻¹)
    (hyL : a.s7_κ (a.s7_yT hb) ∈ centralizerDerived (a.s7_κ (a.s7_tT hb))) :
    ∃ c k : ↥a.s7_N₁, (c : G) ∈ a.K₁ ∧ (k : G) ∈ a.K₁ ∧
      SigmaConfig (a.s7_κ (a.s7_tT hb)) (a.s7_κ (a.s7_yT hb)) (a.s7_κ c) (a.s7_κ k) := by
  obtain ⟨c, k, hcK, hkK, hc3, hc1, hk2, hk1, hkc, hcub, hkub, hd8⟩ := a.s7_exists_ck hb
  have hcN : c ∈ a.s7_N₁ :=
    a.s7tc_mem_N₁ hb hcub (fun hd => (hd8 hd).1)
  have hkN : k ∈ a.s7_N₁ :=
    a.s7tc_mem_N₁ hb hkub (fun hd => (hd8 hd).2)
  refine ⟨⟨c, hcN⟩, ⟨k, hkN⟩, hcK, hkK, ?_⟩
  have hcy : c * a.y = a.y * c := mem_Cen.1 (a.K₁_le hcK)
  have hky : k * a.y = a.y * k := mem_Cen.1 (a.K₁_le hkK)
  have hty : t * a.y = a.y * t := mem_Cen.1 a.t_cy
  have hc3' : c ^ 3 = 1 := by rw [pow_three]; simpa [mul_assoc] using hc3
  have hct : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hc3' hc1
  have hc'K : t * c * t⁻¹ ∈ conjSub t a.K₁ := mem_conjSub.2 ⟨c, hcK, rfl⟩
  have hk'K : t * k * t⁻¹ ∈ conjSub t a.K₁ := mem_conjSub.2 ⟨k, hkK, rfl⟩
  have hyc' : Commute a.y (t * c * t⁻¹) :=
    ((Commute.symm (show Commute t a.y from hty)).mul_right (Commute.symm (show Commute c a.y from hcy))).mul_right
      (Commute.symm (show Commute t a.y from hty)).inv_right
  have hcc' : c * (t * c * t⁻¹) = (t * c * t⁻¹) * c :=
    (a.K₁_K₁t.comm hcK hc'K)
  have hkc' : k * (t * c * t⁻¹) = (t * c * t⁻¹) * k := a.K₁_K₁t.comm hkK hc'K
  have hkk' : k * (t * k * t⁻¹) = (t * k * t⁻¹) * k := a.K₁_K₁t.comm hkK hk'K
  have hy3G : a.y ^ 3 = 1 := by
    have := pow_orderOf_eq_one a.y
    rwa [a.y_ord] at this
  have hc1T : (⟨c, hcN⟩ : ↥a.s7_N₁) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hc'1G : t * c * t⁻¹ ≠ 1 := by
    intro h
    apply hc1
    have := congrArg (fun x => t⁻¹ * x * t) h
    simpa [mul_assoc] using this
  have hy1G : a.y ≠ 1 := by
    intro h
    have := a.y_ord
    rw [h, orderOf_one] at this
    omega
  have hy1T : a.s7_yT hb ≠ 1 := fun h => hy1G (congrArg Subtype.val h)
  have hyT3 : (a.s7_yT hb) ^ 3 = 1 := Subtype.ext hy3G
  have hcT3 : (⟨c, hcN⟩ : ↥a.s7_N₁) ^ 3 = 1 := Subtype.ext hc3'
  have hc'T3 : (a.s7_tT hb * ⟨c, hcN⟩ * (a.s7_tT hb)⁻¹) ^ 3 = 1 := by
    apply Subtype.ext
    show (t * c * t⁻¹) ^ 3 = 1
    rw [conj_pow, hc3']; group
  have hc'1T : a.s7_tT hb * ⟨c, hcN⟩ * (a.s7_tT hb)⁻¹ ≠ 1 := fun h => hc'1G (congrArg Subtype.val h)
  have hycT : Commute (a.s7_yT hb) ⟨c, hcN⟩ := Subtype.ext hcy.symm
  have hyc'T : Commute (a.s7_yT hb) (a.s7_tT hb * ⟨c, hcN⟩ * (a.s7_tT hb)⁻¹) :=
    Subtype.ext hyc'.eq
  have hcc'T : Commute (⟨c, hcN⟩ : ↥a.s7_N₁) (a.s7_tT hb * ⟨c, hcN⟩ * (a.s7_tT hb)⁻¹) :=
    Subtype.ext hcc'
  have h27 : Nat.card ↥(closure ({a.s7_yT hb, (⟨c, hcN⟩ : ↥a.s7_N₁),
      a.s7_tT hb * ⟨c, hcN⟩ * (a.s7_tT hb)⁻¹} : Set ↥a.s7_N₁)) = 27 := by
    refine s7tc_card_closure27 hyT3 hcT3 hc'T3 hy1T hc1T hc'1T hycT hyc'T hcc'T ?_
    intro i j l h
    have h1 := congrArg Subtype.val h
    have e : a.y ^ i * c ^ j * (t * c * t⁻¹) ^ l = 1 := h1
    obtain ⟨e1, e2, e3⟩ := a.s7tc_hind hcK i j l e
    exact ⟨Subtype.ext e1, Subtype.ext e2, Subtype.ext e3⟩
  refine sigmaConfig_of_lift a.s7_κ (Subtype.ext hb.t_mul_t) (Subtype.ext hty.symm)
    (Open.fusionOddCore ↥a.s7_N₁) a.s7_F hinv
    (a.s7_ker_le hb) (a.s7_F_comm_core hb) (a.s7_F_disj_core hb) (a.s7_F_pgroup hb)
    (a.s7_yT_ord hb) ?_ ?_ ?_ ?_ ?_ ?_ h27 ?_ ?_ ?_ hyL
  · have : orderOf (⟨c, hcN⟩ : ↥a.s7_N₁) = 3 := by
      rw [← Subgroup.orderOf_coe]; exact hct
    exact this
  · exact Subtype.ext hk2
  · exact Subtype.ext hcy.symm
  · exact Subtype.ext hyc'.eq
  · exact Subtype.ext hcc'
  · exact Subtype.ext hky.symm
  · exact Subtype.ext hkc
  · exact Subtype.ext hkc'
  · exact Subtype.ext hkk'

end Facts

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
