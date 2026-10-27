module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YElem

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

theorem comm_of_mul_self_of_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y * x := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

theorem mul_self_of_mem_sup_zpowers_of_comm {G : Type*} [Group G] {V₀ : Subgroup G} {t : G}
    (ht : t * t = 1) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hct : ∀ v ∈ V₀, v * t = t * v) {x : G}
    (hx : x ∈ V₀ ⊔ zpowers t) : x * x = 1 := by
  have hV₀t : ∀ v ∈ V₀, t * v * t ∈ V₀ := fun v hv => by
    rw [← hct v hv, mul_assoc, ht, mul_one]
    exact hv
  rcases (mem_sup_zpowers_iff ht hV₀t).1 hx with hx₀ | hx₀
  · exact hV₀ x hx₀
  · generalize hu : x * t = u at hx₀
    obtain rfl : x = u * t := by rw [← hu, mul_assoc, ht, mul_one]
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [hct u hx₀]
      _ = u * u * (t * t) := by group
      _ = 1 := by rw [hV₀ u hx₀, ht, one_mul]

theorem le_or_le_sup_zpowers_of_elem {G : Type*} [Group G] {V V₀ : Subgroup G} {t : G}
    (ht : t * t = 1) (hVt : ∀ v ∈ V, t * v * t ∈ V) (hV : ∀ v ∈ V, v * v = 1)
    (hV₀ : ∀ v, v ∈ V₀ ↔ v ∈ V ∧ v * t = t * v) {E : Subgroup G} (hE : E ≤ V ⊔ zpowers t)
    (hsq : ∀ x ∈ E, x * x = 1) : E ≤ V ∨ E ≤ V₀ ⊔ zpowers t := by
  have hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    comm_of_mul_self_of_mul_self (hV v hv) (hV w hw) (hV _ (mul_mem hv hw))
  by_cases hEV : E ≤ V
  · exact Or.inl hEV
  right
  obtain ⟨k, hkE, hkV⟩ := IsConcreteLE.not_le_iff_exists.1 hEV
  have hfV : k * t ∈ V := ((mem_sup_zpowers_iff ht hVt).1 (hE hkE)).resolve_left hkV
  generalize hf : k * t = f at hfV
  obtain rfl : k = f * t := by rw [← hf, mul_assoc, ht, mul_one]
  have hft : f * t = t * f := by
    have e1 : f * (t * f * t) = f * f := by
      rw [hV f hfV, show f * (t * f * t) = f * t * (f * t) by group]
      exact hsq _ hkE
    have e2 : t * f * t = f := mul_left_cancel e1
    calc f * t = t * f * t * t := by rw [e2]
      _ = t * f := by rw [mul_assoc (t * f), ht, mul_one]
  intro x hx
  have hxk : x * (f * t) = f * t * x :=
    comm_of_mul_self_of_mul_self (hsq x hx) (hsq _ hkE) (hsq _ (mul_mem hx hkE))
  rcases (mem_sup_zpowers_iff ht hVt).1 (hE hx) with hxV | hxV
  · refine mem_sup_left ((hV₀ x).2 ⟨hxV, ?_⟩)
    have hxf : x * f = f * x := hVc x hxV f hfV
    calc x * t = f⁻¹ * (f * x) * t := by group
      _ = f⁻¹ * (x * f) * t := by rw [hxf]
      _ = f⁻¹ * (x * (f * t)) := by group
      _ = f⁻¹ * (f * t * x) := by rw [hxk]
      _ = t * x := by group
  · generalize hy : x * t = y at hxV
    obtain rfl : x = y * t := by rw [← hy, mul_assoc, ht, mul_one]
    refine mul_mem (mem_sup_left ((hV₀ y).2 ⟨hxV, ?_⟩)) (mem_sup_right (mem_zpowers t))
    have e0 : y * t * (f * t) = y * f := by
      calc y * t * (f * t) = y * (t * f) * t := by group
        _ = y * (f * t) * t := by rw [hft]
        _ = y * f * (t * t) := by group
        _ = y * f := by rw [ht, mul_one]
    have e1 : f * y = f * (t * y * t) := by
      calc f * y = y * f := (hVc y hxV f hfV).symm
        _ = y * t * (f * t) := e0.symm
        _ = f * t * (y * t) := hxk
        _ = f * (t * y * t) := by group
    have e2 : y = t * y * t := mul_left_cancel e1
    calc y * t = t * y * t * t := by rw [← e2]
      _ = t * y := by rw [mul_assoc (t * y), ht, mul_one]

theorem mem_normalizer_sup_zpowers_of_elem {G : Type*} [Group G] [Finite G]
    {V V₀ : Subgroup G} {t : G} (ht : t * t = 1) (htV : t ∉ V)
    (hVt : ∀ v ∈ V, t * v * t ∈ V) (hV : ∀ v ∈ V, v * v = 1)
    (hV₀ : ∀ v, v ∈ V₀ ↔ v ∈ V ∧ v * t = t * v) {g : G}
    (hg : g ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G))
    (hgV : g ∈ normalizer (V : Set G)) :
    g ∈ normalizer ((V₀ ⊔ zpowers t : Subgroup G) : Set G) := by
  have hV₀V : V₀ ≤ V := fun v hv => ((hV₀ v).1 hv).1
  have hE : (V₀ ⊔ zpowers t).map (MulAut.conj g).toMonoidHom ≤ V ⊔ zpowers t := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 (sup_le_sup_right hV₀V _ hx)
  have hsq : ∀ x ∈ (V₀ ⊔ zpowers t).map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change g * x * g⁻¹ * (g * x * g⁻¹) = 1
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group,
      mul_self_of_mem_sup_zpowers_of_comm ht (fun v hv => hV v (hV₀V hv))
        (fun v hv => ((hV₀ v).1 hv).2) hx, mul_one, mul_inv_cancel]
  rcases le_or_le_sup_zpowers_of_elem ht hVt hV hV₀ hE hsq with hle | hle
  · exfalso
    have h1 : g * t * g⁻¹ ∈ V := hle ⟨t, mem_sup_right (mem_zpowers t), rfl⟩
    have h2 := (mem_normalizer_iff.1 (inv_mem hgV) _).1 h1
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h2
    exact htV h2
  · exact mem_normalizer_fintype fun x hx => hle ⟨x, hx, rfl⟩

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_F_iff_Y
    (h : d.Hyp) (v : G) :
    v ∈ d.F ↔ v ∈ d.Y ∧ v * d.t = d.t * v := by
  rw [← h.sec4_6.2.2.2.1, Subgroup.mem_inf, mem_centralizer_singleton_iff]

theorem F_le_Y
    (h : d.Hyp) :
    d.F ≤ d.Y := fun v hv => ((h.mem_F_iff_Y v).1 hv).1

theorem t_conj_mem_Y
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) : d.t * y * d.t ∈ d.Y := by
  rw [h.Y_eq_E₂] at hy ⊢
  have := (mem_normalizer_iff.1 ((h.le_normalizer_E₂).2 h.t_mem_U) y).1 hy
  rwa [h.t_inv] at this

theorem mem_withT_Y_iff
    (h : d.Hyp) {x : G} :
    x ∈ d.withT d.Y ↔ x ∈ d.Y ∨ x * d.t ∈ d.Y :=
  mem_sup_zpowers_iff h.t_mul_t fun _ hk => h.t_conj_mem_Y hk

theorem t_not_mem_Y
    (h : d.Hyp) :
    d.t ∉ d.Y := fun ht => h.t_not_mem_E₂ (h.Y_eq_E₂ ▸ ht)

theorem t_mem_NHA₂ (h : d.Hyp) : d.t ∈ normalizer (d.A₂ : Set G) ⊓ d.H := by
  refine Subgroup.mem_inf.2 ⟨mem_normalizer_fintype fun a ha => ?_, h.t_mem_H⟩
  rw [← h.t_comm_of_mem_L (d.pull_le_L _ ha), mul_inv_cancel_right]
  exact ha

theorem NHA₂_le_normalizer_withT_F
    (h : d.Hyp) :
    normalizer (d.A₂ : Set G) ⊓ d.H ≤ normalizer ((d.withT d.F : Subgroup G) : Set G) := by
  rw [h.normalizer_withT_F_eq, h.normalizer_withT_A₂_eq]
  exact le_sup_left

theorem normalizer_withT_F_le_NHA₂Y
    (h : d.Hyp) :
    normalizer ((d.withT d.F : Subgroup G) : Set G) ≤
      (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y := by
  rw [h.normalizer_withT_F_eq, h.normalizer_withT_A₂_eq]
  refine sup_le le_sup_left ?_
  rw [h.sec4_6.1, h.sec4_6.2.2.1]
  refine sup_le (sup_le ?_ le_sup_right) ?_
  · refine le_trans (fun a ha => ?_) le_sup_left
    exact Subgroup.mem_inf.2 ⟨(d.A₂).le_normalizer ha, h.L_le_H (d.pull_le_L _ ha)⟩
  · rw [zpowers_le]
    exact mem_sup_left h.t_mem_NHA₂

theorem conj_mem_D₀_of_NHA₂
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.A₂ : Set G) ⊓ d.H) {x : G} (hx : x ∈ d.D₀) :
    g * x * g⁻¹ ∈ d.D₀ := by
  obtain ⟨hgA, hgH⟩ := Subgroup.mem_inf.1 hg
  have hgF := h.NHA₂_le_normalizer_withT_F hg
  have hle : d.D₀ ≤ d.D₀.comap (MulAut.conj g).toMonoidHom := by
    rw [Data.D₀, commutator_le]
    intro c hc n hn
    change g * ⁅c, n⁆ * g⁻¹ ∈ ⁅d.C₀, d.NLA₂⁆
    rw [show g * ⁅c, n⁆ * g⁻¹ = ⁅g * c * g⁻¹, g * n * g⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    obtain ⟨hnA, hnL⟩ := Subgroup.mem_inf.1 hn
    exact commutator_mem_commutator (conj_mem_oTwo hgF hc) (Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem hgA hnA) (inv_mem hgA),
        (mem_normalizer_iff.1 (h.H_le_normalizer hgH) n).1 hnL⟩)
  exact hle hx

theorem NHA₂_le_normalizer_Y
    (h : d.Hyp) :
    normalizer (d.A₂ : Set G) ⊓ d.H ≤ normalizer (d.Y : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨hyC, hyD⟩ := Subgroup.mem_inf.1 hy
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_, h.conj_mem_D₀_of_NHA₂ hg hyD⟩
  have hx' := h.conj_mem_D₀_of_NHA₂ (inv_mem hg) hx
  rw [inv_inv] at hx'
  have e := mem_centralizer_iff.1 hyC _ hx'
  calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [e]
    _ = g * y * g⁻¹ * x := by group

theorem NHA₂Y_le_normalizer_withT_Y
    (h : d.Hyp) :
    (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y ≤
      normalizer ((d.withT d.Y : Subgroup G) : Set G) := by
  refine sup_le (fun g hg => ?_) fun y hy => (d.withT d.Y).le_normalizer (mem_sup_left hy)
  have hgY := h.NHA₂_le_normalizer_Y hg
  have hgt : g * d.t * g⁻¹ = d.t := by
    rw [mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2, mul_inv_cancel_right]
  have hle : d.withT d.Y ≤ (d.withT d.Y).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun y hy => mem_sup_left ((mem_normalizer_iff.1 hgY y).1 hy)) ?_
    rw [zpowers_le]
    change g * d.t * g⁻¹ ∈ d.withT d.Y
    rw [hgt]
    exact mem_sup_right (mem_zpowers _)
  exact mem_normalizer_fintype fun x hx => hle hx

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem le_Y_or_le_withT_F
    (h : d.Hyp)
    {E : Subgroup G} (hE : E ≤ d.withT d.Y) (hsq : ∀ x ∈ E, x * x = 1) :
    E ≤ d.Y ∨ E ≤ d.withT d.F :=
  le_or_le_sup_zpowers_of_elem h.t_mul_t (fun _ hv => h.t_conj_mem_Y hv) (fun _ hv => h.Y_sq hv)
    h.mem_F_iff_Y hE hsq

theorem normalizer_withT_Y_le_normalizer_Y
    (h : d.Hyp) :
    normalizer ((d.withT d.Y : Subgroup G) : Set G) ≤ normalizer (d.Y : Set G) := by
  intro g hg
  have hE : d.Y.map (MulAut.conj g).toMonoidHom ≤ d.withT d.Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 (mem_sup_left hx)
  have hsq : ∀ x ∈ d.Y.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change g * x * g⁻¹ * (g * x * g⁻¹) = 1
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, h.Y_sq hx, mul_one,
      mul_inv_cancel]
  rcases h.le_Y_or_le_withT_F hE hsq with hle | hle
  · exact mem_normalizer_fintype fun y hy => hle ⟨y, hy, rfl⟩
  · exfalso
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.sec4_6.2.2.2.2.1,
      h.card_withT_F] at h1
    norm_num at h1

theorem normalizer_withT_Y_le_normalizer_withT_F
    (h : d.Hyp) :
    normalizer ((d.withT d.Y : Subgroup G) : Set G) ≤
      normalizer ((d.withT d.F : Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_sup_zpowers_of_elem h.t_mul_t h.t_not_mem_Y (fun _ hv => h.t_conj_mem_Y hv)
    (fun _ hv => h.Y_sq hv) h.mem_F_iff_Y hg (h.normalizer_withT_Y_le_normalizer_Y hg)

theorem sec4_7
    (h : d.Hyp) :
    normalizer ((d.withT d.Y : Subgroup G) : Set G) =
      (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y :=
  le_antisymm (h.normalizer_withT_Y_le_normalizer_withT_F.trans h.normalizer_withT_F_le_NHA₂Y)
    h.NHA₂Y_le_normalizer_withT_Y

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
