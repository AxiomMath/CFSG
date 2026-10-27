module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionElem

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement


namespace Facts

section Alpha

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem exists_u₀ (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) :
    ∃ u : G, u ∈ d.V ⊓ centralizer (d.V : Set G) ∧ u ∈ centralizer (d.P : Set G) ∧ u ≠ 1 ∧
      u * u = 1 ∧ IsConj d.t (u * d.t) := by
  obtain ⟨t', ht'z, ht'c, ht'ne⟩ := hα
  have ht'2 := d.mul_self_of_isConj ht'c
  rcases F.central_mem_U_or d hR ht'z ht'2 with h | h
  · exact (F.not_isConj_of_mem d hR h.1.2 ht'c).elim
  · have ht2 := d.t_mul_self
    have hcomm : t' * d.t = d.t * t' := (mem_centralizer_iff.mp ht'z.2 d.t d.t_mem_P).symm
    refine ⟨t' * d.t, h, mul_mem ht'z.2 (d.t_mem_centralizer_P), ?_, ?_, ?_⟩
    · intro h1
      apply ht'ne
      have := congrArg (· * d.t) h1
      simpa [mul_assoc, ht2] using this
    · calc t' * d.t * (t' * d.t) = t' * (d.t * t') * d.t := by group
        _ = t' * (t' * d.t) * d.t := by rw [hcomm]
        _ = (t' * t') * (d.t * d.t) := by group
        _ = 1 := by rw [ht'2, ht2, one_mul]
    · have : t' * d.t * d.t = t' := by rw [mul_assoc, ht2, mul_one]
      rw [this]
      exact ht'c

theorem isConj_mul_t (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {a : G} (haA : a ∈ A) (ha2 : a * a = 1) : IsConj d.t (a * d.t) := by
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
  obtain ⟨u, hu, -, hu1, hu2, hut⟩ := F.exists_u₀ d hR hα
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨c, hc, hcu⟩ := F.invol_conj u hu.1.2 a haA huo hao
  have hct : c * d.t * c⁻¹ = d.t := by
    rw [d.comm_t_of_mem hc, mul_inv_cancel_right]
  refine hut.trans (isConj_iff.mpr ⟨c, ?_⟩)
  calc c * (u * d.t) * c⁻¹ = (c * u * c⁻¹) * (c * d.t * c⁻¹) := by group
    _ = a * d.t := by rw [hcu, hct]

theorem not_isConj_iff_mem (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) {x : G} (hx : x ∈ W ⊔ zpowers d.t) :
    ¬ IsConj d.t x ↔ x ∈ W := by
  obtain ⟨hWV, hWe, -⟩ := hR.property hW
  constructor
  · intro hnc
    by_contra hxW
    have hxt : x * d.t ∈ W := ((d.mem_adj_iff hWV).mp hx).resolve_left hxW
    have h2 : (x * d.t) * (x * d.t) = 1 := by rw [← sq]; exact hWe.2 _ hxt
    have h3 := F.isConj_mul_t d hR hα (hWV hxt).2 h2
    rw [mul_assoc, d.t_mul_self, mul_one] at h3
    exact hnc h3
  · intro hxW
    exact F.not_isConj_of_mem d hR (hWV hxW).2

end Alpha

end Facts

namespace Facts

section Alpha2

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem conj_mem_V_of_mem (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {n : G} (hn : n ∈ normalizer (d.P : Set G)) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) {v : G}
    (hv : v ∈ W) : n * v * n⁻¹ ∈ d.V := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  have hmem : n * v * n⁻¹ ∈ (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom :=
    ⟨v, mem_sup_left hv, by simp [MulAut.conj_apply]⟩
  have hnc : ¬ IsConj d.t (n * v * n⁻¹) := by
    intro h
    refine F.not_isConj_of_mem d hR (hWV hv).2 (h.trans (isConj_iff.mpr ⟨n⁻¹, ?_⟩))
    group
  rcases F.map_conj_adj d hR hn hW with h | h
  · rw [h] at hmem
    exact hR.le₁ ((F.not_isConj_iff_mem d hR hα (Or.inl rfl) hmem).mp hnc)
  · rw [h] at hmem
    exact hR.le₂ ((F.not_isConj_iff_mem d hR hα (Or.inr rfl) hmem).mp hnc)

theorem mem_normalizer_V (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {n : G} (hn : n ∈ normalizer (d.P : Set G)) : n ∈ normalizer (d.V : Set G) := by
  have hfwd : ∀ m ∈ normalizer (d.P : Set G), ∀ v ∈ d.V, m * v * m⁻¹ ∈ d.V := by
    intro m hm v hv
    have h1 : V₁.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      rintro _ ⟨w, hw, rfl⟩
      exact F.conj_mem_V_of_mem d hR hα hm (Or.inl rfl) hw
    have h2 : V₂.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      rintro _ ⟨w, hw, rfl⟩
      exact F.conj_mem_V_of_mem d hR hα hm (Or.inr rfl) hw
    have h3 : d.V.map (MulAut.conj m).toMonoidHom ≤ d.V := by
      calc d.V.map (MulAut.conj m).toMonoidHom
          = (V₁ ⊔ V₂).map (MulAut.conj m).toMonoidHom := by rw [hR.sup_eq]
        _ = V₁.map (MulAut.conj m).toMonoidHom ⊔ V₂.map (MulAut.conj m).toMonoidHom :=
          Subgroup.map_sup _ _ _
        _ ≤ d.V := sup_le h1 h2
    have := h3 (Subgroup.mem_map_of_mem _ hv)
    simpa [MulAut.conj_apply] using this
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd n hn x hx, fun hx => ?_⟩
  have := hfwd n⁻¹ (inv_mem hn) _ hx
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem conj_V_le_A (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) {g : G}
    (hg : g⁻¹ * d.t * g ∈ d.P ⊓ centralizer (d.P : Set G)) {v : G} (hv : v ∈ d.V) :
    g * v * g⁻¹ ∈ A := by
  have hconj : IsConj d.t (g⁻¹ * d.t * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_of_mem_center d.P_isSylow_centralizer hg hconj
  have hct : g * n⁻¹ * d.t * (g * n⁻¹)⁻¹ = d.t := by
    calc g * n⁻¹ * d.t * (g * n⁻¹)⁻¹ = g * (n⁻¹ * d.t * n) * g⁻¹ := by group
      _ = g * (g⁻¹ * d.t * g) * g⁻¹ := by rw [hnt]
      _ = d.t := by group
  have hc : g * n⁻¹ ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hct
  have hcN : g * n⁻¹ ∈ normalizer (A : Set G) := (centralizer_t_facts d.sector).1 hc
  have hnv : n * v * n⁻¹ ∈ A :=
    ((mem_normalizer_iff.mp (F.mem_normalizer_V d hR hα hn) v).mp hv).2
  have e : g * v * g⁻¹ = (g * n⁻¹) * (n * v * n⁻¹) * (g * n⁻¹)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp hcN _).mp hnv

end Alpha2

end Facts

namespace Facts

section Alpha3

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem sg_eq_zpowers (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) :
    sg A d.R = zpowers d.t := by
  obtain ⟨g, a, hgS, hord, ha1, hcard, ht⟩ := exists_generator_sg d.sector
  have hz : zpowers d.t ≤ sg A d.R := zpowers_le.mpr (t_mem_sg d.sector)
  by_cases ha : a = 1
  · refine (Subgroup.eq_of_le_of_card_ge hz ?_).symm
    rw [Nat.card_zpowers, d.sector.t_order, hcard, ha]
    norm_num
  exfalso
  have h4 : 4 ≤ Nat.card (sg A d.R) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨w, hwR, hww⟩ := exists_sq_eq_t d.sector h4
  obtain ⟨t', ht'z, ht'c, ht'ne⟩ := hα
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_of_mem_center d.P_isSylow_centralizer ht'z ht'c
  have hwP : w ∈ d.P := d.hRP hwR
  have hwK : w ∈ centralizer (A : Set G) := sg_le_centralizer hwR
  have hw'P : n⁻¹ * w * n ∈ d.P := (mem_normalizer_iff''.mp hn w).mp hwP
  have hα' : d.Alpha := ⟨t', ht'z, ht'c, ht'ne⟩
  have hw'V : ∀ v ∈ d.V, (n⁻¹ * w * n) * v = v * (n⁻¹ * w * n) := by
    intro v hv
    have hv' : n * v * n⁻¹ ∈ d.V :=
      (mem_normalizer_iff.mp (F.mem_normalizer_V d hR hα' hn) v).mp hv
    have h := mem_centralizer_iff.mp hwK (n * v * n⁻¹) hv'.2
    calc n⁻¹ * w * n * v = n⁻¹ * (w * (n * v * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * v * n⁻¹) * w) * n := by rw [← h]
      _ = v * (n⁻¹ * w * n) := by group
  have hw'N : n⁻¹ * w * n ∈ normalizer (A : Set G) ⊓ centralizer (d.V : Set G) :=
    ⟨d.P_le_normalizer hw'P, mem_centralizer_iff.mpr fun v hv => (hw'V v hv).symm⟩
  have hmem := F.cent_V d.V d.V_isSylow hw'N
  obtain ⟨u, hu, k, hk, hw'⟩ := mem_sup_of_commute
    (V := d.V ⊓ centralizer (d.V : Set G)) (R := centralizer (A : Set G))
    (fun u hu k hk => mem_centralizer_iff.mp hk u hu.1.2) hmem
  have hkP : k ∈ d.P := by
    have : k = u⁻¹ * (n⁻¹ * w * n) := by rw [hw']; group
    rw [this]
    exact d.P.mul_mem (d.P.inv_mem hu.1.1) hw'P
  have hkR : k ∈ sg A d.R := by
    rw [← d.P_inf_centralizer_eq]
    exact ⟨hkP, hk⟩
  have hu2 : u * u = 1 := by
    rw [← hR.inf_eq] at hu
    rw [← sq]
    exact hR.elem₁.2 u hu.1
  have huk : u * k = k * u := mem_centralizer_iff.mp hk u hu.1.2
  have ht'kk : t' = k * k := by
    calc t' = n⁻¹ * (w * w) * n := by rw [← hnt, hww]
      _ = (n⁻¹ * w * n) * (n⁻¹ * w * n) := by group
      _ = (u * k) * (u * k) := by rw [hw']
      _ = (u * u) * (k * k) := by
        calc u * k * (u * k) = u * (k * u) * k := by group
          _ = u * (u * k) * k := by rw [huk]
          _ = (u * u) * (k * k) := by group
      _ = k * k := by rw [hu2, one_mul]
  have hord' : orderOf t' = 2 := by rw [orderOf_eq_of_isConj ht'c]; exact d.sector.t_order
  exact ht'ne (eq_t_of_orderOf_eq_two d.sector (ht'kk ▸ mul_mem hkR hkR) hord')

end Alpha3

end Facts

namespace Facts

section Alpha4

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem two_dvd_index (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) :
    2 ∣ d.P.index := by
  by_contra hodd
  have hodd' := odd_card_normalizer_class d.P_le_centralizer hodd
  have ht2 := d.t_mul_self
  have hcls : ∀ x : G, (∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n) →
      x ∈ d.P ⊓ centralizer (d.P : Set G) ∧ IsConj d.t x := by
    rintro x ⟨n, hn, rfl⟩
    refine ⟨⟨(mem_normalizer_iff''.mp hn d.t).mp d.t_mem_P, mem_centralizer_iff.mpr fun p hp => ?_⟩,
      isConj_iff.mpr ⟨n⁻¹, by group⟩⟩
    have hp' : n * p * n⁻¹ ∈ d.P := (mem_normalizer_iff.mp hn p).mp hp
    have h := d.P_comm_t hp'
    calc p * (n⁻¹ * d.t * n) = n⁻¹ * ((n * p * n⁻¹) * d.t) * n := by group
      _ = n⁻¹ * (d.t * (n * p * n⁻¹)) * n := by rw [h]
      _ = n⁻¹ * d.t * n * p := by group
  have hmemCU : ∀ x : G, (∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n) →
      x * d.t ∈ d.CU := by
    intro x hx
    obtain ⟨hxz, hxc⟩ := hcls x hx
    have hx2 := d.mul_self_of_isConj hxc
    rcases F.central_mem_U_or d hR hxz hx2 with h | h
    · exact (F.not_isConj_of_mem d hR h.1.2 hxc).elim
    · exact ⟨h, mul_mem hxz.2 (d.t_mem_centralizer_P)⟩
  let f : {x : G // ∃ n ∈ normalizer (d.P : Set G), x = n⁻¹ * d.t * n} → ↥d.CU :=
    fun x => ⟨x.1 * d.t, hmemCU x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (mul_right_cancel this)
    · rintro ⟨u, hu⟩
      have hu2 := hR.mul_self_of_mem_center hu.1
      have hconj := F.isConj_mul_t d hR hα hu.1.1.2 hu2
      have hz : u * d.t ∈ d.P ⊓ centralizer (d.P : Set G) :=
        ⟨d.P.mul_mem hu.1.1.1 d.t_mem_P, mul_mem hu.2 (d.t_mem_centralizer_P)⟩
      obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_of_mem_center d.P_isSylow_centralizer hz hconj
      refine ⟨⟨u * d.t, n, hn, hnt.symm⟩, Subtype.ext ?_⟩
      show u * d.t * d.t = u
      rw [mul_assoc, ht2, mul_one]
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [hcard] at hodd'
  obtain ⟨u₀, hu₀, hu₀P, hu₀1, -, -⟩ := F.exists_u₀ d hR hα
  have hCUP : d.CU ≤ d.P := fun x hx => hx.1.1.1
  have hP2 : IsPGroup 2 ↥d.CU := d.hP.isPGroup.to_le hCUP
  rcases hP2.card_eq_or_dvd with h1 | h2
  · have : d.CU = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hmem : u₀ ∈ d.CU := ⟨hu₀, hu₀P⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hu₀1 hmem
  · exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)

end Alpha4

end Facts

end CFSG.OddStandard.Seitz77
