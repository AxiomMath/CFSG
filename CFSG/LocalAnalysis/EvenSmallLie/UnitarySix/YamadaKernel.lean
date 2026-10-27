module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaWeak

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin
open SolomonWong (mul_comm_of_sq_eq_one card_conjSubgroup conjSubgroup_sq)

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem centralizer_toddE_le (h : Setting G L D t) :
    centralizer (toddE D t : Set G) ≤
      toddA D ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  intro x hx
  have hxH : x ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx t (t_mem_toddE D t)).symm
  set xH : centralizer ({t} : Set G) := ⟨x, hxH⟩
  have hfix : ∀ a ∈ D.A, autH h.H_le xH a = a := by
    intro a ha
    apply Subtype.ext
    rw [autH_apply]
    have hax : (a : G) * x = x * a :=
      mem_centralizer_iff.1 hx a (toddA_le_toddE D t ⟨a, ha, rfl⟩)
    change x * a * x⁻¹ = a
    rw [← hax, mul_inv_cancel_right]
  obtain ⟨a, ha, hα⟩ := h.facts.centralizer_A _ hfix
  have hT := h.inv_mul_mem_T xH a hα
  have e : x = a * ((a : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_left ⟨a, ha, rfl⟩) (mem_sup_right hT)

theorem le_centralizer_toddE (h : Setting G L D t) :
    toddA D ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ≤
      centralizer (toddE D t : Set G) := by
  have hEc : ∀ b ∈ toddE D t, ∀ c ∈ toddE D t, b * c = c * b :=
    fun _ hb _ hc => mul_comm_of_sq_eq_one h.toddE_sq hb hc
  refine sup_le (fun a ha => mem_centralizer_iff.2 fun e he =>
    hEc e he a (toddA_le_toddE D t ha)) (fun c hc => ?_)
  rw [mem_centralizer_iff]
  intro e he
  obtain ⟨a, ha, hea | hea⟩ := h.eq_or_eq_mul_of_mem_toddE he
  · rw [hea]
    exact (mem_centralizer_iff.1 hc.1 a (toddA_le D ha))
  · rw [hea]
    have h1 : a * c = c * a := mem_centralizer_iff.1 hc.1 a (toddA_le D ha)
    have h2 : t * c = c * t := mem_centralizer_singleton_iff.1 hc.2 |>.symm
    calc a * t * c = a * (t * c) := by group
      _ = c * (a * t) := by rw [h2, ← mul_assoc, h1, mul_assoc]

theorem normalizer_toddE_le (h : Setting G L D t) {u : G}
    (hu : u ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) (hut : u ^ 2 = t) :
    normalizer (toddE D t : Set G) ≤ centralizer ({t} : Set G) := by
  intro n hn
  have hv : n * u * n⁻¹ ∈ centralizer (toddE D t : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    have he' : n⁻¹ * e * n ∈ toddE D t := by
      have := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
      rwa [inv_inv] at this
    have hue : (n⁻¹ * e * n) * u = u * (n⁻¹ * e * n) :=
      mem_centralizer_iff.1 (h.le_centralizer_toddE (mem_sup_right hu)) _ he'
    calc e * (n * u * n⁻¹) = n * ((n⁻¹ * e * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * e * n)) * n⁻¹ := by rw [hue]
      _ = n * u * n⁻¹ * e := by group
  obtain ⟨a, ha, c, hc, hac⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha c hc => mem_centralizer_iff.1 (mem_inf.1 hc).1 a (toddA_le D ha))
    (h.centralizer_toddE_le hv)
  have hsq : n * t * n⁻¹ = c ^ 2 := by
    have hcomm : Commute a c := mem_centralizer_iff.1 hc.1 a (toddA_le D ha)
    rw [← hut, show n * u ^ 2 * n⁻¹ = (n * u * n⁻¹) ^ 2 by rw [sq, sq]; group, ← hac, hcomm.mul_pow,
      toddA_sq D a ha, one_mul]
  have hc2 : c ^ 2 ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := pow_mem hc 2
  have hc22 : (c ^ 2) ^ 2 = 1 := by
    rw [← hsq, show (n * t * n⁻¹) ^ 2 = n * t ^ 2 * n⁻¹ by rw [sq, sq]; group, h.t_sq]
    group
  rcases h.eq_t_of_mem_T hc2 hc22 with h1 | h1
  · exfalso
    rw [← hsq] at h1
    exact h.t_ne_one (by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group)
  · rw [← hsq] at h1
    rw [mem_centralizer_singleton_iff]
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h1]

theorem exists_conj_mem_toddE_ne_of_mem (h : Setting G L D t) {s c : G}
    (hsc : s = c⁻¹ * t * c)
    (hs : s ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) (hst : s ≠ t) :
    ∃ g : G, g⁻¹ * t * g ∈ toddE D t ∧ g⁻¹ * t * g ≠ t := by
  have hs2 : s ^ 2 = 1 := by
    rw [hsc, sq, show c⁻¹ * t * c * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c by group, ← sq, h.t_sq]
    group
  obtain ⟨l, hl, hl2, hsl⟩ := h.eq_or_eq_mul_t hs hs2
  have hl1 : l ≠ 1 := by
    rintro rfl
    rcases hsl with h1 | h1
    · apply h.t_ne_one
      calc t = c * s * c⁻¹ := by rw [hsc]; group
        _ = 1 := by rw [h1]; group
    · exact hst (by rw [h1, one_mul])
  have hlord : orderOf (⟨l, hl⟩ : L) = 2 := by
    rw [orderOf_mk]
    exact orderOf_eq_prime hl2 hl1
  obtain ⟨k, hk⟩ := D.conj_into_A _ hlord
  have hkA : (k : G) * l * (k : G)⁻¹ ∈ toddA D := mem_toddA.2 ⟨_, hk⟩
  have hkt : (k : G) * t = t * k := h.comm k.2
  have e : (c * (k : G)⁻¹)⁻¹ * t * (c * (k : G)⁻¹) = (k : G) * s * (k : G)⁻¹ := by
    rw [hsc]
    group
  refine ⟨c * (k : G)⁻¹, ?_, ?_⟩
  · rw [e]
    rcases hsl with h1 | h1
    · rw [h1]
      exact toddA_le_toddE D t hkA
    · rw [h1]
      have e2 : (k : G) * (l * t) * (k : G)⁻¹ = ((k : G) * l * (k : G)⁻¹) * t := by
        calc (k : G) * (l * t) * (k : G)⁻¹ = (k : G) * l * ((k : G)⁻¹ * ((k : G) * t)) *
            (k : G)⁻¹ := by group
          _ = (k : G) * l * ((k : G)⁻¹ * (t * k)) * (k : G)⁻¹ := by rw [hkt]
          _ = ((k : G) * l * (k : G)⁻¹) * t := by group
      rw [e2]
      exact mul_mem (toddA_le_toddE D t hkA) (t_mem_toddE D t)
  · intro h1
    rw [e] at h1
    apply hst
    calc s = (k : G)⁻¹ * ((k : G) * s * (k : G)⁻¹) * k := by group
      _ = (k : G)⁻¹ * (t * k) := by rw [h1, mul_assoc]
      _ = t := by rw [← hkt]; group

theorem exists_conj_mem_LT_of_outer (h : Setting G L D t) {s c : G}
    (hsc : s = c⁻¹ * t * c) (hsH : s ∈ centralizer ({t} : Set G))
    (hout : ∀ m : L, autH h.H_le ⟨s, hsH⟩ ≠ MulAut.conj m) :
    ∃ y : G, y⁻¹ * t * y ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ∧
      y⁻¹ * t * y ≠ t := by
  set α := autH h.H_le ⟨s, hsH⟩ with hαdef
  have hs2 : s * s = 1 := by
    rw [hsc, show c⁻¹ * t * c * (c⁻¹ * t * c) = c⁻¹ * t ^ 2 * c by rw [sq]; group, h.t_sq]
    group
  have hαα : α * α = 1 := by
    rw [hαdef, ← map_mul]
    have : (⟨s, hsH⟩ : centralizer ({t} : Set G)) * ⟨s, hsH⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  obtain ⟨l, hv1, hvmem⟩ := h.facts.fusion α hαα hout
  have hαl : ((α l : L) : G) = s * l * s⁻¹ := autH_apply h.H_le _ l
  have hvG : ((l * (α l)⁻¹ : L) : G) = l * s * (l : G)⁻¹ * s⁻¹ := by
    rw [coe_mul, coe_inv, hαl]
    group
  set W := (fixedSubgroup α).map L.subtype with hWdef
  have hWs : W ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hw' : ((α w : L) : G) = w := congrArg Subtype.val (mem_fixedSubgroup.1 hw)
    rw [autH_apply] at hw'
    change (w : G) * s = s * w
    calc (w : G) * s = s * w * s⁻¹ * s := by rw [hw']
      _ = s * w := by group
  have hvW : ((l * (α l)⁻¹ : L) : G) ∈ ⁅⁅W, W⁆, ⁅W, W⁆⁆ := by
    have := mem_map_of_mem L.subtype hvmem
    rw [map_commutator, map_commutator] at this
    exact this
  set W' := W.map (MulAut.conj c).toMonoidHom with hW'def
  have hW'H : W' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hws := mem_centralizer_singleton_iff.1 (hWs hw)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have ht : t = c * s * c⁻¹ := by rw [hsc]; group
    rw [ht]
    calc c * w * c⁻¹ * (c * s * c⁻¹) = c * (w * s) * c⁻¹ := by group
      _ = c * (s * w) * c⁻¹ := by rw [hws]
      _ = c * s * c⁻¹ * (c * w * c⁻¹) := by group
  have hx : c * (l * s * (l : G)⁻¹ * s⁻¹) * c⁻¹ ∈ ⁅⁅W', W'⁆, ⁅W', W'⁆⁆ := by
    have := mem_map_of_mem (MulAut.conj c).toMonoidHom hvW
    rw [map_commutator, map_commutator, hvG] at this
    have e1 : (MulAut.conj c).toMonoidHom ((l : G) * s * (l : G)⁻¹ * s⁻¹) =
        c * (l * s * (l : G)⁻¹ * s⁻¹) * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e1] at this
    exact this
  have hxLT := h.commutator_commutator_le hW'H hx
  have e : (c * (l : G)⁻¹ * c⁻¹)⁻¹ * t * (c * (l : G)⁻¹ * c⁻¹) =
      c * (l * s * (l : G)⁻¹ * s⁻¹) * c⁻¹ * t := by
    rw [hsc]
    group
  refine ⟨c * (l : G)⁻¹ * c⁻¹, ?_, ?_⟩
  · rw [e]
    exact mul_mem hxLT (mem_sup_right h.t_mem_T)
  · rw [e]
    intro h1
    apply hv1
    apply Subtype.ext
    rw [hvG, coe_one]
    calc (l : G) * s * (l : G)⁻¹ * s⁻¹ =
        c⁻¹ * (c * (l * s * (l : G)⁻¹ * s⁻¹) * c⁻¹ * t) * t⁻¹ * c := by group
      _ = 1 := by rw [h1]; group

theorem exists_conj_mem_toddE_ne (h : Setting G L D t) :
    ∃ g : G, g⁻¹ * t * g ∈ toddE D t ∧ g⁻¹ * t * g ≠ t := by
  by_contra hcon
  push Not at hcon
  have := h.std.simple
  apply false_of_isolated_involution h.std.nonab h.order
  intro y hyH hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  by_contra hyt
  have hy : y = c⁻¹⁻¹ * t * c⁻¹ := by rw [inv_inv, hc]
  by_cases hin : ∃ m : L, autH h.H_le ⟨y, hyH⟩ = MulAut.conj m
  · obtain ⟨g, hg1, hg2⟩ :=
      h.exists_conj_mem_toddE_ne_of_mem hy ((h.exists_conj_iff ⟨y, hyH⟩).1 hin) hyt
    exact hg2 (hcon g hg1)
  · push Not at hin
    obtain ⟨y', hy'1, hy'2⟩ := h.exists_conj_mem_LT_of_outer hy hyH hin
    obtain ⟨g, hg1, hg2⟩ := h.exists_conj_mem_toddE_ne_of_mem rfl hy'1 hy'2
    exact hg2 (hcon g hg1)

theorem exists_sq_eq_t (h : Setting G L D t)
    (hT : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≠ zpowers t) :
    ∃ u ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), u ^ 2 = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcyc, hp⟩ := h.T_facts
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hle : zpowers t ≤ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
    zpowers_le.2 h.t_mem_T
  have hn2 : 2 ≤ n := by
    by_contra hc
    push Not at hc
    have h2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, h.order]
    have hd := Subgroup.card_dvd_of_le hle
    rw [h2, hn] at hd
    interval_cases n
    · exact absurd hd (by norm_num)
    · exact hT (eq_of_le_of_card_ge hle (by rw [hn, h2]; norm_num)).symm
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G))
  rw [hn] at hg₀
  set u := g₀ ^ 2 ^ (n - 2) with hudef
  have hu2 : u ^ 2 = g₀ ^ 2 ^ (n - 1) := by
    rw [hudef, ← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
  have hord : orderOf (g₀ ^ 2 ^ (n - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hg₀]; exact Nat.pow_dvd_pow 2 (by omega)),
      hg₀, Nat.pow_div (by omega) (by norm_num), show n - (n - 1) = 1 by omega, pow_one]
  refine ⟨u, u.2, ?_⟩
  have hu2G : (u : G) ^ 2 = ((g₀ ^ 2 ^ (n - 1) : _) : G) := by
    rw [← SubgroupClass.coe_pow, hu2]
  rw [hu2G]
  have h1 : ((g₀ ^ 2 ^ (n - 1) : _) : G) ^ 2 = 1 := by
    have h1' : (g₀ ^ 2 ^ (n - 1)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g₀ ^ 2 ^ (n - 1))
      rwa [hord] at this
    rw [← SubgroupClass.coe_pow, h1', coe_one]
  rcases h.eq_t_of_mem_T (g₀ ^ 2 ^ (n - 1)).2 h1 with h0 | h0
  · exfalso
    have : g₀ ^ 2 ^ (n - 1) = 1 := Subtype.ext h0
    rw [this, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · exact h0

theorem inf_centralizer_eq (h : Setting G L D t) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  by_contra hT
  obtain ⟨u, hu, hut⟩ := h.exists_sq_eq_t hT
  obtain ⟨g, hgE, hgt⟩ := h.exists_conj_mem_toddE_ne
  obtain ⟨n, hn, hgn⟩ := h.fusion hgE
  have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (h.normalizer_toddE_le hu hut hn)
  apply hgt
  rw [hgn]
  calc n⁻¹ * t * n = n⁻¹ * (t * n) := by group
    _ = n⁻¹ * (n * t) := by rw [hnt]
    _ = t := by group

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
