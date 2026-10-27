module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF2

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf
  card_sup_mul_card_inf_eq)

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem eq_zero_of_forall_commute_rootA {c : K}
    (hc : ∀ a : K, miyamotoXGL h a 0 0 0 * miyamotoXGL h 0 0 c 0 =
      miyamotoXGL h 0 0 c 0 * miyamotoXGL h a 0 0 0) : c = 0 := by
  by_contra hc0
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω + h.bar ω = 1 := by
    obtain ⟨ω, hω⟩ := h.traceLin_surjective 1
    exact ⟨ω, congrArg Subtype.val hω⟩
  have e := hc (c * ω)
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj] at e
  have e4 := e.2.2.2
  simp only [map_zero, mul_zero, add_zero, zero_add, map_mul] at e4
  have hbc : h.bar c ≠ 0 := (map_ne_zero _).2 hc0
  have h1 : h.bar c * c * (ω + h.bar ω) = 0 := by
    linear_combination e4 + (h.bar c * c * ω) * CharTwo.two_eq_zero (R := K)
  rw [hω, mul_one] at h1
  exact mul_ne_zero hbc hc0 h1

end Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem R1G_mem_N1 (_hS : Setting h L η t Q T) : miyamotoR1G h L η ∈ miyamotoN1G h L η := by
  have : CharP K 2 := h.charP
  exact (symm_mem_miyamotoPull_iff h L η).2 (miyamotoR1_mem_N1 h)

theorem R2G_mem_N2 (_hS : Setting h L η t Q T) : miyamotoR2G h L η ∈ miyamotoN2G h L η := by
  have : CharP K 2 := h.charP
  exact (symm_mem_miyamotoPull_iff h L η).2 (miyamotoR2_mem_N2 h)

theorem R1G_mul_self (_hS : Setting h L η t Q T) :
    miyamotoR1G h L η * miyamotoR1G h L η = 1 := by
  simp only [miyamotoR1G]
  rw [← L.coe_mul, ← map_mul]
  have e : (⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : gramSU h (miyamotoJ4 K)) *
      ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ = 1 := Subtype.ext (miyamotoR1_mul_self (K := K))
  rw [e, map_one, OneMemClass.coe_one]

theorem R2G_mul_self (_hS : Setting h L η t Q T) :
    miyamotoR2G h L η * miyamotoR2G h L η = 1 := by
  have : CharP K 2 := h.charP
  simp only [miyamotoR2G]
  rw [← L.coe_mul, ← map_mul]
  have e : (⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ : gramSU h (miyamotoJ4 K)) *
      ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩ = 1 := Subtype.ext (miyamotoR2_mul_self (K := K))
  rw [e, map_one, OneMemClass.coe_one]

theorem R1G_conj_mem_I2r1 (_hS : Setting h L η t Q T) {i : G} (hi : i ∈ miyamotoI2G h L η) :
    (miyamotoR1G h L η)⁻¹ * i * miyamotoR1G h L η ∈ miyamotoI2r1G h L η := by
  have key := miyamotoPull_map_conj h L η (miyamotoI2 h) ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩
  have e : miyamotoI2r1G h L η = (miyamotoI2G h L η).map
      (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom := key
  rw [e, mem_map_conj_inv_iff]
  rwa [show miyamotoR1G h L η * ((miyamotoR1G h L η)⁻¹ * i * miyamotoR1G h L η) *
    (miyamotoR1G h L η)⁻¹ = i by group]

omit [Finite G] in
theorem commute_conj_of_mul_self {r x i : G} (hr : r * r = 1)
    (hx : (r⁻¹ * i * r) * x = x * (r⁻¹ * i * r)) : i * (r⁻¹ * x * r) = (r⁻¹ * x * r) * i := by
  have hj : r⁻¹ * (r⁻¹ * i * r) * r = i := by
    rw [show r⁻¹ * (r⁻¹ * i * r) * r = (r * r)⁻¹ * i * (r * r) by group, hr]
    group
  calc i * (r⁻¹ * x * r) = (r⁻¹ * (r⁻¹ * i * r) * r) * (r⁻¹ * x * r) := by rw [hj]
    _ = r⁻¹ * ((r⁻¹ * i * r) * x) * r := by group
    _ = r⁻¹ * (x * (r⁻¹ * i * r)) * r := by rw [hx]
    _ = (r⁻¹ * x * r) * (r⁻¹ * (r⁻¹ * i * r) * r) := by group
    _ = (r⁻¹ * x * r) * i := by rw [hj]

theorem E_r1_inf_F (hS : Setting h L η t Q T) :
    (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom ⊓
      miyamotoFG h L η t Q = ⊥ := by
  set r := miyamotoR1G h L η with hr
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨e, he, rfl⟩, hxF⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxF ⊢
  rw [← hS.F_inf_centralizer_I2]
  refine mem_inf.2 ⟨hxF, mem_centralizer_iff.2 fun i hi => ?_⟩
  exact commute_conj_of_mul_self hS.R1G_mul_self
    (mem_centralizer_iff.1 (hS.E_le_centralizer_S he) _ (hS.R1G_conj_mem_I2r1 hi))

theorem eq_one_of_mem_rootC_of_commute_rootA (hS : Setting h L η t Q T) {c : G}
    (hc : c ∈ miyamotoPull h L η (miyamotoRootC h))
    (hu : ∀ u ∈ miyamotoPull h L η (miyamotoRootA h), u * c = c * u) : c = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hc
  obtain ⟨c₀, hc₀⟩ := hg
  have key : c₀ = 0 := by
    refine eq_zero_of_forall_commute_rootA h fun a => ?_
    have haS : miyamotoXGL h a 0 0 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootA_le_SU ⟨a, rfl⟩
    have h1 := hu _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨_, haS⟩)).2 ⟨a, rfl⟩)
    have h2 : ⟨_, haS⟩ * g = g * ⟨_, haS⟩ := by
      apply η.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, L.coe_mul, L.coe_mul]
      exact h1
    have h3 := congrArg Subtype.val h2
    simp only [coe_mul] at h3
    rw [← hc₀]
    exact h3
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [hc₀, key, miyamotoXGL_zero, OneMemClass.coe_one]
  rw [hg1, map_one, OneMemClass.coe_one]

theorem F_inf_centralizer_rootA (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ⊓ centralizer (miyamotoPull h L η (miyamotoRootA h) : Set G) =
      miyamotoEG h L η Q := by
  have hUR : miyamotoPull h L η (miyamotoRootA h) ≤ miyamotoRG h L η t Q :=
    hS.rootA_le_W.trans inf_le_left
  refine le_antisymm (fun x hx => ?_) (le_inf hS.E_le_F fun e he => mem_centralizer_iff.2
    fun u hu => (mem_centralizer_iff.1 (hS.RG_le_centralizer_E (hUR hu)) e he).symm)
  obtain ⟨hxF, hxU⟩ := mem_inf.1 hx
  obtain ⟨e, he, y, hy, rfl⟩ := hS.exists_mul_of_mem_F hxF
  obtain ⟨hyF1, hyJ⟩ := mem_inf.1 hy
  have hyU : y ∈ centralizer (miyamotoPull h L η (miyamotoRootA h) : Set G) := by
    have heU : e ∈ centralizer (miyamotoPull h L η (miyamotoRootA h) : Set G) :=
      mem_centralizer_iff.2 fun u hu =>
        (mem_centralizer_iff.1 (hS.RG_le_centralizer_E (hUR hu)) e he).symm
    have := mul_mem (inv_mem heU) hxU
    rwa [inv_mul_cancel_left] at this
  have hJ : miyamotoPull h L η (miyamotoI1r2 h) ≤ miyamotoIG h L η := hS.tori_le_IG.2.1
  have hc : y⁻¹ * t * y * t ∈ miyamotoPull h L η (miyamotoRootC h) := by
    rw [← hS.A1G_inf_centralizer_I1r2]
    exact mem_inf.2 ⟨hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hyF1),
      hS.crossed_mem_centralizer hJ hyJ⟩
  have hcU : ∀ u ∈ miyamotoPull h L η (miyamotoRootA h),
      u * (y⁻¹ * t * y * t) = (y⁻¹ * t * y * t) * u := by
    intro u hu
    have hut : u * t = t * u := mem_centralizer_singleton_iff.1 (hS.PG_le_C (hS.rootA_le_PG hu))
    have huy : u * y = y * u := mem_centralizer_iff.1 hyU u hu
    have huy' : u * y⁻¹ = y⁻¹ * u := by
      calc u * y⁻¹ = y⁻¹ * (y * u) * y⁻¹ := by group
        _ = y⁻¹ * (u * y) * y⁻¹ := by rw [huy]
        _ = y⁻¹ * u := by group
    calc u * (y⁻¹ * t * y * t) = (u * y⁻¹) * t * y * t := by group
      _ = y⁻¹ * (u * t) * y * t := by rw [huy']; group
      _ = y⁻¹ * t * (u * y) * t := by rw [hut]; group
      _ = y⁻¹ * t * y * (u * t) := by rw [huy]; group
      _ = (y⁻¹ * t * y * t) * u := by rw [hut]; group
  have h1 := hS.eq_one_of_mem_rootC_of_commute_rootA hc hcU
  have hyA := (hS.crossed_eq_one_iff_F1 hyF1).1 h1
  have hyC : y ∈ miyamotoPull h L η (miyamotoRootC h) := by
    rw [← hS.A1G_inf_centralizer_I1r2]
    exact mem_inf.2 ⟨hyA, hyJ⟩
  have hy1 := hS.eq_one_of_mem_rootC_of_commute_rootA hyC fun u hu =>
    mem_centralizer_iff.1 hyU u hu
  rw [hy1, mul_one]
  exact he

theorem F2_inf_F1 (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ⊓ miyamotoF1G h L η t = miyamotoFG h L η t Q := by
  refine le_antisymm (fun x hx => ?_) (le_inf (hS.F2_eq ▸ le_sup_left) hS.F_le_F1)
  obtain ⟨hxF2, hxF1⟩ := mem_inf.1 hx
  rw [hS.F2_eq] at hxF2
  obtain ⟨φ, hφ, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer'
    (inf_le_left.trans hS.RG_le_normalizer_F) hxF2
  have hwF1 : w ∈ miyamotoF1G h L η t := by
    have := mul_mem (inv_mem (hS.F_le_F1 hφ)) hxF1
    rwa [inv_mul_cancel_left] at this
  have hw1 : w = 1 := by
    have : w ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
      mem_inf.2 ⟨hwF1, hw.2⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  rw [hw1, mul_one]
  exact hφ

theorem centerIn_F2 (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoF2G h L η t Q) = miyamotoEG h L η Q := by
  have hEF2 : miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q := by
    rw [hS.F2_eq]
    exact hS.E_le_F.trans le_sup_left
  refine le_antisymm (fun z hz => ?_) fun e he => mem_inf.2 ⟨hEF2 he,
    mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 (hS.RG_le_centralizer_E hy.2) e he).symm⟩
  obtain ⟨hzF2, hzC⟩ := mem_inf.1 hz
  have hFF2 : miyamotoFG h L η t Q ≤ miyamotoF2G h L η t Q := by
    rw [hS.F2_eq]
    exact le_sup_left
  have hzF1 : z ∈ miyamotoF1G h L η t := by
    rw [← hS.RG_inf_centralizer_F]
    exact mem_inf.2 ⟨hzF2.2, centralizer_le (SetLike.coe_subset_coe.2 hFF2) hzC⟩
  have hzF : z ∈ miyamotoFG h L η t Q := by
    rw [← hS.F2_inf_F1]
    exact mem_inf.2 ⟨hzF2, hzF1⟩
  rw [← hS.F_inf_centralizer_rootA]
  exact mem_inf.2 ⟨hzF, centralizer_le (SetLike.coe_subset_coe.2
    (hS.rootA_le_W.trans hS.W_le_F2)) hzC⟩

theorem F2_inf_C (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ⊓ centralizer ({t} : Set G) = miyamotoA2G h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_inf hS.A2_le_D2
    ((hS.A2G_le_PG.trans le_sup_right).trans hS.P1_le_miyamotoRG))
    (hS.A2G_le_PG.trans hS.PG_le_C))
  obtain ⟨⟨hxD, hxR⟩, hxC⟩ := hx
  have hxB : x ∈ miyamotoB2 h L η t := by
    rw [← hS.D2_inf_C]
    exact mem_inf.2 ⟨hxD, hxC⟩
  have hxP : x ∈ miyamotoPG h L η := by
    rw [← hS.RG_inf_C]
    exact mem_inf.2 ⟨hxR, hxC⟩
  rw [← hS.B2_inf_L]
  exact mem_inf.2 ⟨hxB, miyamotoPull_le h L η _ hxP⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
