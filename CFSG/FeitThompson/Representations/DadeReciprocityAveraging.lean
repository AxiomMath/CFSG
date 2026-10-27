module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
public import CFSG.FeitThompson.Definitions.DadeAveragingMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise CoprimeComponent ComplexConjugate

variable {G : Type*} [Group G]

def dadeCosetUnion (A : Set G) (H : G → Subgroup G) : Set G := ⋃ a ∈ A, dadeCoset H a

theorem mem_dadeCosetUnion_iff {A : Set G} {H : G → Subgroup G} {y : G} :
    y ∈ dadeCosetUnion A H ↔ ∃ a ∈ A, y ∈ dadeCoset H a := by simp [dadeCosetUnion]

theorem mem_dadeCosetUnion_of_mem_dadeCoset {A : Set G} {H : G → Subgroup G} {a y : G}
    (ha : a ∈ A) (hy : y ∈ dadeCoset H a) : y ∈ dadeCosetUnion A H :=
  mem_dadeCosetUnion_iff.2 ⟨a, ha, hy⟩

theorem subset_dadeCosetUnion (A : Set G) (H : G → Subgroup G) : A ⊆ dadeCosetUnion A H :=
  fun _ ha => mem_dadeCosetUnion_of_mem_dadeCoset ha (self_mem_dadeCoset H _)

theorem dadeCosetUnion_subset_totalDadeSupport (A : Set G) (H : G → Subgroup G) :
    dadeCosetUnion A H ⊆ totalDadeSupport A H := fun _ hy => by
  obtain ⟨a, ha, hya⟩ := mem_dadeCosetUnion_iff.1 hy
  exact dadeSupport_subset_totalDadeSupport ha (dadeCoset_subset_dadeSupport H a hya)

theorem totalDadeSupport_eq_conjugatesOfSet_dadeCosetUnion (A : Set G) (H : G → Subgroup G) :
    totalDadeSupport A H = Group.conjugatesOfSet (dadeCosetUnion A H) :=
  totalDadeSupport_eq_conjugatesOfSet A H

@[simp]
theorem dadeCosetUnion_empty (H : G → Subgroup G) : dadeCosetUnion (∅ : Set G) H = ∅ := by
  simp [dadeCosetUnion]

open Classical in
private noncomputable def dadeWeight (A : Set G) (H : G → Subgroup G) (f : G → ℂ) (y : G) : ℂ :=
  if y ∈ dadeCosetUnion A H then (Nat.card ↥(H (dadeRep A H y)) : ℂ)⁻¹ * f (dadeRep A H y) else 0

open Classical in
private noncomputable def dadeTerm (A : Set G) (H : G → Subgroup G) (f χ : G → ℂ) (a y : G) : ℂ :=
  if a ∈ A ∧ y ∈ dadeCoset H a then (Nat.card ↥(H a) : ℂ)⁻¹ * f a * conj (χ y) else 0

variable {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {f χ : G → ℂ} {a b x : G}

private theorem dadeWeight_eq_zero (h : x ∉ dadeCosetUnion A H) : dadeWeight A H f x = 0 := by
  classical
  rw [dadeWeight, if_neg h]

private theorem sum_dadeTerm_right [Fintype G] (A : Set G) (H : G → Subgroup G) (f χ : G → ℂ)
    (a : G) : ∑ y : G, dadeTerm A H f χ a y = A.indicator f a * conj (dadeAverage A H χ a) := by
  classical
  by_cases ha : a ∈ A
  · rw [Set.indicator_of_mem ha, dadeAverage_apply_of_mem' ha]
    have hre : ∑ y : G, dadeTerm A H f χ a y
        = ∑ v : G, (if v ∈ H a then (Nat.card ↥(H a) : ℂ)⁻¹ * f a * conj (χ (v * a)) else 0) := by
      refine (Fintype.sum_equiv (Equiv.mulRight a) _ _ fun v => ?_).symm
      have he : (Equiv.mulRight a) v = v * a := rfl
      rw [he, dadeTerm]
      by_cases hv : v ∈ H a
      · rw [if_pos hv, if_pos (⟨ha, mul_mem_dadeCoset hv⟩ : a ∈ A ∧ v * a ∈ dadeCoset H a)]
      · rw [if_neg hv, if_neg (show ¬(a ∈ A ∧ v * a ∈ dadeCoset H a) from
          fun hc => hv (by simpa using mem_dadeCoset_iff.1 hc.2))]
    rw [hre, map_mul, map_inv₀, Complex.conj_natCast, map_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ H a
    · rw [if_pos hv, if_pos hv]; ring
    · rw [if_neg hv, if_neg hv]; simp
  · rw [Set.indicator_of_notMem ha, zero_mul, Finset.sum_eq_zero]
    intro y _
    rw [dadeTerm, if_neg (fun hc => ha hc.1)]

variable [Finite G]

private theorem dadeWeight_of_mem_dadeSupport (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b)
    (ha : a ∈ A) {y : G} (hy : y ∈ dadeCosetUnion A H) (hya : y ∈ dadeSupport H a) :
    dadeWeight A H f y = (Nat.card ↥(H a) : ℂ)⁻¹ * f a := by
  classical
  rw [dadeWeight, if_pos hy]
  have hyD : y ∈ totalDadeSupport A H := dadeCosetUnion_subset_totalDadeSupport A H hy
  obtain ⟨l, hl, hlab⟩ := hD.exists_conj_of_dadeSupport_inter_nonempty ha (dadeRep_mem hyD)
    ⟨y, hya, mem_dadeSupport_dadeRep hyD⟩
  rw [← hlab, hf ha hl, hD.conj_smul_H ha hl, IsDadeData.card_conj_smul_H (H := H) (a := a) l]

namespace IsDadeData

theorem eq_of_mem_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) (hb : b ∈ A) {y : G}
    (hya : y ∈ dadeCoset H a) (hyb : y ∈ dadeCoset H b) : a = b := by
  rw [← hD.piComponent_of_mem_dadeCoset ha hya, ← hD.piComponent_of_mem_dadeCoset hb hyb]

theorem mem_centralizer_of_conj_mem (hD : IsDadeData L A H) (ha : a ∈ A) {k : G}
    (hk : k * a * k⁻¹ ∈ A) :
    ∃ l ∈ L, l⁻¹ * k ∈ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨l, hl, hlab⟩ := hD.fusion ha hk (_root_.isConj_iff.2 ⟨k, rfl⟩)
  refine ⟨l, hl, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have key : (l⁻¹ * k) * a * (l⁻¹ * k)⁻¹ = a := by
    rw [show (l⁻¹ * k) * a * (l⁻¹ * k)⁻¹ = l⁻¹ * (k * a * k⁻¹) * l by group, ← hlab]
    group
  calc (l⁻¹ * k) * a = ((l⁻¹ * k) * a * (l⁻¹ * k)⁻¹) * (l⁻¹ * k) := by group
    _ = a * (l⁻¹ * k) := by rw [key]

theorem card_setOf_conj_mem (hD : IsDadeData L A H) (ha : a ∈ A) :
    Nat.card {k : G // k * a * k⁻¹ ∈ A} = Nat.card ↥L * Nat.card ↥(H a) := by
  have hcomm : ∀ u ∈ H a, u * a * u⁻¹ = a := by
    intro u hu
    have h := (hD.le_centralizer ha hu) a rfl
    calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [← h]
      _ = a := by group
  have hmaps : ∀ p : ↥L × ↥(H a), ((p.1 : G) * (p.2 : G)) * a * ((p.1 : G) * (p.2 : G))⁻¹ ∈ A := by
    intro p
    rw [show ((p.1 : G) * (p.2 : G)) * a * ((p.1 : G) * (p.2 : G))⁻¹
      = (p.1 : G) * ((p.2 : G) * a * (p.2 : G)⁻¹) * (p.1 : G)⁻¹ by group, hcomm _ p.2.2]
    exact hD.conj_mem ha p.1.2
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective
    (fun p : ↥L × ↥(H a) => (⟨(p.1 : G) * (p.2 : G), hmaps p⟩ : {k : G // k * a * k⁻¹ ∈ A}))
    ⟨?_, ?_⟩).symm
  · rintro ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ ⟨⟨l', hl'⟩, ⟨u', hu'⟩⟩ heq
    have h1 : l * u = l' * u' := by simpa using heq
    have key : l'⁻¹ * l = u' * u⁻¹ := by
      calc l'⁻¹ * l = l'⁻¹ * (l * u) * u⁻¹ := by group
        _ = l'⁻¹ * (l' * u') * u⁻¹ := by rw [h1]
        _ = u' * u⁻¹ := by group
    have hmem : l'⁻¹ * l ∈ H a ⊓ L := Subgroup.mem_inf.2
      ⟨key ▸ mul_mem hu' (inv_mem hu), mul_mem (inv_mem hl') hl⟩
    rw [hD.inf_eq_bot_left ha] at hmem
    have hll : l = l' := by
      have h0 : l'⁻¹ * l = 1 := by simpa using hmem
      rw [inv_mul_eq_one] at h0
      exact h0.symm
    subst hll
    have huu : u = u' := by simpa using h1
    subst huu
    rfl
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl, hc⟩ := hD.mem_centralizer_of_conj_mem ha hk
    have hprod : (l⁻¹ * k : G) ∈ (H a : Set G) *
        (↑(L ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) := by
      rw [hD.mul_eq ha]; exact hc
    obtain ⟨u, hu, m, hm, hum⟩ := hprod
    replace hu : u ∈ H a := hu
    replace hm : m ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := hm
    replace hum : u * m = l⁻¹ * k := hum
    have hminv : m⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := inv_mem hm.2
    refine ⟨(⟨l * m, mul_mem hl hm.1⟩, ⟨m⁻¹ * u * m, by simpa using hD.conj_mem_H ha hminv hu⟩), ?_⟩
    refine Subtype.ext ?_
    change (l * m) * (m⁻¹ * u * m) = k
    calc (l * m) * (m⁻¹ * u * m) = l * (u * m) := by group
      _ = l * (l⁻¹ * k) := by rw [hum]
      _ = k := by group

theorem conj_mul_mem_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) {u : G} (hu : u ∈ H a)
    {h : G} (hA : h * a * h⁻¹ ∈ A) :
    h * (u * a) * h⁻¹ ∈ dadeCoset H (h * a * h⁻¹) := by
  obtain ⟨l, hl, hlab⟩ := hD.fusion ha hA (_root_.isConj_iff.2 ⟨h, rfl⟩)
  have hc : l⁻¹ * h ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have key : (l⁻¹ * h) * a * (l⁻¹ * h)⁻¹ = a := by
      rw [show (l⁻¹ * h) * a * (l⁻¹ * h)⁻¹ = l⁻¹ * (h * a * h⁻¹) * l by group, ← hlab]
      group
    calc (l⁻¹ * h) * a = ((l⁻¹ * h) * a * (l⁻¹ * h)⁻¹) * (l⁻¹ * h) := by group
      _ = a * (l⁻¹ * h) := by rw [key]
  set c := l⁻¹ * h with hcdef
  have hcomm : Commute c a := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hmem : c * (u * a) * c⁻¹ ∈ dadeCoset H a := by
    have h1 : c * (u * a) * c⁻¹ = (c * u * c⁻¹) * a := by
      calc c * (u * a) * c⁻¹ = c * u * (a * c⁻¹) := by group
        _ = c * u * (c⁻¹ * a) := by rw [← hcomm.inv_left.eq]
        _ = c * u * c⁻¹ * a := by group
    rw [h1]
    exact mul_mem_dadeCoset (hD.conj_mem_H ha hc hu)
  have hlift : h * (u * a) * h⁻¹ = l * (c * (u * a) * c⁻¹) * l⁻¹ := by rw [hcdef]; group
  rw [← hlab, hD.dadeCoset_conj ha hl, hlift]
  exact ⟨_, hmem, rfl⟩

theorem conj_mem_dadeCosetUnion_iff (hD : IsDadeData L A H) (ha : a ∈ A) {y : G}
    (hy : y ∈ dadeCoset H a) (j : G) :
    j * y * j⁻¹ ∈ dadeCosetUnion A H ↔ j * a * j⁻¹ ∈ A := by
  constructor
  · rintro hmem
    obtain ⟨b, hb, hyb⟩ := mem_dadeCosetUnion_iff.1 hmem
    have h1 : piComponent (dadePrimes L A) (j * y * j⁻¹) = b :=
      hD.piComponent_of_mem_dadeCoset hb hyb
    rw [piComponent_conj, hD.piComponent_of_mem_dadeCoset ha hy] at h1
    exact h1 ▸ hb
  · intro hA
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ H a, u * a = y := ⟨y * a⁻¹, mem_dadeCoset_iff.1 hy, by group⟩
    exact mem_dadeCosetUnion_of_mem_dadeCoset hA (hD.conj_mul_mem_dadeCoset ha hu hA)

theorem card_setOf_conj_mem_dadeCosetUnion (hD : IsDadeData L A H) (ha : a ∈ A) {x : G}
    (hx : x ∈ dadeSupport H a) :
    Nat.card {j : G // j * x * j⁻¹ ∈ dadeCosetUnion A H} = Nat.card ↥L * Nat.card ↥(H a) := by
  obtain ⟨y, hy, hconj⟩ := mem_dadeSupport_iff.1 hx
  obtain ⟨c, hc⟩ := _root_.isConj_iff.1 hconj
  rw [← hD.card_setOf_conj_mem ha]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight c) fun j => ?_)
  have hφ : (Equiv.mulRight c) j = j * c := rfl
  rw [hφ, show j * x * j⁻¹ = (j * c) * y * (j * c)⁻¹ by rw [← hc]; group]
  exact hD.conj_mem_dadeCosetUnion_iff ha hy (j * c)

end IsDadeData

section DoubleCount
variable [Fintype G]

private theorem sum_dadeTerm_left (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (y : G) :
    ∑ a : G, dadeTerm A H f χ a y = dadeWeight A H f y * conj (χ y) := by
  classical
  by_cases hy : y ∈ dadeCosetUnion A H
  · obtain ⟨c, hc, hyc⟩ := mem_dadeCosetUnion_iff.1 hy
    rw [Finset.sum_eq_single c, dadeTerm, if_pos ⟨hc, hyc⟩,
      dadeWeight_of_mem_dadeSupport hD hf hc hy (dadeCoset_subset_dadeSupport H c hyc)]
    · intro b _ hbc
      rw [dadeTerm, if_neg (fun hcc => hbc (hD.eq_of_mem_dadeCoset hcc.1 hc hcc.2 hyc))]
    · intro h; exact absurd (Finset.mem_univ c) h
  · rw [dadeWeight_eq_zero hy, zero_mul, Finset.sum_eq_zero]
    intro c _
    rw [dadeTerm]
    by_cases hcc : c ∈ A ∧ y ∈ dadeCoset H c
    · exact absurd (mem_dadeCosetUnion_of_mem_dadeCoset hcc.1 hcc.2) hy
    · rw [if_neg hcc]

private theorem sum_dadeWeight_conj (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (x : G) :
    ∑ j : G, dadeWeight A H f (j * x * j⁻¹)
      = (Nat.card ↥L : ℂ) * dadeSupportExtension A H f x := by
  classical
  by_cases hx : x ∈ totalDadeSupport A H
  · set a := dadeRep A H x with hadef
    have ha : a ∈ A := dadeRep_mem hx
    have hxa : x ∈ dadeSupport H a := mem_dadeSupport_dadeRep hx
    have hterm : ∀ j : G, dadeWeight A H f (j * x * j⁻¹)
        = if j * x * j⁻¹ ∈ dadeCosetUnion A H then (Nat.card ↥(H a) : ℂ)⁻¹ * f a else 0 := by
      intro j
      by_cases hj : j * x * j⁻¹ ∈ dadeCosetUnion A H
      · rw [if_pos hj]
        refine dadeWeight_of_mem_dadeSupport hD hf ha hj ?_
        have h2 := conj_mem_dadeSupport hxa j⁻¹
        rwa [show j⁻¹⁻¹ * x * j⁻¹ = j * x * j⁻¹ by group] at h2
      · rw [if_neg hj, dadeWeight_eq_zero hj]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : (Finset.card (Finset.filter (fun j : G => j * x * j⁻¹ ∈ dadeCosetUnion A H)
        Finset.univ) : ℂ) = (Nat.card ↥L : ℂ) * (Nat.card ↥(H a) : ℂ) := by
      rw [← Nat.cast_mul, ← hD.card_setOf_conj_mem_dadeCosetUnion ha hxa,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard, dadeSupportExtension_apply_of_mem_dadeSupport hD hf ha hxa]
    have hne : (Nat.card ↥(H a) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    field_simp
  · have hzero : ∀ j : G, dadeWeight A H f (j * x * j⁻¹) = 0 := by
      intro j
      refine dadeWeight_eq_zero fun hj => hx ?_
      have h2 := conj_mem_totalDadeSupport (dadeCosetUnion_subset_totalDadeSupport A H hj) j
      rwa [show j⁻¹ * (j * x * j⁻¹) * j = x by group] at h2
    rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const_zero,
      dadeSupportExtension_eq_zero_of_notMem hx, mul_zero]

private theorem sum_dadeWeight_mul_conj (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (hχ : χ ∈ classFun G) :
    ∑ y : G, dadeWeight A H f y * conj (χ y)
      = (Nat.card ↥L : ℂ) * cfInner (dadeSupportExtension A H f) χ := by
  classical
  have hGne : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hrow : ∀ j : G, ∑ x : G, dadeWeight A H f (j * x * j⁻¹) * conj (χ x)
      = ∑ y : G, dadeWeight A H f y * conj (χ y) := by
    intro j
    refine Fintype.sum_equiv ((Equiv.mulLeft j).trans (Equiv.mulRight j⁻¹)) _ _ fun x => ?_
    have he : ((Equiv.mulLeft j).trans (Equiv.mulRight j⁻¹)) x = j * x * j⁻¹ := rfl
    rw [he, classFun.apply_conj hχ x j]
  have key : ∑ j : G, ∑ x : G, dadeWeight A H f (j * x * j⁻¹) * conj (χ x)
      = (Nat.card G : ℂ) * ∑ y : G, dadeWeight A H f y * conj (χ y) := by
    rw [Finset.sum_congr rfl (fun j _ => hrow j), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [Finset.sum_comm] at key
  have key2 : ∑ x : G, ∑ j : G, dadeWeight A H f (j * x * j⁻¹) * conj (χ x)
      = (Nat.card ↥L : ℂ) * ∑ x : G, dadeSupportExtension A H f x * conj (χ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, sum_dadeWeight_conj hD hf x, mul_assoc]
  rw [key2] at key
  rw [cfInner_def, mul_left_comm, ← mul_right_inj' hGne, ← key, ← mul_assoc,
    mul_inv_cancel₀ hGne, one_mul]

private theorem card_mul_cfInner_dadeSupportExtension (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (hχ : χ ∈ classFun G) :
    (Nat.card ↥L : ℂ) * cfInner (dadeSupportExtension A H f) χ
      = ∑ a : G, A.indicator f a * conj (dadeAverage A H χ a) := by
  rw [← sum_dadeWeight_mul_conj hD hf hχ,
    Finset.sum_congr rfl (fun y _ => (sum_dadeTerm_left hD hf y).symm), Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => sum_dadeTerm_right A H f χ a

end DoubleCount

omit [Finite G] in
theorem sum_extendByZero_mul_conj [Fintype G] (L : Subgroup G) [Fintype ↥L] (F : ↥L → ℂ)
    (g : G → ℂ) :
    ∑ x : G, extendByZero L F x * conj (g x) = ∑ y : ↥L, F y * conj (g (y : G)) := by
  classical
  have h1 : ∑ y : ↥L, F y * conj (g (y : G))
      = ∑ y : ↥L, extendByZero L F (y : G) * conj (g (y : G)) :=
    Finset.sum_congr rfl fun y _ => by rw [extendByZero_apply_coe]
  have h2 : ∑ y : ↥L, extendByZero L F (y : G) * conj (g (y : G))
      = ∑ x ∈ Finset.filter (fun x : G => x ∈ L) Finset.univ,
        extendByZero L F x * conj (g x) :=
    (Finset.sum_subtype _ (by simp) (fun x => extendByZero L F x * conj (g x))).symm
  rw [h1, h2]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => ?_).symm
  have hm : x ∉ L := fun h => hx (Finset.mem_filter.2 ⟨Finset.mem_univ x, h⟩)
  rw [extendByZero_of_notMem L F hm, zero_mul]

omit [Finite G] in
theorem indicator_extendByZero_of_mem_dadeDomain {F : ↥L → ℂ} (hF : F ∈ dadeDomain L A) :
    A.indicator (extendByZero L F) = extendByZero L F := by
  funext x
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxL : x ∈ L
    · rw [extendByZero_of_mem _ hxL, dadeDomain.apply_eq_zero hF hx]
    · rw [extendByZero_of_notMem L F hxL]

theorem cfInner_dadeMap_eq_cfInner_dadeAverage (hD : IsDadeData L A H) [Fintype G] [Fintype ↥L]
    (F : dadeDomain L A) {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) χ
      = cfInner ((F : ↥L → ℂ)) (fun y : ↥L => dadeAverage A H χ (y : G)) := by
  have hLne : (Nat.card ↥L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hf := dadeDomain.extendByZero_conj hD F.2
  have key := card_mul_cfInner_dadeSupportExtension hD hf hχ
  rw [Finset.sum_congr rfl (fun a _ => by
      rw [indicator_extendByZero_of_mem_dadeDomain F.2] :
      ∀ a ∈ (Finset.univ : Finset G),
        A.indicator (extendByZero L (F : ↥L → ℂ)) a * conj (dadeAverage A H χ a)
          = extendByZero L (F : ↥L → ℂ) a * conj (dadeAverage A H χ a)),
    sum_extendByZero_mul_conj L (F : ↥L → ℂ) (dadeAverage A H χ)] at key
  rw [dadeMap_apply_coe, ← mul_right_inj' hLne, key, cfInner_def, ← mul_assoc,
    mul_inv_cancel₀ hLne, one_mul]

end CFSG.FeitThompson
