module

public import CFSG.ClassicalInvolution.Asc77.AscT7TFAut
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem mem_normalizer_of_centralizes {K : Subgroup G} {r : G} (hr : ∀ x ∈ K, r * x = x * r) :
    r ∈ Subgroup.normalizer (K : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr (T7F2.conjSub_eq_of_centralizes fun x hx => (hr x hx).symm)

theorem conj_mem_of_mem_normalizer {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) : a * k * a⁻¹ ∈ K := by
  have h := conj_mem_conjSub (n := a) hk
  rwa [mem_normalizer_iff_conjSub_eq.mp ha] at h

theorem inv_conj_mem_of_mem_normalizer {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) : a⁻¹ * k * a ∈ K := by
  have h := conj_mem_conjSub (n := a⁻¹) hk
  have ha' : a⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ ha
  rw [mem_normalizer_iff_conjSub_eq.mp ha'] at h
  simpa using h

theorem isFAut_mul_of_centralizes {K : Subgroup G} {a r : G} (hr : ∀ x ∈ K, r * x = x * r)
    (h : IsFAut K a) : IsFAut K (a * r) := by
  obtain ⟨haN, ha2, Q, R₀, hQ, hQq, hR₀, hcard⟩ := h
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_centralizes hr
  have hcen : K ⊓ Subgroup.centralizer ({a * r} : Set G) =
      K ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      have hrx := hr x hxK
      have h1 : (x * a) * r = (a * x) * r := by
        calc (x * a) * r = x * (a * r) := by group
          _ = (a * r) * x := hx
          _ = a * (r * x) := by group
          _ = a * (x * r) := by rw [hrx]
          _ = (a * x) * r := by group
      exact mul_right_cancel h1
    · rintro ⟨hxK, hx⟩
      refine ⟨hxK, ?_⟩
      have hrx := hr x hxK
      calc x * (a * r) = (x * a) * r := by group
        _ = (a * x) * r := by rw [hx]
        _ = a * (x * r) := by group
        _ = a * (r * x) := by rw [hrx]
        _ = (a * r) * x := by group
  refine ⟨Subgroup.mul_mem _ haN hrN, ?_, Q, R₀, hcen ▸ hQ, hQq, hR₀, hcard⟩
  have hr' : ∀ x ∈ K, (a⁻¹ * r * a) * x = x * (a⁻¹ * r * a) := by
    intro x hx
    have hx1 : a * x * a⁻¹ ∈ K := conj_mem_of_mem_normalizer haN hx
    have h1 := hr _ hx1
    calc (a⁻¹ * r * a) * x = a⁻¹ * (r * (a * x * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * x * a⁻¹) * r) * a := by rw [h1]
      _ = x * (a⁻¹ * r * a) := by group
  intro k hk
  have hsq : (a * r) * (a * r) = (a * a) * ((a⁻¹ * r * a) * r) := by group
  rw [hsq]
  calc (a * a) * ((a⁻¹ * r * a) * r) * k
      = (a * a) * ((a⁻¹ * r * a) * (r * k)) := by group
    _ = (a * a) * ((a⁻¹ * r * a) * (k * r)) := by rw [hr k hk]
    _ = (a * a) * (((a⁻¹ * r * a) * k) * r) := by group
    _ = (a * a) * ((k * (a⁻¹ * r * a)) * r) := by rw [hr' k hk]
    _ = ((a * a) * k) * ((a⁻¹ * r * a) * r) := by group
    _ = (k * (a * a)) * ((a⁻¹ * r * a) * r) := by rw [ha2 k hk]
    _ = k * ((a * a) * ((a⁻¹ * r * a) * r)) := by group

theorem isQuatSub_conjSub {Q : Subgroup G} (h : IsQuatSub Q) (g : G) :
    IsQuatSub (conjSub g Q) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  refine ⟨k, hk, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e

theorem conjSub_inf_centralizer_singleton (g a : G) (K : Subgroup G) :
    conjSub g (K ⊓ Subgroup.centralizer ({a} : Set G)) =
      conjSub g K ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hK, hc⟩
    refine ⟨hK, ?_⟩
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = (g * a * g⁻¹) * x := by group
  · rintro ⟨hK, hc⟩
    refine ⟨hK, ?_⟩
    have h1 : g * ((g⁻¹ * x * g) * a) * g⁻¹ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by
      calc g * ((g⁻¹ * x * g) * a) * g⁻¹ = x * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * x := hc
        _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)

variable [Finite G]

theorem isFAut_conjSub {K : Subgroup G} {a : G} (h : IsFAut K a) (g : G) :
    IsFAut (conjSub g K) (g * a * g⁻¹) := by
  obtain ⟨haN, ha2, Q, R₀, hQ, hQq, hR₀, hcard⟩ := h
  refine ⟨?_, ?_, conjSub g Q, conjSub g R₀, ?_, isQuatSub_conjSub hQq g, hR₀.conj g, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq]
    calc conjSub (g * a * g⁻¹) (conjSub g K) = conjSub (g * a) (conjSub g⁻¹ (conjSub g K)) := by
          rw [conjSub_mul]
      _ = conjSub (g * a) K := by rw [conjSub_inv_conjSub]
      _ = conjSub g (conjSub a K) := conjSub_mul g a K
      _ = conjSub g K := by rw [mem_normalizer_iff_conjSub_eq.mp haN]
  · intro k' hk'
    have hk : g⁻¹ * k' * g ∈ K := mem_conjSub_iff.mp hk'
    have h1 := ha2 _ hk
    calc (g * a * g⁻¹) * (g * a * g⁻¹) * k' = g * (a * a * (g⁻¹ * k' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k' * g) * (a * a)) * g⁻¹ := by rw [h1]
      _ = k' * ((g * a * g⁻¹) * (g * a * g⁻¹)) := by group
  · have := hQ.conj g
    rwa [conjSub_inf_centralizer_singleton] at this
  · rw [natCard_conjSub, natCard_conjSub]
    exact hcard

theorem exists_zpowers_eq {C : Subgroup G} (hC : IsCyclic ↥C) :
    ∃ x : G, Subgroup.zpowers x = C := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun y hy => ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  exact ⟨j, congrArg Subtype.val hj⟩

theorem not_isFAut_of_mem {R : Subgroup G} {z y : G} (hR : IsQuatSub R)
    (hz : IsUniqueInvolution R z) (hy : y ∈ R) : ¬ IsFAut R y := by
  intro hF
  have hR2 : IsPGroup 2 ↥R := AscL62.isPGroup_of_isQuatSub hR
  have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) := hR2.to_le (Subgroup.zpowers_le.mpr hy)
  obtain ⟨x, hxR, hcard, -, hne1, hne2⟩ := T7T.exists_cyclic_of_isFAut hR hz hF hy2
  have hCR : Subgroup.zpowers x ≤ R := Subgroup.zpowers_le.mpr hxR
  by_cases hyC : y ∈ Subgroup.zpowers x
  · apply hne1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyC
    have : Commute (x ^ j) x := (Commute.refl x).zpow_left j
    rw [this.eq]
    group
  · exact hne2 (AscL62.conj_eq_inv_of_not_mem hR hz hCR inferInstance hcard hy hyC
      (Subgroup.mem_zpowers x))

theorem inf_centralizer_le_zpowers {R : Subgroup G} {z : G} (hR : IsQuatSub R)
    (hz : IsUniqueInvolution R z) : R ⊓ Subgroup.centralizer (R : Set G) ≤ Subgroup.zpowers z := by
  intro c hc
  obtain ⟨hcR, hcc⟩ := Subgroup.mem_inf.mp hc
  have hcomm : ∀ h ∈ R, h * c = c * h := Subgroup.mem_centralizer_iff.mp hcc
  obtain ⟨C, hCR, hCc, hcard, -⟩ := hR.exists_cyclic_max
  obtain ⟨x, hxC⟩ := exists_zpowers_eq hCc
  have hxm : x ∈ C := hxC ▸ Subgroup.mem_zpowers x
  have h4 : 4 ≤ Nat.card C := AscL62.four_le_natCard_of_index_two hR hcard
  have hx2 : x * x ≠ 1 := by
    intro h
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    have hcx : Nat.card C = orderOf x := by rw [← hxC, Nat.card_zpowers]
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨b, hbR, hbC⟩ : ∃ b ∈ R, b ∉ C := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show R ≤ C from hcon)
    omega
  by_cases hcC : c ∈ C
  · have h1 : b * c * b⁻¹ = c⁻¹ :=
      AscL62.conj_eq_inv_of_not_mem hR hz hCR hCc hcard hbR hbC hcC
    have h2 : b * c * b⁻¹ = c := by
      calc b * c * b⁻¹ = (c * b) * b⁻¹ := by rw [← hcomm b hbR]
        _ = c := by group
    have hcc2 : c * c = 1 := by
      have : c⁻¹ = c := h1.symm.trans h2
      calc c * c = c * c⁻¹ := by rw [this]
        _ = 1 := by group
    rcases hz.unique c hcR hcc2 with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  · exfalso
    have h1 : c * x * c⁻¹ = x⁻¹ :=
      AscL62.conj_eq_inv_of_not_mem hR hz hCR hCc hcard hcR hcC hxm
    have h2 : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [← hcomm x (hCR hxm)]
        _ = x := by group
    have : x⁻¹ = x := h1.symm.trans h2
    exact hx2 (by
      calc x * x = x * x⁻¹ := by rw [this]
        _ = 1 := by group)

end CFSG.ClassicalInvolution.Asc77.T7U
