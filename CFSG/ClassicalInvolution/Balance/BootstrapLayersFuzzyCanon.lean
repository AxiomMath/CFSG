module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyRigid

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf perfectResidualOf_normalizer_contains
  finite_perfectResidualOf_isPerfect)
open scoped commutatorElement

section Subnormal

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {H N : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hN : g ∈ Subgroup.normalizer (N : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ N : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hN ⊢
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hH hN

theorem isSubnormal_sup_of_normal {J K N : Subgroup G} (hJ : IsSubnormal J K) (hNK : N ≤ K)
    (hN : K ≤ Subgroup.normalizer (N : Set G)) : IsSubnormal (J ⊔ N) K := by
  induction hJ with
  | refl =>
    rw [sup_eq_left.mpr hNK]
    exact IsSubnormal.refl _
  | @step H M K' hHM hHnorm hMK ih =>
    have hMKle : M ≤ K' := isSubnormal_le hMK
    refine IsSubnormal.step (sup_le_sup_right hHM N) ?_ (ih hNK hN)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le_sup_right hHM N)]
    refine sup_le (fun m hm => mem_normalizer_sup ?_ (hN (hMKle hm))) fun n hn => ?_
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnorm hm
    · have hHK : H ≤ K' := hHM.trans hMKle
      have key : ∀ n ∈ N, ∀ x ∈ H ⊔ N, n * x * n⁻¹ ∈ H ⊔ N := by
        intro n hn x hx
        have hx' : x ∈ (↑(H ⊔ N) : Set G) := hx
        rw [Subgroup.coe_mul_of_left_le_normalizer_right H N (hHK.trans hN)] at hx'
        obtain ⟨h, hh, n', hn', rfl⟩ := Set.mem_mul.mp hx'
        have hw : n * h * n⁻¹ * h⁻¹ ∈ N := by
          have h1 : h * n⁻¹ * h⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hN (hHK hh)) n⁻¹).mp (N.inv_mem hn)
          have e : n * h * n⁻¹ * h⁻¹ = n * (h * n⁻¹ * h⁻¹) := by group
          rw [e]
          exact N.mul_mem hn h1
        have e : n * (h * n') * n⁻¹ = (n * h * n⁻¹ * h⁻¹) * h * (n * n' * n⁻¹) := by group
        rw [e]
        exact mul_mem (mul_mem (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left hh))
          (Subgroup.mem_sup_right (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => key n hn y hy, fun hy => ?_⟩
      have := key n⁻¹ (N.inv_mem hn) _ hy
      simpa [mul_assoc] using this

end Subnormal

section Canon

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def canonMember (J : Subgroup G) (z : G) : Subgroup G :=
  perfectResidualOf (J ⊔ involutionOddCore z)

omit [Finite G] in
theorem canonMember_le_sup (J : Subgroup G) (z : G) :
    canonMember J z ≤ J ⊔ involutionOddCore z :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_canonMember {J : Subgroup G} {z : G} (hJ : Group.IsPerfect ↥J) :
    J ≤ canonMember J z :=
  le_perfectResidualOf_of_perfect le_sup_left hJ

omit [Finite G] in
theorem canonMember_sup {J : Subgroup G} {z : G} (hJ : Group.IsPerfect ↥J) :
    canonMember J z ⊔ involutionOddCore z = J ⊔ involutionOddCore z :=
  le_antisymm (sup_le (canonMember_le_sup J z) le_sup_right)
    (sup_le_sup_right (le_canonMember hJ) _)

omit [Finite G] in
theorem isCanonical_canonMember {J : Subgroup G} {z : G} (hJ : Group.IsPerfect ↥J) :
    IsCanonical (canonMember J z) z := by
  unfold IsCanonical
  rw [canonMember_sup hJ]
  rfl

theorem isClassicalMember_canonMember {J : Subgroup G} {z : G} (hJ : IsClassicalMember p f J z) :
    IsClassicalMember p f (canonMember J z) z where
  orderOf_eq_two := hJ.orderOf_eq_two
  mem := le_canonMember hJ.perfect hJ.mem
  perfect := finite_perfectResidualOf_isPerfect _
  subnormal := by
    unfold canonMember
    rw [involutionOddCore_eq_oddCoreIn]
    set X : Subgroup G := Subgroup.centralizer ({z} : Set G) with hX
    have hsup : IsSubnormal (J ⊔ oddCoreIn X) X :=
      isSubnormal_sup_of_normal hJ.subnormal (oddCoreIn_le X) (normalizer_oddCoreIn X)
    set H : Subgroup G := J ⊔ oddCoreIn X with hH
    have hIH : perfectResidualOf H ≤ H := Subgroup.map_subtype_le _
    have hnorm : ((perfectResidualOf H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).mpr
        (Subgroup.le_normalizer.trans (perfectResidualOf_normalizer_contains H))
    exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf hIH hnorm) hsup
  nonempty_equiv := by
    obtain ⟨e'⟩ := hJ.nonempty_equiv
    have hJX : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ.subnormal
    have hJC : J ≤ canonMember J z := le_canonMember hJ.perfect
    have hcC : canonMember J z ≤ Subgroup.centralizer ({z} : Set G) :=
      (canonMember_le_sup J z).trans (sup_le hJX (by
        rw [involutionOddCore_eq_oddCoreIn]
        exact oddCoreIn_le _))
    have hcov : ∀ x ∈ canonMember J z, ∃ s ∈ J, ∃ n ∈ oddCoreIn (canonMember J z), x = s * n := by
      intro x hx
      have hx' : x ∈ (↑(J ⊔ involutionOddCore z) : Set G) := canonMember_le_sup J z hx
      rw [involutionOddCore_eq_oddCoreIn] at hx'
      rw [Subgroup.coe_mul_of_left_le_normalizer_right J _
        (hJX.trans (normalizer_oddCoreIn _))] at hx'
      obtain ⟨j, hj, n, hn, rfl⟩ := Set.mem_mul.mp hx'
      refine ⟨j, hj, n, ?_, rfl⟩
      have hnc : n ∈ canonMember J z := by
        have e : n = j⁻¹ * (j * n) := by group
        rw [e]
        exact (canonMember J z).mul_mem ((canonMember J z).inv_mem (hJC hj)) hx
      refine le_oddCoreIn_of_normalizes (S := canonMember J z ⊓ oddCoreIn
        (Subgroup.centralizer ({z} : Set G))) inf_le_left ?_
        ((odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)) ⟨hnc, hn⟩
      intro y hy
      exact mem_normalizer_inf (Subgroup.le_normalizer hy)
        (normalizer_oddCoreIn _ (hcC hy))
    obtain ⟨φ⟩ := nonempty_quotEquiv_of_surjective hJC (toOddQuot_surjective hJC hcov)
    exact ⟨φ.symm.trans e'⟩

theorem mem_trivialOnQuot_canonMember {J : Subgroup G} {z a : G} (hJ : IsClassicalMember p f J z)
    (ha : a ∈ trivialOnQuot J) (haz : a * z = z * a) :
    a ∈ trivialOnQuot (canonMember J z) := by
  set X : Subgroup G := Subgroup.centralizer ({z} : Set G) with hX
  set N : Subgroup G := oddCoreIn X with hN
  have haX : a ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr haz
  have hJX : J ≤ X := isSubnormal_le hJ.subnormal
  have hnormJN : a ∈ Subgroup.normalizer ((J ⊔ N : Subgroup G) : Set G) :=
    mem_normalizer_sup ha.1 (normalizer_oddCoreIn X haX)
  have hC : canonMember J z = perfectResidualOf (J ⊔ N) := by
    unfold canonMember
    rw [involutionOddCore_eq_oddCoreIn]
  have hnormC : a ∈ Subgroup.normalizer ((canonMember J z : Subgroup G) : Set G) := by
    rw [hC]
    exact perfectResidualOf_normalizer_contains _ hnormJN
  refine ⟨hnormC, fun x hx => ?_⟩
  have hcX : canonMember J z ≤ X :=
    (canonMember_le_sup J z).trans
      (sup_le hJX (by rw [involutionOddCore_eq_oddCoreIn]; exact oddCoreIn_le _))
  have hx' : x ∈ (↑(J ⊔ N) : Set G) := by
    have := canonMember_le_sup J z hx
    rwa [involutionOddCore_eq_oddCoreIn] at this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J N (hJX.trans (normalizer_oddCoreIn X))] at hx'
  obtain ⟨j, hj, n, hn, rfl⟩ := Set.mem_mul.mp hx'
  have h1 : ⁅a, j⁆ ∈ N := oddCoreIn_le_of_isSubnormal hJ.subnormal (ha.2 j hj)
  have h2 : ⁅a, n⁆ ∈ N := by
    have : ⁅a, n⁆ = (a * n * a⁻¹) * n⁻¹ := rfl
    rw [this]
    exact N.mul_mem (conj_mem_oddCoreIn haX hn) (N.inv_mem hn)
  have h3 : j * ⁅a, n⁆ * j⁻¹ ∈ N := conj_mem_oddCoreIn (hJX hj) h2
  have e : ⁅a, j * n⁆ = ⁅a, j⁆ * (j * ⁅a, n⁆ * j⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hmemN : ⁅a, j * n⁆ ∈ N := by
    rw [e]
    exact N.mul_mem h1 h3
  have hmemC : ⁅a, j * n⁆ ∈ canonMember J z := by
    have : ⁅a, j * n⁆ = (a * (j * n) * a⁻¹) * (j * n)⁻¹ := rfl
    rw [this]
    exact (canonMember J z).mul_mem ((Subgroup.mem_normalizer_iff.mp hnormC _).mp hx)
      ((canonMember J z).inv_mem hx)
  refine le_oddCoreIn_of_normalizes (S := canonMember J z ⊓ N) inf_le_left ?_
    ((odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)) ⟨hmemC, hmemN⟩
  intro y hy
  exact mem_normalizer_inf (Subgroup.le_normalizer hy) (normalizer_oddCoreIn X (hcX hy))

theorem mem_trivialOnQuot_of_centralizes {J : Subgroup G} {a : G} (ha : ∀ j ∈ J, a * j = j * a) :
    a ∈ trivialOnQuot J := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : a * y * a⁻¹ = y := by rw [ha y hy]; group
      rw [this]
      exact hy
    · intro hy
      have h1 := ha _ hy
      have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
      have h2 : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
        calc a⁻¹ * (a * y * a⁻¹) * a = a⁻¹ * ((a * y * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * y * a⁻¹)) := by rw [← h1]
          _ = a * y * a⁻¹ := by group
      rw [this, h2]
      exact hy
  · rw [(commutatorElement_eq_one_iff_mul_comm).mpr (ha x hx)]
    exact one_mem _

theorem mem_trivialOnQuot_canonMember_of_centralizes {J : Subgroup G} {z a : G}
    (hJ : IsClassicalMember p f J z) (ha : ∀ j ∈ J, a * j = j * a) :
    a ∈ trivialOnQuot (canonMember J z) :=
  mem_trivialOnQuot_canonMember hJ (mem_trivialOnQuot_of_centralizes ha) (ha z hJ.mem)

end Canon

section Map

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem triangleAxis_map (g z₁ z₂ z₃ : G) :
    (triangleAxis z₁ z₂ z₃).map (MulAut.conj g).toMonoidHom =
      triangleAxis (g * z₁ * g⁻¹) (g * z₂ * g⁻¹) (g * z₃ * g⁻¹) := by
  unfold triangleAxis
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq]

theorem AxisTriangle.map {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) (g : G) :
    AxisTriangle p f (conjSub g J₁) (conjSub g J₂) (conjSub g J₃) (g * z₁ * g⁻¹) (g * z₂ * g⁻¹)
      (g * z₃ * g⁻¹) := by
  have hc : ∀ {x y : G}, x * y = y * x →
      (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) := by
    intro x y hxy
    calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
  exact ⟨hT.cls₁.conj g, hT.cls₂.conj g, hT.cls₃.conj g, hc hT.comm₁₂, hc hT.comm₁₃, hc hT.comm₂₃,
    trivialOnQuot_conjSub hT.tq₁₂ g, trivialOnQuot_conjSub hT.tq₁₃ g,
    trivialOnQuot_conjSub hT.tq₂₁ g, trivialOnQuot_conjSub hT.tq₂₃ g,
    trivialOnQuot_conjSub hT.tq₃₁ g, trivialOnQuot_conjSub hT.tq₃₂ g⟩

end Map

end CFSG.ClassicalInvolution.Balance.Bootstrap
