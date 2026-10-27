module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

open CFSG.Open Subgroup
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A] {V K : Subgroup A} {c : A}

theorem inv_eq_self_of_mem (hV : IsElemAbelian 2 V) {x : A} (hx : x ∈ V) : x⁻¹ = x := by
  have h := hV.2 x hx
  rw [pow_two] at h
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem comm_of_mem (hV : IsElemAbelian 2 V) {x y : A} (hx : x ∈ V) (hy : y ∈ V) :
    x * y = y * x :=
  CFSG.Quasithin.B2F.isElemAbelian_comm hV hx hy

theorem conj_eq_of_comm {g x : A} (h : x * g = g * x) : g * x * g⁻¹ = x := by
  rw [← h, mul_inv_cancel_right]

theorem comm_of_conj_eq {g x : A} (h : g * x * g⁻¹ = x) : x * g = g * x := by
  calc x * g = (g * x * g⁻¹) * g := by rw [h]
    _ = g * x := by group

theorem le_normalizer_fixed (hKV : K ≤ normalizer (V : Set A))
    (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ centralizer (V : Set A)) :
    K ≤ normalizer ((V ⊓ centralizer ({c} : Set A) : Subgroup A) : Set A) := by
  refine le_normalizer_of_conj fun k hk u hu => ?_
  have hw : k * u * k⁻¹ ∈ V := (mem_normalizer_iff.mp (hKV hk) u).mp hu.1
  refine ⟨hw, mem_centralizer_singleton_iff.mpr ?_⟩
  have hcu : c * u * c⁻¹ = u := conj_eq_of_comm (mem_centralizer_singleton_iff.mp hu.2)
  have hz := hcK k hk
  have hzw : (k * u * k⁻¹) * (c * k * c⁻¹ * k⁻¹) = (c * k * c⁻¹ * k⁻¹) * (k * u * k⁻¹) :=
    mem_centralizer_iff.mp hz _ hw
  have h1 : c * (k * u * k⁻¹) * c⁻¹ = k * u * k⁻¹ := by
    calc c * (k * u * k⁻¹) * c⁻¹
        = (c * k * c⁻¹ * k⁻¹) * (k * (c * u * c⁻¹) * k⁻¹) * (c * k * c⁻¹ * k⁻¹)⁻¹ := by group
      _ = (c * k * c⁻¹ * k⁻¹) * (k * u * k⁻¹) * (c * k * c⁻¹ * k⁻¹)⁻¹ := by rw [hcu]
      _ = (k * u * k⁻¹) * (c * k * c⁻¹ * k⁻¹) * (c * k * c⁻¹ * k⁻¹)⁻¹ := by rw [hzw]
      _ = k * u * k⁻¹ := by group
  exact comm_of_conj_eq h1

theorem commutator_mem_fixed (hV : IsElemAbelian 2 V) (hcV : c ∈ normalizer (V : Set A))
    (hc2 : c * c ∈ centralizer (V : Set A)) {v : A} (hv : v ∈ V) :
    c * v * c⁻¹ * v⁻¹ ∈ V ⊓ centralizer ({c} : Set A) := by
  have hu : c * v * c⁻¹ ∈ V := (mem_normalizer_iff.mp hcV v).mp hv
  refine ⟨V.mul_mem hu (V.inv_mem hv), mem_centralizer_singleton_iff.mpr ?_⟩
  have hccv : (c * c) * v * (c * c)⁻¹ = v :=
    conj_eq_of_comm (mem_centralizer_iff.mp hc2 v hv)
  have hui : (c * v * c⁻¹)⁻¹ = c * v * c⁻¹ := inv_eq_self_of_mem hV hu
  have hvi : v⁻¹ = v := inv_eq_self_of_mem hV hv
  have h1 : c * (c * v * c⁻¹ * v⁻¹) * c⁻¹ = c * v * c⁻¹ * v⁻¹ := by
    calc c * (c * v * c⁻¹ * v⁻¹) * c⁻¹ = ((c * c) * v * (c * c)⁻¹) * (c * v * c⁻¹)⁻¹ := by
          group
      _ = v * (c * v * c⁻¹) := by rw [hccv, hui]
      _ = (c * v * c⁻¹) * v := comm_of_mem hV hv hu
      _ = c * v * c⁻¹ * v⁻¹ := by rw [hvi]
  exact comm_of_conj_eq h1

section Abelian

variable (hV : IsElemAbelian 2 V) (hKV : K ≤ normalizer (V : Set A))
  (hcV : c ∈ normalizer (V : Set A))
  (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ centralizer (V : Set A))
  (hc2 : c * c ∈ centralizer (V : Set A))
  (hKU : K ≤ centralizer ((V ⊓ centralizer ({c} : Set A) : Subgroup A) : Set A))

include hV hKV hcV hcK hc2 hKU in
theorem commutator_mem_fixed_of_le {k v : A} (hk : k ∈ K) (hv : v ∈ V) :
    k * v * k⁻¹ * v⁻¹ ∈ V ⊓ centralizer ({c} : Set A) := by
  have hkv : k * v * k⁻¹ ∈ V := (mem_normalizer_iff.mp (hKV hk) v).mp hv
  have hd : k * v * k⁻¹ * v⁻¹ ∈ V := V.mul_mem hkv (V.inv_mem hv)
  refine ⟨hd, mem_centralizer_singleton_iff.mpr ?_⟩
  have hw := commutator_mem_fixed hV hcV hc2 hv
  have hkw : k * (c * v * c⁻¹ * v⁻¹) * k⁻¹ = c * v * c⁻¹ * v⁻¹ :=
    conj_eq_of_comm (mem_centralizer_iff.mp (hKU hk) _ hw)
  have hz := hcK k hk
  have hwv : (c * v * c⁻¹ * v⁻¹) * v ∈ V := V.mul_mem hw.1 hv
  have hkwv : k * ((c * v * c⁻¹ * v⁻¹) * v) * k⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hKV hk) _).mp hwv
  have hzc : (k * ((c * v * c⁻¹ * v⁻¹) * v) * k⁻¹) * (c * k * c⁻¹ * k⁻¹) =
      (c * k * c⁻¹ * k⁻¹) * (k * ((c * v * c⁻¹ * v⁻¹) * v) * k⁻¹) :=
    mem_centralizer_iff.mp hz _ hkwv
  have hcomm : (c * v * c⁻¹ * v⁻¹) * (k * v * k⁻¹ * v⁻¹) =
      (k * v * k⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹) := comm_of_mem hV hw.1 hd
  have h1 : c * (k * v * k⁻¹ * v⁻¹) * c⁻¹ = k * v * k⁻¹ * v⁻¹ := by
    calc c * (k * v * k⁻¹ * v⁻¹) * c⁻¹
        = (c * k * c⁻¹ * k⁻¹) * (k * ((c * v * c⁻¹ * v⁻¹) * v) * k⁻¹) *
            (c * k * c⁻¹ * k⁻¹)⁻¹ * ((c * v * c⁻¹ * v⁻¹) * v)⁻¹ := by group
      _ = (k * ((c * v * c⁻¹ * v⁻¹) * v) * k⁻¹) * (c * k * c⁻¹ * k⁻¹) *
            (c * k * c⁻¹ * k⁻¹)⁻¹ * ((c * v * c⁻¹ * v⁻¹) * v)⁻¹ := by rw [hzc]
      _ = (k * (c * v * c⁻¹ * v⁻¹) * k⁻¹) * (k * v * k⁻¹ * v⁻¹) *
            (c * v * c⁻¹ * v⁻¹)⁻¹ := by group
      _ = (c * v * c⁻¹ * v⁻¹) * (k * v * k⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹)⁻¹ := by rw [hkw]
      _ = (k * v * k⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹)⁻¹ := by
          rw [hcomm]
      _ = k * v * k⁻¹ * v⁻¹ := by group
  exact comm_of_conj_eq h1

include hV hKV hcV hcK hc2 hKU in
theorem commutator_mem_centralizer_of_le {k h : A} (hk : k ∈ K) (hh : h ∈ K) :
    k * h * k⁻¹ * h⁻¹ ∈ centralizer (V : Set A) := by
  have key : ∀ v ∈ V, (k * h) * v * (k * h)⁻¹ = (h * k) * v * (h * k)⁻¹ := by
    intro v hv
    have hdk := commutator_mem_fixed_of_le hV hKV hcV hcK hc2 hKU hk hv
    have hdh := commutator_mem_fixed_of_le hV hKV hcV hcK hc2 hKU hh hv
    have hk' : k * (h * v * h⁻¹ * v⁻¹) * k⁻¹ = h * v * h⁻¹ * v⁻¹ :=
      conj_eq_of_comm (mem_centralizer_iff.mp (hKU hk) _ hdh)
    have hh' : h * (k * v * k⁻¹ * v⁻¹) * h⁻¹ = k * v * k⁻¹ * v⁻¹ :=
      conj_eq_of_comm (mem_centralizer_iff.mp (hKU hh) _ hdk)
    have hcomm : (h * v * h⁻¹ * v⁻¹) * (k * v * k⁻¹ * v⁻¹) =
        (k * v * k⁻¹ * v⁻¹) * (h * v * h⁻¹ * v⁻¹) := comm_of_mem hV hdh.1 hdk.1
    calc (k * h) * v * (k * h)⁻¹
        = (k * (h * v * h⁻¹ * v⁻¹) * k⁻¹) * (k * v * k⁻¹ * v⁻¹) * v := by group
      _ = (h * v * h⁻¹ * v⁻¹) * (k * v * k⁻¹ * v⁻¹) * v := by rw [hk']
      _ = (k * v * k⁻¹ * v⁻¹) * (h * v * h⁻¹ * v⁻¹) * v := by rw [hcomm]
      _ = (h * (k * v * k⁻¹ * v⁻¹) * h⁻¹) * (h * v * h⁻¹ * v⁻¹) * v := by rw [hh']
      _ = (h * k) * v * (h * k)⁻¹ := by group
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : (h * k)⁻¹ * v * (h * k) ∈ V := by
    have := (mem_normalizer_iff.mp (hKV (K.mul_mem hh hk)) ((h * k)⁻¹ * v * (h * k))).mpr
    apply this
    simpa [mul_assoc] using hv
  have h1 := key _ hv'
  have h2 : (k * h * k⁻¹ * h⁻¹) * v * (k * h * k⁻¹ * h⁻¹)⁻¹ = v := by
    calc (k * h * k⁻¹ * h⁻¹) * v * (k * h * k⁻¹ * h⁻¹)⁻¹
        = (k * h) * ((h * k)⁻¹ * v * (h * k)) * (k * h)⁻¹ := by group
      _ = (h * k) * ((h * k)⁻¹ * v * (h * k)) * (h * k)⁻¹ := by rw [h1]
      _ = v := by group
  exact comm_of_conj_eq h2

end Abelian

theorem not_le_centralizer_fixed (hV : IsElemAbelian 2 V) (hKV : K ≤ normalizer (V : Set A))
    (hcV : c ∈ normalizer (V : Set A))
    (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ centralizer (V : Set A))
    (hc2 : c * c ∈ centralizer (V : Set A)) (hKp : ⁅K, K⁆ = K)
    (hKC : ¬ K ≤ centralizer (V : Set A)) :
    ¬ K ≤ centralizer ((V ⊓ centralizer ({c} : Set A) : Subgroup A) : Set A) := by
  intro hKU
  apply hKC
  rw [← hKp, commutator_le]
  intro k hk h hh
  rw [commutatorElement_def]
  exact commutator_mem_centralizer_of_le hV hKV hcV hcK hc2 hKU hk hh

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64
