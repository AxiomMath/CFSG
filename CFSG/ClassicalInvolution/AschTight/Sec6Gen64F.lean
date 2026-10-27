module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64E
public import CFSG.ClassicalInvolution.Asc77.AscSix69

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem conjSub_centralizer_singleton (g x : G) :
    conjSub g (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group

omit [Finite G] in
theorem isSylow2In_conjSub {V P : Subgroup G} (h : IsSylow2In V P) (g : G) :
    IsSylow2In (conjSub g V) (conjSub g P) := IsSylow2In.conj h g

omit [Finite G] in
theorem OddCompl.conj {H U N₀ : Subgroup G} (hN : OddCompl H U N₀) (g : G) :
    OddCompl (conjSub g H) (conjSub g U) (conjSub g N₀) where
  le := conjSub_mono hN.le
  odd := by rw [AscL62.natCard_conjSub]; exact hN.odd
  dec := by
    intro h hh
    rw [mem_conjSub_iff] at hh
    obtain ⟨n, hn, w, hw, he⟩ := hN.dec _ hh
    refine ⟨g * n * g⁻¹, conj_mem_conjSub hn, g * w * g⁻¹, conj_mem_conjSub hw, ?_⟩
    calc h = g * (g⁻¹ * h * g) * g⁻¹ := by group
      _ = g * (n * w) * g⁻¹ := by rw [he]
      _ = g * n * g⁻¹ * (g * w * g⁻¹) := by group
  mem_of_odd := by
    intro x hx hodd
    rw [mem_conjSub_iff] at hx ⊢
    refine hN.mem_of_odd _ hx ?_
    have e : orderOf (g⁻¹ * x * g) = orderOf x := by
      have := (MulAut.conj g⁻¹).orderOf_eq x
      simpa [MulAut.conj_apply] using this
    rw [e]
    exact hodd

omit [Finite G] in
theorem mem_centralizer_mul {x a b : G} (ha : x ∈ Subgroup.centralizer ({a} : Set G))
    (hb : x ∈ Subgroup.centralizer ({b} : Set G)) :
    x ∈ Subgroup.centralizer ({a * b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb ⊢
  calc x * (a * b) = (x * a) * b := by group
    _ = (a * x) * b := by rw [ha]
    _ = a * (x * b) := by group
    _ = a * (b * x) := by rw [hb]
    _ = a * b * x := by group

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem zj_comm : z * j = j * z :=
  Subgroup.mem_centralizer_singleton_iff.mp (c.U_le_centralizer c.z_mem_U)

theorem zj_sq : (z * j) * (z * j) = 1 := by
  calc (z * j) * (z * j) = z * (j * z) * j := by group
    _ = z * (z * j) * j := by rw [c.zj_comm]
    _ = (z * z) * (j * j) := by group
    _ = 1 := by rw [c.hz.sq, c.hj.sq, one_mul]

omit [Finite G] in
theorem zj_ne_z : z * j ≠ z := fun h => c.hj.ne_one (by simpa using h)

omit [Finite G] in
theorem zj_ne_j : z * j ≠ j := fun h => c.hz.ne_one (by simpa using h)

theorem U_le_centralizer_zj : Subgroup.zpowers u ≤ Subgroup.centralizer ({z * j} : Set G) :=
  fun _ hx => mem_centralizer_mul (Subgroup.mem_centralizer_singleton_iff.mpr
    (AscL62.cyclic_comm inferInstance hx c.z_mem_U)) (c.U_le_centralizer hx)

theorem V_le_centralizer_zj : Subgroup.zpowers v ≤ Subgroup.centralizer ({z * j} : Set G) :=
  fun _ hx => mem_centralizer_mul (c.symm.U_le_centralizer hx) (c.V_le_centralizer_j hx)

variable {r : G}

omit [Finite G] in
theorem J'_mem : conjSub r J ∈ Ω := c.hΩ.conjInvariant r J c.hJ

theorem J'_inv (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    IsUniqueInvolution (conjSub r J) (z * j) := by
  have := c.hj.conj r
  rwa [c.conj_j_of_not_mem hr hru] at this

theorem J'_ne_K (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) : conjSub r J ≠ K := by
  intro h
  have hK : IsUniqueInvolution (conjSub r J) z := by rw [h]; exact c.hz
  exact c.zj_ne_z ((c.J'_inv hr hru).eq hK)

theorem J'_ne_J (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) : conjSub r J ≠ J := by
  intro h
  have hJ : IsUniqueInvolution (conjSub r J) j := by rw [h]; exact c.hj
  exact c.zj_ne_j ((c.J'_inv hr hru).eq hJ)

omit [Finite G] in
theorem conj_z (hr : r ∈ R) : r * z * r⁻¹ = z := by
  rw [c.z_comm (c.hR.1 hr)]
  group

omit [Finite G] in
theorem CJ'_eq_conj (hr : r ∈ R) : conjSub r J ⊓ Subgroup.centralizer ({z} : Set G) =
    conjSub r (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  rw [conjSub_inf, conjSub_centralizer_singleton, c.conj_z hr]

theorem CJ'_eq (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    conjSub r J ⊓ Subgroup.centralizer ({z} : Set G) =
      conjSub r J ⊓ Subgroup.centralizer ({j} : Set G) := by
  have hc : ∀ x ∈ conjSub r J, x * (z * j) = (z * j) * x := fun x hx =>
    ((c.J'_inv hr hru).commute_of_mem hx).symm
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hxz⟩
    refine ⟨hx, ?_⟩
    have h1 := hc x hx
    calc x * j = x * (z * (z * j)) := by rw [← mul_assoc z, c.hz.sq, one_mul]
      _ = (x * z) * (z * j) := by group
      _ = (z * x) * (z * j) := by rw [hxz]
      _ = z * (x * (z * j)) := by group
      _ = z * ((z * j) * x) := by rw [h1]
      _ = (z * z) * j * x := by group
      _ = j * x := by rw [c.hz.sq, one_mul]
  · rintro ⟨hx, hxj⟩
    refine ⟨hx, ?_⟩
    have h1 := hc x hx
    calc x * z = x * (z * j) * j := by rw [mul_assoc x, mul_assoc z, c.hj.sq, mul_one]
      _ = (z * j) * x * j := by rw [h1]
      _ = (z * j) * (x * j) := by group
      _ = (z * j) * (j * x) := by rw [hxj]
      _ = z * (j * j) * x := by group
      _ = z * x := by rw [c.hj.sq, mul_one]

theorem U_le_normalizer_J' (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    Subgroup.zpowers u ≤ Subgroup.normalizer ((conjSub r J : Subgroup G) : Set G) :=
  le_normalizer_of_le_centralizer c.hΩ c.J'_mem c.hK (c.J'_ne_K hr hru) (c.J'_inv hr hru) c.hUK
    c.U_isPGroup (by have := c.four_le_U; omega) c.U_le_centralizer_zj

theorem V_le_normalizer_J' (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    Subgroup.zpowers v ≤ Subgroup.normalizer ((conjSub r J : Subgroup G) : Set G) :=
  le_normalizer_of_le_centralizer c.hΩ c.J'_mem c.hJ (c.J'_ne_J hr hru) (c.J'_inv hr hru) c.hVJ
    c.symm.U_isPGroup (by have := c.symm.four_le_U; omega) c.V_le_centralizer_zj

theorem sylow_V' (hr : r ∈ R) : IsSylow2In (conjSub r (Subgroup.zpowers v))
    (conjSub r J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  rw [c.CJ'_eq_conj hr]
  exact IsSylow2In.conj c.sylow_V r

theorem CJ'_le_normalizer_K (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    conjSub r J ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  inf_centralizer_le_normalizer c.hΩ c.J'_mem c.hK (c.J'_ne_K hr hru) c.hz (c.sylow_V' hr)
    (AscL62.isCyclic_conjSub r inferInstance)
    (by rw [AscL62.natCard_conjSub]; exact c.symm.four_le_U) c.hUK c.U_isPGroup c.four_le_U
    (c.U_le_normalizer_J' hr hru) (fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (AscL62.cyclic_comm inferInstance hx c.z_mem_U))

theorem CJ'_le_normalizer_J (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    conjSub r J ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  rw [c.CJ'_eq hr hru]
  have hsyl : IsSylow2In (conjSub r (Subgroup.zpowers v))
      (conjSub r J ⊓ Subgroup.centralizer ({j} : Set G)) := c.CJ'_eq hr hru ▸ c.sylow_V' hr
  exact inf_centralizer_le_normalizer c.hΩ c.J'_mem c.hJ (c.J'_ne_J hr hru) c.hj hsyl
    (AscL62.isCyclic_conjSub r inferInstance)
    (by rw [AscL62.natCard_conjSub]; exact c.symm.four_le_U) c.hVJ c.symm.U_isPGroup
    c.symm.four_le_U (c.V_le_normalizer_J' hr hru) c.V_le_centralizer_j

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
