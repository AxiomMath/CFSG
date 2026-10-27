module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Crit
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Quad

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q : Subgroup (MulAut V)}

omit [Finite V] in
theorem Emb55Data.centralizes_of_y (d : Emb55Data V G T Y H Q) {y : MulAut V} (hy : y ∈ Y)
    (hy1 : y ≠ 1) {S : Subgroup (MulAut V)} (hSinv : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S)
    (hSy : ∀ x ∈ S, y * x = x * y) : ∀ h ∈ H, ∀ x ∈ S, h * x = x * h := by
  set N : Subgroup (MulAut V) := H ⊓ Subgroup.centralizer (S : Set (MulAut V)) with hN
  have hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh),
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h ∈ S := by simpa using hSinv h⁻¹ (H.inv_mem hh) x hx
    have := Subgroup.mem_centralizer_iff.mp hn.2 _ hx'
    calc x * (h * n * h⁻¹) = h * ((h⁻¹ * x * h) * n) * h⁻¹ := by group
      _ = h * (n * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
      _ = (h * n * h⁻¹) * x := by group
  have hyN : y ∈ N := ⟨d.yH hy, Subgroup.mem_centralizer_iff.mpr fun x hx => (hSy x hx).symm⟩
  have hYN : Y ≤ N := by
    rw [← d.sec.zpowers_eq hy hy1]
    exact Subgroup.zpowers_le.mpr hyN
  have hHN : H ≤ N := d.gen N inf_le_left hNnorm hYN
  intro h hh x hx
  exact (Subgroup.mem_centralizer_iff.mp (hHN hh).2 x hx).symm

structure Cfg55 (V : Type) [CommGroup V] (G T Y H Q D : Subgroup (MulAut V)) (y a : MulAut V) :
    Prop where
  data : Emb55Data V G T Y H Q
  hy : y ∈ Y
  hy1 : y ≠ 1
  hyQ : y ∉ Q
  DQ : D ≤ Q
  D3 : ∀ x ∈ D, x ^ 3 = 1
  Dinv : ∀ h ∈ H, ∀ x ∈ D, h * x * h⁻¹ ∈ D
  Dcl : ∀ x ∈ D, ∀ q ∈ Q, ⁅x, q⁆ ∈ D ∧ ∀ z ∈ D, ⁅x, q⁆ * z = z * ⁅x, q⁆
  aD : a ∈ D
  hya : y * a ≠ a * y
  d0H : ∀ h ∈ H, h * ⁅a, ⁅a, y⁆⁆ = ⁅a, ⁅a, y⁆⁆ * h
  d01 : ⁅a, ⁅a, y⁆⁆ ≠ 1

theorem Emb55Data.exists_cfg (d : Emb55Data V G T Y H Q) {y : MulAut V} (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hyQ : y ∉ Q) : ∃ D a, Cfg55 V G T Y H Q D y a := by
  obtain ⟨D, hDQ, hD3, hDinv, hDcl, hDfix⟩ := d.exists_crit hy hy1
  have h1 : ∃ a ∈ D, y * a ≠ a * y := by
    by_contra hcon
    push Not at hcon
    have hcent := d.centralizes_of_y hy hy1 hDinv (fun x hx => hcon x hx)
    have hH3 : IsPGroup 3 ↥H := hDfix fun h hh x hx => hcent h hh x hx
    have hHQ : H ≤ Q :=
      d.Qmax H le_rfl (fun h hh n hn => H.mul_mem (H.mul_mem hh hn) (H.inv_mem hh)) hH3
    exact hyQ (hHQ (d.yH hy))
  obtain ⟨a, haD, hya⟩ := h1
  have haQ : a ∈ Q := hDQ haD
  set c : MulAut V := ⁅a, y⁆ with hcdef
  have hcD : c ∈ D := by
    have h2 : y * a⁻¹ * y⁻¹ ∈ D := hDinv y (d.yH hy) a⁻¹ (D.inv_mem haD)
    have e : c = a * (y * a⁻¹ * y⁻¹) := by rw [hcdef, commutatorElement_def]; group
    rw [e]; exact D.mul_mem haD h2
  have hcQ : c ∈ Q := hDQ hcD
  have hd0 := hDcl a haD c hcQ
  have hZinv : ∀ h ∈ H, ∀ z ∈ D ⊓ Subgroup.centralizer (D : Set (MulAut V)),
      h * z * h⁻¹ ∈ D ⊓ Subgroup.centralizer (D : Set (MulAut V)) := by
    intro h hh z hz
    refine Subgroup.mem_inf.mpr ⟨hDinv h hh z (Subgroup.mem_inf.mp hz).1,
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h ∈ D := by simpa using hDinv h⁻¹ (H.inv_mem hh) x hx
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ hx'
    calc x * (h * z * h⁻¹) = h * ((h⁻¹ * x * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
      _ = (h * z * h⁻¹) * x := by group
  have hZy : ∀ z ∈ D ⊓ Subgroup.centralizer (D : Set (MulAut V)), y * z = z * y := by
    intro z hz
    have hzD : z ∈ D := (Subgroup.mem_inf.mp hz).1
    have hzC := (Subgroup.mem_inf.mp hz).2
    have hzQ : z ∈ Q := hDQ hzD
    have hcz : ⁅z, y⁆ ∈ D := by
      have h2 : y * z⁻¹ * y⁻¹ ∈ D := hDinv y (d.yH hy) z⁻¹ (D.inv_mem hzD)
      have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]; exact D.mul_mem hzD h2
    have hcomm : z * ⁅z, y⁆ = ⁅z, y⁆ * z := (Subgroup.mem_centralizer_iff.mp hzC _ hcz).symm
    have := d.quad hy hy1 hyQ hzQ hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  have hZH := d.centralizes_of_y hy hy1 hZinv hZy
  refine ⟨D, a, ⟨d, hy, hy1, hyQ, hDQ, hD3, hDinv, hDcl, haD, hya, ?_, ?_⟩⟩
  · intro h hh
    exact hZH h hh _ (Subgroup.mem_inf.mpr ⟨hd0.1,
      Subgroup.mem_centralizer_iff.mpr fun z hz => (hd0.2 z hz).symm⟩)
  · intro h1
    have hac : a * c = c * a := commutatorElement_eq_one_iff_mul_comm.mp h1
    have := d.quad hy hy1 hyQ haQ hac
    exact hya (commutatorElement_eq_one_iff_mul_comm.mp this).symm

end CFSG.CGT.PushingUpLit.CGT6E
