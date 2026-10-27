module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

section Lift

variable {H : Type} [Group H] [Finite H]

theorem exists_mem_centralizer_of_quot_comm {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {x h : H}
    (hx : x * x = 1)
    (hc : (QuotientGroup.mk h : H ⧸ N) * QuotientGroup.mk x = QuotientGroup.mk x * QuotientGroup.mk h) :
    ∃ v ∈ N, v⁻¹ * h ∈ Subgroup.centralizer ({x} : Set H) := by
  set a := h * x * h⁻¹ with ha
  have ha2 : a * a = 1 := by
    calc a * a = h * (x * x) * h⁻¹ := by rw [ha]; group
      _ = 1 := by rw [hx]; group
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hax : a⁻¹ * x ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk (a⁻¹ * x) : H ⧸ N) =
        (QuotientGroup.mk h * QuotientGroup.mk x * (QuotientGroup.mk h)⁻¹)⁻¹ * QuotientGroup.mk x := by
      rw [ha]
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, hc]
    group
  obtain ⟨v, hv, hva⟩ := exists_conj_zpowers_of_mul_mem_odd hN ha2 hx hax
  have hvN : v ∈ N := by
    have hxN : a * x ∈ N := by rwa [hai] at hax
    exact (Subgroup.zpowers_le.mpr hxN) hv
  refine ⟨v, hvN, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : h * x * h⁻¹ = v * x * v⁻¹ := by rw [← ha]; exact hva
  calc v⁻¹ * h * x = v⁻¹ * (h * x * h⁻¹) * h := by group
    _ = v⁻¹ * (v * x * v⁻¹) * h := by rw [e1]
    _ = x * (v⁻¹ * h) := by group

theorem mem_sup_of_quot_gen (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N)) {x y : H}
    (hx : x * x = 1) (hy : y * y = 1)
    (hgen : Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ N)} : Set (H ⧸ N)) ⊔
      Subgroup.centralizer ({(QuotientGroup.mk y : H ⧸ N)} : Set (H ⧸ N)) = ⊤) (h : H) :
    h ∈ Subgroup.centralizer ({x} : Set H) ⊔ Subgroup.centralizer ({y} : Set H) ⊔ N := by
  set Λ : Subgroup H := Subgroup.centralizer ({x} : Set H) ⊔ Subgroup.centralizer ({y} : Set H) ⊔ N
    with hΛ
  have hNΛ : N ≤ Λ := le_sup_right
  have key : ∀ {z : H}, (hz : z * z = 1) → ∀ q : H ⧸ N,
      q ∈ Subgroup.centralizer ({(QuotientGroup.mk z : H ⧸ N)} : Set (H ⧸ N)) →
      Subgroup.centralizer ({z} : Set H) ≤ Λ → q ∈ Λ.map (QuotientGroup.mk' N) := by
    intro z hz q hq hzΛ
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hvN, hvC⟩ := exists_mem_centralizer_of_quot_comm hN hz
      (Subgroup.mem_centralizer_singleton_iff.mp hq)
    refine ⟨v⁻¹ * h', hzΛ hvC, ?_⟩
    show (QuotientGroup.mk (v⁻¹ * h') : H ⧸ N) = QuotientGroup.mk h'
    rw [QuotientGroup.eq]
    have : (v⁻¹ * h')⁻¹ * h' = h'⁻¹ * v * h'⁻¹⁻¹ := by group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance v hvN h'⁻¹
  have hle : (⊤ : Subgroup (H ⧸ N)) ≤ Λ.map (QuotientGroup.mk' N) := by
    rw [← hgen]
    refine sup_le (fun q hq => key hx q hq ?_) (fun q hq => key hy q hq ?_)
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hmem : (QuotientGroup.mk h : H ⧸ N) ∈ Λ.map (QuotientGroup.mk' N) := hle (Subgroup.mem_top _)
  obtain ⟨l, hl, hlh⟩ := hmem
  have hlh' : (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk h := hlh
  rw [QuotientGroup.eq] at hlh'
  have : h = l * (l⁻¹ * h) := by group
  rw [this]
  exact Λ.mul_mem hl (hNΛ hlh')

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
