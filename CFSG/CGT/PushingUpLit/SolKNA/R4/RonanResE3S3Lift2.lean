module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

theorem sup_centralizer_of_quot {Q : Type} [Group Q] {z s : Q}
    (hnt : ∀ y : Q, ∀ m ∈ Subgroup.center Q, y * z * y⁻¹ = z * m → m = 1)
    (hconj : ∃ g : Q, s = g * z * g⁻¹)
    (h : Subgroup.centralizer ({(QuotientGroup.mk z : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) ⊔
      Subgroup.centralizer ({(QuotientGroup.mk s : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) = ⊤) :
    Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q) = ⊤ := by
  obtain ⟨g, hg⟩ := hconj
  have hZG : ∀ c ∈ Subgroup.center Q,
      c ∈ Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q) := by
    intro c hc
    apply Subgroup.mem_sup_left
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_center_iff.mp hc) z).symm
  have h1 : ∀ x : Q, (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) ∈
      Subgroup.centralizer ({(QuotientGroup.mk z : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) →
      x ∈ Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hw : (QuotientGroup.mk (x * z * x⁻¹) : Q ⧸ Subgroup.center Q) =
        QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx,
        mul_inv_cancel_right]
    have hm : z⁻¹ * (x * z * x⁻¹) ∈ Subgroup.center Q := by
      have h3 := (Subgroup.center Q).inv_mem (QuotientGroup.eq.mp hw)
      have h4 : ((x * z * x⁻¹)⁻¹ * z)⁻¹ = z⁻¹ * (x * z * x⁻¹) := by group
      rwa [h4] at h3
    have hm1 : z⁻¹ * (x * z * x⁻¹) = 1 := hnt x _ hm (by group)
    have hxz : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = z * (z⁻¹ * (x * z * x⁻¹)) := by group
        _ = z := by rw [hm1, mul_one]
    apply Subgroup.mem_sup_left
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hxz
  have h2 : ∀ x : Q, (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) ∈
      Subgroup.centralizer ({(QuotientGroup.mk s : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) →
      x ∈ Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hw : (QuotientGroup.mk (x * s * x⁻¹) : Q ⧸ Subgroup.center Q) =
        QuotientGroup.mk s := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx,
        mul_inv_cancel_right]
    have hm0 : s⁻¹ * (x * s * x⁻¹) ∈ Subgroup.center Q := by
      have h3 := (Subgroup.center Q).inv_mem (QuotientGroup.eq.mp hw)
      have h4 : ((x * s * x⁻¹)⁻¹ * s)⁻¹ = s⁻¹ * (x * s * x⁻¹) := by group
      rwa [h4] at h3
    obtain ⟨m, hmdef⟩ : ∃ m : Q, m = s⁻¹ * (x * s * x⁻¹) := ⟨_, rfl⟩
    have hm : m ∈ Subgroup.center Q := by
      rw [hmdef]
      exact hm0
    have hxs : x * s * x⁻¹ = s * m := by
      rw [hmdef]
      group
    have hmc : ∀ a : Q, a * m = m * a := Subgroup.mem_center_iff.mp hm
    have hkey : (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ = z * m := by
      have hxs' : x * (g * z * g⁻¹) * x⁻¹ = g * z * g⁻¹ * m := by
        rw [← hg]
        exact hxs
      calc (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹
            = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹ * m) * g := by rw [hxs']
        _ = z * (g⁻¹ * (m * g)) := by group
        _ = z * (g⁻¹ * (g * m)) := by rw [← hmc g]
        _ = z * m := by group
    have hm1 : m = 1 := hnt (g⁻¹ * x * g) m hm hkey
    rw [hm1, mul_one] at hxs
    apply Subgroup.mem_sup_right
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hxs
  have hle1 : Subgroup.centralizer ({(QuotientGroup.mk z : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) ≤
      (Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q)).map
        (QuotientGroup.mk' (Subgroup.center Q)) := by
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact Subgroup.mem_map.mpr ⟨x, h1 x ha, rfl⟩
  have hle2 : Subgroup.centralizer ({(QuotientGroup.mk s : Q ⧸ Subgroup.center Q)} :
        Set (Q ⧸ Subgroup.center Q)) ≤
      (Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q)).map
        (QuotientGroup.mk' (Subgroup.center Q)) := by
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact Subgroup.mem_map.mpr ⟨x, h2 x ha, rfl⟩
  have htop : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) ≤
      (Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q)).map
        (QuotientGroup.mk' (Subgroup.center Q)) := by
    have := sup_le hle1 hle2
    rwa [h] at this
  rw [eq_top_iff]
  intro x _
  obtain ⟨y₀, hy₀, hy₀x⟩ :=
    Subgroup.mem_map.mp (htop (Subgroup.mem_top (QuotientGroup.mk x)))
  rw [QuotientGroup.mk'_apply] at hy₀x
  have hc : y₀⁻¹ * x ∈ Subgroup.center Q := QuotientGroup.eq.mp hy₀x
  have hmem := Subgroup.mul_mem _ hy₀ (hZG _ hc)
  rwa [mul_inv_cancel_left] at hmem

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
