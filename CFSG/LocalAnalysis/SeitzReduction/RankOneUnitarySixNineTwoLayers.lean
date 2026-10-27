module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.RankOne

variable {G : Type*} [Group G]

theorem layers_comm_comm_mem {M N : Subgroup G} {a : G} (haa : a * a = 1)
    (haM : ∀ y ∈ M, a * y * a⁻¹ ∈ M) (hM2 : ∀ x ∈ M, x * x ∈ N) {z : G} (hz : z ∈ M) :
    (z * a * z⁻¹ * a⁻¹) * a * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹ ∈ N := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have e1 : a * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹ = z * a * z⁻¹ * a⁻¹ := by
    calc a * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹ = (a * a) * z * a⁻¹ * z⁻¹ * a⁻¹ := by group
      _ = z * a⁻¹ * z⁻¹ * a⁻¹ := by rw [haa, one_mul]
      _ = z * a * z⁻¹ * a⁻¹ := by rw [ha]
  have e2 : (z * a * z⁻¹ * a⁻¹) * a * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹ =
      (z * a * z⁻¹ * a⁻¹) * (a * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹) := by group
  rw [e2, e1]
  have hzM : z * a * z⁻¹ * a⁻¹ ∈ M := by
    simpa [mul_assoc] using mul_mem hz (haM _ (inv_mem hz))
  exact hM2 _ hzM

theorem layers_comm_mem {M : Subgroup G} {a : G} (haM : ∀ y ∈ M, a * y * a⁻¹ ∈ M) {x : G}
    (hx : x ∈ M) : x * a * x⁻¹ * a⁻¹ ∈ M := by
  simpa [mul_assoc] using mul_mem hx (haM _ (inv_mem hx))

theorem layers_comm_swap_mem {M N : Subgroup G} {t v : G} (htv : t * v = v * t)
    (htM : ∀ y ∈ M, t * y * t⁻¹ ∈ M) (hvM : ∀ y ∈ M, v * y * v⁻¹ ∈ M)
    (hMN : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) {z : G} (hz : z ∈ M) :
    ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹)⁻¹ *
      ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹) ∈ N := by
  have hb : t * (v * z * v⁻¹) * t⁻¹ = v * (t * z * t⁻¹) * v⁻¹ := by
    calc t * (v * z * v⁻¹) * t⁻¹ = (t * v) * z * (t * v)⁻¹ := by group
      _ = (v * t) * z * (v * t)⁻¹ := by rw [htv]
      _ = v * (t * z * t⁻¹) * v⁻¹ := by group
  have haM : t * z * t⁻¹ ∈ M := htM z hz
  have hbM : v * (t * z * t⁻¹) * v⁻¹ ∈ M := hvM _ haM
  have hcM : v * z * v⁻¹ ∈ M := hvM z hz
  have e : ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹)⁻¹ *
      ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹) =
      ((v * z * v⁻¹) * ((v * (t * z * t⁻¹) * v⁻¹)⁻¹ * (t * z * t⁻¹)) * (v * z * v⁻¹)⁻¹ *
        ((v * (t * z * t⁻¹) * v⁻¹)⁻¹ * (t * z * t⁻¹))⁻¹) *
      ((v * (t * z * t⁻¹) * v⁻¹)⁻¹ * (t * z * t⁻¹) * (v * (t * z * t⁻¹) * v⁻¹)⁻¹⁻¹ *
        (t * z * t⁻¹)⁻¹) := by
    calc ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹)⁻¹ *
          ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹) =
        (v * z * v⁻¹) * (v * (t * z * t⁻¹) * v⁻¹)⁻¹ * (t * z * t⁻¹) * (v * z * v⁻¹)⁻¹ *
          (t * (v * z * v⁻¹) * t⁻¹) * (t * z * t⁻¹)⁻¹ := by group
      _ = (v * z * v⁻¹) * (v * (t * z * t⁻¹) * v⁻¹)⁻¹ * (t * z * t⁻¹) * (v * z * v⁻¹)⁻¹ *
          (v * (t * z * t⁻¹) * v⁻¹) * (t * z * t⁻¹)⁻¹ := by rw [hb]
      _ = _ := by group
  rw [e]
  exact mul_mem (hMN _ hcM _ (mul_mem (inv_mem hbM) haM)) (hMN _ (inv_mem hbM) _ haM)

theorem exists_comm_mem_of_free_layers {M N H : Subgroup G} {t v : G} (hNH : N ≤ H) (hHM : H ≤ M)
    (hNc : ∀ n ∈ N, ∀ x ∈ M, n * x = x * n)
    (hMN : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hM2 : ∀ x ∈ M, x * x ∈ N)
    (htM : ∀ x ∈ M, t * x * t⁻¹ ∈ M) (hvM : ∀ x ∈ M, v * x * v⁻¹ ∈ M)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hvN : ∀ n ∈ N, v * n * v⁻¹ ∈ N) (htt : t * t = 1)
    (hvv : v * v = 1) (htv : t * v = v * t)
    (hker : ∀ x ∈ M, x * t * x⁻¹ * t⁻¹ ∈ N → x ∈ H)
    (hsurj : ∀ y ∈ H, ∃ z ∈ M, (z * t * z⁻¹ * t⁻¹)⁻¹ * y ∈ N)
    (hfreeH : ∀ y ∈ H, y * v * y⁻¹ * v⁻¹ ∈ N → ∃ w ∈ H, (w * v * w⁻¹ * v⁻¹)⁻¹ * y ∈ N)
    {x : G} (hx : x ∈ M) (hxv : x * v * x⁻¹ * v⁻¹ ∈ N) :
    ∃ w ∈ M, (w * v * w⁻¹ * v⁻¹)⁻¹ * x ∈ N := by
  have hcen : ∀ n ∈ N, ∀ y ∈ M, y * n * y⁻¹ = n := fun n hn y hy => by
    rw [← hNc n hn y hy, mul_inv_cancel_right]
  have hcM : x * t * x⁻¹ * t⁻¹ ∈ M := layers_comm_mem htM hx
  have hcH : x * t * x⁻¹ * t⁻¹ ∈ H := hker _ hcM (layers_comm_comm_mem htt htM hM2 hx)
  have hcv : (x * t * x⁻¹ * t⁻¹) * v * (x * t * x⁻¹ * t⁻¹)⁻¹ * v⁻¹ ∈ N := by
    have hn' : t * (x * v * x⁻¹ * v⁻¹) * t⁻¹ ∈ N := htN _ hxv
    have h1 : v⁻¹ * t * v = t := by rw [mul_assoc, htv, inv_mul_cancel_left]
    have h2 : v⁻¹ * t⁻¹ = t⁻¹ * v⁻¹ := by rw [← mul_inv_rev, htv, mul_inv_rev]
    have hvc : v * (x * t * x⁻¹ * t⁻¹) * v⁻¹ =
        (x * v * x⁻¹ * v⁻¹)⁻¹ * (x * t * x⁻¹ * t⁻¹) * (t * (x * v * x⁻¹ * v⁻¹) * t⁻¹) := by
      calc v * (x * t * x⁻¹ * t⁻¹) * v⁻¹ = v * x * (v⁻¹ * t * v) * x⁻¹ * (v⁻¹ * t⁻¹) := by
            rw [h1, h2]; group
        _ = _ := by group
    have e : (x * t * x⁻¹ * t⁻¹) * v * (x * t * x⁻¹ * t⁻¹)⁻¹ * v⁻¹ =
        (x * t * x⁻¹ * t⁻¹) * (t * (x * v * x⁻¹ * v⁻¹) * t⁻¹)⁻¹ * (x * t * x⁻¹ * t⁻¹)⁻¹ *
          (x * v * x⁻¹ * v⁻¹) := by
      calc (x * t * x⁻¹ * t⁻¹) * v * (x * t * x⁻¹ * t⁻¹)⁻¹ * v⁻¹ =
          (x * t * x⁻¹ * t⁻¹) * (v * (x * t * x⁻¹ * t⁻¹) * v⁻¹)⁻¹ := by group
        _ = _ := by rw [hvc]; group
    rw [e, hcen _ (inv_mem hn') _ hcM]
    exact mul_mem (inv_mem hn') hxv
  obtain ⟨w₁, hw₁H, hw₁⟩ := hfreeH _ hcH hcv
  obtain ⟨z, hzM, hz⟩ := hsurj w₁ hw₁H
  obtain ⟨m, hmN, rfl⟩ : ∃ m ∈ N, w₁ = (z * t * z⁻¹ * t⁻¹) * m :=
    ⟨_, hz, by group⟩
  have hτzM : z * t * z⁻¹ * t⁻¹ ∈ M := layers_comm_mem htM hzM
  have hνmN : m * v * m⁻¹ * v⁻¹ ∈ N := by
    simpa [mul_assoc] using mul_mem hmN (hvN _ (inv_mem hmN))
  have hνprod : (z * t * z⁻¹ * t⁻¹ * m) * v * (z * t * z⁻¹ * t⁻¹ * m)⁻¹ * v⁻¹ =
      (m * v * m⁻¹ * v⁻¹) * ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹) := by
    calc (z * t * z⁻¹ * t⁻¹ * m) * v * (z * t * z⁻¹ * t⁻¹ * m)⁻¹ * v⁻¹ =
        ((z * t * z⁻¹ * t⁻¹) * (m * v * m⁻¹ * v⁻¹) * (z * t * z⁻¹ * t⁻¹)⁻¹) *
          ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹) := by group
      _ = _ := by rw [hcen _ hνmN _ hτzM]
  have heM : z * v * z⁻¹ * v⁻¹ ∈ M := layers_comm_mem hvM hzM
  have he : ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹)⁻¹ *
      (x * t * x⁻¹ * t⁻¹) ∈ N := by
    have hsw := layers_comm_swap_mem htv htM hvM hMN hzM
    rw [hνprod] at hw₁
    have e : ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹)⁻¹ *
        (x * t * x⁻¹ * t⁻¹) =
        (((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹)⁻¹ *
          ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹))⁻¹ *
        (((m * v * m⁻¹ * v⁻¹) *
          ((z * t * z⁻¹ * t⁻¹) * v * (z * t * z⁻¹ * t⁻¹)⁻¹ * v⁻¹))⁻¹ * (x * t * x⁻¹ * t⁻¹)) *
        ((x * t * x⁻¹ * t⁻¹)⁻¹ * (m * v * m⁻¹ * v⁻¹) * (x * t * x⁻¹ * t⁻¹)⁻¹⁻¹) := by group
    rw [e, hcen _ hνmN _ (inv_mem hcM)]
    exact mul_mem (mul_mem (inv_mem hsw) hw₁) hνmN
  have hxeM : x * (z * v * z⁻¹ * v⁻¹)⁻¹ ∈ M := mul_mem hx (inv_mem heM)
  have hτeM : (z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹ ∈ M :=
    layers_comm_mem htM heM
  have hxeH : x * (z * v * z⁻¹ * v⁻¹)⁻¹ ∈ H := by
    refine hker _ hxeM ?_
    have e : (x * (z * v * z⁻¹ * v⁻¹)⁻¹) * t * (x * (z * v * z⁻¹ * v⁻¹)⁻¹)⁻¹ * t⁻¹ =
        ((x * (z * v * z⁻¹ * v⁻¹)⁻¹) *
          ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹)⁻¹ *
          (x * (z * v * z⁻¹ * v⁻¹)⁻¹)⁻¹ *
          ((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹)⁻¹⁻¹) *
        (((z * v * z⁻¹ * v⁻¹) * t * (z * v * z⁻¹ * v⁻¹)⁻¹ * t⁻¹)⁻¹ * (x * t * x⁻¹ * t⁻¹)) := by
      group
    rw [e]
    exact mul_mem (hMN _ hxeM _ (inv_mem hτeM)) he
  have hνe : (z * v * z⁻¹ * v⁻¹) * v * (z * v * z⁻¹ * v⁻¹)⁻¹ * v⁻¹ ∈ N :=
    layers_comm_comm_mem hvv hvM hM2 hzM
  have hνeM : (z * v * z⁻¹ * v⁻¹) * v * (z * v * z⁻¹ * v⁻¹)⁻¹ * v⁻¹ ∈ M :=
    hNH.trans hHM hνe
  have hνxe : (x * (z * v * z⁻¹ * v⁻¹)⁻¹) * v * (x * (z * v * z⁻¹ * v⁻¹)⁻¹)⁻¹ * v⁻¹ ∈ N := by
    have e : (x * (z * v * z⁻¹ * v⁻¹)⁻¹) * v * (x * (z * v * z⁻¹ * v⁻¹)⁻¹)⁻¹ * v⁻¹ =
        ((x * (z * v * z⁻¹ * v⁻¹)⁻¹) *
          ((z * v * z⁻¹ * v⁻¹) * v * (z * v * z⁻¹ * v⁻¹)⁻¹ * v⁻¹)⁻¹ *
          (x * (z * v * z⁻¹ * v⁻¹)⁻¹)⁻¹ *
          ((z * v * z⁻¹ * v⁻¹) * v * (z * v * z⁻¹ * v⁻¹)⁻¹ * v⁻¹)⁻¹⁻¹) *
        (((z * v * z⁻¹ * v⁻¹) * v * (z * v * z⁻¹ * v⁻¹)⁻¹ * v⁻¹)⁻¹ * (x * v * x⁻¹ * v⁻¹)) := by
      group
    rw [e]
    exact mul_mem (hMN _ hxeM _ (inv_mem hνeM)) (mul_mem (inv_mem hνe) hxv)
  obtain ⟨w₂, hw₂H, hw₂⟩ := hfreeH _ hxeH hνxe
  have hw₂M : w₂ ∈ M := hHM hw₂H
  have hpM : w₂ * v * w₂⁻¹ * v⁻¹ ∈ M := layers_comm_mem hvM hw₂M
  refine ⟨w₂ * z, mul_mem hw₂M hzM, ?_⟩
  have e : ((w₂ * z) * v * (w₂ * z)⁻¹ * v⁻¹)⁻¹ * x =
      ((w₂ * v * w₂⁻¹ * v⁻¹)⁻¹ * (w₂ * (z * v * z⁻¹ * v⁻¹)⁻¹ * w₂⁻¹ *
          (z * v * z⁻¹ * v⁻¹)⁻¹⁻¹) * (w₂ * v * w₂⁻¹ * v⁻¹)⁻¹⁻¹) *
        ((w₂ * v * w₂⁻¹ * v⁻¹)⁻¹ * (z * v * z⁻¹ * v⁻¹)⁻¹ * (w₂ * v * w₂⁻¹ * v⁻¹)⁻¹⁻¹ *
          (z * v * z⁻¹ * v⁻¹)⁻¹⁻¹) *
        ((z * v * z⁻¹ * v⁻¹)⁻¹ * ((w₂ * v * w₂⁻¹ * v⁻¹)⁻¹ * (x * (z * v * z⁻¹ * v⁻¹)⁻¹)) *
          (z * v * z⁻¹ * v⁻¹)⁻¹⁻¹) := by group
  have hk₁ := hMN _ hw₂M _ (inv_mem heM)
  rw [e, hcen _ hk₁ _ (inv_mem hpM), hcen _ hw₂ _ (inv_mem heM)]
  exact mul_mem (mul_mem hk₁ (hMN _ (inv_mem hpM) _ (inv_mem heM))) hw₂

end CFSG.SeitzReduction.RankOne
