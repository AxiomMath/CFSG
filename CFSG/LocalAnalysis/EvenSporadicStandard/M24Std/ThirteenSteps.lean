module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.Thirteen

open Subgroup

variable {G : Type} [Group G]

theorem comm_z_mul {D : Subgroup G} (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {z a b : G}
    (ha : a ∈ D) (hb : z * b * z⁻¹ * b⁻¹ ∈ D) :
    z * (a * b) * z⁻¹ * (a * b)⁻¹ = z * a * z⁻¹ * a⁻¹ * (z * b * z⁻¹ * b⁻¹) := by
  have h := hD a ha _ hb
  calc z * (a * b) * z⁻¹ * (a * b)⁻¹
        = z * a * z⁻¹ * (a⁻¹ * (a * (z * b * z⁻¹ * b⁻¹)) * a⁻¹) := by group
    _ = z * a * z⁻¹ * a⁻¹ * (z * b * z⁻¹ * b⁻¹) := by rw [h]; group

theorem comm_z_conj {z y : G} (h : y * z = z * y) (d : G) :
    z * (y * d * y⁻¹) * z⁻¹ * (y * d * y⁻¹)⁻¹ = y * (z * d * z⁻¹ * d⁻¹) * y⁻¹ := by
  calc z * (y * d * y⁻¹) * z⁻¹ * (y * d * y⁻¹)⁻¹
        = z * y * d * (z * y)⁻¹ * y * d⁻¹ * y⁻¹ := by group
    _ = y * z * d * (y * z)⁻¹ * y * d⁻¹ * y⁻¹ := by rw [h]
    _ = y * (z * d * z⁻¹ * d⁻¹) * y⁻¹ := by group

theorem comm_z_mul_of_eq_one {z s u : G} (hu : z * u * z⁻¹ * u⁻¹ = 1) :
    z * (s * u) * z⁻¹ * (s * u)⁻¹ = z * s * z⁻¹ * s⁻¹ := by
  calc z * (s * u) * z⁻¹ * (s * u)⁻¹ = z * s * z⁻¹ * (z * u * z⁻¹ * u⁻¹) * s⁻¹ := by group
    _ = z * s * z⁻¹ * s⁻¹ := by rw [hu, mul_one]

theorem comm_z_eq_one_of_comm {z g : G} (h : g * z = z * g) : z * g * z⁻¹ * g⁻¹ = 1 := by
  rw [← h]
  group

theorem conj_mem_egV {A : Subgroup G} {z g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hz : ∃ a ∈ A, g * z * g⁻¹ = a * z) : ∀ v ∈ egV A z, g * v * g⁻¹ ∈ egV A z := by
  obtain ⟨a, ha, hgz⟩ := hz
  unfold egV
  have hle : A ⊔ zpowers z ≤ (A ⊔ zpowers z).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ?_
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left (hA b hb)
    · rw [zpowers_le]
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hgz]
      exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers z))
  intro v hv
  have h := hle hv
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem mem_egM_of {A : Subgroup G} {z g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hA' : ∀ a ∈ A, g⁻¹ * a * g ∈ A) (hz : ∃ a ∈ A, g * z * g⁻¹ = a * z)
    (hz' : ∃ a ∈ A, g⁻¹ * z * g = a * z) : g ∈ egM A z := by
  have h1 := conj_mem_egV hA hz
  have h2 := conj_mem_egV (g := g⁻¹) (by simpa only [inv_inv] using hA')
    (by simpa only [inv_inv] using hz')
  unfold egM
  rw [mem_normalizer_iff]
  intro v
  refine ⟨h1 v, fun hv => ?_⟩
  have h3 := h2 _ hv
  rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at h3

theorem mem_egM_of_mem_normalizer {B : Subgroup G} {z g : G} (hg : g ∈ normalizer (B : Set G))
    (hgz : g * z = z * g) : g ∈ egM B z := by
  have hgz' : g⁻¹ * z = z * g⁻¹ := Commute.inv_left hgz
  refine mem_egM_of (fun b hb => (mem_normalizer_iff.mp hg b).mp hb)
    (fun b hb => (mem_normalizer_iff''.mp hg b).mp hb) ⟨1, B.one_mem, ?_⟩ ⟨1, B.one_mem, ?_⟩
  · rw [one_mul, hgz, mul_inv_cancel_right]
  · rw [one_mul, hgz', inv_mul_cancel_right]

theorem exists_fixed_comm_z {D : Subgroup G} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    {z y c d₀ : G} (hyz : y * z = z * y) (hy3 : y * y * y = 1)
    (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D) (hyD' : ∀ d ∈ D, y⁻¹ * d * y ∈ D)
    (hzD : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ D) (hd₀ : d₀ ∈ D) (hc : z * d₀ * z⁻¹ * d₀⁻¹ = c)
    (hyc : y * c * y⁻¹ = c) (hcc : c * c = 1) :
    ∃ d ∈ D, y * d * y⁻¹ = d ∧ z * d * z⁻¹ * d⁻¹ = c := by
  have hy2 : y * y = y⁻¹ := eq_inv_of_mul_eq_one_left hy3
  have hyz' : y⁻¹ * z = z * y⁻¹ := Commute.inv_left hyz
  have hyc' : y⁻¹ * c * y = c := by
    calc y⁻¹ * c * y = y⁻¹ * (y * c * y⁻¹) * y := by rw [hyc]
      _ = c := by group
  have h1 : y * d₀ * y⁻¹ ∈ D := hyD _ hd₀
  have h2 : y⁻¹ * d₀ * y ∈ D := hyD' _ hd₀
  refine ⟨d₀ * (y * d₀ * y⁻¹) * (y⁻¹ * d₀ * y), D.mul_mem (D.mul_mem hd₀ h1) h2, ?_, ?_⟩
  · have e1 : y * (y * d₀ * y⁻¹) * y⁻¹ = y⁻¹ * d₀ * y := by
      calc y * (y * d₀ * y⁻¹) * y⁻¹ = y * y * d₀ * (y * y)⁻¹ := by group
        _ = y⁻¹ * d₀ * y := by rw [hy2, inv_inv]
    have e2 : y * (y⁻¹ * d₀ * y) * y⁻¹ = d₀ := by group
    calc y * (d₀ * (y * d₀ * y⁻¹) * (y⁻¹ * d₀ * y)) * y⁻¹
        = y * d₀ * y⁻¹ * (y * (y * d₀ * y⁻¹) * y⁻¹) * (y * (y⁻¹ * d₀ * y) * y⁻¹) := by group
      _ = y * d₀ * y⁻¹ * (y⁻¹ * d₀ * y) * d₀ := by rw [e1, e2]
      _ = d₀ * (y * d₀ * y⁻¹) * (y⁻¹ * d₀ * y) := by
        rw [hDc _ (D.mul_mem h1 h2) _ hd₀]
        simp only [mul_assoc]
  · have t1 : z * (y * d₀ * y⁻¹) * z⁻¹ * (y * d₀ * y⁻¹)⁻¹ = c := by
      rw [comm_z_conj hyz, hc, hyc]
    have t2 : z * (y⁻¹ * d₀ * y) * z⁻¹ * (y⁻¹ * d₀ * y)⁻¹ = c := by
      have h := comm_z_conj hyz' d₀
      rw [inv_inv] at h
      rw [h, hc, hyc']
    rw [comm_z_mul hDc (D.mul_mem hd₀ h1) (hzD _ h2), comm_z_mul hDc hd₀ (hzD _ h1), hc, t1, t2,
      hcc, one_mul]

theorem comm_mem_of_rank_two {A B D : Subgroup G} {z x y d : G}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD2 : ∀ a ∈ D, a * a = 1) (hBD : B ≤ D)
    (hτ : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ B) (honto : ∀ b ∈ B, ∃ d ∈ D, z * d * z⁻¹ * d⁻¹ = b)
    (hker : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ = 1 → d ∈ B)
    (hxz : x * z = z * x) (hxx : x * x = 1) (hxD : ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hx1 : ∀ b ∈ B, b * (x * b⁻¹ * x⁻¹) ∈ A ⊓ B)
    (hx2 : ∀ c ∈ A ⊓ B, ∃ b ∈ B, c = b * (x * b⁻¹ * x⁻¹))
    (hyz : y * z = z * y) (hyB : ∀ b ∈ B, y * b * y⁻¹ = b ↔ b ∈ A)
    (hd : d ∈ D) (hyd : y * d * y⁻¹ = d) :
    x * d * x⁻¹ * d⁻¹ ∈ A ⊓ B := by
  have hzD : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ D := fun d hd => hBD (hτ d hd)
  have hβB : z * d * z⁻¹ * d⁻¹ ∈ B := hτ d hd
  have hβA : z * d * z⁻¹ * d⁻¹ ∈ A := by
    rw [← hyB _ hβB, ← comm_z_conj hyz, hyd]
  obtain ⟨b, hb, hβ⟩ := hx2 _ (mem_inf.mpr ⟨hβA, hβB⟩)
  obtain ⟨d', hd', hτd'⟩ := honto b hb
  have hxd' : x * d' * x⁻¹ ∈ D := hxD d' hd'
  obtain ⟨u, hu⟩ : ∃ u, u = x * d' * x⁻¹ * d' := ⟨_, rfl⟩
  have huD : u ∈ D := hu ▸ D.mul_mem hxd' hd'
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hτu : z * u * z⁻¹ * u⁻¹ = z * d * z⁻¹ * d⁻¹ := by
    have hw : b * (x * b⁻¹ * x⁻¹) ∈ D := hBD (mem_inf.mp (hx1 b hb)).2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hD2 b (hBD hb))
    rw [hu, comm_z_mul hDc hxd' (hzD d' hd'), comm_z_conj hxz, hτd', hβ]
    calc x * b * x⁻¹ * b = x * b * x⁻¹ * b⁻¹ := by rw [hbi]
      _ = (b * (x * b⁻¹ * x⁻¹))⁻¹ := by group
      _ = b * (x * b⁻¹ * x⁻¹) := inv_eq_of_mul_eq_one_right (hD2 _ hw)
  have hβ'B : d * u ∈ B := by
    refine hker _ (D.mul_mem hd huD) ?_
    rw [comm_z_mul hDc hd (hzD u huD), hτu]
    exact hD2 _ (hBD hβB)
  have hxu : x * u * x⁻¹ = u := by
    have hc := hDc d' hd' u huD
    calc x * u * x⁻¹ = x * x * d' * x⁻¹ * d' * x⁻¹ := by rw [hu]; group
      _ = d' * x * d' * x⁻¹ := by rw [hxx, one_mul, hxi]
      _ = d' * u * d'⁻¹ := by rw [hu]; group
      _ = u := by rw [hc, mul_inv_cancel_right]
  have hux : u * x⁻¹ = x⁻¹ * u := by
    calc u * x⁻¹ = x⁻¹ * (x * u * x⁻¹) := by group
      _ = x⁻¹ * u := by rw [hxu]
  have key : x * d * x⁻¹ * d⁻¹ = (d * u * (x * (d * u)⁻¹ * x⁻¹))⁻¹ := by
    calc x * d * x⁻¹ * d⁻¹ = x * d * (x⁻¹ * u) * u⁻¹ * d⁻¹ := by group
      _ = x * d * (u * x⁻¹) * u⁻¹ * d⁻¹ := by rw [hux]
      _ = (d * u * (x * (d * u)⁻¹ * x⁻¹))⁻¹ := by group
  rw [key]
  exact (A ⊓ B).inv_mem (hx1 _ hβ'B)

theorem comm_of_closure {Z K : Subgroup G} {X : Set G} {y : G}
    (hX : closure X = Z) (hZ2 : ∀ x ∈ Z, x * x = 1)
    (hXK : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hyZ : closure {w : G | ∃ x ∈ Z, w = x * (y * x⁻¹ * y⁻¹)} = Z)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ = k) :
    ∀ x ∈ Z, ∀ k ∈ K, x * k = k * x := by
  have hN : Z ≤ normalizer (K : Set G) := by
    rw [← hX, closure_le]
    intro x hx
    have hxZ : x ∈ Z := hX ▸ subset_closure hx
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro h
    refine ⟨hXK x hx h, fun hh => ?_⟩
    have e : x * (x * h * x⁻¹) * x⁻¹ = h := by
      calc x * (x * h * x⁻¹) * x⁻¹ = x * x * h * (x * x)⁻¹ := by group
        _ = h := by rw [hZ2 x hxZ, one_mul, inv_one, mul_one]
    rw [← e]
    exact hXK x hx _ hh
  intro x hx k hk
  have hgen : Z ≤ centralizer {k} := by
    rw [← hyZ, closure_le]
    rintro w ⟨x', hx', rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h1 : x'⁻¹ * k * x'⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (hN (Z.inv_mem hx')) k).mp hk
    have h2 := hyK _ h1
    have h3 := hyK k hk
    have h4 : y * x'⁻¹ * y⁻¹ * k * (y * x'⁻¹ * y⁻¹)⁻¹ = x'⁻¹ * k * x' := by
      calc y * x'⁻¹ * y⁻¹ * k * (y * x'⁻¹ * y⁻¹)⁻¹
          = y * x'⁻¹ * y⁻¹ * (y * k * y⁻¹) * (y * x'⁻¹ * y⁻¹)⁻¹ := by rw [h3]
        _ = y * (x'⁻¹ * k * x'⁻¹⁻¹) * y⁻¹ := by group
        _ = x'⁻¹ * k * x' := by rw [h2, inv_inv]
    calc x' * (y * x'⁻¹ * y⁻¹) * k
        = x' * (y * x'⁻¹ * y⁻¹ * k * (y * x'⁻¹ * y⁻¹)⁻¹) * (y * x'⁻¹ * y⁻¹) := by group
      _ = k * (x' * (y * x'⁻¹ * y⁻¹)) := by rw [h4]; group
  exact mem_centralizer_singleton_iff.mp (hgen hx)

end CFSG.EvenSporadicStandard.M24Std.Thirteen
