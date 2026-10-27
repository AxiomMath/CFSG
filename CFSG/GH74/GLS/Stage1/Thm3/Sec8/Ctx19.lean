module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx18

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem W_conj_h (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ Wsub S U) :
    h⁻¹ * x * h ∈ Wsub S U := by
  have h1 : h * (h⁻¹ * x * h) * h⁻¹ ∈ Wsub S U := by
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e]; exact hx
  exact ((Subgroup.mem_normalizer_iff.1 hs.h_W) _).2 h1

theorem U_conj_h (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ U) : h⁻¹ * x * h ∈ U := by
  have := ((Subgroup.mem_normalizer_iff.1 (inv_mem hs.h_norm)) x).1 hx
  simpa using this

theorem y_sq (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ y₂ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₂P : y₂ ∈ Pof S K₂) (hy₁sq : y₁ * y₁ = z) (hy₂sq : y₂ * y₂ = z) :
    (y₁ * y₂) * (y₁ * y₂) = 1 := by
  have hc : y₁ * y₂ = y₂ * y₁ := hs.P_comm hII y₁ hy₁P y₂ hy₂P
  calc (y₁ * y₂) * (y₁ * y₂) = y₁ * (y₂ * y₁) * y₂ := by group
    _ = y₁ * (y₁ * y₂) * y₂ := by rw [← hc]
    _ = (y₁ * y₁) * (y₂ * y₂) := by group
    _ = 1 := by rw [hy₁sq, hy₂sq]; exact hs.z_sq

theorem y_inv_V₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ y₂ : G}
    (hy₂P : y₂ ∈ Pof S K₂) (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) :
    ∀ c ∈ Vof S K₁ W₂, (y₁ * y₂) * c * (y₁ * y₂)⁻¹ = c⁻¹ := by
  intro c hc
  have h1 : c * y₂ = y₂ * c := hs.P_comm hII c hc.2 y₂ hy₂P
  calc (y₁ * y₂) * c * (y₁ * y₂)⁻¹ = y₁ * (y₂ * c) * y₂⁻¹ * y₁⁻¹ := by group
    _ = y₁ * (c * y₂) * y₂⁻¹ * y₁⁻¹ := by rw [h1]
    _ = y₁ * c * y₁⁻¹ := by group
    _ = c⁻¹ := hy₁inv c hc

theorem y_inv_V₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ y₂ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₂inv : ∀ c ∈ Vof S K₂ W₁, y₂ * c * y₂⁻¹ = c⁻¹) :
    ∀ c ∈ Vof S K₂ W₁, (y₁ * y₂) * c * (y₁ * y₂)⁻¹ = c⁻¹ := by
  intro c hc
  have h1 : y₁ * c = c * y₁ := hs.P_comm hII y₁ hy₁P c hc.2
  calc (y₁ * y₂) * c * (y₁ * y₂)⁻¹ = y₁ * (y₂ * c * y₂⁻¹) * y₁⁻¹ := by group
    _ = y₁ * c⁻¹ * y₁⁻¹ := by rw [hy₂inv c hc]
    _ = (y₁ * c * y₁⁻¹)⁻¹ := by group
    _ = c⁻¹ := by rw [h1]; group

theorem y_mem_W (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ y₂ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₂P : y₂ ∈ Pof S K₂)
    (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹)
    (hy₂inv : ∀ c ∈ Vof S K₂ W₁, y₂ * c * y₂⁻¹ = c⁻¹) : y₁ * y₂ ∈ Wsub S U := by
  have h1 := hs.y₁_conj_u hII hq hy₁P hy₁inv
  have h2 := hs.y₂_conj_u hII hq hy₂P hy₂inv
  have hz1 : y₁ * z * y₁⁻¹ = z := by rw [← hs.z_comm hII hy₁P.1]; group
  have h3 : (y₁ * y₂) * u * (y₁ * y₂)⁻¹ = u := by
    calc (y₁ * y₂) * u * (y₁ * y₂)⁻¹ = y₁ * (y₂ * u * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * (u * z) * y₁⁻¹ := by rw [h2]
      _ = (y₁ * u * y₁⁻¹) * (y₁ * z * y₁⁻¹) := by group
      _ = (u * z) * z := by rw [h1, hz1]
      _ = u := by rw [mul_assoc, hs.z_sq, mul_one]
  rw [hs.mem_W_iff hII]
  refine ⟨mul_mem hy₁P.1 hy₂P.1, ?_⟩
  calc (y₁ * y₂) * u = ((y₁ * y₂) * u * (y₁ * y₂)⁻¹) * (y₁ * y₂) := by group
    _ = u * (y₁ * y₂) := by rw [h3]

theorem not_mem_A_of_inv (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y : G}
    (hy : ∀ c ∈ Vof S K₁ W₂, y * c * y⁻¹ = c⁻¹) : y ∉ Aof S K₁ W₂ h := by
  intro hyA
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, h1, h2⟩ := hs.u_decomp hII hq
  have hcomm : y * v₁ = v₁ * y := hs.A_comm hII hq hrec y hyA v₁ (Subgroup.mem_sup_left hv₁)
  have h3 := hy v₁ hv₁
  have h4 : y * v₁ * y⁻¹ = v₁ := by rw [hcomm]; group
  rw [h4] at h3
  have h5 : v₁ * v₁ = 1 := by
    calc v₁ * v₁ = v₁ * v₁⁻¹ := congrArg (v₁ * ·) h3
      _ = 1 := by group
  apply hs.z_ne
  rw [← h1]
  exact h5

theorem y_inv_A_of_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y : G}
    (hyW : y ∈ Wsub S U) (hyA : y ∉ Aof S K₁ W₂ h)
    (hyinv : ∀ c ∈ Vof S K₁ W₂, y * c * y⁻¹ = c⁻¹)
    (hrel : (Aof S K₁ W₂ h).relIndex (Wsub S U) = 2) :
    ∀ a ∈ Aof S K₁ W₂ h, y * a * y⁻¹ = a⁻¹ := by
  have hy'W : h⁻¹ * y * h ∈ Wsub S U := hs.W_conj_h hyW
  have hy'A : h⁻¹ * y * h ∉ Aof S K₁ W₂ h := by
    intro h'
    apply hyA
    have := (hs.A_conj hII hq hrec hk h').1
    have e : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rwa [e] at this
  have hdiff : (h⁻¹ * y * h) * y⁻¹ ∈ Aof S K₁ W₂ h :=
    Basic.mul_inv_mem_of_relIndex_two hrel hy'W hyW hy'A hyA
  have hyS : y ∈ S := hyW.1
  have hVh : ∀ c ∈ conjugate (Vof S K₁ W₂) h, y * c * y⁻¹ = c⁻¹ := by
    intro c hc
    have hc' : h * c * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hc
    have hcA : c ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right hc
    have h1 : (h⁻¹ * y * h) * c * (h⁻¹ * y * h)⁻¹ = c⁻¹ := by
      have h2 := hyinv _ hc'
      calc (h⁻¹ * y * h) * c * (h⁻¹ * y * h)⁻¹
          = h⁻¹ * (y * (h * c * h⁻¹) * y⁻¹) * h := by group
        _ = h⁻¹ * (h * c * h⁻¹)⁻¹ * h := by rw [h2]
        _ = c⁻¹ := by group
    have hdA : y * c * y⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hyS hcA
    have h3 := hs.A_comm hII hq hrec _ hdiff _ hdA
    have h4 : (h⁻¹ * y * h) * c * (h⁻¹ * y * h)⁻¹ =
        ((h⁻¹ * y * h) * y⁻¹) * (y * c * y⁻¹) * ((h⁻¹ * y * h) * y⁻¹)⁻¹ := by group
    rw [h4, h3] at h1
    calc y * c * y⁻¹ = (y * c * y⁻¹) * ((h⁻¹ * y * h) * y⁻¹) * ((h⁻¹ * y * h) * y⁻¹)⁻¹ := by group
      _ = c⁻¹ := h1
  intro a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
  have ha₁A : a₁ ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left ha₁
  have ha₂A : a₂ ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right ha₂
  have hc12 : a₁ * a₂ = a₂ * a₁ := hs.A_comm hII hq hrec a₁ ha₁A a₂ ha₂A
  calc y * (a₁ * a₂) * y⁻¹ = (y * a₁ * y⁻¹) * (y * a₂ * y⁻¹) := by group
    _ = a₁⁻¹ * a₂⁻¹ := by rw [hyinv a₁ ha₁, hVh a₂ ha₂]
    _ = (a₂ * a₁)⁻¹ := by rw [mul_inv_rev]
    _ = (a₁ * a₂)⁻¹ := by rw [hc12]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
