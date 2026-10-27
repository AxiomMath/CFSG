module

public import CFSG.ClassicalInvolution.Asc77.AscT7V3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace C22G

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem comm_sq (c : Ctx p f Ω W) (ρ σ : Rep Ω W) {z t g : G}
    (hz : IsUniqueInvolution ρ.K z) (hK : σ.K ≠ ρ.K) (hg : g ∈ ρ.K ⊓ W) (hg4 : orderOf g = 4)
    (hτz : σ.r * z * σ.r⁻¹ = t * z) :
    σ.r * g * σ.r⁻¹ * g⁻¹ ∈ σ.K ⊓ W ∧
      (σ.r * g * σ.r⁻¹ * g⁻¹) * (σ.r * g * σ.r⁻¹ * g⁻¹) = t := by
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hgsq : g * g = z := sq_eq_involution_of_orderOf_four hz hg.1 hg4
  have hgW : g ∈ W := hg.2
  have hz2 : z * z = 1 := hz.sq
  have hxW : σ.r * g * σ.r⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer g).mp hgW
  refine ⟨c.comm_mem σ ρ hK hg, ?_⟩
  have h1 : (σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹) = t * z := by
    calc (σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹) = σ.r * (g * g) * σ.r⁻¹ := by group
      _ = t * z := by rw [hgsq, hτz]
  have hgi : g⁻¹ ∈ W := W.inv_mem hgW
  have h2 : g⁻¹ * g⁻¹ = z := by
    have : g⁻¹ * g⁻¹ = (g * g)⁻¹ := by group
    rw [this, hgsq]
    exact inv_eq_of_mul_eq_one_right hz2
  have hc : (σ.r * g * σ.r⁻¹) * g⁻¹ = g⁻¹ * (σ.r * g * σ.r⁻¹) := hcomm _ hxW _ hgi
  calc σ.r * g * σ.r⁻¹ * g⁻¹ * (σ.r * g * σ.r⁻¹ * g⁻¹)
      = (σ.r * g * σ.r⁻¹) * (g⁻¹ * (σ.r * g * σ.r⁻¹)) * g⁻¹ := by group
    _ = (σ.r * g * σ.r⁻¹) * ((σ.r * g * σ.r⁻¹) * g⁻¹) * g⁻¹ := by rw [← hc]
    _ = ((σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹)) * (g⁻¹ * g⁻¹) := by group
    _ = (t * z) * z := by rw [h1, h2]
    _ = t := by rw [mul_assoc, hz2, mul_one]

theorem exists_centralized_pair (c : Ctx p f Ω W) (ρ₀ ρ₁ σ : Rep Ω W) {z t g₀ g₁ : G}
    (hz₀ : IsUniqueInvolution ρ₀.K z) (hz₁ : IsUniqueInvolution ρ₁.K z)
    (ht : IsUniqueInvolution σ.K t) (hK₀ : σ.K ≠ ρ₀.K) (hK₁ : σ.K ≠ ρ₁.K)
    (hn₀ : ρ₀.K ∉ omegaNbr Ω σ.K) (hg₀ : g₀ ∈ ρ₀.K ⊓ W) (ho₀ : orderOf g₀ = 4)
    (hg₁ : g₁ ∈ ρ₁.K ⊓ W) (ho₁ : orderOf g₁ = 4) :
    ∃ g₁' : G, g₁' ∈ ρ₁.K ⊓ W ∧ orderOf g₁' = 4 ∧
      σ.R ≤ Subgroup.centralizer ({g₀ * g₁'} : Set G) := by
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hτz : σ.r * z * σ.r⁻¹ = t * z := c.conj_involution σ ρ₀ hK₀ hn₀ ht hz₀
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution ρ₀ hz₀
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hz2 : z * z = 1 := hz₀.sq
  have hht : t * t = 1 := ht.sq
  obtain ⟨he₀W, he₀sq⟩ := comm_sq c ρ₀ σ hz₀ hK₀ hg₀ ho₀ hτz
  obtain ⟨he₁W, he₁sq⟩ := comm_sq c ρ₁ σ hz₁ hK₁ hg₁ ho₁ hτz
  set e₀ : G := σ.r * g₀ * σ.r⁻¹ * g₀⁻¹ with he₀
  set e₁ : G := σ.r * g₁ * σ.r⁻¹ * g₁⁻¹ with he₁
  have hg₀W : g₀ ∈ W := hg₀.2
  have hg₁W : g₁ ∈ W := hg₁.2
  have hge₀ : σ.r * g₀ * σ.r⁻¹ = e₀ * g₀ := by rw [he₀]; group
  have hge₁ : σ.r * g₁ * σ.r⁻¹ = e₁ * g₁ := by rw [he₁]; group
  have hcase : e₁ = e₀ ∨ e₁ = e₀⁻¹ := by
    have hsq : (e₁ * e₀⁻¹) * (e₁ * e₀⁻¹) = 1 := by
      have hc := hcomm _ he₁W.2 _ (W.inv_mem he₀W.2)
      calc (e₁ * e₀⁻¹) * (e₁ * e₀⁻¹) = e₁ * (e₀⁻¹ * e₁) * e₀⁻¹ := by group
        _ = e₁ * (e₁ * e₀⁻¹) * e₀⁻¹ := by rw [← hc]
        _ = (e₁ * e₁) * (e₀⁻¹ * e₀⁻¹) := by group
        _ = t * t := by
            rw [he₁sq]
            congr 1
            have : e₀⁻¹ * e₀⁻¹ = (e₀ * e₀)⁻¹ := by group
            rw [this, he₀sq]
            exact inv_eq_of_mul_eq_one_right hht
        _ = 1 := hht
    have hmem : e₁ * e₀⁻¹ ∈ σ.K := σ.K.mul_mem he₁W.1 (σ.K.inv_mem he₀W.1)
    rcases ht.unique _ hmem hsq with h | h
    · left
      calc e₁ = (e₁ * e₀⁻¹) * e₀ := by group
        _ = e₀ := by rw [h, one_mul]
    · right
      have hinv : e₀⁻¹ = e₀ * t := by
        have : e₀ * (e₀ * t) = 1 := by
          rw [← mul_assoc, he₀sq, hht]
        exact inv_eq_of_mul_eq_one_right this
      calc e₁ = (e₁ * e₀⁻¹) * e₀ := by group
        _ = t * e₀ := by rw [h]
        _ = e₀ * t := hcomm _ htW _ he₀W.2
        _ = e₀⁻¹ := hinv.symm
  have hrW : ∀ x ∈ W, σ.r * x * σ.r⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer x).mp hx
  rcases hcase with hB | hA
  ·
    refine ⟨g₁⁻¹, ⟨ρ₁.K.inv_mem hg₁.1, W.inv_mem hg₁W⟩, by rw [orderOf_inv]; exact ho₁, ?_⟩
    have hy : g₀ * g₁⁻¹ ∈ W := W.mul_mem hg₀W (W.inv_mem hg₁W)
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g₀ * g₁⁻¹) * σ.r⁻¹ = g₀ * g₁⁻¹ := by
      have hinv₁ : σ.r * g₁⁻¹ * σ.r⁻¹ = (e₁ * g₁)⁻¹ := by rw [← hge₁]; group
      calc σ.r * (g₀ * g₁⁻¹) * σ.r⁻¹ = (σ.r * g₀ * σ.r⁻¹) * (σ.r * g₁⁻¹ * σ.r⁻¹) := by group
        _ = (e₀ * g₀) * (e₁ * g₁)⁻¹ := by rw [hge₀, hinv₁]
        _ = (e₀ * g₀) * (e₀ * g₁)⁻¹ := by rw [hB]
        _ = (e₀ * g₀) * (g₁⁻¹ * e₀⁻¹) := by group
        _ = g₀ * g₁⁻¹ * (e₀ * e₀⁻¹) := by
            have h3 := hcomm _ he₀W.2 _ hg₀W
            have h4 := hcomm _ he₀W.2 _ (W.inv_mem hg₁W)
            calc (e₀ * g₀) * (g₁⁻¹ * e₀⁻¹) = (g₀ * e₀) * (g₁⁻¹ * e₀⁻¹) := by rw [h3]
              _ = g₀ * (e₀ * g₁⁻¹) * e₀⁻¹ := by group
              _ = g₀ * (g₁⁻¹ * e₀) * e₀⁻¹ := by rw [h4]
              _ = g₀ * g₁⁻¹ * (e₀ * e₀⁻¹) := by group
        _ = g₀ * g₁⁻¹ := by group
    exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    refine ⟨g₁, hg₁, ho₁, ?_⟩
    have hy : g₀ * g₁ ∈ W := W.mul_mem hg₀W hg₁W
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g₀ * g₁) * σ.r⁻¹ = g₀ * g₁ := by
      calc σ.r * (g₀ * g₁) * σ.r⁻¹ = (σ.r * g₀ * σ.r⁻¹) * (σ.r * g₁ * σ.r⁻¹) := by group
        _ = (e₀ * g₀) * (e₁ * g₁) := by rw [hge₀, hge₁]
        _ = (e₀ * g₀) * (e₀⁻¹ * g₁) := by rw [hA]
        _ = (g₀ * e₀) * (e₀⁻¹ * g₁) := by rw [hcomm _ he₀W.2 _ hg₀W]
        _ = g₀ * (e₀ * e₀⁻¹) * g₁ := by group
        _ = g₀ * g₁ := by group
    exact mul_inv_eq_iff_eq_mul.mp h1

theorem exists_orderOf_four_mem_inf_W (c : Ctx p f Ω W) (ρ : Rep Ω W) :
    ∃ g : G, g ∈ ρ.K ⊓ W ∧ orderOf g = 4 := by
  obtain ⟨hKW, -, hcyc, h4, -⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hp2 : IsPGroup 2 ↥(ρ.K ⊓ W) := by
    rw [← hKW]
    exact ρ.hRK.2.1.to_le inf_le_left
  have hcyc' : IsCyclic ↥(ρ.K ⊓ W) := hKW ▸ hcyc
  have h4' : 4 ≤ Nat.card ↥(ρ.K ⊓ W) := hKW ▸ h4
  obtain ⟨x, hx, hx4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hp2 hcyc' h4'
  exact ⟨x, hx, hx4⟩

end C22G

end CFSG.ClassicalInvolution.Asc77
