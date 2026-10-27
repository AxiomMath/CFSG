module

public import CFSG.GH74.Generic.BProg.B1.PilotS3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

namespace S3Rk1Basic

variable {G : Type} [Group G]

theorem pcomp_of_circ {x : G} {K : Subgroup G} (hc : IsJ2Circ x K) :
    IsPCompIn 2 (centralizer ({x} : Set G)) K :=
  hc.1.1.1.2.2

theorem orderOf_x_of_circ {x : G} {K : Subgroup G} (hc : IsJ2Circ x K) : orderOf x = 2 :=
  hc.1.1.1.1

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G}
    (hg : g ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, g = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = (k * h)⁻¹ := by rw [hc h hh k hk]
          _ = h⁻¹ * k⁻¹ := by group }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
    (fun k hk => ⟨1, one_mem _, k, hk, by simp⟩)
  exact hle hg

theorem comm_E_x {x : G} {K E : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) (hEK : E ≤ K)
    {e : G} (he : e ∈ E) : e * x = x * e :=
  (Subgroup.mem_centralizer_singleton_iff.1 (hK (hEK he)))

theorem decomp_A {x : G} {K A E : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) (hEK : E ≤ K)
    (hAE : A = E ⊔ zpowers x) (hx : orderOf x = 2) {d : G} (hd : d ∈ A) :
    ∃ e ∈ E, d = e ∨ d = e * x := by
  have hc : ∀ e ∈ E, ∀ k ∈ zpowers x, e * k = k * e := by
    intro e he k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute e x from comm_E_x hK hEK he) n).eq
  obtain ⟨e, he, z, hz, rfl⟩ := exists_mul_of_mem_sup hc (hAE ▸ hd)
  refine ⟨e, he, ?_⟩
  rcases B1.PilotS5.mem_zpowers_of_two hx hz with h1 | h1
  · left; rw [h1, mul_one]
  · right; rw [h1]

theorem mem_normalizer_of_le_centralizer {x : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G)) : x ∈ normalizer (K : Set G) :=
  Subgroup.centralizer_le_normalizer (K : Set G)
    (Subgroup.mem_centralizer_iff.2 fun _ hk => Subgroup.mem_centralizer_singleton_iff.1 (hKC hk))

theorem A_le_normalizer {x : G} {K A E : Subgroup G} (hK : K ≤ centralizer ({x} : Set G))
    (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x) (hx : orderOf x = 2) :
    A ≤ normalizer (K : Set G) := by
  intro d hd
  obtain ⟨e, he, h | h⟩ := decomp_A hK hEK hAE hx hd
  · rw [h]; exact Subgroup.le_normalizer (hEK he)
  · rw [h]
    exact (normalizer (K : Set G)).mul_mem (Subgroup.le_normalizer (hEK he))
      (mem_normalizer_of_le_centralizer hK)

variable [Finite G]

theorem exists_E {x : G} {K A : Subgroup G} (hc : IsJ2Circ x K) (hsrc : IsSource2 x K A)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 ∧ x ∉ K := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := pcomp_of_circ hc
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨-, -, -, hcase⟩ := hsrc
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, hxE, hEel, hE4, -⟩
  · exact (B1.PilotS3.not_qShape1_of_center_trivial h1 hZ).elim
  · exact ⟨E, hEK, hAE, hxE, hEel, hE4,
      B1.PilotS5.not_mem_of_center_trivial (orderOf_x_of_circ hc) hK.1 hZ⟩

end S3Rk1Basic

end CFSG.GH74.Generic.BProg.B3
