module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseCent
public import CFSG.GH74.QTGen4.Recog.Ku.CloseFinB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

theorem alt_six_invol_conj_two {σ₁ σ₂ : Equiv.Perm (Fin 6)}
    (h₁ : Equiv.Perm.sign σ₁ = 1) (h₁' : σ₁ * σ₁ = 1) (h₁1 : σ₁ ≠ 1)
    (h₂ : Equiv.Perm.sign σ₂ = 1) (h₂' : σ₂ * σ₂ = 1) (h₂1 : σ₂ ≠ 1) :
    ∃ a : Equiv.Perm (Fin 6), Equiv.Perm.sign a = 1 ∧ a * σ₂ * a⁻¹ = σ₁ := by
  obtain ⟨ρ₁, hρ₁, hc₁⟩ := alt_six_invol_conj σ₁ h₁ h₁' h₁1
  obtain ⟨ρ₂, hρ₂, hc₂⟩ := alt_six_invol_conj σ₂ h₂ h₂' h₂1
  refine ⟨ρ₁⁻¹ * ρ₂, ?_, ?_⟩
  · rw [map_mul, map_inv, hρ₁, hρ₂, inv_one, one_mul]
  · have e₁ : ρ₁⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3) * ρ₁ = σ₁ := by
      rw [← hc₁]; group
    calc (ρ₁⁻¹ * ρ₂) * σ₂ * (ρ₁⁻¹ * ρ₂)⁻¹
        = ρ₁⁻¹ * (ρ₂ * σ₂ * ρ₂⁻¹) * ρ₁ := by group
      _ = σ₁ := by rw [hc₂, e₁]

variable {G : Type} [Group G]

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

omit [Finite G] in
theorem perm_invol_of_mem {x : G} (hx : x ∈ N) (hx2 : x * x = 1) (hx1 : x ∉ E) :
    Equiv.Perm.sign (Ψ.π ⟨x, hx⟩) = 1 ∧ Ψ.π ⟨x, hx⟩ * Ψ.π ⟨x, hx⟩ = 1 ∧
      Ψ.π ⟨x, hx⟩ ≠ 1 := by
  refine ⟨Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt _), ?_,
    fun h => hx1 ((Ψ.ker ⟨x, hx⟩).mp h)⟩
  have h1 : (⟨x, hx⟩ * ⟨x, hx⟩ : N) = 1 := Subtype.ext (by simpa using hx2)
  rw [← map_mul, h1, map_one]

theorem exists_conj_mem_E_of_coset {i v' : G} (hi : i ∈ N) (hv' : v' ∈ N)
    (hi2 : i * i = 1) (hv2 : v' * v' = 1) (hi1 : i ∉ E)
    (hπ : Ψ.π ⟨v', hv'⟩ = Ψ.π ⟨i, hi⟩) : ∃ f ∈ E, f * i * f⁻¹ = v' := by
  obtain ⟨hσ_sign, hσσ, hσ1⟩ := Ψ.perm_invol_of_mem hi hi2 hi1
  obtain ⟨e, he_def⟩ : ∃ e : G, e = i * v' := ⟨_, rfl⟩
  have he : e ∈ E := by
    rw [he_def]
    have h1 : Ψ.π (⟨i, hi⟩ * ⟨v', hv'⟩) = 1 := by rw [map_mul, hπ, hσσ]
    exact (Ψ.ker _).mp h1
  have hv'ie : v' = i * e := by rw [he_def, ← mul_assoc, hi2, one_mul]
  have key : i * e * i = e := by
    have h3 : (i * e * i) * e = 1 := by
      have h4 := hv2
      rw [hv'ie] at h4
      simp only [mul_assoc] at h4 ⊢
      exact h4
    calc i * e * i = (i * e * i) * (e * e) := by rw [Ψ.E_mul_self e he, mul_one]
      _ = ((i * e * i) * e) * e := by group
      _ = e := by rw [h3, one_mul]
  obtain ⟨w, hw⟩ := Ψ.surj e he
  have hfix : actS6 (Ψ.π ⟨i, hi⟩) w = w := by
    have h1 : i * e * i⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨i, hi⟩) w) := by
      rw [← hw]; exact Ψ.act ⟨i, hi⟩ w
    rw [inv_eq_of_mul_eq_one_right hi2, key] at h1
    apply Ψ.inj
    rw [hw]
    exact h1.symm
  obtain ⟨u, hu⟩ := fix_eq_commutator_of_invol _ hσ_sign hσσ hσ1 w hfix
  have hgu : Ψ.Φ u * Ψ.Φ (actS6 (Ψ.π ⟨i, hi⟩) u) = e := by
    rw [← Ψ.add, ← hu, hw]
  have hact_u : i * Ψ.Φ u * i = Ψ.Φ (actS6 (Ψ.π ⟨i, hi⟩) u) := by
    have h1 : i * Ψ.Φ u * i⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨i, hi⟩) u) := Ψ.act ⟨i, hi⟩ u
    rw [inv_eq_of_mul_eq_one_right hi2] at h1
    exact h1
  refine ⟨Ψ.Φ u, Ψ.mem u, ?_⟩
  have hfuinv : (Ψ.Φ u)⁻¹ = Ψ.Φ u :=
    inv_eq_of_mul_eq_one_right (Ψ.E_mul_self _ (Ψ.mem u))
  have hcomm : e * i = i * e := by
    calc e * i = (i * e * i) * i := by rw [key]
      _ = i * e * (i * i) := by simp only [mul_assoc]
      _ = i * e := by rw [hi2, mul_one]
  have hfin : Ψ.Φ u * i * Ψ.Φ u = i * e := by
    calc Ψ.Φ u * i * Ψ.Φ u = Ψ.Φ u * (i * Ψ.Φ u * i) * i := by
          simp only [mul_assoc, hi2, mul_one]
      _ = Ψ.Φ u * Ψ.Φ (actS6 (Ψ.π ⟨i, hi⟩) u) * i := by rw [hact_u]
      _ = e * i := by rw [hgu]
      _ = i * e := hcomm
  rw [hfuinv, hv'ie, hfin]

theorem invol_conj_z {v₀ : G} (hv₀N : v₀ ∈ N) (hv₀E : v₀ ∉ E) (hv₀ : v₀ * v₀ = 1)
    (hv₀z : ∃ g : G, g * z * g⁻¹ = v₀) {i : G} (hiN : i ∈ N) (hi : i * i = 1) (hi1 : i ≠ 1) :
    ∃ g : G, g * z * g⁻¹ = i := by
  by_cases hiE : i ∈ E
  · exact Ψ.exists_conj_z hiE hi1
  obtain ⟨g₀, hg₀⟩ := hv₀z
  obtain ⟨hσv_s, hσv_i, hσv_1⟩ := Ψ.perm_invol_of_mem hv₀N hv₀ hv₀E
  obtain ⟨hσi_s, hσi_i, hσi_1⟩ := Ψ.perm_invol_of_mem hiN hi hiE
  obtain ⟨a, ha_sign, ha⟩ :=
    alt_six_invol_conj_two hσi_s hσi_i hσi_1 hσv_s hσv_i hσv_1
  obtain ⟨n, hn⟩ := Ψ.π_surj a (Equiv.Perm.mem_alternatingGroup.mpr ha_sign)
  obtain ⟨v', hv'_def⟩ : ∃ v' : G, v' = (n : G) * v₀ * (n : G)⁻¹ := ⟨_, rfl⟩
  have hv'N : v' ∈ N := by
    rw [hv'_def]
    exact N.mul_mem (N.mul_mem n.2 hv₀N) (N.inv_mem n.2)
  have hv'2 : v' * v' = 1 := by
    have h1 : v' * v' = (n : G) * (v₀ * v₀) * (n : G)⁻¹ := by
      rw [hv'_def]; group
    rw [h1, hv₀, mul_one, mul_inv_cancel]
  have hv'π : Ψ.π ⟨v', hv'N⟩ = Ψ.π ⟨i, hiN⟩ := by
    have hsub : (⟨v', hv'N⟩ : N) = n * ⟨v₀, hv₀N⟩ * n⁻¹ :=
      Subtype.ext hv'_def
    rw [hsub, map_mul, map_mul, map_inv, hn]
    exact ha
  obtain ⟨f, hf, hfi⟩ := Ψ.exists_conj_mem_E_of_coset hiN hv'N hi hv'2 hiE hv'π
  have hv'z : (n : G) * g₀ * z * ((n : G) * g₀)⁻¹ = v' := by
    calc (n : G) * g₀ * z * ((n : G) * g₀)⁻¹
        = (n : G) * (g₀ * z * g₀⁻¹) * (n : G)⁻¹ := by group
      _ = v' := by rw [hg₀, hv'_def]
  refine ⟨f⁻¹ * ((n : G) * g₀), ?_⟩
  calc f⁻¹ * ((n : G) * g₀) * z * (f⁻¹ * ((n : G) * g₀))⁻¹
      = f⁻¹ * (((n : G) * g₀) * z * ((n : G) * g₀)⁻¹) * f := by group
    _ = f⁻¹ * v' * f := by rw [hv'z]
    _ = i := by rw [← hfi]; group

end KuA6Model

end CFSG.GH74.QTGen4.Ku
