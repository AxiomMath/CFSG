module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AA4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL48B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma normalizer_le_normalizer_centralizer {G : Type*} [Group G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((centralizer (H : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have hkey : ∀ {k : G}, k ∈ normalizer (H : Set G) →
      ∀ x ∈ centralizer (H : Set G), k * x * k⁻¹ ∈ centralizer (H : Set G) := by
    intro k hk x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hky : k⁻¹ * y * k ∈ H := by
      have h1 := (Subgroup.mem_set_normalizer_iff.mp
        ((normalizer (H : Set G)).inv_mem hk) y).mp hy
      simpa using h1
    calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [hx (k⁻¹ * y * k) hky]
      _ = (k * x * k⁻¹) * y := by group
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨hkey hg x, fun hx => ?_⟩
  have hmem := hkey ((normalizer (H : Set G)).inv_mem hg) (g * x * g⁻¹) hx
  have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [heq] at hmem

theorem exists_adjust_of_conj (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {u : G} (hu : u = tau ∨ u = t * tau) (hg : ∃ g : G, g * u * g⁻¹ = t) :
    ∃ g ∈ ctxM t tau x₁ x₂ ⊓ normalizer ((closure {t, tau} : Subgroup G) : Set G),
      g * u * g⁻¹ = t ∧
      g ∈ centralizer ((closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) : Set G) := by
  set V : Subgroup G := closure {t, tau} with hVdef
  set Sig : Subgroup G := closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} with hSigdef
  set A : Subgroup G := closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} with hAdef
  set W : Subgroup G := closure {x₁ ^ 2, (x₁ * x₂) ^ 2} with hWdef
  obtain ⟨g₀, hg₀conj, hg₀N⟩ := exists_normalizer_V_of_conj h h43 h44 hu hg
  obtain ⟨hcent_eq, hAB, _hcard, hinf, hcomm⟩ := centralizer_t_tau_of h h43 h44
  have hcent_eq' : centralizer (V : Set G) = V ⊔ Sig := hcent_eq
  have hcomm' : ∀ v ∈ V, ∀ s ∈ Sig, v * s = s * v := hcomm
  have hinf' : V ⊓ Sig = ⊥ := hinf
  have hV : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    simpa [pow_two] using hAB.2 v hv
  have hSig_eq : L ⊓ centralizer ({tau} : Set G) = Sig := by
    rw [hSigdef]; exact h.cent_L_tau
  have hA_eq : A = oddOrderGrp Sig := by
    rw [hAdef, closure_y_z_rho_eq_oddOrderGrp h, hSig_eq]
  obtain ⟨e₄⟩ := h.perm_four
  have hφ : ↥Sig ≃* Equiv.Perm (Fin 4) :=
    (MulEquiv.subgroupCongr hSig_eq).symm.trans e₄
  have hsup_cent : V ⊔ Sig = centralizer (V : Set G) := hcent_eq'.symm
  have hg₀N' : g₀ ∈ normalizer ((V ⊔ Sig : Subgroup G) : Set G) := by
    rw [hsup_cent]
    exact (normalizer_le_normalizer_centralizer V) hg₀N
  obtain ⟨σ, hσSig, hσcent⟩ :=
    exists_mul_centralizes_oddOrderGrp (V := V) (Sig := Sig) hcomm' hinf' hV hφ hg₀N'
  have huV : u ∈ V := by
    rcases hu with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hσu : σ * u = u * σ := (hcomm' u huV σ hσSig).symm
  have hσt : σ * t = t * σ := (hcomm' t htV σ hσSig).symm
  have hconj : (σ * g₀) * u * (σ * g₀)⁻¹ = t := by
    calc (σ * g₀) * u * (σ * g₀)⁻¹
        = σ * (g₀ * u * g₀⁻¹) * σ⁻¹ := by group
      _ = σ * t * σ⁻¹ := by rw [hg₀conj]
      _ = t := by rw [hσt]; group
  have hgCentA : (σ * g₀) ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ oddOrderGrp Sig := hA_eq ▸ ha
    have h1 := hσcent a ha'
    calc a * (σ * g₀) = ((σ * g₀) * a * (σ * g₀)⁻¹) * (σ * g₀) := by rw [h1]
      _ = (σ * g₀) * a := by group
  have hSig_le_cent : Sig ≤ centralizer (V : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hcomm' v hv s hs
  have hσN : σ ∈ normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G) (hSig_le_cent hσSig)
  have hgN : (σ * g₀) ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem hσN hg₀N
  have hW_le_A : W ≤ A := by
    rw [hWdef, hAdef]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp
  have hgCentW : (σ * g₀) ∈ centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hgCentA ⊢
    intro w hw
    exact hgCentA w (hW_le_A hw)
  have hgW : (σ * g₀) ∈ normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer (W : Set G) hgCentW
  have hVW : V ⊔ W = ctxX t tau x₁ x₂ := by
    show V ⊔ W = closure ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)
    rw [hVdef, hWdef, ← Subgroup.closure_union]
    have hset : ({t, tau} : Set G) ∪ {x₁ ^ 2, (x₁ * x₂) ^ 2} =
        {t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
  have hgM : (σ * g₀) ∈ ctxM t tau x₁ x₂ := by
    show (σ * g₀) ∈ normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G)
    rw [← hVW]
    exact (Subgroup.inf_normalizer_le_normalizer_sup V W) ⟨hgN, hgW⟩
  exact ⟨σ * g₀, ⟨hgM, hgN⟩, hconj, hgCentA⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
