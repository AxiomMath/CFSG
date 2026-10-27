module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCentrality

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section ExclTools

variable {G : Type*} [Group G]

theorem cj_thompsonJ_eq [Finite G] {D : Subgroup G} {a : G} (hD : cj D a = D) :
    cj (thompsonJ D) a = thompsonJ D := by
  have key : thompsonJ D ≤ cj (thompsonJ D) a⁻¹ := by
    refine thompsonJ_le_of_forall fun A hA x hx => ?_
    have h1 : IsMaxElemAbelian D (cj A a) := by
      have := isMaxElemAbelian_cj a hA
      rwa [hD] at this
    have h2 : cj A a ≤ thompsonJ D := maxElem_le_thompsonJ h1
    rw [mem_cj]
    have : a⁻¹ * x * a⁻¹⁻¹ ∈ cj A a := by
      rw [mem_cj]; simpa [mul_assoc] using hx
    exact h2 this
  have heq : thompsonJ D = cj (thompsonJ D) a⁻¹ := Subgroup.eq_of_le_of_card_ge key card_cj.le
  calc cj (thompsonJ D) a = cj (cj (thompsonJ D) a⁻¹) a := by rw [← heq]
    _ = thompsonJ D := cj_cj_inv

theorem exists_ne_zero_mem_submodule {k : Type*} [Field k] (p : ℙ k (Fin 2 → k)) :
    ∃ w ∈ p.submodule, w ≠ 0 := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, p = Projectivization.mk k v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  exact ⟨v, by rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v, hv⟩

theorem smul_point_eq_of_mem {k : Type*} [Field k] {p : ℙ k (Fin 2 → k)}
    {g : Matrix.SpecialLinearGroup (Fin 2) k} {w : Fin 2 → k} (hw0 : w ≠ 0)
    (hw : w ∈ p.submodule) (hgw : g • w ∈ p.submodule) : g • p = p := by
  have hgw0 : g • w ≠ 0 := by
    intro h0
    apply hw0
    have := congrArg (fun x => g⁻¹ • x) h0
    simpa using this
  have e1 := eq_mk_of_mem_submodule hw0 hw
  have e2 := eq_mk_of_mem_submodule hgw0 hgw
  calc g • p = g • Projectivization.mk k w hw0 := by rw [← e1]
    _ = Projectivization.mk k (g • w) hgw0 := Projectivization.smul_mk g hw0
    _ = p := e2.symm

section Seed

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem normalizer_Zfix_le_Mnorm {y : G} (hy : y ∈ Subgroup.normalizer (Zfix S : Set G)) :
    y ∈ Mnorm S ρ := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  rw [mem_Mnorm_iff hℓ]
  obtain ⟨s₀, hs₀S, hs₀Q⟩ := h.not_sylow_le_core
  have hT1 := (h.natural_module_facts hℓ).1
  have hψZ : ∀ z : Ecore G, (z : G) ∈ Zfix S → Multiplicative.toAdd (ψ z) ∈ ℓ.submodule := by
    intro z hz
    refine (hT1 s₀ hs₀S hs₀Q z hz.1).mp ?_
    have := IsSeed.Zfix_central hz hs₀S
    show s₀ * (z : G) * s₀⁻¹ = z
    rw [this]; group
  obtain ⟨w, hwℓ, hw0⟩ := exists_ne_zero_mem_submodule ℓ
  obtain ⟨e, heV, heψ⟩ := h.ψ_Vmod_surj (Multiplicative.ofAdd w)
  have heZ : (e : G) ∈ Zfix S := by
    refine ⟨heV, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    by_cases hsQ : s ∈ CFSG.pCore 2 G
    · exact Ecore_commute_core hsQ e.2
    · have := (hT1 s hs hsQ e heV).mpr (by rw [heψ]; exact hwℓ)
      calc s * (e : G) = (s * e * s⁻¹) * s := by group
        _ = e * s := by rw [this]
  have hye : y * (e : G) * y⁻¹ ∈ Zfix S := (Subgroup.mem_normalizer_iff.mp hy e).mp heZ
  set e' : Ecore G := ⟨y * e * y⁻¹, (inferInstance : (Ecore G).Normal).conj_mem e e.2 y⟩
  have h1 := h.ψ_equiv y e e' rfl
  have h2 : Multiplicative.toAdd (ψ e') = ρ y • w := by
    rw [Matrix.SpecialLinearGroup.smul_def, h1, heψ]; rfl
  have hρw : ρ y • w ∈ ℓ.submodule := by rw [← h2]; exact hψZ e' hye
  exact smul_point_eq_of_mem hw0 hwℓ hρw

theorem Hone_le_of_mem_not_Mnorm {J : Subgroup G} (hTJ : thompsonJ (S : Subgroup G) ≤ J) {d : G}
    (hdJ : d ∈ J) (hdM : d ∉ Mnorm S ρ) : Hone S ≤ J := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  obtain ⟨hmapA, -⟩ := h.max_outside hA hAQ
  have hne : ℓ ≠ ρ d • ℓ := fun e => hdM ((mem_Mnorm_iff hℓ).mpr e.symm)
  refine Hone_le_of_sup_core_eq_top hTJ (h.sup_core_eq_top hne ?_ ?_)
  · rw [← hℓ, ← hmapA]
    exact Subgroup.map_mono fun a ha => hTJ (maxElem_le_thompsonJ hA ha)
  · rw [rootGrp_smul_eq_map, ← hℓ, ← hmapA]
    rintro _ ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨d * a * d⁻¹, J.mul_mem (J.mul_mem hdJ (hTJ (maxElem_le_thompsonJ hA ha)))
      (J.inv_mem hdJ), by simp [map_mul, map_inv]⟩

open scoped commutatorElement in
theorem commutator_Hone_le_of_not_Mnorm (α : (S : Subgroup G) ≃* (S : Subgroup G))
    {d : G} (hdM : d ∉ Mnorm S ρ)
    (hd : ∀ f ∈ aimg (S : Subgroup G) α (Fcore G), d * f * d⁻¹ * f⁻¹ ∈ Fcore G) :
    ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G := by
  have hNV : ∀ n ∈ (⊤ : Subgroup G), ∀ v ∈ Fcore G, n * v * n⁻¹ ∈ Fcore G :=
    fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n
  set J := commModIn (aimg (S : Subgroup G) α (Fcore G)) (Fcore G) ⊤ hNV with hJ
  have hZaF : aimg (S : Subgroup G) α (Zfix S) ≤ Fcore G := h.aimg_Zfix_le_Fcore α
  have hTJ : thompsonJ (S : Subgroup G) ≤ J := by
    intro t ht
    refine ⟨trivial, fun f hf => ?_⟩
    have h1 : t * f * t⁻¹ * f⁻¹ ∈ (⁅thompsonJ (S : Subgroup G),
        aimg (S : Subgroup G) α (Fcore G)⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ht hf
    rw [h.commutator_thompsonJ_aimg_Fcore α] at h1
    have h2 := (Fcore G).inv_mem (hZaF h1)
    have e : ⁅f, t⁆ = (t * f * t⁻¹ * f⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]; exact h2
  have hdJ : d ∈ J := by
    refine ⟨trivial, fun f hf => ?_⟩
    have e : ⁅f, d⁆ = (d * f * d⁻¹ * f⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]; exact (Fcore G).inv_mem (hd f hf)
  have hH := h.Hone_le_of_mem_not_Mnorm hTJ hdJ hdM
  rw [Subgroup.commutator_le]
  intro y hy f hf
  have e : ⁅y, f⁆ = ⁅f, y⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Fcore G).inv_mem ((hH hy).2 f hf)

theorem mem_core_of_mem_Mnorm_of_mem_cj {g d : G} (hgM : g ∉ Mnorm S ρ)
    (hd : d ∈ cj (S : Subgroup G) g) (hdM : d ∈ Mnorm S ρ) : d ∈ CFSG.pCore 2 G := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hs : g * d * g⁻¹ ∈ (S : Subgroup G) := mem_cj.mp hd
  have hu : ρ (g * d * g⁻¹) ∈ rootGrp ℓ := by rw [← hℓ]; exact ⟨_, hs, rfl⟩
  rw [mem_Mnorm_iff hℓ] at hdM
  have hfix : ρ (g * d * g⁻¹) • (ρ g • ℓ) = ρ g • ℓ := by
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul, hdM]
  by_cases h1 : ρ (g * d * g⁻¹) = 1
  · have hx : g * d * g⁻¹ ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨hs, h1⟩
    rw [h.sylow_inf_ker] at hx
    have := (CFSG.pCore_normal (G := G) (p := 2)).conj_mem _ hx g⁻¹
    simpa [mul_assoc] using this
  · exfalso
    apply hgM
    rw [mem_Mnorm_iff hℓ]
    exact eq_of_smul_eq_of_mem_rootGrp hu h1 hfix

end IsSeed

end Seed

end ExclTools

end CFSG.QuasithinUnique.Setup.Campbell
