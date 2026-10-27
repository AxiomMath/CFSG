module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Set

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fz410x_fz410_fusk_map_centralizer {G : Type} [Group G] (φ : G ≃* G) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((X.map φ.toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have := congrArg φ (h y' hy')
    simpa using this
  · intro h y hy
    have := congrArg φ.symm (h (φ y) ⟨y, hy, rfl⟩)
    simpa using this

theorem fz410x_fz410_fusk_conj_apply {G : Type} [Group G] (k x : G) :
    (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k := by
  change MulAut.conj k⁻¹ x = k⁻¹ * x * k
  rw [MulAut.conj_apply]
  simp

theorem fz410x_fz410_fusk_conj_pow {G : Type} [Group G] (k x : G) (n : ℕ) :
    (k⁻¹ * x * k) ^ n = k⁻¹ * x ^ n * k := by
  simpa using conj_pow (a := k⁻¹) (b := x) (i := n)

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}

theorem fz410x_fz410_fusk_S_eq_T_inf (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P) :
    S = T ⊓ centralizer ({t} : Set G) := by
  have hle : S ≤ T ⊓ centralizer ({t} : Set G) := by
    intro x hx
    exact ⟨D.isT2.S_le hx, show x ∈ centralizer ({t} : Set G) from D.ctx.le_invCent hx⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [D.facts.card_S, D.ctx.card_S, D.card_two]
  norm_num

theorem fz410x_fz410_fusk_sylow (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)
    {e g : G} (he : e ∈ E) (hg : g * t * g⁻¹ = e * (t * s)) :
    ∃ k : G, k * t * k⁻¹ = e * (t * s) ∧
      ∀ x ∈ fz410CR R (e * (t * s)), k⁻¹ * x * k ∈ S := by
  set i : G := e * (t * s) with hi_def
  have hgt : g * t * g⁻¹ = i := by rw [hi_def]; exact hg
  have hfus : Fz410Fus R Z i := D.facts.fus_ets e he
  let C : Subgroup G := fz410CR R i
  have hCR : C ≤ R := inf_le_left
  have hCp : IsPGroup 2 C := D.str.pgroup_T.to_le (hCR.trans D.str.RT)
  let Qg : Subgroup G := C.map (MulAut.conj g⁻¹).toMonoidHom
  have hQH : Qg ≤ invCent t := by
    intro q hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨x, hx, hconj⟩ := hq
    rw [← hconj]
    have hconj' : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by simp [MulAut.conj_apply]
    rw [hconj']
    have hxi : i * x = x * i := (Subgroup.mem_centralizer_iff.mp hx.2) i rfl
    show g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc t * (g⁻¹ * x * g) = g⁻¹ * (g * t * g⁻¹) * x * g := by group
      _ = g⁻¹ * (i * x) * g := by rw [hgt]; group
      _ = g⁻¹ * (x * i) * g := by rw [hxi]
      _ = g⁻¹ * x * (g * t * g⁻¹) * g := by rw [hgt]; group
      _ = (g⁻¹ * x * g) * t := by group
  have hQp : IsPGroup 2 Qg := hCp.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨c, hcH, hcQ⟩ :=
    S4A.exists_conj_le_of_isPGroup hQH hQp D.ctx.le_invCent D.ctx.isPGroup D.ctx.relIndex_odd
  let k : G := g * c⁻¹
  have hct : c⁻¹ * t * c = t := by
    have hc : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hcH) t rfl
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hc]
      _ = t := by group
  have hkt : k * t * k⁻¹ = i := by
    show (g * c⁻¹) * t * (g * c⁻¹)⁻¹ = i
    calc (g * c⁻¹) * t * (g * c⁻¹)⁻¹ = g * (c⁻¹ * t * c) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [hct]
      _ = i := hgt
  have hCkay : ∀ x ∈ C, k⁻¹ * x * k ∈ S := by
    intro x hx
    have hxQ : g⁻¹ * x * g ∈ Qg := by
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      simp [MulAut.conj_apply]
    have h := hcQ (g⁻¹ * x * g) hxQ
    rw [show (g * c⁻¹)⁻¹ * x * (g * c⁻¹) = c * (g⁻¹ * x * g) * c⁻¹ by group]
    exact h
  exact ⟨k, hkt, hCkay⟩

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
