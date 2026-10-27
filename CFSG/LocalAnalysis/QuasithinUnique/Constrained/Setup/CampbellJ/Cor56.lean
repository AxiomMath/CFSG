module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.Quasithin.Background.C118TwoSeeds

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem aimg_mul_J {G : Type*} [Group G] {T : Subgroup G} (δ ε : T ≃* T)
    (Y : Subgroup G) (hY : Y ≤ T) : aimg T (δ * ε) Y = aimg T δ (aimg T ε Y) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := mem_aimg.mp hx
    refine mem_aimg.mpr ⟨ε y, mem_aimg.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [← hxy]
    rfl
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_aimg.mp hx
    obtain ⟨y, hy, hyz⟩ := mem_aimg.mp hz
    refine mem_aimg.mpr ⟨y, hy, ?_⟩
    have hzy : z = ε y := Subtype.ext hyz.symm
    rw [hzy]
    rfl

private theorem aimg_conj_eq_cj_J {G : Type*} [Group G] {T : Subgroup G} {β : T ≃* T} {x : G}
    (hβ : ∀ y : T, ((β y : T) : G) = x⁻¹ * (y : G) * x) (Y : Subgroup G) (hY : Y ≤ T) :
    aimg T β Y = cj Y x := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hz
    rw [mem_cj, hβ y]
    have : x * (x⁻¹ * (y : G) * x) * x⁻¹ = (y : G) := by group
    rw [this]
    exact hy
  · intro hz
    rw [mem_cj] at hz
    refine mem_aimg.mpr ⟨⟨x * z * x⁻¹, hY hz⟩, hz, ?_⟩
    rw [hβ]
    group

theorem aimgJ_Fcore_normal_of_lamHyp (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Hone S) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) x =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  change cj (aimg T α (Fcore G)) x = aimg T α (Fcore G)
  by_contra hneq
  have hFα : aimg T α (Fcore G) ≠ Fcore G := fun heq =>
    hneq (by rw [heq, cj_eq_self_of_normal (Y := Fcore G)])
  obtain ⟨β, hβΛ, hβact⟩ := hΛ.inner x hx
  set γ : MulAut T := α⁻¹ * β * α with hγdef
  have hγmem : γ ∈ Λ := by
    rw [hγdef]
    exact Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hα) hβΛ) hα
  have hFγ : aimg T γ (Fcore G) ≠ Fcore G := by
    intro heq
    have hαγ : α * γ = β * α := by rw [hγdef]; group
    have h1 : aimg T α (aimg T γ (Fcore G)) = aimg T α (Fcore G) := by rw [heq]
    rw [← aimg_mul_J α γ (Fcore G) (Fcore_le_JS h), hαγ,
      aimg_mul_J β α (Fcore G) (Fcore_le_JS h),
      aimg_conj_eq_cj_J hβact (aimg T α (Fcore G)) aimg_le] at h1
    exact hneq h1
  have hZα := aimgJ_Zfix_le_center_Hone h α (hΛ.vmod α hα) hFα
  have hZγ := aimgJ_Zfix_le_center_Hone h γ (hΛ.vmod γ hγmem) hFγ
  have hcjZα : cj (aimg T α (Zfix S)) x = aimg T α (Zfix S) := by
    apply cj_eq_of_forall_mem
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (Hone S : Set G) := (hZα hz).2
    have hcomm := Subgroup.mem_centralizer_iff.mp hzc x hx.2
    have : x * z * x⁻¹ = z := by rw [hcomm]; group
    rwa [this]
  have hZγeq : aimg T γ (Zfix S) = Zfix S := by
    rw [hγdef]
    rw [aimg_mul_J (α⁻¹ * β) α (Zfix S) (Zfix_le_JS h),
      aimg_mul_J α⁻¹ β (aimg T α (Zfix S)) aimg_le,
      aimg_conj_eq_cj_J hβact (aimg T α (Zfix S)) aimg_le, hcjZα]
    exact aimg_symm_aimg (α := α) (Zfix_le_JS h)
  have hZcent : Zfix S ≤ Subgroup.centralizer (Hone S : Set G) := by
    intro z hz
    rw [← hZγeq] at hz
    exact (hZγ hz).2
  have hZfixH : Zfix S ≤ Hone S := (Zfix_le_JS h).trans Subgroup.le_normalClosure
  exact h.not_Zfix_le_center (h.le_center_of_le_Hone (le_inf hZfixH hZcent)
    fun s hs z hz => IsSeed.Zfix_central hz hs)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
