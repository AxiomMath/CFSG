module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF08
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06h

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open scoped Pointwise
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem hfus_I (h3a : ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
      R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ C.D.F.ρ₃.K →
      T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1) {e : G} (heS₀ : e ∉ sZero Ω W S)
    (he2 : e * e = 1) (heR : ∀ v ∈ R, v * e = e * v) (heR' : ∀ v ∈ R', v * e = e * v) (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {e}, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * e * g ∉ sZero Ω W S := by
  intro hx
  have hzR : R ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (centralizes_conj_z (z_mem_S C) hg (C.hd.hR.2.2 hv) (heR v hv))
  have hzh : g * z * g⁻¹ = z := by
    by_contra hne
    exact C.ne_conj_z C.mem C.hRsyl C.hzK hzR hne g rfl
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hzh]
  have hgz' : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hgz
  have hRS : conjSub g⁻¹ R ≤ (S : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    have := hg v ⟨C.hd.hR.2.2 hv, Subgroup.mem_centralizer_singleton_iff.mpr (heR v hv)⟩
    simpa using this
  have hR'S : conjSub g⁻¹ R' ≤ (S : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    have := hg v ⟨C.hd.hR'.2.2 hv, Subgroup.mem_centralizer_singleton_iff.mpr (heR' v hv)⟩
    simpa using this
  set x := g⁻¹ * e * g with hxdef
  have hxc : ∀ v, (v ∈ R ∨ v ∈ R') → v * x = x * v := by
    intro v hv
    have hv' : g * v * g⁻¹ ∈ R ∨ g * v * g⁻¹ ∈ R' := by
      rcases conj_R_cases C hgz' hRS hR'S with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hv with hv | hv
        · left
          rw [← h1, mem_conjSub_iff] at hv
          simpa using hv
        · right
          rw [← h2, mem_conjSub_iff] at hv
          simpa using hv
      · rcases hv with hv | hv
        · right
          rw [← h2, mem_conjSub_iff] at hv
          simpa using hv
        · left
          rw [← h1, mem_conjSub_iff] at hv
          simpa using hv
    have hc : (g * v * g⁻¹) * e = e * (g * v * g⁻¹) := by
      rcases hv' with h | h
      · exact heR _ h
      · exact heR' _ h
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * e) * g := by rw [hxdef]; group
      _ = g⁻¹ * (e * (g * v * g⁻¹)) * g := by rw [hc]
      _ = x * v := by rw [hxdef]; group
  have hx1 : x * C.D.x₁ * x⁻¹ = C.D.x₁ := by
    rw [← hxc _ (Or.inl C.x₁_mem_R)]; group
  have hx2 : x * C.D.x₂ * x⁻¹ = C.D.x₂ := by
    rw [← hxc _ (Or.inr C.x₂_mem_R')]; group
  have hxW := mem_centralizer_W_of_sZero C hx hx1 hx2
  have hxS : x ∈ (S : Subgroup G) := hx.1
  have hxA : x ∈ C.A := by
    refine (C.mem_A).mpr ⟨hxS, hxW, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hxc v (Or.inl hv)
    · exact mem_normalizer_iff_conjSub_eq.mpr (Ctx8Frame.conjSub_eq_of_commute C.hyp C.hK'tw.1
        C.x₂_mem_K' C.orderOf_x₂ (hxc _ (Or.inr C.x₂_mem_R')).symm)
    · exact mem_normalizer_iff_conjSub_eq.mpr (Ctx8Frame.conjSub_eq_of_commute C.hyp
        C.D.F.ρ₃.hK C.x₃_mem_J C.orderOf_x₃
        (Subgroup.mem_centralizer_iff.mp hxW _ C.D.x₃_mem).symm)
  have hxD : x ∈ C.Dg := ⟨hxA, by
    show x ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hxc v (Or.inr hv)⟩
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3a
  have hx2' : x * x = 1 := by
    rw [hxdef]
    calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2]; group
  have he1 : e ≠ 1 := fun h => heS₀ (h ▸ Subgroup.one_mem _)
  have hx1' : x ≠ 1 := by
    intro h
    apply he1
    calc e = g * x * g⁻¹ := by rw [hxdef]; group
      _ = 1 := by rw [h]; group
  have hxz : (⟨x, hxD⟩ : ↥C.Dg) = ⟨z, C.z_mem_Dg⟩ :=
    eq_of_inj_zpowers C.orderOf_x₃ hμ (Subtype.ext hx2') (fun h => hx1' (congrArg Subtype.val h))
      (Subtype.ext C.hzK.sq) (fun h => C.hzK.ne_one (congrArg Subtype.val h))
  have hxz' : x = z := congrArg Subtype.val hxz
  apply heS₀
  have he : e = z := by
    calc e = g * x * g⁻¹ := by rw [hxdef]; group
      _ = z := by rw [hxz', hzh]
  rw [he]
  exact inf_le_sZero (C.W_le_P C.hd.hzW)

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
