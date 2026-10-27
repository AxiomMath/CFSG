module

public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.RankThree.PartOne.SEITZ3

theorem exists_conj_le_of_sylow_torsion {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) {T E : Subgroup G} (hST : (S₀ : Subgroup G) ≤ T)
    (hE : ∀ x ∈ T, x ^ p = 1 → x ∈ E) {F : Subgroup G} (hF : ∀ x ∈ F, x ^ p = 1) :
    ∃ h : G, ∀ x ∈ F, h⁻¹ * x * h ∈ E := by
  have hFp : IsPGroup p F := fun ⟨x, hx⟩ => ⟨1, by
    apply Subtype.ext
    simpa using hF x hx⟩
  obtain ⟨S', hS'⟩ := hFp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S₀ S'
  refine ⟨h, fun x hx => ?_⟩
  have hx' : x ∈ (S' : Subgroup G) := hS' hx
  rw [← hh, Sylow.coe_subgroup_smul] at hx'
  have h1 : h⁻¹ * x * h ∈ (S₀ : Subgroup G) := by
    have := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hx'
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  refine hE _ (hST h1) ?_
  have hxp := hF x hx
  calc (h⁻¹ * x * h) ^ p = h⁻¹ * x ^ p * h := by
        simpa [inv_inv] using conj_pow (a := h⁻¹) (b := x) (i := p)
    _ = 1 := by rw [hxp]; simp

theorem exists_conj_le_of_sylow_torsion_modGL {M : Type*} [Group M] {p : ℕ} [Fact p.Prime]
    {Γ T E : Subgroup M} [Finite Γ] (S₀ : Sylow p ↥Γ) (hST : (S₀ : Subgroup ↥Γ) ≤ T.subgroupOf Γ)
    (hE : ∀ x ∈ T, x ^ p = 1 → x ∈ E) {F : Subgroup M} (hFΓ : F ≤ Γ)
    (hF : ∀ x ∈ F, x ^ p = 1) : ∃ h ∈ Γ, F.map (MulAut.conj h).toMonoidHom ≤ E := by
  obtain ⟨h, hh⟩ := exists_conj_le_of_sylow_torsion S₀ (T := T.subgroupOf Γ)
    (E := E.subgroupOf Γ) hST (fun x hx hxp => hE _ hx (by simpa using congrArg Subtype.val hxp))
    (F := F.subgroupOf Γ) (fun x hx => Subtype.ext (by simpa using hF _ hx))
  refine ⟨((h⁻¹ : ↥Γ) : M), (h⁻¹).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmem := hh ⟨x, hFΓ hx⟩ hx
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
