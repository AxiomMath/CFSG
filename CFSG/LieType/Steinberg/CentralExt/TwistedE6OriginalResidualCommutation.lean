module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalFieldLangSquare
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalReflectionCommutation
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalRecipeSourceSquare
set_option linter.style.haveILetI false
public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE8F
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag Tag.rank

set_option backward.isDefEq.respectTransparency false in
theorem TwE6ToralCoords.original_residuals_commute_of_odd_kernel
    {n : ℕ} {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X) (hodd : Odd (Nat.card ψ.ker))
    {r s : MulAut Bs} {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hne : α ≠ β) (hneg : α ≠ -β)
    (hr : ∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b)))
    (hs : ∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β (Multiplicative.toAdd (κ b)))
    (hHr : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (hHs : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
      ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (hcomm : r * s = s * r) :
    ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs s, a * b = b * a := by
  have h0 := hκ.iform_eq_zero_of_original_reflections_commute hα hβ hne hneg hr hs hcomm
  obtain ⟨ι, e, g, M, ζ0, hζ0, he, hMg, hMw, hζ0o, mu, hmu, hμΓ, hact, hmark⟩ :=
    hκ.exists_original_field_lang_residual_square hn hK h3 hσ hψ hker hodd
  let Hr := MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)
  let Hs := MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)
  let ar := fun b : ↥Hr => zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ (b : Bs)))
  let as := fun b : ↥Hs => zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ (b : Bs)))
  have hkr : famKernel (Set.range ar) = {α, -α} := hκ.famKernel_ggHyperplane hα hHr hζ0 hζ0o
  have hks : famKernel (Set.range as) = {β, -β} := hκ.famKernel_ggHyperplane hβ hHs hζ0 hζ0o
  have ht (v : Fin Tag.E6.rank → ZMod 3) :
      ∃ k : ℕ, zetaVec (τ := Tag.E6) ζ0 hζ0 v ^ (3 ^ k) = 1 := by
    refine ⟨1, ?_⟩
    apply funext
    intro i
    simp only [Pi.pow_apply, Pi.one_apply, pow_one, zetaVec_apply]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ0, one_pow]
  have horth : ∀ u ∈ famKernel (Set.range ar), ∀ v ∈ famKernel (Set.range as),
      dotProduct u (Matrix.mulVec Tag.E6.symmetrizedCartan v) = 0 := by
    intro u hu v hv
    rw [hkr] at hu
    rw [hks] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv, dotProduct_mulVec_eq_iform]
      exact h0
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_right (τ := Tag.E6), h0, neg_zero]
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_left (τ := Tag.E6), h0, neg_zero]
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_left (τ := Tag.E6),
        CFSG.LieType.Chevalley.iform_neg_right (τ := Tag.E6), h0, neg_zero, neg_zero]
  have hΓadj : M.D.Γ ≤ adjointGroup Tag.E6 GGL :=
    (Subgroup.commutator_le_self M.D.model).trans inf_le_left
  have hc := ResidualA2Pair.commutation_of_orthogonal_families
    (Or.inr (Or.inl rfl)) Nat.prime_three (by decide) ar as
    (fun b => ht _) (fun b => ht _) M.D.Γ hΓadj horth
  have hμker : mu.ker = ψ.ker := by
    rw [hmu, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj M.D.g0).symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (baseChangeGL_injective _),
      MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
  let Cr := (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)).subgroupOf X
  let Cs := (X ⊓ Subgroup.centralizer (ggHyperplane Bs s : Set G)).subgroupOf X
  have hR (t : MulAut Bs) : (ggRankOneIn X Bs t).subgroupOf X =
      ggOTwoPrime ((X ⊓ Subgroup.centralizer (ggHyperplane Bs t : Set G)).subgroupOf X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        (show ggRankOneIn X Bs t ≤ X from (ggOTwoPrime_le _).trans inf_le_left),
      ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  have hlift := ggOTwoPrime_commutation_of_map_of_central_odd_kernel mu
    (hμker.symm ▸ hker) (hμker.symm ▸ hodd) Cr Cs (by
      intro u hu v hv
      rw [← hR r, hmark r] at hu
      rw [← hR s, hmark s] at hv
      exact hc u hu v hv)
  have hrmap : (ggOTwoPrime Cr).map X.subtype = ggRankOneIn X Bs r := by
    dsimp only [Cr]
    rw [ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
    rfl
  have hsmap : (ggOTwoPrime Cs).map X.subtype = ggRankOneIn X Bs s := by
    dsimp only [Cs]
    rw [ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
    rfl
  intro x hx y hy
  rw [← hrmap] at hx
  rw [← hsmap] at hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
  exact congrArg (fun z : ↥X => (z : G)) (hlift u hu v hv)

set_option backward.isDefEq.respectTransparency false in
theorem TwE6CoverData.original_residuals_commute
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords D.lab.n D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α β : Fin Tag.E6.rank → ℤ),
      IsRoot Tag.E6 α → IsRoot Tag.E6 β → α ≠ β → α ≠ -β →
      (∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
        ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b))) →
      (∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) =
        ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β (Multiplicative.toAdd (κ b))) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      r * s = s * r →
      ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs s, a * b = b * a := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ r s α β hα hβ hne hneg hr hs hHr hHs hcomm
  exact hκ.original_residuals_commute_of_odd_kernel D.hn D.hK D.h3 D.hσ D.hψ
    (le_of_eq D.hker) (D.psi_odd_kernel hn3) hα hβ hne hneg hr hs hHr hHs hcomm

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
