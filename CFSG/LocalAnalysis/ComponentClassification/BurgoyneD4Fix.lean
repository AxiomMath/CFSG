module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOResGrp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O (CompData)
open CFSG.ComponentClassification.Burgoyne.PSL (isSubnormal_subgroupOf_of_normalizes
  mul_conj_mul_inv)

theorem fix_closure {T : Type*} [Group T] {y : MulAut T} {s : Set T} (hs : ∀ x ∈ s, y x = x) :
    ∀ x ∈ closure s, y x = x := by
  have hle : closure s ≤ MonoidHom.eqLocus y.toMonoidHom (MonoidHom.id T) := by
    rw [closure_le]
    exact hs
  exact fun x hx => hle hx

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem fix_of_compData [Finite (StatedProj H)]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    {t : MulAut (StatedProj H)} (φ : H →* H) (hφ : ∀ g, t (projH H g) = projH H (φ g))
    {F₀ : Subgroup (GL ι K)} (hF₀H : F₀ ≤ H)
    (hF₀φ : ∀ X (hX : X ∈ F₀), φ ⟨X, hF₀H hX⟩ = ⟨X, hF₀H hX⟩)
    (hF₀n : ∀ h : H, φ h = h → ∀ X ∈ F₀, (h : GL ι K) * X * (h : GL ι K)⁻¹ ∈ F₀)
    (hcd : CompData F₀) {y : MulAut (StatedProj H)} (hy : y ∈ oddCoreIn B t)
    {X : GL ι K} (hX : X ∈ F₀) : y (projH H ⟨X, hF₀H hX⟩) = projH H ⟨X, hF₀H hX⟩ := by
  set F := MonoidHom.eqLocus φ (MonoidHom.id H) with hF
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixedH hinj hB φ hφ (F := F) (fun _ h => h)
    (fun _ hh _ hg => conj_mem_eqLocus_of_scalarH φ hh hg)
  set F₀' := F₀.subgroupOf H with hF₀'
  have hF₀'F : F₀' ≤ F := by
    intro Y hY
    have hY' : (Y : GL ι K) ∈ F₀ := mem_subgroupOf.1 hY
    have e := hF₀φ Y hY'
    change φ Y = Y
    exact e
  have hF₀'sub : ((F₀'.map (conjProjH H)).subgroupOf
      (B ⊓ centralizer ({t} : Set (MulAut (StatedProj H))))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_normalizes (map_mono hF₀'F) ?_ hsub
    rintro _ ⟨f, hf, rfl⟩ _ ⟨z, hz, rfl⟩
    refine ⟨f * z * f⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
    have := hF₀n f hf _ (mem_subgroupOf.1 hz)
    simpa using this
  obtain ⟨-, m, L, hsup, hL⟩ := hcd
  have hfixL : ∀ i, ∀ Y : H, (Y : GL ι K) ∈ L i → y (projH H Y) = projH H Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf H with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans hF₀H)).symm hq
    have hLF : Lh ≤ F₀' := fun Z hZ => mem_subgroupOf.2 (hLI (mem_subgroupOf.1 hZ))
    have hQim := isQuasisimple_map_conjProjH hinj hLhq
    have hQsub : ((Lh.map (conjProjH H)).subgroupOf
        (B ⊓ centralizer ({t} : Set (MulAut (StatedProj H))))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hLF) ?_ hF₀'sub
      rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
      have hx' : (x : GL ι K) ∈ F₀ := mem_subgroupOf.1 hx
      have hl' : (l : GL ι K) ∈ L i := mem_subgroupOf.1 hl
      simpa using hLn _ hx' _ hl'
    have hc := commute_of_mem_pPrimeCore ((map_mono (hLF.trans hF₀'F)).trans hle) hQim hQsub
      (even_card_of_isQuasisimple hQim) hy ⟨Y, mem_subgroupOf.2 hY, rfl⟩
    apply hinj
    rw [← mul_conj_mul_inv]
    change y * conjProjH H Y * y⁻¹ = conjProjH H Y
    rw [hc, mul_inv_cancel_right]
  have hF₀sup : F₀' ≤ MonoidHom.eqLocus (y.toMonoidHom.comp (projH H)) (projH H) := by
    intro Y hY
    have hY' : (Y : GL ι K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf H).map H.subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hF₀H)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z hZ => ?_ : (⨆ i, (L i).subgroupOf H) ≤ _) hY'L
    exact hfixL i Z (mem_subgroupOf.1 hZ)
  exact hF₀sup (mem_subgroupOf.2 hX)

end CFSG.ComponentClassification.Burgoyne.D4
