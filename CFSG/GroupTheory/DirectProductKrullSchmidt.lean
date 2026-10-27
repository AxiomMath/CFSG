module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
public import CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Dec

public section

namespace CFSG.SignalizerFunctorTheorem.McBride

open Subgroup CFSG.Quasithin

variable {Γ : Type*} [Group Γ]

private theorem centreless_factors_permuted {X : Type*} [Group X] [Finite X] {ι : Type*}
    [Finite ι] {Xs : ι → Subgroup X} (h : IsIndexedDirectProduct Xs)
    (hind : ∀ i, IsIndecomposableGroup ↥(Xs i)) (hZ : Subgroup.center X = ⊥)
    (α : MulAut X) : ∃ τ : Equiv.Perm ι, ∀ i, (Xs i).map α.toMonoidHom = Xs (τ i) := by
  obtain ⟨τ, hτ⟩ := krull_schmidt_aut_permutes h hind α
  exact ⟨τ, fun i => by simpa [hZ] using hτ i⟩

private theorem isIndexedDirectProduct_subgroupOf [Finite Γ] {S : Set (Subgroup Γ)}
    {N : Subgroup Γ} (h : IsDirectProduct S N) (Xs : ↥S → Subgroup ↥N)
    (hXs : ∀ i : ↥S, Xs i = (i.1 : Subgroup Γ).subgroupOf N) :
    IsIndexedDirectProduct Xs :=
  haveI : Fintype (↥S) := Fintype.ofFinite (↥S); by
  classical
  have hnormal : ∀ i : ↥S, (Xs i).Normal := fun i => by
    rw [hXs i]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (h.le i.2)).mpr (h.le_normalizer i.2)
  have hindep : iSupIndep Xs := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hle : (⨆ (j : ↥S) (_ : j ≠ i), Xs j) ≤ (sSup (S \ {i.1})).subgroupOf N := by
      refine iSup₂_le fun j hj => ?_
      rw [hXs j]
      exact Subgroup.subgroupOf_mono N
        (le_sSup (s := S \ {i.1}) ⟨j.2, fun hh => hj (Subtype.ext hh)⟩)
    have hx1 : (x : Γ) ∈ (i.1 : Subgroup Γ) := by
      rw [hXs i] at hx
      exact hx.1
    have hx2 : (x : Γ) ∈ sSup (S \ {i.1}) := hle hx.2
    have hd := h.indep i.2
    rw [disjoint_iff] at hd
    have : (x : Γ) ∈ (i.1 : Subgroup Γ) ⊓ sSup (S \ {i.1}) := ⟨hx1, hx2⟩
    rw [hd] at this
    exact Subtype.ext (by simpa using this)
  have htop : (⨆ i : ↥S, Xs i) = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup]
    have hcongr : (⨆ i : ↥S, (Xs i).map N.subtype) = ⨆ i : ↥S, (i.1 : Subgroup Γ) :=
      iSup_congr fun i => by rw [hXs i]; exact Subgroup.map_subgroupOf_eq_of_le (h.le i.2)
    rw [hcongr, ← sSup_eq_iSup', h.sSup_eq, ← Subgroup.subgroupOf_self N,
      Subgroup.map_subgroupOf_eq_of_le le_rfl]
  exact ⟨hnormal, hindep, htop⟩

private theorem center_subgroupOf_eq_bot [Finite Γ] {S : Set (Subgroup Γ)} {N : Subgroup Γ}
    (h : IsDirectProduct S N) (hZ : ∀ A ∈ S, center ↥A = ⊥) (Xs : ↥S → Subgroup ↥N)
    (hXs : ∀ i : ↥S, Xs i = (i.1 : Subgroup Γ).subgroupOf N)
    (hdirect : IsIndexedDirectProduct Xs) : Subgroup.center ↥N = ⊥ :=
  haveI : Fintype (↥S) := Fintype.ofFinite (↥S); by
  classical
  have hcenterXs : ∀ i : ↥S, Subgroup.center ↥(Xs i) = ⊥ := fun i => by
    rw [hXs i]
    exact CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3.Sigma3Dec.center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (h.le i.2)) (fun y hy => by
        have hyc : y ∈ Subgroup.center ↥(i.1) :=
          Subgroup.mem_center_iff.mpr (fun g => (hy g).symm)
        rw [hZ i.1 i.2] at hyc
        simpa using hyc)
  have hcomm : Pairwise fun i j : ↥S => ∀ x y : ↥N, x ∈ Xs i → y ∈ Xs j → Commute x y := by
    intro i j hij x y hx hy
    rw [hXs i] at hx
    rw [hXs j] at hy
    rw [commute_iff_eq]
    exact Subtype.ext
      ((h.commute i.1 i.2 j.1 j.2 (fun hh => hij (Subtype.ext hh)) x.1
        (Subgroup.mem_subgroupOf.mp hx) y.1 (Subgroup.mem_subgroupOf.mp hy)).eq)
  let F : (∀ i : ↥S, ↥(Xs i)) →* ↥N := Subgroup.noncommPiCoprod (H := Xs) hcomm
  have hinj : Function.Injective F :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := Xs) (hcomm := hcomm) hdirect.independent
  have hrange : F.range = ⊤ := by
    rw [show F.range = ⨆ i : ↥S, Xs i from
      Subgroup.noncommPiCoprod_range (H := Xs) (hcomm := hcomm)]
    exact hdirect.iSup_eq_top
  have hsurj : Function.Surjective F := fun y => by
    have hy : y ∈ F.range := by rw [hrange]; trivial
    rwa [MonoidHom.mem_range] at hy
  let e : ↥N ≃* (∀ i : ↥S, ↥(Xs i)) := (MulEquiv.ofBijective F ⟨hinj, hsurj⟩).symm
  have hcenterPi : Subgroup.center (∀ i : ↥S, ↥(Xs i)) = ⊥ := by
    rw [Subgroup.center_pi, Subgroup.pi_eq_bot_iff]
    exact hcenterXs
  exact CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3.Sigma3Dec.center_eq_bot_of_mulEquiv e
    (fun y hy => by
      have hyc : y ∈ Subgroup.center (∀ i : ↥S, ↥(Xs i)) :=
        Subgroup.mem_center_iff.mpr (fun g => (hy g).symm)
      rw [hcenterPi] at hyc
      simpa using hyc)

theorem IsDirectProduct.map_conj_mem [Finite Γ] {S : Set (Subgroup Γ)} {N : Subgroup Γ}
    (h : IsDirectProduct S N) (hind : ∀ A ∈ S, IsIndecomposableGroup ↥A)
    (hZ : ∀ A ∈ S, center ↥A = ⊥) {g : Γ} (hg : g ∈ normalizer (N : Set Γ)) {A : Subgroup Γ}
    (hA : A ∈ S) : A.map (MulAut.conj g).toMonoidHom ∈ S := by
  classical
  let Xs : ↥S → Subgroup ↥N := fun i => (i.1 : Subgroup Γ).subgroupOf N
  have hXs : ∀ i : ↥S, Xs i = (i.1 : Subgroup Γ).subgroupOf N := fun _ => rfl
  have hdirect : IsIndexedDirectProduct Xs := isIndexedDirectProduct_subgroupOf h Xs hXs
  have hZ' : Subgroup.center ↥N = ⊥ := center_subgroupOf_eq_bot h hZ Xs hXs hdirect
  have hind' : ∀ i : ↥S, IsIndecomposableGroup ↥(Xs i) := fun i =>
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3.Sigma3Dec.isIndecomposableGroup_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (h.le i.2)) (hind i.1 i.2)
  let α : MulAut ↥N := N.normalizerMonoidHom ⟨g, hg⟩
  have hα : ∀ t : ↥N, ((α t : ↥N) : Γ) = g * t * g⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe N ⟨g, hg⟩ t
  obtain ⟨τ, hτ⟩ := centreless_factors_permuted hdirect hind' hZ' α
  have hcomp : N.subtype.comp α.toMonoidHom = (MulAut.conj g).toMonoidHom.comp N.subtype := by
    ext x
    change N.subtype (α x) = MulAut.conj g (N.subtype x)
    rw [MulAut.conj_apply]
    exact hα x
  have hkey : ∀ i : ↥S, ((Xs i).map α.toMonoidHom).map N.subtype =
      (i.1).map (MulAut.conj g).toMonoidHom := by
    intro i
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hXs i,
      Subgroup.map_subgroupOf_eq_of_le (h.le i.2)]
  have h1 := congrArg (Subgroup.map N.subtype) (hτ ⟨A, hA⟩)
  rw [hkey ⟨A, hA⟩] at h1
  rw [hXs (τ ⟨A, hA⟩), Subgroup.map_subgroupOf_eq_of_le (h.le (τ ⟨A, hA⟩).2)] at h1
  rw [h1]
  exact (τ ⟨A, hA⟩).2

end CFSG.SignalizerFunctorTheorem.McBride
