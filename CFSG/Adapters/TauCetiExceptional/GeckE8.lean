module

public import CFSG.Adapters.TauCetiExceptional.GeckAssembly

public noncomputable section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint.Chevalley Matrix

namespace GeckE8

@[expose] def normCheck : Bool :=
  (List.range e8Certificate.roots.length).all fun k =>
    (e8Certificate.root k ᵥ* CartanMatrix.E 8) ⬝ᵥ e8Certificate.root k == 2

theorem normCheck_eq_true : normCheck = true := by
  decide +kernel

theorem norm_eq_two {v : Fin 8 → ℤ} (hv : IsRoot .E8 v) :
    (v ᵥ* CartanMatrix.E 8) ⬝ᵥ v = 2 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e8Certificate_check hv
  have h := normCheck_eq_true
  simp only [normCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h k hk

theorem isRoot_e8Coroot
    (j : Fin 240) : IsRoot .E8 (DynkinType.e8Coroot j) := by
  let ψ : {v : Fin Tag.E8.rank → ℤ // IsRoot .E8 v} → Fin 240 := fun v =>
    (DynkinType.exists_e8Coroot_eq (norm_eq_two v.2)).choose
  have hψ : ∀ v, DynkinType.e8Coroot (ψ v) = v.1 := fun v =>
    (DynkinType.exists_e8Coroot_eq (norm_eq_two v.2)).choose_spec
  have hbij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun v w h => Subtype.ext (by rw [← hψ v, ← hψ w, h]), ?_⟩
    rw [card_isRoot, Fintype.card_fin]
    rfl
  obtain ⟨v, rfl⟩ := hbij.2 j
  rw [hψ]
  exact v.2

theorem root_eq (j : Fin 240) (l : Fin 8) :
    (DynkinType.E8.simplyConnectedRootDatum DynkinType.valid_E8).root j l =
      ∑ k, DynkinType.e8Coroot j k * DynkinType.E8.cartanMatrix k l := by
  rw [DynkinType.simplyConnectedRootDatum_E8, DynkinType.e8SimplyConnectedRootDatum_root,
    DynkinType.cartanMatrix_E8]
  exact congrFun (DynkinType.e8Root_apply j) l

theorem cartan_eq (i j : Fin 8) : Tag.E8.cartan j i = DynkinType.E8.cartanMatrix i j := by
  rw [DynkinType.cartanMatrix_E8]
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def rootData :
    GeckRoots.RootData .E8 .E8 DynkinType.valid_E8 where
  node := Equiv.refl _
  coord j := DynkinType.e8Coroot j
  root_eq := root_eq
  isRoot := isRoot_e8Coroot
  card := rfl
  cartan := cartan_eq

end GeckE8

def geckMatchE8
    : GeckMatch .E8 .E8 DynkinType.valid_E8 :=
  GeckE8.rootData.toGeckMatch

end CFSG.TauCetiBridge
