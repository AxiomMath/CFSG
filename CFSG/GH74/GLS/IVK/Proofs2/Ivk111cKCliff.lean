module

public import CFSG.GH74.GLS.IVK.Statements.Sec11

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped MonoidAlgebra
open Representation CFSG CFSG.Theory.Representation CFSG.GH74.GLS.IVK

namespace Mix11cK

section Clifford

variable {k : Type} [Field k] {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module k V]

theorem clifford_core [FiniteDimensional k V] (ρ : Representation k H V)
    (hρ : IsSimpleModule k[H] ρ.asModule) (K : Subgroup H) [K.Normal]
    (hK : Function.Injective (resRep ρ K)) (hKne : Nontrivial K) {m : ℕ}
    (hmin : ∀ (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W]
      (σ : Representation k ↥K W), IsSimpleModule k[K] σ.asModule →
      (∃ x, σ x ≠ 1) → m ≤ Module.finrank k W)
    (hd : Module.finrank k V < 2 * m) :
    IsSimpleModule k[K] (resRep ρ K).asModule := by
  have hirr : IsIrreducible ρ := (irreducible_iff_isSimpleModule_asModule ρ).2 hρ
  have : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨S, hSirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (ρ.comp K.subtype)
  have hSatom : IsAtom S := (Subrepresentation.irreducible_iff_isAtom S).1 hSirr
  let T : Submodule k V := ⨆ g : H, Submodule.map (ρ g) S.toSubmodule
  have hTstable : ∀ x : H, ∀ v ∈ T, ρ x v ∈ T := by
    intro x v hv
    have hle : T ≤ Submodule.comap (ρ x) T := by
      refine iSup_le fun g => ?_
      rintro w ⟨u, hu, rfl⟩
      show ρ x (ρ g u) ∈ T
      have h1 : ρ (x * g) u = ρ x (ρ g u) := by rw [map_mul]; rfl
      rw [← h1]
      exact Submodule.mem_iSup_of_mem (x * g) ⟨u, hu, rfl⟩
    exact hle hv
  have hS1 : S.toSubmodule ≤ T := fun v hv =>
    Submodule.mem_iSup_of_mem 1 ⟨v, hv, by simp⟩
  have hTtop : T = ⊤ := by
    let Tρ : Subrepresentation ρ := ⟨T, fun g v hv => hTstable g v hv⟩
    have hTne : Tρ ≠ ⊥ := by
      intro h
      apply hSatom.1
      apply Subrepresentation.toSubmodule_injective
      have h2 : T = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact le_bot_iff.1 (h2 ▸ hS1)
    rcases eq_bot_or_eq_top Tρ with h | h
    · exact absurd h hTne
    · exact congrArg Subrepresentation.toSubmodule h
  have hSnt : ∃ x : K, ∃ v ∈ S.toSubmodule, ρ x v ≠ v := by
    by_contra hcon
    have htriv : ∀ x : K, ∀ v ∈ S.toSubmodule, ρ x v = v := fun x v hv => by
      by_contra h
      exact hcon ⟨x, v, hv, h⟩
    have hall : ∀ x : K, ρ x = 1 := by
      intro x
      apply LinearMap.ext
      intro v
      have hv : v ∈ T := by rw [hTtop]; exact Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun v => ρ x v = v) hv ?_ ?_ ?_
      · intro g w hw
        obtain ⟨u, hu, rfl⟩ := hw
        have hconj : g⁻¹ * (x : H) * g ∈ K := by
          have := Subgroup.Normal.conj_mem inferInstance (x : H) x.2 g⁻¹
          rwa [inv_inv] at this
        have h1 : ρ g (ρ (g⁻¹ * (x : H) * g) u) = ρ x (ρ g u) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2
          group
        have h2 := htriv ⟨g⁻¹ * (x : H) * g, hconj⟩ u hu
        change ρ (g⁻¹ * (x : H) * g) u = u at h2
        rw [← h1, h2]
      · simp
      · intro a b ha hb
        simp [map_add, ha, hb]
    obtain ⟨a, b, hab⟩ := hKne.exists_pair_ne
    apply hab
    apply hK
    show ρ (a : H) = ρ (b : H)
    have ha := hall a
    have hb := hall b
    simp only [Module.End.one_eq_id] at ha hb
    rw [ha, hb]
  have hS_simple : IsSimpleModule k[K] (S.toRepresentation).asModule :=
    (irreducible_iff_isSimpleModule_asModule _).1 hSirr
  have hSnt' : ∃ x, S.toRepresentation x ≠ 1 := by
    obtain ⟨x, v, hv, hne⟩ := hSnt
    refine ⟨x, fun h => hne ?_⟩
    have := LinearMap.congr_fun h ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hm : m ≤ Module.finrank k S.toSubmodule :=
    hmin S.toSubmodule S.toRepresentation hS_simple hSnt'
  have hS_top : S = ⊤ := by
    by_contra hne
    have hex : ∃ g : H, ¬ (Submodule.map (ρ g) S.toSubmodule ≤ S.toSubmodule) := by
      by_contra hcon
      have hcon' : ∀ g : H, Submodule.map (ρ g) S.toSubmodule ≤ S.toSubmodule := fun g => by
        by_contra h
        exact hcon ⟨g, h⟩
      apply hne
      apply Subrepresentation.toSubmodule_injective
      have hTle : T ≤ S.toSubmodule := iSup_le hcon'
      exact top_le_iff.1 (hTtop ▸ hTle)
    obtain ⟨g, hg⟩ := hex
    have hSg'atom : IsAtom (conjugateSubrepresentationOrderIso ρ K g S) :=
      (OrderIso.isAtom_iff (conjugateSubrepresentationOrderIso ρ K g) S).2 hSatom
    have hSg'sub : (conjugateSubrepresentationOrderIso ρ K g S).toSubmodule =
        Submodule.map (ρ g) S.toSubmodule :=
      conjugateSubrepresentationOrderIso_toSubmodule ρ K g S
    let Sg' := conjugateSubrepresentationOrderIso ρ K g S
    let I : Subrepresentation (ρ.comp K.subtype) :=
      ⟨Sg'.toSubmodule ⊓ S.toSubmodule, fun x v hv =>
        ⟨Sg'.apply_mem_toSubmodule x hv.1, S.apply_mem_toSubmodule x hv.2⟩⟩
    have hIS : I ≤ S := fun v hv => hv.2
    have hI : I = ⊥ := by
      rcases hSatom.le_iff.1 hIS with h | h
      · exact h
      · exfalso
        have hSle : S ≤ Sg' := fun v hv => (h ▸ hv : v ∈ I).1
        have hSeq : S = Sg' := (hSg'atom.le_iff.1 hSle).resolve_left hSatom.1
        apply hg
        rw [← hSg'sub]
        exact (hSeq ▸ le_refl _ : Sg' ≤ S)
    have hdisj : Disjoint Sg'.toSubmodule S.toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hI
    have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisj
    have hSg'dim : Module.finrank k Sg'.toSubmodule = Module.finrank k S.toSubmodule := by
      rw [hSg'sub]
      exact (Submodule.equivMapOfInjective (ρ g) (Representation.apply_bijective ρ g).1
        S.toSubmodule).finrank_eq.symm
    omega
  have hStop : IsAtom (⊤ : Subrepresentation (ρ.comp K.subtype)) := hS_top ▸ hSatom
  have hsimple : IsSimpleOrder (Subrepresentation (ρ.comp K.subtype)) :=
    isSimpleOrder_iff_isAtom_top.2 hStop
  exact (irreducible_iff_isSimpleModule_asModule (ρ.comp K.subtype)).1 hsimple

end Clifford

end Mix11cK

end CFSG.GH74.GLS.Stage4.Rest
