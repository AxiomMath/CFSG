module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def OmegaCentDecomp : Prop :=
  ∀ s : ↥CFSG.AGLEmbedding.Om8, (MulAut.conj s) ^ 3 = 1 → MulAut.conj s ≠ 1 →
    ∃ (k : ℕ) (A₀ A₁ : Subgroup ↥CFSG.AGLEmbedding.Om8), 1 ≤ k ∧ k ≤ 4 ∧
      Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8) = A₀ ⊔ A₁ ∧
      (∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a) ∧ A₀ ⊓ A₁ = ⊥ ∧
      (∃ (E : Type) (_ : Field E) (hE : UnitaryFieldData 2 1 E) (W : Type) (_ : AddCommGroup W)
        (_ : Module E W) (_ : FiniteDimensional E W) (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E),
        Hf.IsSymm ∧ Hf.SeparatingLeft ∧ Module.finrank E W = k ∧ Nonempty (↥A₁ ≃* sesqUnitaryGroup Hf)) ∧
      (∀ K : Subgroup ↥CFSG.AGLEmbedding.Om8, IsComponentOf K A₀ →
        catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two)

theorem omega_comp_om8 (GU : GUBlockFacts) (OC : OmegaCentDecomp) (s : ↥CFSG.AGLEmbedding.Om8)
    (hs3 : (MulAut.conj s) ^ 3 = 1) (hs1 : MulAut.conj s ≠ 1)
    {L : Subgroup ↥CFSG.AGLEmbedding.Om8}
    (hL : IsComponentOf L (Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8))) :
    catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU4two := by
  obtain ⟨k, A₀, A₁, hk1, hk4, hC, hcomm, hdisj, hunit, hcomp0⟩ := OC s hs3 hs1
  have hLC : IsComponentOf L (A₀ ⊔ A₁) := by
    rw [← hC]
    exact hL
  rcases comp_le_or_le hcomm hLC with hLA₀ | hLA₁
  · exact hcomp0 L (isComponentOf_of_le_factor hLC hLA₀)
  · have hLC' : IsComponentOf L (A₁ ⊔ A₀) := by
      rw [sup_comm]
      exact hLC
    have hcompA1 := isComponentOf_of_le_factor hLC' hLA₁
    obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hunit
    have hK1 : IsComponentOf (L.subgroupOf A₁) ⊤ := isComponentOf_top_subgroupOf hcompA1
    have hK2 := isComponentOf_map_mulEquiv hK1 eA1
    rw [Subgroup.map_top_of_surjective _ eA1.surjective] at hK2
    have hGU := GU E hE W Hf hsymm hsep
    rcases (by omega : k ≤ 3 ∨ k = 4) with hm | hm
    · exfalso
      exact not_comp_top_of_solvable (hGU.1 (by rw [hfr]; omega)) hK2
    · obtain ⟨hcat, -, -⟩ := hGU.2 (by rw [hfr]; exact hm) _ hK2
      let K2 : Subgroup (sesqUnitaryGroup Hf) := (L.subgroupOf A₁).map eA1.toMonoidHom
      let eLK2 : ↥L ≃* ↥K2 :=
        (Subgroup.subgroupOfEquivOfLe hLA₁).symm.trans
          (Subgroup.equivMapOfInjective (L.subgroupOf A₁) eA1.toMonoidHom eA1.injective)
      let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥K2 ⧸ Subgroup.center ↥K2) :=
        QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥K2) eLK2
          (Subgroup.map_center_eq eLK2)
      exact catalogIs_of_mulEquiv eQ.symm hcat

theorem transport_conj {T S : Type} [Group T] [Group S] (e : T ≃* S) (s : T) :
    e.symm.trans ((MulAut.conj s).trans e) = MulAut.conj (e s) := by
  apply MulEquiv.ext
  intro x
  simp [MulAut.conj_apply]

theorem conj_pow_apply' {T S : Type} [Group T] [Group S] (e : T ≃* S) (α : MulAut T) (n : ℕ) (x : S) :
    ((e.symm.trans (α.trans e)) ^ n) x = e ((α ^ n) (e.symm x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
    congr 1
    simp

theorem omegaPlusCompRes_of_residuals (OC : OmegaCentDecomp) (GU : GUBlockFacts) : OmegaPlusCompRes := by
  intro T _ hT α h3 h1 hs L hL
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_d4two hT
  have hα : e.symm.trans ((MulAut.conj s).trans e) = MulAut.conj (e s) := transport_conj e s
  have h3' : (MulAut.conj (e s)) ^ 3 = 1 := by
    rw [← hα]
    apply MulEquiv.ext
    intro x
    rw [conj_pow_apply', h3, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
  have h1' : MulAut.conj (e s) ≠ 1 := by
    intro h
    apply h1
    apply MulEquiv.ext
    intro t
    have hx := congrArg (fun f : MulAut ↥CFSG.AGLEmbedding.Om8 => f (e t)) (hα.trans h)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at hx
    rw [MulAut.one_apply]
    exact e.injective hx
  have hL0 : IsComponentOf L (Subgroup.centralizer ({s} : Set T)) := (fixSub_conj s) ▸ hL
  have hL' : IsComponentOf (L.map e.toMonoidHom)
      (Subgroup.centralizer ({e s} : Set ↥CFSG.AGLEmbedding.Om8)) := by
    have h := isComponentOf_map_mulEquiv hL0 e
    rwa [map_centralizer_singleton e s] at h
  have hres := omega_comp_om8 GU OC (e s) h3' h1' hL'
  let eL : ↥L ≃* ↥(L.map e.toMonoidHom) := Subgroup.equivMapOfInjective L e.toMonoidHom e.injective
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥(L.map e.toMonoidHom) ⧸ Subgroup.center ↥(L.map e.toMonoidHom)) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.map e.toMonoidHom)) eL
      (Subgroup.map_center_eq eL)
  exact catalogIs_of_mulEquiv eQ.symm hres

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
