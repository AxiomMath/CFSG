module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three20
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.Open
open scoped Matrix MatrixGroups Pointwise

theorem isRoot_of_mem_e7T3A5SubA2 {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ e7T3A5SubA2) : IsRoot Tag.E7 α := by
  obtain ⟨γ, hγ, rfl⟩ := hα
  exact IsRoot.smul hγ.1 e7T3A5Transport

section Certs


theorem e7T3QLayer_le_model {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}
    (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    {v : WeylGroup Tag.E7} {b : Fin Tag.E7.rank → Lˣ}
    (hS : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hSsub : e7T3A5SubA2 ⊆ rootCharKernel b)
    {Φ' : SL(6, L) ≃* SL(6, L)} {P : Subgroup (ModGL Tag.E7 L)}
    (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hΦ' : ∀ X : SL(6, L),
      ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
          canonicalRep (coxeterSystem Tag.E7) L v) *
        Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) *
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
          canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ = a5Frame L (Φ' X))
    (hP : P = (fixSubgroup Φ').map
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (a5Frame L))) :
    rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ≤ P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hVdef
  set n' : ModGL Tag.E7 L := V⁻¹ * F.n * V with hn'def
  have hΦV : Units.map (entrywiseHom Fr) V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  let Γ : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n' (Units.map (entrywiseHom Fr))
  have hcommΓ : ⁅Γ, Γ⁆ = (fixSubgroup Φ').map (a5Frame L) :=
    commutator_Gamma Fr n' Φ' (fun X => hΦ' X) hq
  let QL : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L e7T3A5SubA2 ⊓ twistedFixedPoints F.n (Units.map (entrywiseHom Fr))
  have hQLqs : CFSG.IsQuasisimple ↥QL :=
    isQuasisimple_e7T3QLayer (L := L) (p := p) hf hK hε hq2 F.n F.hnm
      (monomialSubgroup_le_adjointGroup' F.hnm) (fun x => F.hnW x)
  have hQLperf : ⁅QL, QL⁆ = QL := by
    haveI : Group.IsPerfect ↥QL := hQLqs.1
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hQΓ : QL.map (MulAut.conj V⁻¹).toMonoidHom ≤ Γ := by
    rintro x ⟨g, hg, rfl⟩
    have hx : (MulAut.conj V⁻¹).toMonoidHom g = V⁻¹ * g * V := by
      simp [MulAut.conj_apply]
    rw [hx]
    refine ⟨?_, ?_⟩
    · exact CFSG.HardMathSupport.Lang.TwE6Step3.canonicalRep_inv_conj_mem_rootSpan (K := L) v
        (fun γ hγ => ⟨isRoot_of_mem_e7T3A5SubA2 hγ, by
          have hγb : γ ∈ rootCharKernel b := hSsub hγ
          rw [hS] at hγb
          obtain ⟨β, hβ, rfl⟩ := hγb
          simpa using hβ⟩) hg.1
    · refine (mem_twistedFixedPoints_conj (Φ := Units.map (entrywiseHom Fr)) hΦV).2 ?_
      have hconj : V * (V⁻¹ * g * V) * V⁻¹ = g := by group
      rw [hconj]
      exact hg.2
  have hmap : QL.map (MulAut.conj V⁻¹).toMonoidHom =
      ⁅QL.map (MulAut.conj V⁻¹).toMonoidHom, QL.map (MulAut.conj V⁻¹).toMonoidHom⁆ := by
    conv_lhs => rw [← hQLperf]
    rw [Subgroup.map_commutator]
  have hle : QL.map (MulAut.conj V⁻¹).toMonoidHom ≤ (fixSubgroup Φ').map (a5Frame L) := by
    calc QL.map (MulAut.conj V⁻¹).toMonoidHom
        = ⁅QL.map (MulAut.conj V⁻¹).toMonoidHom, QL.map (MulAut.conj V⁻¹).toMonoidHom⁆ := hmap
      _ ≤ ⁅Γ, Γ⁆ := Subgroup.commutator_mono hQΓ hQΓ
      _ = (fixSubgroup Φ').map (a5Frame L) := hcommΓ
  intro g hg
  have hg' : V⁻¹ * g * V ∈ (fixSubgroup Φ').map (a5Frame L) := by
    refine hle ⟨g, hg, ?_⟩
    simp [MulAut.conj_apply]
  rw [hP, ← Subgroup.map_map]
  exact Subgroup.mem_map.mpr ⟨V⁻¹ * g * V, hg', by simp [MulAut.conj_apply]; group⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
