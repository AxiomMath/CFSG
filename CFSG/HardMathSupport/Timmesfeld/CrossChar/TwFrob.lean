module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.RankThree.PartOne.KGD.D4Twist

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical
open scoped Matrix MatrixGroups

section Model

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def fixModel (Φ : ModGL τ L →* ModGL τ L) : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ Φ.eqLocus (MonoidHom.id _)

theorem mem_fixModel {Φ : ModGL τ L →* ModGL τ L} {y : ModGL τ L} :
    y ∈ fixModel Φ ↔ y ∈ adjointGroup τ L ∧ Φ y = y :=
  Iff.rfl

theorem twModel_eq_fixModel (n : ModGL τ L) (Fr : L →+* L) :
    twModel n Fr = fixModel ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))) :=
  rfl

theorem twistedTorusOf_le_fixModel
    (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) :
    twistedTorusOf n Φ ≤ fixModel ((MulAut.conj n).toMonoidHom.comp Φ) := fun _ hx =>
  ⟨twistedTorusOf_le_adjointGroup n Φ hx, (mem_twistedTorusOf.1 hx).2⟩

theorem map_conj_fixModel {Φ : ModGL τ L →* ModGL τ L} {n g0 : ModGL τ L}
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) :
    (fixModel ((MulAut.conj n).toMonoidHom.comp Φ)).map (MulAut.conj g0).toMonoidHom =
      fixModel Φ := by
  have hginv : Φ g0⁻¹ = n⁻¹ * g0⁻¹ := by rw [map_inv, hg0, mul_inv_rev]
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyF⟩, rfl⟩
    have hyF' : n * Φ y * n⁻¹ = y := hyF
    have hyC' : y ∈ adjointGroup τ L := hyC
    refine ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem hg0C hyC')
      ((adjointGroup τ L).inv_mem hg0C), ?_⟩
    change Φ (g0 * y * g0⁻¹) = g0 * y * g0⁻¹
    calc Φ (g0 * y * g0⁻¹) = g0 * (n * Φ y * n⁻¹) * g0⁻¹ := by
          rw [map_mul, map_mul, hg0, hginv]
          group
      _ = g0 * y * g0⁻¹ := by rw [hyF']
  · rintro ⟨hxC, hxF⟩
    have hxF' : Φ x = x := hxF
    have hxC' : x ∈ adjointGroup τ L := hxC
    refine ⟨g0⁻¹ * x * g0, ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem
      ((adjointGroup τ L).inv_mem hg0C) hxC') hg0C, ?_⟩, ?_⟩
    · change n * Φ (g0⁻¹ * x * g0) * n⁻¹ = g0⁻¹ * x * g0
      rw [map_mul, map_mul, hginv, hxF', hg0]
      group
    · change g0 * (g0⁻¹ * x * g0) * g0⁻¹ = x
      group

end Model

section TwFrob

variable {L : Type} [Field L]

@[expose] noncomputable def twFrob (t : TwistTag) (n : ModGL t.tag L) (Fr : L →+* L) :
    ModGL t.tag L →* ModGL t.tag L :=
  (MulAut.conj n).toMonoidHom.comp (twistHom t L Fr)

theorem twFrob_apply (t : TwistTag) (n : ModGL t.tag L) (Fr : L →+* L) (g : ModGL t.tag L) :
    twFrob t n Fr g = n * twistHom t L Fr g * n⁻¹ :=
  rfl

theorem fixModel_twFrob (t : TwistTag) (n : ModGL t.tag L) (Fr : L →+* L) :
    fixModel (twFrob t n Fr) =
      fixModel ((MulAut.conj n).toMonoidHom.comp (twistHom t L Fr)) :=
  rfl


theorem map_twFrob_rootSubgroup (t : TwistTag) {Fr : L →+* L} (hFr : Function.Surjective Fr)
    (v : WeylGroup t.tag) {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    (rootSubgroup t.tag L β).map (twFrob t (canonicalRep (coxeterSystem t.tag) L v) Fr) =
      rootSubgroup t.tag L (v • permLattice t.perm β) := by
  rw [twFrob, ← Subgroup.map_map, map_twistHom_rootSubgroup t L hFr hβ,
    (canonical_weyl_root_transport t.tag L).2.1 v _ (hβ.permLattice t.cartan_perm)]

theorem map_twFrob_rootSpan (t : TwistTag) {Fr : L →+* L} (hFr : Function.Surjective Fr)
    (v : WeylGroup t.tag) {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α) :
    (rootSpan t.tag L S).map (twFrob t (canonicalRep (coxeterSystem t.tag) L v) Fr) =
      rootSpan t.tag L ((fun α => v • permLattice t.perm α) '' S) := by
  rw [twFrob, ← Subgroup.map_map, map_twistHom_rootSpan t L hFr hS,
    (canonical_weyl_root_transport t.tag L).1 v _ (by
      rintro _ ⟨α, hα, rfl⟩
      exact (hS α hα).permLattice t.cartan_perm), Set.image_image]

theorem twFrob_rootSL2 (t : TwistTag) {n : ModGL t.tag L} (hn : n ∈ monomialSubgroup t.tag L)
    (Fr : L →+* L) {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    ∃ s : Lˣ, ∀ A : SL2 L, twFrob t n Fr (rootSL2 t.tag L β A) =
      rootSL2 t.tag L (weylQuotientHom t.tag L ⟨n, hn⟩ • permLattice t.perm β)
        (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A)) := by
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartOne.KGD.exists_conj_rootSL2_eq_twist hn hβ
  refine ⟨s, fun A => ?_⟩
  rw [twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply,
    CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field, ← hs]
  group

theorem twFrob_rootDiagUnit (t : TwistTag) (Fr : L →+* L) (v : WeylGroup t.tag)
    (a : Fin t.tag.rank → Lˣ) :
    twFrob t (canonicalRep (coxeterSystem t.tag) L v) Fr (rootDiagUnit t.tag a) =
      rootDiagUnit t.tag (weylTuple v fun i => Units.map Fr.toMonoidHom (a (t.perm.symm i))) := by
  rw [twFrob_apply, twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]

theorem twisted_weylTuple_eq_iff_fixedCharTuples (t : TwistTag) (Fr : L →+* L)
    (v : WeylGroup t.tag) (M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)
    (hv : ∀ x, v • permLattice t.perm x = M *ᵥ x) (a : Fin t.tag.rank → Lˣ) :
    weylTuple v (fun i => Units.map Fr.toMonoidHom (a (t.perm.symm i))) = a ↔
      a ∈ fixedCharTuples M Fr := by
  set ρ := t.perm with hρ
  have hchar : ∀ u, rootChar (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) u =
      Units.map Fr.toMonoidHom (rootChar a (permLattice ρ.symm u)) := by
    intro u
    rw [rootChar_map_tuple Fr (fun i => a (ρ.symm i)) u, rootChar_permLattice a ρ.symm u]
  constructor
  · intro h z
    have h1 : rootChar a (M *ᵥ z) =
        rootChar (weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))))
          (v • permLattice ρ z) := by rw [h, hv]
    rw [h1, rootChar_weylTuple, inv_smul_smul, hchar, permLattice_symm_permLattice]
  · intro ha
    funext i
    have e1 : weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) i =
        Units.map Fr.toMonoidHom (rootChar a (permLattice ρ.symm (v⁻¹ • Pi.single i 1))) := by
      rw [weylTuple, hchar]
    rw [e1, ← ha, ← hv, permLattice_permLattice_symm, smul_inv_smul, CTTorus.rootChar_single]

theorem twistedTorusOf_twistHom_eq_map [IsAlgClosed L] (t : TwistTag) (Fr : L →+* L)
    (v : WeylGroup t.tag) (M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ)
    (hv : ∀ x, v • permLattice t.perm x = M *ᵥ x) :
    twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v) (twistHom t L Fr) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom t.tag L) := by
  have key : ∀ a : Fin t.tag.rank → Lˣ,
      canonicalRep (coxeterSystem t.tag) L v * twistHom t L Fr (rootDiagUnit t.tag a) *
          (canonicalRep (coxeterSystem t.tag) L v)⁻¹ = rootDiagUnit t.tag a ↔
        a ∈ fixedCharTuples M Fr := fun a => by
    rw [← twFrob_apply, twFrob_rootDiagUnit,
      (rootDiagUnit_injective (τ := t.tag) (K := L)).eq_iff]
    exact twisted_weylTuple_eq_iff_fixedCharTuples t Fr v M hv a
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
    exact ⟨a, (key a).1 (mem_twistedTorusOf.1 hx).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, (key a).2 ha⟩

end TwFrob

end CFSG.HardMathSupport.Timmesfeld.CrossChar
