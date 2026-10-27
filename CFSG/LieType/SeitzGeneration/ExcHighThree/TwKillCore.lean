module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillSigned
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillCycleElt
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section TwCore

theorem twisted_kill_core {L : Type} [Field L] [IsAlgClosed L] (p f : ℕ) [Fact p.Prime] [CharP L p]
    (hf : 1 ≤ f) (Fr : L →+* L) (hFr : Fr = iterateFrobenius L p f)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag L)
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : twistHom TwistTag.E6 L Fr g0 = g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
    (M : Subgroup (ModGL TwistTag.E6.tag L))
    (hT : ∀ z ∈ M, g0⁻¹ * z * g0 ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) (twistHom TwistTag.E6 L Fr))
    (α : Fin TwistTag.E6.tag.rank → ℤ) (hα : IsRoot TwistTag.E6.tag α)
    (hk : ∀ z ∈ M, ∃ a : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag a = g0⁻¹ * z * g0 ∧ rootChar a α = 1) :
    ∃ uL : ModGL TwistTag.E6.tag L, uL ∈ adjointGroup TwistTag.E6.tag L ∧ uL ≠ 1 ∧ uL ^ p = 1 ∧
      twistHom TwistTag.E6 L Fr uL = uL ∧ ∀ z ∈ M, uL * z = z * uL := by
  classical
  subst hFr
  choose a ha using fun z : M => hk z.1 z.2
  have hαfam : α ∈ familyKernel a := ⟨hα, fun z => (ha z).2⟩
  have hpF : Fact (Nat.Prime p) := inferInstance
  have hconj : ∀ z : M, rootDiagUnit TwistTag.E6.tag (a z) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        rootDiagUnit TwistTag.E6.tag (fun i => Units.map (iterateFrobenius L p f).toMonoidHom
          (a z (TwistTag.E6.perm.symm i))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ := by
    intro z
    have h1 := mem_twistedTorusOf.1 (hT z.1 z.2)
    have h2 : twistHom TwistTag.E6 L (iterateFrobenius L p f) (g0⁻¹ * z * g0) =
        rootDiagUnit TwistTag.E6.tag (fun i => Units.map (iterateFrobenius L p f).toMonoidHom
          (a z (TwistTag.E6.perm.symm i))) := by
      rw [← (ha z).1, twistHom_rootDiagUnit_eq]
    rw [(ha z).1, ← h2]
    exact h1.2.symm
  have hwrel : ∀ (z : M) (x : Fin TwistTag.E6.tag.rank → ℤ),
      rootChar (a z) (v • x) = Units.map (iterateFrobenius L p f).toMonoidHom
        (rootChar (a z) (permLattice TwistTag.E6.perm.symm x)) := by
    intro z x
    rw [(rootDiagUnit_eq_conj_canonicalRep_iff (a z) _ v).1 (hconj z) x, rootChar_permLattice,
      rootChar_map_tuple]
  have hFrinj : Function.Injective (Units.map (iterateFrobenius L p f).toMonoidHom) :=
    fun x y h => Units.ext ((iterateFrobenius L p f).injective (congrArg Units.val h))
  have hFrs : Function.Surjective (iterateFrobenius L p f) := fun y => by
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : p.Prime).pos f)
    exact ⟨c, by rw [iterateFrobenius_def, hc]⟩
  have hwS : (fun γ => v • permLattice TwistTag.E6.perm γ) '' familyKernel a = familyKernel a := by
    ext β
    constructor
    · rintro ⟨γ, ⟨hγ, hγa⟩, rfl⟩
      refine ⟨IsRoot.smul (hγ.permLattice TwistTag.E6.cartan_perm) v, fun z => ?_⟩
      rw [hwrel z, CFSG.LieType.Chevalley.permLattice_symm_permLattice, hγa z, map_one]
    · rintro ⟨hβ, hβa⟩
      refine ⟨permLattice TwistTag.E6.perm.symm (v⁻¹ • β), ⟨?_, fun z => ?_⟩, ?_⟩
      · have hr : IsRoot TwistTag.E6.tag (v⁻¹ • β) := IsRoot.smul hβ v⁻¹
        exact hr.permLattice (π := TwistTag.E6.perm.symm) (fun i j => by
          have h := TwistTag.E6.cartan_perm (TwistTag.E6.perm.symm i) (TwistTag.E6.perm.symm j)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm)
      · apply hFrinj
        rw [map_one, ← hwrel z (v⁻¹ • β), smul_inv_smul, hβa z]
      · simp only
        rw [CFSG.LieType.Chevalley.permLattice_permLattice_symm, smul_inv_smul]
  obtain ⟨x, hx, n, β, hn, hper, hβ0, hβS, horth, hgβ⟩ := kill_cycle_signed a v hwS hαfam
  have hxstab : ∀ i, x ∈ rootCharStabilizerSubgroup (a i) :=
    fun i => closure_refl_stab a (familyKernel a) (fun γ hγ => hγ) hx i
  have hxS : (fun β => x • β) '' familyKernel a = familyKernel a :=
    image_eq_of_mem_stab (familyKernel a) x (fun β hβ => stab_mem_familyKernel a hxstab hβ)
      (fun β hβ => stab_mem_familyKernel a (fun i => inv_mem (hxstab i)) hβ)
  have hxw : (fun γ => (x * v) • permLattice TwistTag.E6.perm γ) '' familyKernel a = familyKernel a := by
    have e : (fun γ => (x * v) • permLattice TwistTag.E6.perm γ) =
        (fun β => x • β) ∘ (fun γ => v • permLattice TwistTag.E6.perm γ) :=
      funext fun γ => mul_smul x v _
    rw [e, Set.image_comp, hwS, hxS]
  obtain ⟨k, hk', hkxv⟩ := canonicalRep_mul_mem (R := L) x v
  have hQk : canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) =
      k⁻¹ * (canonicalRep (coxeterSystem TwistTag.E6.tag) L x *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L v) := by
    rw [hkxv]
    group
  have hxM : canonicalRep (coxeterSystem TwistTag.E6.tag) L x ∈ familyGroup (K := L) a :=
    canonicalRep_closure_mem_familyGroup a hx
  have hm_mem : canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹ ∈ familyGroup (K := L) a := by
    have hm : canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L x)⁻¹ * k := by
      rw [hQk]
      group
    rw [hm]
    exact mul_mem (inv_mem hxM) (torus_le_familyGroup a hk')
  have hn' : g0⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L p f) g0 =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) := by
    rw [hg0]
    group
  have hst : ∀ y ∈ familyGroup (K := L) a, frobTwistGL TwistTag.E6.tag L p f
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) * diagramMap TwistTag.E6 L) y ∈
        familyGroup (K := L) a := by
    intro y hy
    have e : frobTwistGL TwistTag.E6.tag L p f
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) * diagramMap TwistTag.E6 L) y =
          twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))
            (iterateFrobenius L p f) y := by
      rw [frobTwistGL_apply, twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply]
      group
    rw [e]
    exact twFrob_mem_familyGroup TwistTag.E6 hFrs (x * v) a hxw hy
  have hLang : ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) *
        twistHom TwistTag.E6 L (iterateFrobenius L p f) z *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹) = c := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo p a f hf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) * diagramMap TwistTag.E6 L) hst c hc
    refine ⟨z, hz, ?_⟩
    rw [← hzc, CFSG.LieType.Chevalley.twistHom_apply]
    group
  obtain ⟨ζ, hζ, hζQ⟩ := exists_mem_lang_conj (twistHom TwistTag.E6 L (iterateFrobenius L p f))
    (M := familyGroup (K := L) a) hm_mem hn' hLang
  obtain ⟨v', hv'mem, hv'F, hv'1, hv'p⟩ := twisted_cycle_element (L := L) p f hf
    (x * v) n hn β hper (fun k => (hβS k).1) horth hgβ (familyKernel a) hβS
  have hv'fam : v' ∈ familyGroup (K := L) a := rootSpan_le_familyGroup a hv'mem
  have hζadj : ζ ∈ adjointGroup TwistTag.E6.tag L := familyGroup_le_adjoint a hζ
  have hv'adj : v' ∈ adjointGroup TwistTag.E6.tag L := familyGroup_le_adjoint a hv'fam
  have hg1F : twistHom TwistTag.E6 L (iterateFrobenius L p f) (g0 * ζ) =
      (g0 * ζ) * canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) := by
    calc twistHom TwistTag.E6 L (iterateFrobenius L p f) (g0 * ζ)
        = (g0 * ζ) * ((g0 * ζ)⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L p f) (g0 * ζ)) := by group
      _ = (g0 * ζ) * canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) := by rw [hζQ]
  have hFv : twistHom TwistTag.E6 L (iterateFrobenius L p f) v' =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹ * v' *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) := by
    rw [twFrob_apply] at hv'F
    calc twistHom TwistTag.E6 L (iterateFrobenius L p f) v'
        = (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹ *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) *
              twistHom TwistTag.E6 L (iterateFrobenius L p f) v' *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v))⁻¹) *
            canonicalRep (coxeterSystem TwistTag.E6.tag) L (x * v) := by group
      _ = _ := by rw [hv'F]
  refine ⟨(g0 * ζ) * v' * (g0 * ζ)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem hg0C hζadj) hv'adj) (inv_mem (mul_mem hg0C hζadj))
  · intro h
    apply hv'1
    calc v' = (g0 * ζ)⁻¹ * ((g0 * ζ) * v' * (g0 * ζ)⁻¹) * (g0 * ζ) := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hv'p]
    group
  · rw [map_mul, map_mul, map_inv, hg1F, hFv]
    group
  · intro z hz
    have hd := (ha ⟨z, hz⟩).1
    have hζd : ζ * rootDiagUnit TwistTag.E6.tag (a ⟨z, hz⟩) =
        rootDiagUnit TwistTag.E6.tag (a ⟨z, hz⟩) * ζ := familyGroup_comm a ⟨z, hz⟩ hζ
    have hvd : v' * rootDiagUnit TwistTag.E6.tag (a ⟨z, hz⟩) =
        rootDiagUnit TwistTag.E6.tag (a ⟨z, hz⟩) * v' := familyGroup_comm a ⟨z, hz⟩ hv'fam
    set d := rootDiagUnit TwistTag.E6.tag (a ⟨z, hz⟩) with hdef
    have hconjd : ζ * d * ζ⁻¹ = d := by rw [hζd]; group
    have hbz : z = (g0 * ζ) * d * (g0 * ζ)⁻¹ := by
      calc z = g0 * (g0⁻¹ * z * g0) * g0⁻¹ := by group
        _ = g0 * d * g0⁻¹ := by rw [hd]
        _ = g0 * (ζ * d * ζ⁻¹) * g0⁻¹ := by rw [hconjd]
        _ = (g0 * ζ) * d * (g0 * ζ)⁻¹ := by group
    rw [hbz]
    calc (g0 * ζ * v' * (g0 * ζ)⁻¹) * ((g0 * ζ) * d * (g0 * ζ)⁻¹)
        = (g0 * ζ) * (v' * d) * (g0 * ζ)⁻¹ := by group
      _ = (g0 * ζ) * (d * v') * (g0 * ζ)⁻¹ := by rw [hvd]
      _ = ((g0 * ζ) * d * (g0 * ζ)⁻¹) * ((g0 * ζ) * v' * (g0 * ζ)⁻¹) := by group

end TwCore

end CFSG.LieType.SeitzGeneration.ExcHighThree
