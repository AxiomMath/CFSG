module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangCanonical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

theorem exists_lang_canonicalRep_tw
    {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (t : TwistTag) (e : ℕ) (he : 1 ≤ e) {b : Fin t.tag.rank → Lˣ} {u g : ModGL t.tag L}
    (hg : g ∈ adjointGroup t.tag L) (hu : twistHom t L (iterateFrobenius L ℓ e) u = u)
    (hgu : g⁻¹ * u * g = rootDiagUnit t.tag b) :
    ∃ g' ∈ adjointGroup t.tag L, ∃ w : WeylGroup t.tag, g'⁻¹ * u * g' = rootDiagUnit t.tag b ∧
      g'⁻¹ * twistHom t L (iterateFrobenius L ℓ e) g' =
        canonicalRep (coxeterSystem t.tag) L w := by
  have hn := conj_frob_rootDiag_of_conj_eq (F := twistHom t L (iterateFrobenius L ℓ e)) hu hgu
  obtain ⟨w', z, hz, hzF⟩ :=
    exists_lang_datum_of_plane_twisted ℓ t e he (fun _ : Unit => b) hg (fun _ => hn)
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => b) hz
  refine ⟨g * z, mul_mem hg (mem_familyCentralizer.1 hzC).1, w', ?_, hzF⟩
  calc (g * z)⁻¹ * u * (g * z) = z⁻¹ * (g⁻¹ * u * g) * z := by group
    _ = z⁻¹ * rootDiagUnit t.tag b * z := by rw [hgu]
    _ = rootDiagUnit t.tag b := inv_conj_rootDiag_of_mem_familyCentralizer hzC

private theorem rootChar_smul_canonicalRep_tw
    {L : Type} [Field L] (t : TwistTag) {Fr : L →+* L}
    {b : Fin t.tag.rank → Lˣ} {w : WeylGroup t.tag}
    (hnd : canonicalRep (coxeterSystem t.tag) L w *
        twistHom t L Fr (rootDiagUnit t.tag b) *
        (canonicalRep (coxeterSystem t.tag) L w)⁻¹ =
      rootDiagUnit t.tag b) :
    ∀ v : Fin t.tag.rank → ℤ,
      rootChar b (w • v) =
        Units.map Fr.toMonoidHom (rootChar b (permLattice t.perm.symm v)) := by
  intro v
  have hFd : twistHom t L Fr (rootDiagUnit t.tag b) =
      rootDiagUnit t.tag (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i))) :=
    twistHom_rootDiagUnit_eq (σ := Fr) b
  rw [hFd] at hnd
  have h1 := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b
    (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i))) w).1 hnd.symm v
  have h2 : rootChar (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i))) v =
      Units.map Fr.toMonoidHom (rootChar b (permLattice t.perm.symm v)) := by
    rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple Fr (fun i => b (t.perm.symm i)) v,
      rootChar_permLattice b t.perm.symm v]
  rw [h2] at h1
  exact h1

private theorem image_familyKernel_canonicalRep_tw
    {L : Type} [Field L] (t : TwistTag) {Fr : L →+* L}
    (hFrinj : Function.Injective (Units.map Fr.toMonoidHom))
    {b : Fin t.tag.rank → Lˣ} {w : WeylGroup t.tag}
    (hw : ∀ v : Fin t.tag.rank → ℤ,
      rootChar b (w • v) =
        Units.map Fr.toMonoidHom (rootChar b (permLattice t.perm.symm v))) :
    (fun α => w • permLattice t.perm α) '' familyKernel (fun _ : Unit => b) =
      familyKernel (fun _ : Unit => b) := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
    refine ⟨IsRoot.smul (hα.permLattice t.cartan_perm) w, fun s => ?_⟩
    rw [hw, CFSG.LieType.Chevalley.permLattice_symm_permLattice, hαa s, map_one]
  · rintro ⟨hβ, hβa⟩
    refine ⟨permLattice t.perm.symm (w⁻¹ • β), ⟨?_, fun s => ?_⟩, ?_⟩
    · have hr : IsRoot t.tag (w⁻¹ • β) := IsRoot.smul hβ w⁻¹
      exact hr.permLattice (π := t.perm.symm) (fun i j => by
        have h := t.cartan_perm (t.perm.symm i) (t.perm.symm j)
        simp only [Equiv.apply_symm_apply] at h
        exact h.symm)
    · apply hFrinj
      rw [map_one, ← hw (w⁻¹ • β), smul_inv_smul, hβa s]
    · simp only
      rw [CFSG.LieType.Chevalley.permLattice_permLattice_symm, smul_inv_smul]

private theorem lang_familyGroup_twisted
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (t : TwistTag) (e : ℕ) (he : 1 ≤ e)
    {Fr : L →+* L} (hFrdef : Fr = iterateFrobenius L 2 e) (hFrs : Function.Surjective Fr)
    {b : Fin t.tag.rank → Lˣ} {w v : WeylGroup t.tag}
    (himg : (fun α => w • permLattice t.perm α) '' familyKernel (fun _ : Unit => b) =
      familyKernel (fun _ : Unit => b))
    (hnv : canonicalRep (coxeterSystem t.tag) L v ∈
      familyGroup (K := L) (fun _ : Unit => b))
    (hQ : canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) =
      (canonicalRep (coxeterSystem t.tag) L v)⁻¹ *
        canonicalRep (coxeterSystem t.tag) L w) :
    ∀ c ∈ familyGroup (K := L) (fun _ : Unit => b),
      ∃ z ∈ familyGroup (K := L) (fun _ : Unit => b),
        z⁻¹ * (canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) * twistHom t L Fr z *
          (canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w))⁻¹) = c := by
  have hst : ∀ x ∈ familyGroup (K := L) (fun _ : Unit => b),
      frobTwistGL t.tag L 2 e
        (canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) * diagramMap t L) x ∈
        familyGroup (K := L) (fun _ : Unit => b) := by
    intro x hx
    have hx' : frobTwistGL t.tag L 2 e
        (canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) * diagramMap t L) x =
        (canonicalRep (coxeterSystem t.tag) L v)⁻¹ *
          twFrob t (canonicalRep (coxeterSystem t.tag) L w) Fr x *
            canonicalRep (coxeterSystem t.tag) L v := by
      rw [frobTwistGL_apply, twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply,
        hFrdef, hQ]
      group
    rw [hx']
    exact mul_mem (mul_mem (inv_mem hnv)
      (twFrob_mem_familyGroup t hFrs w (fun _ : Unit => b) himg hx)) hnv
  intro c hc
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo 2 (fun _ : Unit => b) e he
    (canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) * diagramMap t L) hst c hc
  refine ⟨z, hz, ?_⟩
  rw [← hzc, CFSG.LieType.Chevalley.twistHom_apply, hFrdef]
  group

theorem exists_lang_canonicalRep_kernelWeyl_tw
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (t : TwistTag) (e : ℕ) (he : 1 ≤ e) {b : Fin t.tag.rank → Lˣ} {u g : ModGL t.tag L}
    (hg : g ∈ adjointGroup t.tag L) (hu : twistHom t L (iterateFrobenius L 2 e) u = u)
    (hgu : g⁻¹ * u * g = rootDiagUnit t.tag b) {w : WeylGroup t.tag}
    (hgw : g⁻¹ * twistHom t L (iterateFrobenius L 2 e) g =
      canonicalRep (coxeterSystem t.tag) L w)
    {v : WeylGroup t.tag} (hv : v ∈ kernelWeylGroup (rootCharHom b)) :
    ∃ g' ∈ adjointGroup t.tag L, g'⁻¹ * u * g' = rootDiagUnit t.tag b ∧
      g'⁻¹ * twistHom t L (iterateFrobenius L 2 e) g' =
        canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) := by
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L 2 e := ⟨_, rfl⟩
  rw [← hFrdef] at hu hgw ⊢
  let nw : ModGL t.tag L := canonicalRep (coxeterSystem t.tag) L w
  let nv : ModGL t.tag L := canonicalRep (coxeterSystem t.tag) L v
  let nQ : ModGL t.tag L := canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w)
  have hgw' : g⁻¹ * twistHom t L Fr g = nw := hgw
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y
      (pow_pos (Fact.out : Nat.Prime 2).pos e)
    exact ⟨x, by rw [hFrdef, iterateFrobenius_def, hx]⟩
  have hFrinj : Function.Injective (Units.map Fr.toMonoidHom) := fun x y h =>
    Units.ext (Fr.injective (congrArg Units.val h))
  have hnd : nw * twistHom t L Fr (rootDiagUnit t.tag b) * nw⁻¹ =
      rootDiagUnit t.tag b := by
    have h := conj_frob_rootDiag_of_conj_eq (F := twistHom t L Fr) hu hgu
    rwa [hgw'] at h
  have hw := rootChar_smul_canonicalRep_tw t hnd
  have himg := image_familyKernel_canonicalRep_tw t hFrinj hw
  have hnv : nv ∈ familyGroup (K := L) (fun _ : Unit => b) :=
    canonicalRep_mem_familyGroup_of_mem_kernelWeyl (b := b) (v := v) hv
  have hQ : nQ = nv⁻¹ * nw := by
    change canonicalRep (coxeterSystem t.tag) L (v⁻¹ * w) =
      (canonicalRep (coxeterSystem t.tag) L v)⁻¹ *
        canonicalRep (coxeterSystem t.tag) L w
    rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]
  have hn : g⁻¹ * twistHom t L Fr g = nv * nQ := by
    rw [hgw', hQ]
    group
  have hLang := lang_familyGroup_twisted t e he hFrdef hFrs himg hnv hQ
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj (twistHom t L Fr)
    (M := familyGroup (K := L) (fun _ : Unit => b))
    (Q := nQ) (g := g) (m := nv) hnv hn hLang
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => b) hz
  refine ⟨g * z, mul_mem hg (mem_familyCentralizer.1 hzC).1, ?_, ?_⟩
  · calc (g * z)⁻¹ * u * (g * z) = z⁻¹ * (g⁻¹ * u * g) * z := by group
      _ = z⁻¹ * rootDiagUnit t.tag b * z := by rw [hgu]
      _ = rootDiagUnit t.tag b := inv_conj_rootDiag_of_mem_familyCentralizer hzC
  · exact hzF

end CFSG.HardMathSupport.Timmesfeld.CrossChar
