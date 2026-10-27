module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniPsu
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Fld
public import CFSG.GH74.L5U5.Models
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open scoped commutatorElement

section Certs


variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {y : Ω}
  {X J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hJ : GLAPComponent p X J) (hJS : J ≤ S)
  (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hyp : y ^ p = 1)
  {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
  (θ : PSimple p S ≃* StatedProj (StatedSU d (2 ^ n) K)) (ψ : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
  (hindy : LargeEvenInduces θ (indRel p S y) ψ) (B : GL (Fin d) K) (σ : K ≃+* K)
  (hψB : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = B * glMap σ (g : GL (Fin d) K) * B⁻¹ →
    ψ (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
  (hBmem : ∀ g ∈ StatedSU d (2 ^ n) K, B * glMap σ g * B⁻¹ ∈ StatedSU d (2 ^ n) K)
  (hmoved : ∃ c : K, h.bar c = c ∧ σ c ≠ c)

include hp hp2 hSp hJ hJS hJy hyp h hindy hψB hBmem hmoved

theorem l154_uni_fieldOn_su [Finite K]
    (hblock : L154BlockSU n d K h ((chevTransfer p S J).map θ.toMonoidHom)) : FieldOn p y J := by
  classical
  obtain ⟨m, E, instE, finE, k, ι, N, hm3, hk1, hk2, hcardE, hN, hline, hmem, hscal, hJPiff⟩ := hblock
  have hnq : (m, 2 ^ k) ≠ (3, 2) := by
    intro hc
    have h1 : m = 3 := congrArg Prod.fst hc
    have h2 : 2 ^ k = 2 := congrArg Prod.snd hc
    have := hk2 h1
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hperfM : commutator ↥(StatedSU m (2 ^ k) E) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardE hm3 hnq)
  have hsimple : IsSimpleGroup (LargeEvenProj (StatedSU m (2 ^ k) E)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E 2 k hcardE m hm3 hnq
  let ι' : ↥(StatedSU m (2 ^ k) E) →* GL (Fin d) K := ι.comp (StatedSU m (2 ^ k) E).subtype
  obtain ⟨e₀, hequi⟩ := l154_J_matrix_equiv hp hSp hJ hJS hJy θ ψ hindy B σ hψB hBmem
    (LargeEvenProjMk (StatedSU m (2 ^ k) E)) (QuotientGroup.mk'_surjective _)
    (ker_projMk_uni_le_center _) hsimple ι' (fun t => hmem t.1 t.2)
    (fun t z hz => by
      obtain ⟨c, hc⟩ := hscal (t : GL (Fin m) E) z hz
      refine (projMk_eq_iff_uni _ t 1).2 ⟨c⁻¹, ?_⟩
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin m) c⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin m) c)⁻¹ := map_inv _ c
      rw [e1, ← hc]
      simp)
    (fun z => (hJPiff z).trans ⟨fun ⟨t, ht, ht', hπ⟩ => ⟨⟨t, ht⟩, hπ⟩,
      fun ⟨t, hπ⟩ => ⟨t.1, t.2, hmem t.1 t.2, hπ⟩⟩)
  obtain ⟨c₁, hc₁b, hc₁σ⟩ := hmoved
  have hnot : MulAut.congr e₀ (MI.indAut p J y hJy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSU m (2 ^ k) E)) (LargeEvenGUSet (Fin m) E (2 ^ k)) := by
    refine l154_notInner_of_line ι hperfM σ B (LargeEvenGUSet (Fin m) E (2 ^ k)) ?_ e₀ _ hequi N hN
      {c | h.bar c = c} (map_one h.bar) hc₁b hc₁σ (fun c hc => hline c hc)
    intro P hP m' hm'
    obtain ⟨τ', hτ'm, hτ'⟩ := exists_frob_equiv hcardE
    obtain ⟨A', hA', hAeq⟩ := exists_heldGU_of_GUSet hτ'm hcardE hτ' P hP
    have := conj_mem_statedSU hτ' hτ'm hA' hm'
    rwa [hAeq] at this
  obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  subst hr
  exact fieldOn_of_notInner hp hp2 hJy hyp
    (l154_marking_J_uni hp hJ hJy (r := r) (by omega) hk1 (fun hr2 => hk2 (by omega)) hcardE e₀ hnot)

theorem l154_uni_fieldOn_sl [Finite K]
    (hblock : L154BlockSL n d K h ((chevTransfer p S J).map θ.toMonoidHom)) : FieldOn p y J := by
  classical
  obtain ⟨m, E, instE, finE, k, ι, N, hm2, hk2, hcardE, hN, hline, hmem, hscal, hJPiff⟩ := hblock
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have h22 : m ≠ 2 ∨ Nat.card E ≠ 2 := Or.inr (by rw [hcardE]; omega)
  have h23 : m ≠ 2 ∨ Nat.card E ≠ 3 := Or.inr (by rw [hcardE]; omega)
  have hperfM : commutator ↥(StatedSL m E) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL E hm2 h22 h23)
  have hsimple : IsSimpleGroup (LargeEvenProj (StatedSL m E)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL E hm2 h22 h23
  let ι' : ↥(StatedSL m E) →* GL (Fin d) K := ι.comp (StatedSL m E).subtype
  obtain ⟨e₀, hequi⟩ := l154_J_matrix_equiv hp hSp hJ hJS hJy θ ψ hindy B σ hψB hBmem
    (LargeEvenProjMk (StatedSL m E)) (QuotientGroup.mk'_surjective _)
    (ker_projMk_uni_le_center _) hsimple ι' (fun t => hmem t.1 t.2)
    (fun t z hz => by
      obtain ⟨c, hc⟩ := hscal (t : GL (Fin m) E) z hz
      refine (projMk_eq_iff_uni _ t 1).2 ⟨c⁻¹, ?_⟩
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin m) c⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin m) c)⁻¹ := map_inv _ c
      rw [e1, ← hc]
      simp)
    (fun z => (hJPiff z).trans ⟨fun ⟨t, ht, ht', hπ⟩ => ⟨⟨t, ht⟩, hπ⟩,
      fun ⟨t, hπ⟩ => ⟨t.1, t.2, hmem t.1 t.2, hπ⟩⟩)
  obtain ⟨c₁, hc₁b, hc₁σ⟩ := hmoved
  have hnot : MulAut.congr e₀ (MI.indAut p J y hJy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSL m E)) Set.univ := by
    refine l154_notInner_of_line ι hperfM σ B Set.univ ?_ e₀ _ hequi N hN
      {c | h.bar c = c} (map_one h.bar) hc₁b hc₁σ (fun c hc => hline c hc)
    intro P _ m' hm'
    exact (inferInstance : (StatedSL m E).Normal).conj_mem m' hm' P
  obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  subst hr
  obtain ⟨e, he⟩ := exists_notInner_of_eq (largeEvenSLGroup_eq_statedSL (K := E) (r + 1))
    (MI.indAut p J y hJy) ⟨e₀, hnot⟩
  exact fieldOn_of_notInner hp hp2 hJy hyp
    (l154_marking_J hp hJ hJy (r := r) (k := k) (by omega) (by omega) (fun _ => hk2) hcardE e he)

theorem l154_uni_fieldOn_sl2 [Finite K]
    (hblock : L154BlockSL2 n d K h ((chevTransfer p S J).map θ.toMonoidHom)) : FieldOn p y J := by
  classical
  obtain ⟨F, instF, finF, k, ι, N, hk2, hcardF, hN, hinj, hline, hmem, hcen, hJPiff⟩ := hblock
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  haveI : CharP F 2 := charP_two_of_card_pow hcardF
  have hF2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h22 : (2 : ℕ) ≠ 2 ∨ Nat.card F ≠ 2 := Or.inr (by rw [hcardF]; omega)
  have h23 : (2 : ℕ) ≠ 2 ∨ Nat.card F ≠ 3 := Or.inr (by rw [hcardF]; omega)
  have hperfM : commutator ↥(StatedSL 2 F) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL F le_rfl h22 h23)
  have hsimple : IsSimpleGroup (LargeEvenProj (StatedSL 2 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F le_rfl h22 h23
  obtain ⟨e₀, hequi⟩ := l154_J_matrix_equiv hp hSp hJ hJS hJy θ ψ hindy B σ hψB hBmem
    (LargeEvenProjMk (StatedSL 2 F)) (QuotientGroup.mk'_surjective _)
    (ker_projMk_uni_le_center _) hsimple ι hmem
    (fun t z hz => by
      have ht := hcen t ⟨z, hz⟩
      rw [CFSG.GH74.L5U5.center_statedSL_eq (F := F) 2] at ht
      exact (QuotientGroup.eq_one_iff t).2 ht)
    (fun z => (hJPiff z).trans ⟨fun ⟨t, ht, hπ⟩ => ⟨t, hπ⟩, fun ⟨t, hπ⟩ => ⟨t, hmem t, hπ⟩⟩)
  obtain ⟨c₁, hc₁b, hc₁σ⟩ := hmoved
  have hnot : MulAut.congr e₀ (MI.indAut p J y hJy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSL 2 F)) Set.univ :=
    l154_notInner_sl2 hF2 ι hperfM σ B e₀ _ hequi N hN {c | h.bar c = c} (map_one h.bar) hc₁b hc₁σ
      (fun c hc => hline c hc)
  obtain ⟨e, he⟩ := exists_notInner_of_eq (largeEvenSLGroup_eq_statedSL (K := F) 2)
    (MI.indAut p J y hJy) ⟨e₀, hnot⟩
  exact fieldOn_of_notInner hp hp2 hJy hyp
    (l154_marking_J hp hJ hJy (r := 1) (k := k) le_rfl (by omega) (fun _ => hk2) hcardF e he)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X
