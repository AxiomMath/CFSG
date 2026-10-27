module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem mem_normalizer_torusGroup_of_conj
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {Q : ModGL τ L}
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t') :
    Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  obtain ⟨A, hA, -, N, hNpos, hAN⟩ := CFSG.HardMathSupport.C14W1.exists_lattice_map Q hQT
  set B := A ^ (N - 1) with hB
  have hBA : B * A = A ^ N := by
    rw [hB, ← pow_succ, Nat.sub_add_cancel hNpos]
  have hsurj : ∀ t, ∃ t', Q * rootDiagUnit τ t' * Q⁻¹ = rootDiagUnit τ t := by
    intro t
    refine ⟨CFSG.HardMathSupport.C14Torus.tmap B t, ?_⟩
    rw [hA, CFSG.HardMathSupport.C14Torus.tmap_tmap, hBA, hAN,
      CFSG.HardMathSupport.C14Torus.tmap_one_left]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    rw [hA l]
    exact rootDiagUnit_mem_torusGroup (CFSG.HardMathSupport.C14Torus.tmap A l)
  · intro hx
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    obtain ⟨l', hl'⟩ := hsurj l
    have hx' : x = rootDiagUnit τ l' := by
      have h := congrArg (fun z => Q⁻¹ * z * Q) (hl.trans hl'.symm)
      simpa [mul_assoc] using h
    rw [hx']
    exact rootDiagUnit_mem_torusGroup l'

private theorem inf_centralizer_torusGroup_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] :
    adjointGroup τ L ⊓ Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) =
      torusGroup τ L := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgAdj, hgCent⟩ := Subgroup.mem_inf.1 hg
    refine mem_torusGroup_of_forall_commute_rootDiagUnit hgAdj fun t => ?_
    exact ((Subgroup.mem_centralizer_iff.1 hgCent) (rootDiagUnit τ t)
      (rootDiagUnit_mem_torusGroup t)).symm
  · intro g hg
    refine Subgroup.mem_inf.2 ⟨torusGroup_le_adjointGroup hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    exact rootDiagUnit_mul_comm_of_mem_torusGroup t hg

private theorem cartan_perm_zpow_apply {t : TwistTag} (j : ℤ) (i k : Fin t.tag.rank) :
    t.tag.cartan ((t.perm ^ j) i) ((t.perm ^ j) k) = t.tag.cartan i k := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg j
  · subst j
    exact TwistTag.cartan_perm_pow t n i k
  · subst j
    rw [zpow_neg, zpow_natCast]
    exact cartan_perm_symm (fun i k => TwistTag.cartan_perm_pow t n i k) i k

private theorem symmetrizedCartan_permLattice_zpow {t : TwistTag} (j : ℤ)
    (i k : Fin t.tag.rank) :
    t.tag.symmetrizedCartan ((t.perm ^ j) i) ((t.perm ^ j) k) =
      t.tag.symmetrizedCartan i k := by
  have hsymm : t.tag.symmetrizedCartan = t.tag.cartan := by
    cases t <;> decide
  simpa only [hsymm] using cartan_perm_zpow_apply (t := t) j i k

private theorem diagramMap_pow_conj_pinnedX
    {t : TwistTag} {L : Type} [Field L] (h2 : (2 : L) = 0) (n : ℕ)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (c : L) :
    diagramMap t L ^ n * pinnedX t.tag L α c * (diagramMap t L ^ n)⁻¹ =
      pinnedX t.tag L (permLattice (t.perm ^ n) α) c := by
  induction n generalizing α c with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one]
    change pinnedX t.tag L α c =
      pinnedX t.tag L (permLattice (1 : Equiv.Perm (Fin t.tag.rank)) α) c
    rw [show permLattice (1 : Equiv.Perm (Fin t.tag.rank)) α = α from by
      rw [Equiv.Perm.one_def]
      rfl]
  | succ n ih =>
    rw [pow_succ, pow_succ (t.perm), permLattice_mul]
    calc
      diagramMap t L ^ n * diagramMap t L * pinnedX t.tag L α c *
          (diagramMap t L ^ n * diagramMap t L)⁻¹ =
          diagramMap t L ^ n * (diagramMap t L * pinnedX t.tag L α c *
            (diagramMap t L)⁻¹) * (diagramMap t L ^ n)⁻¹ := by
        rw [mul_inv_rev]
        group
      _ = diagramMap t L ^ n * pinnedX t.tag L (permLattice t.perm α) c *
            (diagramMap t L ^ n)⁻¹ := by
        rw [← twistHom_id_eq, twistHom_id_pinnedX h2 hα]
      _ = pinnedX t.tag L (permLattice (t.perm ^ n) (permLattice t.perm α)) c :=
        ih (IsRoot.permLattice t.cartan_perm hα) c

private theorem diagramMap_inv_pow_conj_pinnedX
    {t : TwistTag} {L : Type} [Field L] (h2 : (2 : L) = 0) (n : ℕ)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (c : L) :
    (diagramMap t L ^ n)⁻¹ * pinnedX t.tag L α c * ((diagramMap t L ^ n)⁻¹)⁻¹ =
      pinnedX t.tag L (permLattice ((t.perm ^ n)⁻¹) α) c := by
  have hα' : IsRoot t.tag (permLattice ((t.perm ^ n)⁻¹) α) :=
    IsRoot.permLattice (cartan_perm_symm (fun i k => TwistTag.cartan_perm_pow t n i k)) hα
  have h := diagramMap_pow_conj_pinnedX (t := t) (L := L) h2 n hα' c
  have hperm : permLattice (t.perm ^ n) (permLattice ((t.perm ^ n)⁻¹) α) = α := by
    rw [← permLattice_mul, mul_inv_cancel, Equiv.Perm.one_def]
    rfl
  rw [hperm] at h
  rw [inv_inv, ← h]
  group

private theorem diagramMap_zpow_conj_pinnedX
    {t : TwistTag} {L : Type} [Field L] (h2 : (2 : L) = 0) (j : ℤ)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (c : L) :
    diagramMap t L ^ j * pinnedX t.tag L α c * (diagramMap t L ^ j)⁻¹ =
      pinnedX t.tag L (permLattice (t.perm ^ j) α) c := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg j
  · subst j
    exact diagramMap_pow_conj_pinnedX h2 n hα c
  · subst j
    simpa only [zpow_neg, zpow_natCast] using diagramMap_inv_pow_conj_pinnedX h2 n hα c

private def permLatticeAddEquiv {t : TwistTag} (j : ℤ) :
    (Fin t.tag.rank → ℤ) ≃+ (Fin t.tag.rank → ℤ) where
  toFun := permLattice (t.perm ^ j)
  invFun := permLattice ((t.perm ^ j)⁻¹)
  left_inv := by
    intro v
    rw [← permLattice_mul, inv_mul_cancel]
    rw [Equiv.Perm.one_def]
    rfl
  right_inv := by
    intro v
    rw [← permLattice_mul, mul_inv_cancel]
    rw [Equiv.Perm.one_def]
    rfl
  map_add' := by
    intro x y
    rfl

private theorem exists_eq_mul_canonicalRep_of_mem_adjoint
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {Q' : ModGL τ L}
    (hQadj : Q' ∈ adjointGroup τ L)
    (hQnorm : Q' ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hCV : adjointGroup τ L ⊓ Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) =
      torusGroup τ L) :
    ∃ h ∈ torusGroup τ L, ∃ w : WeylGroup τ,
      Q' = h * canonicalRep (coxeterSystem τ) L w ∧
      (∀ x y : Fin τ.rank → ℤ, iform (w • x) (w • y) = iform x y) ∧
      (∀ α, IsRoot τ α → IsRoot τ (w • α)) ∧
      (∀ α, IsRoot τ α → ∀ c : L, canonicalRep (coxeterSystem τ) L w *
        pinnedX τ L α c * (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (w • α) c) ∧
      (∀ t, ∃ t', canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ t *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ t') ∧
      (adjointGroup τ L).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom = adjointGroup τ L := by
  obtain ⟨h, hh, w, hQeq⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer
      (k := L) (V := (torusGroup τ L : Set (ModGL τ L))) (fun _ hx => hx) hCV
      (Subgroup.mem_inf.2 ⟨hQadj, hQnorm⟩)
  refine ⟨h, hh, w, hQeq, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact iform_smul w x y
  · intro α hα
    exact IsRoot.smul hα w
  · intro α hα c
    exact canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero w hα c
  · intro t
    have hmem := canonicalRep_mem_normalizer (R := L) w
    exact exists_rootDiagUnit_eq_of_mem_torusGroup
      ((Subgroup.mem_normalizer_iff.1 hmem (rootDiagUnit τ t)).1
        (rootDiagUnit_mem_torusGroup t))
  · exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer (canonicalRep_mem_adjointGroup (coxeterSystem τ) L w))

theorem exists_eq_torus_mul_pinned
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {Q' : ModGL τ L}
    (hQT : ∀ t, ∃ t', Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t')
    (hQ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n) :
    ∃ h ∈ torusGroup τ L, ∃ Q₀ : ModGL τ L, ∃ θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ),
      Q' = h * Q₀ ∧ (∀ x y, iform (θ x) (θ y) = iform x y) ∧
      (∀ α, IsRoot τ α → IsRoot τ (θ α)) ∧
      (∀ α, IsRoot τ α → ∀ c : L, Q₀ * pinnedX τ L α c * Q₀⁻¹ = pinnedX τ L (θ α) c) ∧
      (∀ t, ∃ t', Q₀ * rootDiagUnit τ t * Q₀⁻¹ = rootDiagUnit τ t') ∧
      (adjointGroup τ L).map (MulAut.conj Q₀).toMonoidHom = adjointGroup τ L := by
  classical
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hQTnorm := mem_normalizer_torusGroup_of_conj (τ := τ) (L := L) hQT
  have hCV := inf_centralizer_torusGroup_eq (τ := τ) (L := L)
  rcases hQ with hQadj | ⟨t, j, htag, n, hn, hQeq⟩
  · obtain ⟨h, hh, w, hQeq, hiform, hroot, hX, hT, hadj⟩ :=
      exists_eq_mul_canonicalRep_of_mem_adjoint (τ := τ) (L := L) hQadj hQTnorm hCV
    exact ⟨h, hh, canonicalRep (coxeterSystem τ) L w,
      DistribMulAction.toAddEquiv (Fin τ.rank → ℤ) w, hQeq, hiform, hroot, hX, hT, hadj⟩
  · subst τ
    have hQeq' : Q' = diagramMap t L ^ j * n := by simpa using hQeq
    have hPnormT : diagramMap t L ∈
        Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
        rw [diagramMap_mul_rootDiagUnit, mul_assoc, mul_inv_cancel, mul_one]
        exact rootDiagUnit_mem_torusGroup _
      · intro hx
        obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
        have hforward : diagramMap t L *
            rootDiagUnit t.tag (fun i => b (t.perm i)) * (diagramMap t L)⁻¹ =
            rootDiagUnit t.tag b := by
          rw [diagramMap_mul_rootDiagUnit, mul_assoc, mul_inv_cancel, mul_one]
          congr 1
          funext i
          simp
        have hx' : x = rootDiagUnit t.tag (fun i => b (t.perm i)) := by
          have h := congrArg (fun z => (diagramMap t L)⁻¹ * z * diagramMap t L)
            (hb.trans hforward.symm)
          simpa [mul_assoc] using h
        rw [hx']
        exact rootDiagUnit_mem_torusGroup _
    have hPzpowNormT : diagramMap t L ^ j ∈
        Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) :=
      Subgroup.zpow_mem _ hPnormT j
    have hnNormT : n ∈
        Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) := by
      have hPinv : (diagramMap t L ^ j)⁻¹ ∈
          Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) :=
        Subgroup.inv_mem _ hPzpowNormT
      have hn_eq : n = (diagramMap t L ^ j)⁻¹ * Q' := by
        rw [hQeq']
        group
      rw [hn_eq]
      exact Subgroup.mul_mem _ hPinv hQTnorm
    obtain ⟨h₁, hh₁, w, hn_eq, -, -, -, -, -⟩ :=
      exists_eq_mul_canonicalRep_of_mem_adjoint (τ := t.tag) (L := L) hn hnNormT hCV
    refine ⟨diagramMap t L ^ j * h₁ * (diagramMap t L ^ j)⁻¹,
      (Subgroup.mem_normalizer_iff.1 hPzpowNormT h₁).1 hh₁,
      diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w,
      (DistribMulAction.toAddEquiv (Fin t.tag.rank → ℤ) w).trans
        (permLatticeAddEquiv (t := t) j), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hQeq', hn_eq]
      group
    · intro x y
      change iform (permLattice (t.perm ^ j) (w • x))
        (permLattice (t.perm ^ j) (w • y)) = iform x y
      rw [CFSG.LieType.Chevalley.ToralSign.iform_permLattice
        (fun i k => symmetrizedCartan_permLattice_zpow (t := t) j i k)]
      exact iform_smul w x y
    · intro α hα
      exact IsRoot.permLattice (fun i k => cartan_perm_zpow_apply (t := t) j i k)
        (IsRoot.smul hα w)
    · intro α hα c
      change (diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w) *
          pinnedX t.tag L α c *
          (diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w)⁻¹ =
          pinnedX t.tag L (permLattice (t.perm ^ j) (w • α)) c
      calc
        (diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w) *
            pinnedX t.tag L α c *
            (diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w)⁻¹ =
            diagramMap t L ^ j *
              (canonicalRep (coxeterSystem t.tag) L w * pinnedX t.tag L α c *
                (canonicalRep (coxeterSystem t.tag) L w)⁻¹) *
              (diagramMap t L ^ j)⁻¹ := by group
        _ = diagramMap t L ^ j * pinnedX t.tag L (w • α) c *
              (diagramMap t L ^ j)⁻¹ := by
            rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα c]
        _ = pinnedX t.tag L (permLattice (t.perm ^ j) (w • α)) c :=
            diagramMap_zpow_conj_pinnedX h2 j (IsRoot.smul hα w) c
    · intro s
      have hmem : diagramMap t L ^ j * canonicalRep (coxeterSystem t.tag) L w ∈
          Subgroup.normalizer (torusGroup t.tag L : Set (ModGL t.tag L)) :=
        Subgroup.mul_mem _ hPzpowNormT (canonicalRep_mem_normalizer (R := L) w)
      exact exists_rootDiagUnit_eq_of_mem_torusGroup
        ((Subgroup.mem_normalizer_iff.1 hmem (rootDiagUnit t.tag s)).1
          (rootDiagUnit_mem_torusGroup s))
    · have hPmap : (adjointGroup t.tag L).map
          (MulAut.conj (diagramMap t L ^ j)).toMonoidHom = adjointGroup t.tag L := by
        simpa using CFSG.LieType.AlgebraicGroups.map_conj_diagramMap_zpow
          (t := t) (L := L) j
      have hnmap : (adjointGroup t.tag L).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) L w)).toMonoidHom =
          adjointGroup t.tag L :=
        CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer
          (Subgroup.le_normalizer
            (canonicalRep_mem_adjointGroup (coxeterSystem t.tag) L w))
      rw [map_mul MulAut.conj (diagramMap t L ^ j)
        (canonicalRep (coxeterSystem t.tag) L w)]
      rw [CFSG.LieType.Chevalley.map_toMonoidHom_mul_mulAut, hnmap, hPmap]

theorem bijOn_familyKernel_of_mapsTo_famM
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {e : ℕ} {h Q₀ : ModGL τ L} (hh : h ∈ torusGroup τ L)
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} (hθ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQ₀ : ∀ α, IsRoot τ α → ∀ c : L, Q₀ * pinnedX τ L α c * Q₀⁻¹ = pinnedX τ L (θ α) c)
    {F₀ : adjointGroup τ L →* adjointGroup τ L}
    (hF₀ : ∀ g, (F₀ g : ModGL τ L) = frobTwistGL τ L 2 e (h * Q₀) g)
    (hM : ∀ g ∈ famM a, F₀ g ∈ famM a) :
    Set.BijOn θ (familyKernel a) (familyKernel a) := by
  classical
  have hmaps : Set.MapsTo θ (familyKernel a) (familyKernel a) := by
    intro α hα
    obtain ⟨hαroot, hαchar⟩ := hα
    have hθroot : IsRoot τ (θ α) := hθ α hαroot
    refine ⟨hθroot, fun i => ?_⟩
    have hXspan : pinnedX τ L α 1 ∈ rootSpan τ L (familyKernel a) := by
      rw [rootSpan_eq_closure]
      exact Subgroup.subset_closure ⟨α, ⟨hαroot, hαchar⟩, 1, rfl⟩
    have hXadj : pinnedX τ L α 1 ∈ adjointGroup τ L :=
      rootSpan_le_adjointGroup L (familyKernel a) hXspan
    let X : adjointGroup τ L := ⟨pinnedX τ L α 1, hXadj⟩
    have hXmem : X ∈ famM a :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hXspan)
    have hFXmem : F₀ X ∈ famM a := hM X hXmem
    have hFXgroup : ((F₀ X : adjointGroup τ L) : ModGL τ L) ∈ familyGroup (K := L) a :=
      Subgroup.mem_subgroupOf.1 hFXmem
    have hFX : ((F₀ X : adjointGroup τ L) : ModGL τ L) =
        pinnedX τ L (θ α) (torusRootChar h (θ α)) := by
      rw [hF₀ X, frobTwistGL_apply]
      rw [show (X : ModGL τ L) = pinnedX τ L α 1 from rfl]
      rw [entrywiseFrobGL_pinnedX (p := 2) e α 1, map_one]
      calc
        (h * Q₀) * pinnedX τ L α 1 * (h * Q₀)⁻¹ =
            h * (Q₀ * pinnedX τ L α 1 * Q₀⁻¹) * h⁻¹ := by group
        _ = h * pinnedX τ L (θ α) 1 * h⁻¹ := by rw [hQ₀ α hαroot 1]
        _ = pinnedX τ L (θ α) (torusRootChar h (θ α) * 1) :=
          conj_pinnedX_of_mem_torusGroup hh hθroot 1
        _ = pinnedX τ L (θ α) (torusRootChar h (θ α)) := by rw [mul_one]
    have hcent : pinnedX τ L (θ α) (torusRootChar h (θ α)) ∈ familyCentralizer τ L a := by
      rw [← hFX]
      exact familyGroup_le_familyCentralizer (K := L) a hFXgroup
    have hcomm := (mem_familyCentralizer.1 hcent).2 i
    rw [rootDiagUnit_conj_pinnedX (K := L) (a i) hθroot
      (torusRootChar h (θ α))] at hcomm
    have hmul : (rootChar (a i) (θ α) : L) * torusRootChar h (θ α) =
        torusRootChar h (θ α) :=
      pinnedX_injective τ L (θ α) hcomm
    have hu : torusRootChar h (θ α) ≠ 0 :=
      torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) (θ α)
    have hone : (rootChar (a i) (θ α) : L) = 1 := by
      refine mul_right_cancel₀ hu ?_
      simpa using hmul
    exact Units.ext hone
  have hfin : (familyKernel a).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1
  exact (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 fun α _ β _ h => θ.injective h

end CFSG.HardMathSupport.C14Idx
