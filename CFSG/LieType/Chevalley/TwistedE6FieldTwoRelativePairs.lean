module

public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeRoots
public import CFSG.LieType.Chevalley.F4FieldTwoRootPairs

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap
open CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree (vecBEq vecBEq_iff)
open scoped commutatorElement

theorem exists_pairTable_row
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (hne : r ≠ s) (hne' : r ≠ -s) :
    ∃ row ∈ pairTable .F4, ∃ w : WeylGroup .F4,
      w • orbitCertRoot .F4 row.1 = r ∧ w • orbitCertRoot .F4 row.2.1 = s := by
  obtain ⟨row, ⟨hrow, horb⟩, -⟩ := (rank_two_pair_certificate .F4).1 r s hr hs hne hne'
  obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 horb
  rw [Prod.smul_mk, Prod.mk.injEq] at hw
  exact ⟨row, hrow, w, hw.1, hw.2⟩

theorem exists_weyl_pair_transport
    {r s r' s' : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hr' : IsRoot .F4 r') (hs' : IsRoot .F4 s') (hne : r ≠ s)
    (hne' : r ≠ -s) (hne₂ : r' ≠ s') (hne₂' : r' ≠ -s')
    (hl₁ : f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid r' ⬝ᵥ f4Euclid r')
    (hl₂ : f4Euclid s ⬝ᵥ f4Euclid s = f4Euclid s' ⬝ᵥ f4Euclid s')
    (hip : f4Euclid r ⬝ᵥ f4Euclid s = f4Euclid r' ⬝ᵥ f4Euclid s') :
    ∃ w : WeylGroup .F4, w • r = r' ∧ w • s = s' := by
  obtain ⟨row₁, hrow₁, w₁, h₁r, h₁s⟩ := exists_pairTable_row hr hs hne hne'
  obtain ⟨row₂, hrow₂, w₂, h₂r, h₂s⟩ := exists_pairTable_row hr' hs' hne₂ hne₂'
  have a₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.1) (orbitCertRoot .F4 row₁.1)
  have b₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.2.1) (orbitCertRoot .F4 row₁.2.1)
  have c₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.1) (orbitCertRoot .F4 row₁.2.1)
  have a₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.1) (orbitCertRoot .F4 row₂.1)
  have b₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.2.1) (orbitCertRoot .F4 row₂.2.1)
  have c₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.1) (orbitCertRoot .F4 row₂.2.1)
  simp only [h₁r, h₁s] at a₁ b₁ c₁
  simp only [h₂r, h₂s] at a₂ b₂ c₂
  obtain ⟨e₁, e₂⟩ := f4_pairTable_invariants_injective row₁ hrow₁ row₂ hrow₂
    (a₁.symm.trans (hl₁.trans a₂)) (b₁.symm.trans (hl₂.trans b₂)) (c₁.symm.trans (hip.trans c₂))
  refine ⟨w₂ * w₁⁻¹, ?_, ?_⟩
  · rw [mul_smul, ← h₁r, inv_smul_smul, e₁, h₂r]
  · rw [mul_smul, ← h₁s, inv_smul_smul, e₂, h₂s]

theorem exists_pair_conj
    {r s r' s' : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hr' : IsRoot .F4 r') (hs' : IsRoot .F4 s') (hne : r ≠ s)
    (hne' : r ≠ -s) (hne₂ : r' ≠ s') (hne₂' : r' ≠ -s')
    (hl₁ : f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid r' ⬝ᵥ f4Euclid r')
    (hl₂ : f4Euclid s ⬝ᵥ f4Euclid s = f4Euclid s' ⬝ᵥ f4Euclid s')
    (hip : f4Euclid r ⬝ᵥ f4Euclid s = f4Euclid r' ⬝ᵥ f4Euclid s') :
    ∃ w : WeylGroup .F4, w • r = r' ∧ w • s = s' ∧ ∃ w', IsLift w w' ∧
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈ graphFixedRootGroup TwistTag.E6 K barHom ∧
      ∀ t, (relRootGroup t).map
          (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
        relRootGroup (w • t) := by
  obtain ⟨w, hwr, hws⟩ :=
    exists_weyl_pair_transport hr hs hr' hs' hne hne' hne₂ hne₂' hl₁ hl₂ hip
  obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w
  exact ⟨w, hwr, hws, w', hw', canonicalRep_mem_root hw'.1, map_conj_relRootGroup hw'⟩

@[expose] def relSupport (r s : Fin Tag.F4.rank → ℤ) : Set (Fin Tag.F4.rank → ℤ) :=
  {t | IsRoot .F4 t ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ t = a • r + b • s}

@[expose] def relSpan
    (I : Set (Fin Tag.F4.rank → ℤ)) : Subgroup (ModGL TwistTag.E6.tag K) :=
  ⨆ t ∈ I, relRootGroup t

theorem relRootGroup_le_relSpan
    {I : Set (Fin Tag.F4.rank → ℤ)} {t : Fin Tag.F4.rank → ℤ}
    (ht : t ∈ I) : relRootGroup t ≤ relSpan I :=
  le_iSup₂_of_le t ht le_rfl

theorem relSupport_smul
    (w : WeylGroup .F4) (r s : Fin Tag.F4.rank → ℤ) :
    relSupport (w • r) (w • s) = (fun t => w • t) '' relSupport r s := by
  ext t
  constructor
  · rintro ⟨ht, a, b, ha, hb, rfl⟩
    refine ⟨a • r + b • s, ⟨?_, a, b, ha, hb, rfl⟩,
      by simp only [smul_add, smul_comm w a, smul_comm w b]⟩
    have h := IsRoot.smul ht w⁻¹
    rwa [smul_add, smul_comm w⁻¹ a, smul_comm w⁻¹ b, inv_smul_smul, inv_smul_smul] at h
  · rintro ⟨t, ⟨ht, a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨IsRoot.smul ht w, a, b, ha, hb, by simp only [smul_add, smul_comm w a, smul_comm w b]⟩

theorem map_conj_relSpan
    {w : WeylGroup .F4} {w' : WeylGroup TwistTag.E6.tag} (h : IsLift w w')
    (I : Set (Fin Tag.F4.rank → ℤ)) :
    (relSpan I).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
      relSpan ((fun t => w • t) '' I) := by
  rw [relSpan, relSpan, iSup_image]
  simp only [Subgroup.map_iSup, map_conj_relRootGroup h]

abbrev mixedRoots (r s : Fin Tag.F4.rank → ℤ) : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {β | IsRoot TwistTag.E6.tag β ∧ relProj β ∈ relSupport r s}

theorem nsmul_add_nsmul_coeffs (r s : Fin Tag.F4.rank → ℤ) (a b a₁ b₁ a₂ b₂ : ℕ) :
    a • (a₁ • r + b₁ • s) + b • (a₂ • r + b₂ • s) =
      (a * a₁ + b * a₂) • r + (a * b₁ + b * b₂) • s := by
  simp only [smul_add, add_smul, mul_smul]
  abel

theorem nsmul_add_nsmul_left (r s : Fin Tag.F4.rank → ℤ) (a b a₂ b₂ : ℕ) :
    a • r + b • (a₂ • r + b₂ • s) = (a + b * a₂) • r + (b * b₂) • s := by
  simp only [smul_add, add_smul, mul_smul]
  abel

theorem nsmul_add_nsmul_right (r s : Fin Tag.F4.rank → ℤ) (a b a₂ b₂ : ℕ) :
    a • s + b • (a₂ • r + b₂ • s) = (b * a₂) • r + (a + b * b₂) • s := by
  simp only [smul_add, add_smul, mul_smul]
  abel

theorem one_le_mul_of_one_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

theorem mixedRoots_pos {r s : Fin Tag.F4.rank → ℤ} (hrp : 0 < height r) (hsp : 0 < height s) :
    ∀ β ∈ mixedRoots r s, IsRoot TwistTag.E6.tag β ∧ 0 < height β := by
  rintro β ⟨hβ, -, a, b, ha, hb, hβe⟩
  refine ⟨hβ, ?_⟩
  rw [← height_relProj, hβe, height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem mixedRoots_closed
    (r s : Fin Tag.F4.rank → ℤ) :
    ∀ α ∈ mixedRoots r s, ∀ β ∈ mixedRoots r s, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ mixedRoots r s := by
  rintro α ⟨-, -, a₁, b₁, ha₁, hb₁, hα⟩ β ⟨-, -, a₂, b₂, ha₂, hb₂, hβ⟩ a b ha hb hroot
  refine ⟨hroot, isRoot_relProj hroot, a * a₁ + b * a₂, a * b₁ + b * b₂,
    le_add_right (one_le_mul_of_one_le ha ha₁), le_add_right (one_le_mul_of_one_le ha hb₁), ?_⟩
  rw [relProj_nsmul_add_nsmul, hα, hβ, nsmul_add_nsmul_coeffs]

theorem mixedRoots_perm (r s : Fin Tag.F4.rank → ℤ) :
    ∀ β ∈ mixedRoots r s, permLattice TwistTag.E6.perm β ∈ mixedRoots r s := by
  rintro β ⟨hβ, hβI⟩
  exact ⟨hβ.permLattice TwistTag.E6.cartan_perm, by rw [relProj_permLattice]; exact hβI⟩

theorem pos_of_mem_relFibre {t : Fin Tag.F4.rank → ℤ} (ht : 0 < height t)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ relFibre t) :
    IsRoot TwistTag.E6.tag β ∧ 0 < height β :=
  ⟨hβ.1, by rw [← height_relProj, hβ.2]; exact ht⟩

theorem commutator_rootSpan_relFibre_le
    {r s : Fin Tag.F4.rank → ℤ} (hrp : 0 < height r)
    (hsp : 0 < height s) (hne : r ≠ s) :
    ⁅rootSpan TwistTag.E6.tag K (relFibre r), rootSpan TwistTag.E6.tag K (relFibre s)⁆ ≤
      rootSpan TwistTag.E6.tag K (mixedRoots r s) := by
  set M := mixedRoots r s
  set S := relFibre r ∪ relFibre s ∪ M
  have hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    rintro α ((hα | hα) | hα)
    · exact pos_of_mem_relFibre hrp hα
    · exact pos_of_mem_relFibre hsp hα
    · exact mixedRoots_pos hrp hsp α hα
  have hclosed : ∀ α ∈ S, ∀ β ∈ M, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ M := by
    rintro α ((hα | hα) | hα) β hβM a b ha hb hroot
    · obtain ⟨-, -, a₂, b₂, ha₂, hb₂, hβ⟩ := hβM
      refine ⟨hroot, isRoot_relProj hroot, a + b * a₂, b * b₂, le_add_right ha,
        one_le_mul_of_one_le hb hb₂, ?_⟩
      rw [relProj_nsmul_add_nsmul, hα.2, hβ, nsmul_add_nsmul_left]
    · obtain ⟨-, -, a₂, b₂, ha₂, hb₂, hβ⟩ := hβM
      refine ⟨hroot, isRoot_relProj hroot, b * a₂, a + b * b₂, one_le_mul_of_one_le hb ha₂,
        le_add_right ha, ?_⟩
      rw [relProj_nsmul_add_nsmul, hα.2, hβ, nsmul_add_nsmul_right]
    · exact mixedRoots_closed r s α hα β hβM a b ha hb hroot
  have hMS : M ⊆ S := fun β hβ => Or.inr hβ
  obtain ⟨hle, hnorm⟩ := positive_root_ideal_normality TwistTag.E6.tag K hMS hS hclosed
  have key : ∀ g ∈ rootSpan TwistTag.E6.tag K S, ∀ h ∈ rootSpan TwistTag.E6.tag K M,
      g * h * g⁻¹ ∈ rootSpan TwistTag.E6.tag K M := fun g hg h hh =>
    Subgroup.mem_subgroupOf.1 (hnorm.conj_mem ⟨h, hle hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨g, hg⟩)
  have hN : rootSpan TwistTag.E6.tag K S ≤
      Subgroup.normalizer (rootSpan TwistTag.E6.tag K M : Set (ModGL TwistTag.E6.tag K)) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key g hg h hh, fun hh => ?_⟩
    have h' := key g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using h'
  rw [rootSpan_eq_closure K (relFibre r), rootSpan_eq_closure K (relFibre s)]
  refine commutator_closure_le_of_le_normalizer ?_ ?_ hN ?_
  · rw [← rootSpan_eq_closure]
    exact rootSpan_mono fun β hβ => Or.inl (Or.inl hβ)
  · rw [← rootSpan_eq_closure]
    exact rootSpan_mono fun β hβ => Or.inl (Or.inr hβ)
  · rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d, rfl⟩
    have hαβ : α ≠ β := fun h => hne (by rw [← hα.2, ← hβ.2, h])
    have hcomm := commutator_rootSubgroup_le K hα.1 hβ.1 (pos_of_mem_relFibre hrp hα).2
      (pos_of_mem_relFibre hsp hβ).2 hαβ
    refine (hcomm.trans ?_) (Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure ⟨c, rfl⟩) (Subgroup.subset_closure ⟨d, rfl⟩))
    refine iSup₂_le fun γ hγ => le_iSup₂_of_le γ ?_ le_rfl
    obtain ⟨hγr, a, b, ha, hb, hγe⟩ := hγ
    refine ⟨hγr, isRoot_relProj hγr, a, b, ha, hb, ?_⟩
    rw [hγe, relProj_nsmul_add_nsmul, hα.2, hβ.2]

theorem commutator_relRootGroup_le_of_pos
    {r s : Fin Tag.F4.rank → ℤ} (hrp : 0 < height r)
    (hsp : 0 < height s) (hne : r ≠ s) :
    ⁅relRootGroup r, relRootGroup s⁆ ≤ relSpan (relSupport r s) := by
  have h1 : ⁅relRootGroup r, relRootGroup s⁆ ≤ rootSpan TwistTag.E6.tag K (mixedRoots r s) ⊓
      twistedFixedGroup TwistTag.E6 K barHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_inf.2 ⟨commutator_rootSpan_relFibre_le hrp hsp hne
      (Subgroup.commutator_mem_commutator hx.1 hy.1), ?_⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 hy.2) (inv_mem hx.2)) (inv_mem hy.2)
  refine h1.trans fun g hg => ?_
  obtain ⟨k, O, hO, hrange⟩ : ∃ (k : ℕ) (O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ)),
      Function.Injective O ∧ Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ mixedRoots r s} := by
    have hfin : {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ mixedRoots r s}.Finite :=
      ((finite_setOf_isRoot TwistTag.E6.tag).image TwistTag.E6.diagramOrbit).subset
        fun O' ⟨⟨α, hα, hαO⟩, _⟩ => ⟨α, hα, hαO⟩
    obtain ⟨k, O, hO⟩ := hfin.fin_embedding
    exact ⟨k, O, O.injective, hO⟩
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (mixedRoots_pos hrp hsp) (mixedRoots_perm r s) (mixedRoots_closed r s) O hO hrange
  obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ Set.range O := Set.mem_range_self j
  rw [hrange] at hOj
  obtain ⟨⟨α, hα, hαO⟩, hsub⟩ := hOj
  have hαM : α ∈ mixedRoots r s := hsub (by rw [← hαO]; exact TwistTag.E6.self_mem_diagramOrbit α)
  have hmem : ((u j : ModGL TwistTag.E6.tag K)) ∈ relRootGroup (relProj α) := by
    rw [relRootGroup, relFibre_relProj hα, hαO]
    exact (u j).2
  exact relRootGroup_le_relSpan hαM.2 hmem

theorem pairTable_rep_pos : ∀ row ∈ pairTable .F4,
    0 < height (orbitCertRoot .F4 row.1) ∧ 0 < height (orbitCertRoot .F4 row.2.1) := by
  decide +kernel

theorem commutator_relRootGroup_le
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hne : r ≠ s) (hne' : r ≠ -s) :
    ⁅relRootGroup r, relRootGroup s⁆ ≤ relSpan (relSupport r s) := by
  obtain ⟨row, hrow, w, hwr, hws⟩ := exists_pairTable_row hr hs hne hne'
  obtain ⟨hp₁, hp₂⟩ := pairTable_rep_pos row hrow
  have hne₀ : orbitCertRoot .F4 row.1 ≠ orbitCertRoot .F4 row.2.1 := fun h =>
    hne (by rw [← hwr, ← hws, h])
  obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w
  have h := Subgroup.map_mono
    (f := (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom)
    (commutator_relRootGroup_le_of_pos hp₁ hp₂ hne₀)
  rw [Subgroup.map_commutator, map_conj_relRootGroup hw', map_conj_relRootGroup hw',
    map_conj_relSpan hw', ← relSupport_smul, hwr, hws] at h
  exact h

@[expose] def isRootB (v : Fin Tag.F4.rank → ℤ) : Bool :=
  (List.range 48).any fun k => vecBEq (Tag.F4.rootCertificate.root k) v

theorem isRoot_iff_isRootB
    (v : Fin Tag.F4.rank → ℤ) : IsRoot .F4 v ↔ isRootB v = true := by
  rw [isRoot_f4_iff, isRootB, List.any_eq_true]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, List.mem_range.2 k.2, vecBEq_iff.2 rfl⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, List.mem_range.1 hk⟩, vecBEq_iff.1 h⟩

@[expose] def coeffList (r s : Fin Tag.F4.rank → ℤ) : List (ℕ × ℕ) :=
  (List.range 12).flatMap fun a => ((List.range 12).filter fun b =>
    1 ≤ a && 1 ≤ b && isRootB (a • r + b • s)).map fun b => (a, b)

@[expose] def expectedCoeffs (A B C : ℚ) : List (ℕ × ℕ) :=
  if (A = B ∧ 2 * C = -A) ∨ (A = 1 ∧ B = 1 ∧ C = 0) then [(1, 1)]
  else if A = 2 ∧ B = 1 ∧ C = -1 then [(1, 1), (1, 2)]
  else if A = 1 ∧ B = 2 ∧ C = -1 then [(1, 1), (2, 1)]
  else []

theorem coeffList_pairTable : ∀ row ∈ pairTable .F4,
    coeffList (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.2.1) =
      expectedCoeffs (f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.1))
        (f4Euclid (orbitCertRoot .F4 row.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1))
        (f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1)) := by
  decide +kernel

theorem height_root_le : ∀ k : Fin 48, height (Tag.F4.rootCertificate.root k) ≤ 11 := by
  decide +kernel

theorem mem_coeffList
    {r s : Fin Tag.F4.rank → ℤ} (hrp : 0 < height r) (hsp : 0 < height s)
    (a b : ℕ) : (a, b) ∈ coeffList r s ↔ 1 ≤ a ∧ 1 ≤ b ∧ IsRoot .F4 (a • r + b • s) := by
  simp only [coeffList, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a', -, b', ⟨-, ⟨ha, hb⟩, hroot⟩, rfl, rfl⟩
    exact ⟨ha, hb, (isRoot_iff_isRootB _).2 hroot⟩
  · rintro ⟨ha, hb, hroot⟩
    obtain ⟨k, hk⟩ := isRoot_f4_iff.1 hroot
    have hh := height_root_le k
    rw [hk, height_nsmul_add_nsmul] at hh
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hab : (a : ℤ) + b ≤ 11 := by nlinarith
    refine ⟨a, by omega, b, ⟨by omega, ⟨ha, hb⟩, (isRoot_iff_isRootB _).1 hroot⟩, rfl, rfl⟩

theorem relSupport_eq
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (hne : r ≠ s) (hne' : r ≠ -s) :
    relSupport r s = (fun ab : ℕ × ℕ => ab.1 • r + ab.2 • s) ''
      {ab | ab ∈ expectedCoeffs (f4Euclid r ⬝ᵥ f4Euclid r) (f4Euclid s ⬝ᵥ f4Euclid s)
        (f4Euclid r ⬝ᵥ f4Euclid s)} := by
  obtain ⟨row, hrow, w, hwr, hws⟩ := exists_pairTable_row hr hs hne hne'
  obtain ⟨hp₁, hp₂⟩ := pairTable_rep_pos row hrow
  have eA := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.1)
  have eB := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.2.1) (orbitCertRoot .F4 row.2.1)
  have eC := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.2.1)
  simp only [hwr, hws] at eA eB eC
  rw [eA, eB, eC, ← coeffList_pairTable row hrow, ← hwr, ← hws, relSupport_smul]
  ext t
  constructor
  · rintro ⟨t, ⟨ht, a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨(a, b), (mem_coeffList hp₁ hp₂ a b).2 ⟨ha, hb, ht⟩,
      by simp only [smul_add, smul_comm w a, smul_comm w b]⟩
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb, hroot⟩ := (mem_coeffList hp₁ hp₂ a b).1 hab
    exact ⟨a • orbitCertRoot .F4 row.1 + b • orbitCertRoot .F4 row.2.1, ⟨hroot, a, b, ha, hb, rfl⟩,
      by simp only [smul_add, smul_comm w a, smul_comm w b]⟩

theorem relSupport_cases
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (hne : r ≠ s) (hne' : r ≠ -s) :
    (((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = 0)) → relSupport r s = {r + s}) ∧
    ((f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = {r + s, r + 2 • s}) ∧
    ((f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = {r + s, 2 • r + s}) ∧
    (¬((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = 0)) →
      ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = -1) →
      ¬(f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = ∅) := by
  rw [relSupport_eq hr hs hne hne', expectedCoeffs]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h₁ h₂ h₃ => ?_⟩
  · rw [ite_eq_left h]
    ext t
    simp
  · have h₀ : ¬((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = 0)) := by
      rw [h.1, h.2.1, h.2.2]
      norm_num
    rw [ite_eq_right h₀, ite_eq_left h]
    ext t
    simp [eq_comm]
  · have h₀ : ¬((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = 0)) := by
      rw [h.1, h.2.1, h.2.2]
      norm_num
    have h₀' : ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = -1) := by
      rw [h.1]
      norm_num
    rw [ite_eq_right h₀, ite_eq_right h₀', ite_eq_left h]
    ext t
    simp [eq_comm]
  · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
    ext t
    simp

end CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
