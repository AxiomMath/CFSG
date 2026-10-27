module

public import CFSG.LieType.Chevalley.AllRootWeylInfinitesimal
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.LangRootArithmeticG2

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley.RootWalk

section Tangent

variable (τ : Tag) (R : Type*) [CommRing R]

@[expose] def tangentH (i : Fin τ.rank) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl _ => 0
    | .inr α => ((∑ j, τ.cartan i j * α.1 j : ℤ) : R) • Finsupp.single (Sum.inr α) 1

variable {τ R}

theorem tangentH_hVec (i j : Fin τ.rank) : tangentH τ R i (hVec τ R j) = 0 := by
  rw [hVec, tangentH, Finsupp.linearCombination_single, smul_zero]

theorem tangentH_rootVec (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    tangentH τ R i (rootVec τ R α) = ((∑ j, τ.cartan i j * α j : ℤ) : R) • rootVec τ R α := by
  rw [rootVec_eq_single_of_isRoot' hα, tangentH, Finsupp.linearCombination_single, one_smul]

end Tangent

@[expose] def g2ArtifactRoot (b : Fin 12) : Fin Tag.G2.rank → ℤ :=
  decodeVec (Tag.G2.witnesses.roots.getD b 0)

theorem g2ArtifactRoot_eq : g2ArtifactRoot = ![![-2, -3], ![-1, -3], ![-1, -2], ![-1, -1],
    ![-1, 0], ![0, -1], ![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]] := by
  funext b j
  fin_cases b <;> fin_cases j <;> rfl

theorem g2Witnesses_length : Tag.G2.witnesses.roots.length = 12 :=
  rfl

theorem isRoot_g2ArtifactRoot
    (b : Fin 12) : IsRoot Tag.G2 (g2ArtifactRoot b) :=
  isRoot_decodeVec_witness (by rw [g2Witnesses_length]; exact b.2)

@[expose] def g2FixedPos : Fin 14 → ℕ :=
  ![9, 5, 10, 6, 3, 2, 0, 1, 4, 7, 11, 13, 8, 12]

theorem g2FixedPos_lt (l : Fin 14) : g2FixedPos l < dim Tag.G2 := by
  fin_cases l <;> decide

@[expose] def g2FixedBasis
    (l : Fin 14) : Label Tag.G2 :=
  posLabel (g2FixedPos l) (g2FixedPos_lt l)

theorem g2FixedBasis_injective
    : Function.Injective g2FixedBasis := by
  intro l l' h
  have hpos : g2FixedPos l = g2FixedPos l' := posLabel_injective _ _ h
  have hinj : Function.Injective g2FixedPos := by decide
  exact hinj hpos

theorem g2FixedBasis_bijective
    : Function.Bijective g2FixedBasis := by
  refine ⟨g2FixedBasis_injective, fun b => ?_⟩
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  have hsurj : ∀ p < dim Tag.G2, ∃ l, g2FixedPos l = p := by decide
  obtain ⟨l, rfl⟩ := hsurj p hp
  exact ⟨l, rfl⟩

theorem weight_g2FixedBasis
    (l : Fin 14) :
    (g2FixedBasis l).weight = if g2FixedPos l < Tag.G2.rank then 0
      else height (Tag.G2.rootCertificate.root (g2FixedPos l - Tag.G2.rank)) := by
  unfold g2FixedBasis posLabel
  by_cases h : g2FixedPos l < Tag.G2.rank
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]
    rfl

theorem g2FixedBasis_precedes
    (l : Fin 13) :
    (g2FixedBasis l.castSucc).Precedes (g2FixedBasis l.succ) := by
  fin_cases l
  all_goals try exact Or.inl (by rw [weight_g2FixedBasis, weight_g2FixedBasis]; decide)
  · refine Or.inr ⟨by rw [weight_g2FixedBasis, weight_g2FixedBasis]; decide, ?_⟩
    show Pi.Lex (· < ·) (· < ·) (Tag.G2.rootCertificate.root 1) (Tag.G2.rootCertificate.root 0)
    exact ⟨⟨0, by decide⟩, fun j hj => absurd (Fin.lt_def.1 hj) (Nat.not_lt_zero _), by decide⟩
  · refine Or.inr ⟨by rw [weight_g2FixedBasis, weight_g2FixedBasis]; decide, ?_⟩
    show (⟨0, by decide⟩ : Fin Tag.G2.rank) < ⟨1, by decide⟩
    decide
  · refine Or.inr ⟨by rw [weight_g2FixedBasis, weight_g2FixedBasis]; decide, ?_⟩
    show Pi.Lex (· < ·) (· < ·) (Tag.G2.rootCertificate.root 2) (Tag.G2.rootCertificate.root 5)
    exact ⟨⟨0, by decide⟩, fun j hj => absurd (Fin.lt_def.1 hj) (Nat.not_lt_zero _), by decide⟩

variable (R : Type) [CommRing R]

@[expose] def g2TangentMat
    (k : Fin 14) : Module.End R (RootModule Tag.G2 R) :=
  if h : (k : ℕ) < 12 then pinnedE Tag.G2 R (g2ArtifactRoot ⟨k, h⟩)
  else tangentH Tag.G2 R (Tag.G2.idx (k - 12))

@[expose] def g2MinorPos : Fin 14 → Fin 14 × Fin 14 :=
  ![(6, 0), (5, 0), (3, 0), (2, 0), (1, 0), (2, 1), (2, 3), (0, 1), (2, 4), (2, 7), (0, 5),
    (0, 6), (0, 0), (2, 2)]

@[expose] def g2FixedEntry
    (A : Module.End R (RootModule Tag.G2 R)) (p q : Fin 14) : R :=
  A (Finsupp.single (g2FixedBasis q) 1) (g2FixedBasis p)

@[expose] def g2TangentMinor
    : Matrix (Fin 14) (Fin 14) R :=
  Matrix.of fun k l => g2FixedEntry R (g2TangentMat R k) (g2MinorPos l).1 (g2MinorPos l).2

@[expose] def g2TangentEntry
    (k a c : ℕ) : ℤ :=
  if k < 12 then
    pinnedSignW .G2 k * coefAt a (colOf (entries .G2 (witnessCertPos .G2 k) 1) c)
  else if c < 2 then 0
  else if a = c then
    ∑ j : Fin Tag.G2.rank, Tag.G2.cartan (Tag.G2.idx (k - 12)) j *
      Tag.G2.rootCertificate.root (c - 2) j
  else 0

variable {R}

theorem posCoord_smul_posVec
    {a c : ℕ} (hc : c < dim Tag.G2) (r : R) :
    posCoord Tag.G2 R a (r • posVec Tag.G2 R c) = if a = c then r else 0 := by
  rw [map_smul, posCoord_posVec hc, smul_eq_mul]
  split_ifs <;> simp

theorem g2FixedEntry_eq
    (A : Module.End R (RootModule Tag.G2 R)) (p q : Fin 14) :
    g2FixedEntry R A p q =
      posCoord Tag.G2 R (g2FixedPos p) (A (posVec Tag.G2 R (g2FixedPos q))) := by
  rw [g2FixedEntry, g2FixedBasis, g2FixedBasis, ← posVec_eq_single (g2FixedPos_lt q)]
  simp only [posCoord, g2FixedPos_lt p, ↓reduceDIte, Finsupp.lapply_apply]

theorem posCoord_g2TangentMat
    {F : Type} [Field F] (k : Fin 14) {a c : ℕ} (hc : c < 14) :
    posCoord Tag.G2 F a (g2TangentMat F k (posVec Tag.G2 F c)) = (g2TangentEntry k a c : F) := by
  have hc' : c < dim Tag.G2 := hc
  unfold g2TangentMat g2TangentEntry
  by_cases hk : (k : ℕ) < 12
  · simp only [hk, ↓reduceDIte, ↓reduceIte]
    have hb : (k : ℕ) < Tag.G2.witnesses.roots.length := by
      rw [g2Witnesses_length]
      exact hk
    have hpos := witnessCertPos_lt hb
    have hvalid := (validEntries_of_validB (validB_of_allValid g2_allValid hpos
      (show 1 ∈ [1, 2, 3] by simp))).colOf c
    rw [(rootOperatorFamily Tag.G2).pinnedE_eq_smul_D F (isRoot_g2ArtifactRoot ⟨k, hk⟩)]
    have hs : (rootOperatorFamily Tag.G2).pinnedFamilySign (g2ArtifactRoot ⟨k, hk⟩) =
        pinnedSignW .G2 k := (pinnedSignW_eq hb).symm
    have hD : (rootOperatorFamily Tag.G2).D F ⟨g2ArtifactRoot ⟨k, hk⟩,
        isRoot_g2ArtifactRoot ⟨k, hk⟩⟩ 1 =
        entriesOp Tag.G2 F (entries .G2 (witnessCertPos .G2 k) 1) := by
      change dataD Tag.G2 F ⟨decodeVec (Tag.G2.witnesses.roots.getD k 0), _⟩ 1 = _
      rw [dataD, rootPos_witness hb]
      simp
    rw [hs, hD, LinearMap.smul_apply, entriesOp_posVec _ hc', map_smul,
      posCoord_vecOf a hvalid, smul_eq_mul]
    push_cast
    rfl
  · simp only [hk, ↓reduceDIte, ↓reduceIte]
    by_cases hc2 : c < 2
    · have hc2' : c < Tag.G2.rank := hc2
      have e : posVec Tag.G2 F c = hVec Tag.G2 F ⟨c, hc2⟩ := by
        simp only [posVec, hc2', ↓reduceDIte]
      rw [e, tangentH_hVec, map_zero]
      simp [hc2]
    · have hm : c - 2 < Tag.G2.rootCertificate.roots.length := by
        have : Tag.G2.rootCertificate.roots.length = 12 := rfl
        omega
      have hc2' : ¬c < Tag.G2.rank := hc2
      have e : posVec Tag.G2 F c = rootVec Tag.G2 F (Tag.G2.rootCertificate.root (c - 2)) := by
        simp only [posVec, hc2', ↓reduceDIte]
        rfl
      rw [e, tangentH_rootVec _ (isRoot_rootCertificate_root hm), ← e, posCoord_smul_posVec hc']
      simp only [hc2, ↓reduceIte]
      split_ifs <;> simp

@[expose] def g2MinorDiag : Fin 14 → ℤ :=
  ![-2, 1, -1, -1, 1, 1, 2, 1, -2, -1, -1, 1, 1, 1]

theorem g2TangentEntry_minor
    : ∀ k l : Fin 14,
    g2TangentEntry k (g2FixedPos (g2MinorPos l).1) (g2FixedPos (g2MinorPos l).2) =
      if k = l then g2MinorDiag k else 0 := by
  decide +kernel

theorem g2TangentMinor_eq
    (F : Type) [Field F] :
    g2TangentMinor F = (Matrix.diagonal g2MinorDiag).map (Int.cast : ℤ → F) := by
  ext k l
  rw [g2TangentMinor, Matrix.of_apply, g2FixedEntry_eq,
    posCoord_g2TangentMat k (g2FixedPos_lt _), g2TangentEntry_minor, Matrix.map_apply,
    Matrix.diagonal_apply]

theorem det_g2TangentMinor
    (F : Type) [Field F] : (g2TangentMinor F).det = 8 := by
  rw [g2TangentMinor_eq, show (Matrix.diagonal g2MinorDiag).map (Int.cast : ℤ → F) =
    (Int.castRingHom F).mapMatrix (Matrix.diagonal g2MinorDiag) from rfl, ← RingHom.map_det,
    Matrix.det_diagonal]
  rw [show ∏ i, g2MinorDiag i = 8 by decide]
  simp

theorem linearIndependent_g2TangentMat
    (F : Type) [Field F] [CharP F 3] :
    LinearIndependent F (g2TangentMat F) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hdet : (g2TangentMinor F).det ≠ 0 := by
    rw [det_g2TangentMinor]
    intro h
    have h8 : ((8 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F 3] at h8
    norm_num at h8
  have hv : Matrix.vecMul g (g2TangentMinor F) = 0 := by
    funext l
    have h := congrArg (fun A => g2FixedEntry F A (g2MinorPos l).1 (g2MinorPos l).2) hg
    simp only [g2FixedEntry, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.vecMul, dotProduct, g2TangentMinor, Matrix.of_apply, g2FixedEntry,
      Pi.zero_apply]
    exact h
  exact fun k => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) k

theorem lt_twelve_certWitnessPos
    (α : {α // IsRoot Tag.G2 α}) :
    certWitnessPos .G2 (rootPos α) < 12 := by
  have h := certWitnessPos_lt (τ := .G2) (rootPos_lt α)
  rwa [g2Witnesses_length] at h

@[expose] def g2TangentIndex
    : {α // IsRoot Tag.G2 α} ⊕ Fin Tag.G2.rank → Fin 14
  | .inl α => ⟨certWitnessPos .G2 (rootPos α), by
      have h := lt_twelve_certWitnessPos α
      omega⟩
  | .inr i => ⟨12 + i, by have : (i : ℕ) < 2 := i.2; omega⟩

theorem g2ArtifactRoot_g2TangentIndex
    (α : {α // IsRoot Tag.G2 α})
    (h : certWitnessPos .G2 (rootPos α) < 12) :
    g2ArtifactRoot ⟨certWitnessPos .G2 (rootPos α), h⟩ = α.1 := by
  rw [g2ArtifactRoot]
  exact (decodeVec_certWitnessPos (rootPos_lt α)).trans (root_rootPos α)

theorem g2TangentIndex_injective
    : Function.Injective g2TangentIndex := by
  rintro (α | i) (β | j) h
  · have h' : certWitnessPos .G2 (rootPos α) = certWitnessPos .G2 (rootPos β) :=
      congrArg Fin.val h
    have hα := g2ArtifactRoot_g2TangentIndex α (lt_twelve_certWitnessPos α)
    have hβ := g2ArtifactRoot_g2TangentIndex β (lt_twelve_certWitnessPos β)
    refine congrArg Sum.inl (Subtype.ext ?_)
    rw [← hα, ← hβ]
    exact congrArg g2ArtifactRoot (Fin.ext h')
  · have h1 := (g2TangentIndex (.inl α)).2
    have h2 : (g2TangentIndex (.inl α) : ℕ) = 12 + j := congrArg Fin.val h
    simp only [g2TangentIndex] at h1 h2
    have := certWitnessPos_lt (τ := .G2) (rootPos_lt α)
    rw [g2Witnesses_length] at this
    omega
  · have h2 : 12 + (i : ℕ) = (g2TangentIndex (.inl β) : ℕ) := congrArg Fin.val h
    simp only [g2TangentIndex] at h2
    have := certWitnessPos_lt (τ := .G2) (rootPos_lt β)
    rw [g2Witnesses_length] at this
    omega
  · have h2 : 12 + (i : ℕ) = 12 + j := congrArg Fin.val h
    exact congrArg Sum.inr (Fin.ext (by omega))

theorem linearIndependent_pinnedE_tangentH
    (F : Type) [Field F] [CharP F 3] :
    LinearIndependent F (Sum.elim (fun α : {α // IsRoot Tag.G2 α} => pinnedE Tag.G2 F α.1)
      (tangentH Tag.G2 F)) := by
  have h := (linearIndependent_g2TangentMat F).comp g2TangentIndex g2TangentIndex_injective
  convert h using 1
  funext x
  rcases x with α | i
  · simp only [Sum.elim_inl, Function.comp_apply, g2TangentMat, g2TangentIndex]
    simp only [lt_twelve_certWitnessPos α, ↓reduceDIte]
    rw [g2ArtifactRoot_g2TangentIndex]
  · simp only [Sum.elim_inr, Function.comp_apply, g2TangentMat, g2TangentIndex]
    simp only [show ¬(12 + (i : ℕ) < 12) by omega, ↓reduceDIte]
    congr 1
    exact Fin.ext (by simp [Tag.idx, Nat.mod_eq_of_lt i.2])

section Dual

variable {τ : Tag} {S : Type} [CommRing S]

theorem pinnedX_of_mul_self_eq_zero
    (α : Fin τ.rank → ℤ) {e : S} (he : e * e = 0) :
    (pinnedX τ S α e : Module.End S (RootModule τ S)) =
      (1 : Module.End S (RootModule τ S)) + e • pinnedE τ S α := by
  have h2 : e ^ 2 = 0 := by rw [sq, he]
  have h3 : e ^ 3 = 0 := by rw [pow_succ, h2, zero_mul]
  rw [pinnedX_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [pinnedCoeff_zero, pinnedCoeff_one, h2, h3]

theorem coe_zpow_of_eq_one_add {u : Sˣ} {e : S} (hu : (u : S) = 1 + e) (he : e * e = 0)
    (m : ℤ) : ((u ^ m : Sˣ) : S) = 1 + (m : S) * e := by
  have hinv : ((u⁻¹ : Sˣ) : S) = 1 - e := by
    have h : (u : S) * (1 - e) = 1 := by rw [hu]; linear_combination (-1 : S) * he
    exact (Units.inv_eq_of_mul_eq_one_right h)
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, hu]
    push_cast
    linear_combination (n : S) * he
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hinv]
    push_cast
    linear_combination (n : S) * he

theorem torusElt_of_eq_one_add
    (i : Fin τ.rank) {u : Sˣ} {e : S} (hu : (u : S) = 1 + e)
    (he : e * e = 0) :
    (torusElt τ S i u : Module.End S (RootModule τ S)) =
      (1 : Module.End S (RootModule τ S)) + e • tangentH τ S i := by
  refine rootModule_end_ext (fun j => ?_) fun α hα => ?_
  · rw [torusElt_hVec, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      tangentH_hVec, smul_zero, add_zero]
  · rw [torusElt_rootVec i _ hα, coe_zpow_of_eq_one_add hu he, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.smul_apply, tangentH_rootVec i hα]
    generalize (∑ j, τ.cartan i j * α j) = m
    rw [add_smul, one_smul, mul_comm, mul_smul]

variable (F : Type) [CommRing F]

@[expose] def dualOneAddEps : (DualNumber F)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by
    linear_combination (DualNumber.eps_mul_eps : (DualNumber.eps : DualNumber F) * _ = 0) * -1
  inv_val := by
    linear_combination (DualNumber.eps_mul_eps : (DualNumber.eps : DualNumber F) * _ = 0) * -1

end Dual

theorem exceptional_Lang_G2_tangent_rank_arithmetic
    (k : Type) [Field k] (hk : ringChar k = 3) :
    (∀ i j : Fin Tag.G2.rank, tangentH Tag.G2 k i (hVec Tag.G2 k j) = 0) ∧
    (∀ (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ), IsRoot Tag.G2 α →
      tangentH Tag.G2 k i (rootVec Tag.G2 k α) =
        ((∑ j, Tag.G2.cartan i j * α j : ℤ) : k) • rootVec Tag.G2 k α) ∧
    LinearIndependent k (Sum.elim (fun α : {α // IsRoot Tag.G2 α} => pinnedE Tag.G2 k α.1)
      (tangentH Tag.G2 k)) ∧
    g2ArtifactRoot = ![![-2, -3], ![-1, -3], ![-1, -2], ![-1, -1], ![-1, 0], ![0, -1], ![0, 1],
      ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]] ∧
    Function.Bijective g2FixedBasis ∧
    (∀ l : Fin 13, (g2FixedBasis l.castSucc).Precedes (g2FixedBasis l.succ)) ∧
    (∀ l : Fin 14, g2MinorPos l = (![(6, 0), (5, 0), (3, 0), (2, 0), (1, 0), (2, 1), (2, 3),
      (0, 1), (2, 4), (2, 7), (0, 5), (0, 6), (0, 0), (2, 2)] : Fin 14 → Fin 14 × Fin 14) l) ∧
    (g2TangentMinor (ZMod 3)).det = 2 ∧
    (∀ α : Fin Tag.G2.rank → ℤ,
      (pinnedX Tag.G2 (DualNumber k) α DualNumber.eps :
          Module.End (DualNumber k) (RootModule Tag.G2 (DualNumber k))) =
        (1 : Module.End (DualNumber k) (RootModule Tag.G2 (DualNumber k))) +
          (DualNumber.eps : DualNumber k) • pinnedE Tag.G2 (DualNumber k) α) ∧
    ∀ i : Fin Tag.G2.rank,
      (torusElt Tag.G2 (DualNumber k) i (dualOneAddEps k) :
          Module.End (DualNumber k) (RootModule Tag.G2 (DualNumber k))) =
        (1 : Module.End (DualNumber k) (RootModule Tag.G2 (DualNumber k))) +
          (DualNumber.eps : DualNumber k) • tangentH Tag.G2 (DualNumber k) i := by
  have : CharP k 3 := ringChar.of_eq hk
  refine ⟨tangentH_hVec, fun i α hα => tangentH_rootVec i hα,
    linearIndependent_pinnedE_tangentH k, g2ArtifactRoot_eq, g2FixedBasis_bijective,
    g2FixedBasis_precedes, fun l => rfl, ?_,
    fun α => pinnedX_of_mul_self_eq_zero α DualNumber.eps_mul_eps,
    fun i => torusElt_of_eq_one_add i rfl DualNumber.eps_mul_eps⟩
  rw [det_g2TangentMinor]
  decide

end CFSG.LieType.Chevalley
