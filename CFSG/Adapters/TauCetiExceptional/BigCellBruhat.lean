module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Adapters.TauCetiExceptional.BigCellOp

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Minors

variable {A : Type*} [CommRing A] {n : ℕ}

theorem leadMinor_mul_mul {L M U : Matrix (Fin n) (Fin n) A} (hL : ∀ i j, i < j → L i j = 0)
    (hU : ∀ i j, j < i → U i j = 0) (k : ℕ) :
    leadMinor (L * M * U) k = leadMinor L k * leadMinor M k * leadMinor U k := by
  set p : Fin n → Prop := fun i => i.val < k with hp
  have hl : L.toBlock p (fun i => ¬p i) = 0 := by
    ext i j
    have hi := i.2
    have hj := j.2
    simp only [hp] at hi hj
    exact hL _ _ (Fin.lt_def.2 (by omega))
  have hu : U.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    have hi := i.2
    have hj := j.2
    simp only [hp] at hi hj
    exact hU _ _ (Fin.lt_def.2 (by omega))
  rw [leadMinor, leadMinor, leadMinor, leadMinor, Matrix.toBlock_mul_eq_add p p p, hu,
    Matrix.mul_zero, add_zero, Matrix.toBlock_mul_eq_add p p p, hl, Matrix.zero_mul, add_zero,
    Matrix.det_mul, Matrix.det_mul]

theorem lower_diag_mul {D L : Matrix (Fin n) (Fin n) A} (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, i < j → L i j = 0) (i j : Fin n) (hij : i < j) : (D * L) i j = 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hD i k hk.symm, zero_mul])
    (fun hi => absurd (Finset.mem_univ i) hi), hL i j hij, mul_zero]

end Minors

variable {τ : Tag}

abbrev kPos
    (τ : Tag) : ℕ := (Finset.univ.filter fun a : Label τ => 0 < a.weight).card

theorem weight_le_of_precedes {a b : Label τ} (h : b.Precedes a) : a.weight ≤ b.weight := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.ge

theorem position_lt_kPos_iff
    (a : Label τ) : a.position < kPos τ ↔ 0 < a.weight := by
  classical
  constructor
  · intro ha
    by_contra hw
    push Not at hw
    have hsub : (Finset.univ.filter fun b : Label τ => 0 < b.weight) ⊆
        Finset.univ.filter fun b : Label τ => b.Precedes a := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact .inl (by omega)
    have := Finset.card_le_card hsub
    dsimp only [kPos] at ha
    unfold Label.position at ha
    omega
  · intro hw
    have hsub : (Finset.univ.filter fun b : Label τ => b.Precedes a) ⊆
        (Finset.univ.filter fun b : Label τ => 0 < b.weight).erase a := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine Finset.mem_erase.2 ⟨fun e => Label.Precedes.irrefl a (e ▸ hb), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := weight_le_of_precedes hb
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_lt_of_mem (s := Finset.univ.filter fun b : Label τ =>
      0 < b.weight) (Finset.mem_filter.2 ⟨Finset.mem_univ a, hw⟩)
    unfold Label.position
    convert lt_of_le_of_lt h1 h2

theorem kPos_pos (τ : Tag) : 0 < kPos τ :=
  Finset.card_pos.2 ⟨Sum.inr ⟨Pi.single (⟨0, τ.rank_pos⟩ : Fin τ.rank) (1 : ℤ),
    isRoot_single τ _⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      simp only [Label.weight, height_single]
      exact one_pos⟩⟩

theorem kPos_le (τ : Tag) : kPos τ ≤ nLab τ :=
  (Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_univ.le)

theorem leadMinor_kPos_eq_zero
    {K : Type} [CommRing K] {g : (Module.End K (RootModule τ K))ˣ}
    {w : WeylGroup τ} (hg : MapsRootLines g w) (hw : w ≠ 1) :
    leadMinor (natMat τ K g) (kPos τ) = 0 := by
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw
  obtain ⟨c, hc⟩ := hg _ (isRoot_single τ i)
  set b : Label τ := Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩
  have hb : (posEquiv τ b).val < kPos τ := by
    rw [posEquiv_val, position_lt_kPos_iff]
    simp only [b, Label.weight, height_single]
    exact one_pos
  refine Matrix.det_eq_zero_of_column_eq_zero ⟨posEquiv τ b, hb⟩ fun r => ?_
  rw [Matrix.toBlock_apply, natMat_apply, Equiv.symm_apply_apply]
  have hv : Finsupp.single b (1 : K) = rootVec τ K (Pi.single i 1) := by
    rw [rootVec, dite_eq_left (isRoot_single τ i)]
  rw [hv, hc, rootVec, dite_eq_left (IsRoot.smul (isRoot_single τ i) w), Finsupp.smul_apply,
    Finsupp.single_eq_of_ne, smul_zero]
  intro e
  have hpos : ((posEquiv τ).symm (r : Fin (nLab τ))).position < kPos τ := by
    rw [← posEquiv_val, Equiv.apply_symm_apply]
    exact r.2
  have hr' := (position_lt_kPos_iff _).1 hpos
  rw [e] at hr'
  simp only [Label.weight] at hr'
  omega

theorem bigCellDet_eq_zero_of_leadMinor_kPos {K : Type} [CommRing K]
    {M : Matrix (Fin (nLab τ)) (Fin (nLab τ)) K} (h : leadMinor M (kPos τ) = 0) :
    bigCellDet M = 0 := by
  have h1 := kPos_pos τ
  have h2 := kPos_le τ
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨kPos τ - 1, by omega⟩ : Fin (nLab τ))) ?_
  rw [show kPos τ - 1 + 1 = kPos τ by omega]
  exact h

theorem natMat_borel_upper
    {K : Type} [Field K] {b : ModGL τ K} (hb : b ∈ borelGroup τ K)
    (i j : Fin (nLab τ)) (hji : j < i) :
    natMat τ K (b : Module.End K (RootModule τ K)) i j = 0 := by
  rw [natMat_apply]
  exact (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 b hb _ _
    ((precedes_iff_posEquiv_lt _ _).2 (by simpa using hji))

theorem exists_bigCellMat_eq_natMat
    {K : Type} [Field K] {z : ModGL τ K}
    (hz : z ∈ adjointGroup τ K) (hΔ : bigCellDet (natMat τ K z) ≠ 0) :
    ∃ (cm : Fin (nPos τ) → K) (a : Fin τ.rank → Kˣ) (cp : Fin (nPos τ) → K),
      bigCellMat cm a cp = natMat τ K z := by
  have hBS := triangular_borel_structure.{0, 0} τ K
  have hnz : nLong K * z ∈ (adjointGroup τ K : Set (ModGL τ K)) :=
    mul_mem (canonicalRep_mem_adjointGroup _ K _) hz
  rw [adjointGroup_eq_iUnion_bruhatCell] at hnz
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hnz
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hw
  have hz' : z = (nLong K)⁻¹ * b * canonicalRep (coxeterSystem τ) K w * b' := by
    rw [mul_assoc, mul_assoc, ← mul_assoc b, hbb, inv_mul_cancel_left]
  have hTU : ∀ x ∈ borelGroup τ K, ∃ t ∈ torusGroup τ K, ∃ u ∈ posUnipotent τ K, t * u = x := by
    intro x hx
    have hx' : x ∈ (borelGroup τ K : Set (ModGL τ K)) := hx
    rw [hBS.2.2.2.2.1] at hx'
    obtain ⟨t, ht, u, hu, e⟩ := Set.mem_mul.1 hx'
    exact ⟨t, ht, u, hu, e⟩
  obtain ⟨t₁, ht₁, u₁, hu₁, rfl⟩ := hTU b hb
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := hTU b' hb'
  have hN : nLong K ∈ Subgroup.normalizer (torusGroup τ K : Set (ModGL τ K)) :=
    (canonical_weyl_root_transport τ K).2.2 (longest τ)
  have ht₁' : (nLong K)⁻¹ * t₁ * nLong K ∈ torusGroup τ K := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) t₁).1 ht₁
    rwa [inv_inv] at this
  by_cases hww : w = longest τ
  · subst hww
    have hu₁' : t₁ * u₁ * t₁⁻¹ ∈ posUnipotent τ K :=
      (Subgroup.mem_normalizer_iff.1 (hBS.2.2.1 ht₁) u₁).1 hu₁
    have hbij := (positive_root_collection τ K).2 (posRootEnum τ) (posRootEnum_injective τ)
      (range_posRootEnum τ)
    obtain ⟨cm, -, hcm⟩ := hbij.2.2 hu₁'
    obtain ⟨cp, -, hcp⟩ := hbij.2.2 hu₂
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mul_mem ht₁' ht₂)
    refine ⟨cm, a, cp, ?_⟩
    rw [bigCellMat_eq_natMat]
    congr 2
    change (nLong K)⁻¹ * uProd K cm * nLong K * rootDiagUnit τ a * uProd K cp = z
    have e1 : uProd K cm = t₁ * u₁ * t₁⁻¹ := hcm
    have e2 : uProd K cp = u₂ := hcp
    rw [e1, e2, ← ha, hz']
    group
  · exfalso
    apply hΔ
    have hmaps := ((mapsRootLines_canonicalRep (R := K) (longest τ)).inv).mul
      (mapsRootLines_canonicalRep (R := K) w)
    have hne : (longest τ)⁻¹ * w ≠ 1 := fun e => hww (inv_mul_eq_one.1 e).symm
    have hzf : (z : Module.End K (RootModule τ K)) =
        ((((nLong K)⁻¹ * t₁ * nLong K) * ((nLong K)⁻¹ * u₁ * nLong K) :
          (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
        ((((nLong K)⁻¹ * canonicalRep (coxeterSystem τ) K w) :
          (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
        (((t₂ * u₂) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) := by
      rw [← Units.val_mul, ← Units.val_mul, hz']
      congr 1
      group
    have hL : ∀ i j, i < j → natMat τ K ((((nLong K)⁻¹ * t₁ * nLong K) *
        ((nLong K)⁻¹ * u₁ * nLong K) : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) i j = 0 := by
      intro i j hij
      rw [Units.val_mul, map_mul]
      exact lower_diag_mul (natMat_torusGroup ht₁')
        (natMat_negUnipotent (conj_mem_negUnipotent hu₁)).2 i j hij
    apply bigCellDet_eq_zero_of_leadMinor_kPos
    rw [hzf, map_mul, map_mul, leadMinor_mul_mul hL (natMat_borel_upper hb'),
      leadMinor_kPos_eq_zero hmaps hne, mul_zero, zero_mul]

end CFSG.TauCetiBridge.BigCell
