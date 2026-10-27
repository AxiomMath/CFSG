module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMap
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniLevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

@[expose] def uniBlockSub (h : UnitaryFieldData p f K) (I : Finset ℕ) :
    (j : Option ↥I) → Subgroup (uniBlockGroup K s ε I j)
  | none => hypSU h s ε
  | some b => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →* _).range

theorem eIdx_ne_of_ne {r : ℕ} {I : Finset ℕ} {b b' : ℕ} (hb : b ∈ I) (hb' : b' ∈ I)
    (hb1 : 1 ≤ b) (hb1' : 1 ≤ b') (hne : b' ≠ b) (hbr : b ≤ r) (hbr' : b' ≤ r)
    (k : Fin (b' - predCut I b')) (k' : Fin (b - predCut I b)) :
    eIdx r ε hbr' k ≠ eIdx r ε hbr k' := by
  intro he
  have e := congrArg fullPos he
  rw [fullPos_eIdx, fullPos_eIdx] at e
  have := k.isLt
  have := k'.isLt
  have := predCut_lt (I := I) hb1
  have := predCut_lt (I := I) hb1'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := le_predCut hb' hlt
    omega
  · have := le_predCut hb hlt
    omega

theorem eBlockHom_leviEHom_self (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {r : ℕ}
    {I : Finset ℕ} {b : ℕ} (hb : b ∈ I) (hb1 : 1 ≤ b) (hbr : b ≤ r)
    (A : Matrix.SpecialLinearGroup (Fin (b - predCut I b)) K)
    (hA : leviEHom h ε hbr A ∈ flagStabilizer h r ε ↑I) :
    eBlockHom h hε hb hb1 hbr ⟨_, hA⟩ = Matrix.SpecialLinearGroup.toGL A := by
  ext k k'
  simp only [coe_eBlockHom, coe_leviEHom, submatrix_apply, eIdx_eq_inl_finIdx,
    ToralCensus.leviMatTwistedA, blk3_inl_inl, extendMat_apply_map]
  rfl

theorem eBlockHom_leviEHom_of_ne (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {r : ℕ}
    {I : Finset ℕ} {b b' : ℕ} (hb : b ∈ I) (hb' : b' ∈ I) (hb1 : 1 ≤ b) (hb1' : 1 ≤ b')
    (hbr : b ≤ r) (hbr' : b' ≤ r) (hbb : b' ≠ b)
    (A : Matrix.SpecialLinearGroup (Fin (b' - predCut I b')) K)
    (hA : leviEHom h ε hbr' A ∈ flagStabilizer h r ε ↑I) :
    eBlockHom h hε hb hb1 hbr ⟨_, hA⟩ = 1 := by
  ext k k'
  simp only [coe_eBlockHom, coe_leviEHom, submatrix_apply, eIdx_eq_inl_finIdx,
    ToralCensus.leviMatTwistedA, blk3_inl_inl]
  rw [extendMat_apply_of_not_mem _ _ (Or.inl fun ⟨k₀, hk₀⟩ =>
    eIdx_ne_of_ne (ε := ε) hb hb' hb1 hb1' hbb hbr hbr' k₀ k
      (by rw [eIdx_eq_inl_finIdx, eIdx_eq_inl_finIdx, hk₀]))]
  by_cases hkk : k = k'
  · subst hkk
    simp
  · rw [Units.val_one, one_apply_ne hkk, one_apply_ne fun he => hkk (finIdx_injective hbr he)]

theorem resBlockHom_leviEHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ}
    (ht : t ∈ I) {a b : ℕ} (hbt : b ≤ t) (A : Matrix.SpecialLinearGroup (Fin (b - a)) K)
    (hA : leviEHom h ε ((hbt.trans (Nat.le_add_right t s))) A ∈
      flagStabilizer h (t + s) ε I) :
    resBlockHom h hε ht ⟨_, hA⟩ = 1 := by
  have hD : barInvT h (extendMat (finIdx_injective (a := a)
      (hbt.trans (Nat.le_add_right t s))) (A : Matrix (Fin (b - a)) (Fin (b - a)) K)) =
      extendMat (finIdx_injective (a := a) (hbt.trans (Nat.le_add_right t s)))
        (barInvT h (A : Matrix (Fin (b - a)) (Fin (b - a)) K)) :=
    barInvT_extendMat h _ (by rw [A.2]; exact isUnit_one)
  have hout : ∀ i : Fin s, Fin.natAdd t i ∉ Set.range (finIdx (a := a)
      (hbt.trans (Nat.le_add_right t s))) := fun i hi => by
    rw [mem_range_finIdx] at hi
    simp at hi
    omega
  ext x y
  simp only [coe_resBlockHom, coe_leviEHom, submatrix_apply, ToralCensus.leviMatTwistedA]
  rcases x with i | l | i <;> rcases y with j | m | j
  · simp only [resIdx, blk3_inl_inl]
    rw [extendMat_apply_of_not_mem _ _ (Or.inl (hout i))]
    simp [one_apply]
  all_goals first
    | (simp [resIdx, blk3, one_apply]; done)
    | skip
  · simp only [resIdx, blk3_inr_inr_inr_inr, hD]
    rw [extendMat_apply_of_not_mem _ _ (Or.inl (hout i))]
    simp [one_apply]

theorem resBlockHom_leviResHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ}
    (ht : t ∈ I) (B : hypSU h s ε) (hB : leviResHom h hε t B ∈ flagStabilizer h (t + s) ε I) :
    resBlockHom h hε ht ⟨_, hB⟩ = (B : GL (HypIndex s ε) K) := by
  ext x y
  rw [coe_resBlockHom, coe_leviResHom, submatrix_extendMat]

theorem eBlockHom_leviResHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) {b : ℕ} (hb : b ∈ I) (B : hypSU h s ε)
    (hB : leviResHom h hε t B ∈ flagStabilizer h (t + s) ε ↑I) :
    eBlockHom h hε hb (hI.le b hb).1 ((hI.le b hb).2.trans (Nat.le_add_right t s)) ⟨_, hB⟩ =
      1 := by
  ext k k'
  rw [coe_eBlockHom, coe_leviResHom, submatrix_extendMat_of_disjoint _ (eIdx_injective _)]
  · rfl
  · intro k₀ y he
    have e := congrArg fullPos he
    rw [fullPos_eIdx, fullPos_resIdx] at e
    have := k₀.isLt
    have := (hI.le b hb).2
    omega

theorem uniLeviHom_leviEHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (b : ↥I) (A : Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K)
    (hA : leviEHom h ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)) A ∈
      flagStabilizer h (t + s) ε ↑I) :
    uniLeviHom h hε hI ⟨_, hA⟩ =
      Pi.mulSingle (M := uniBlockGroup K s ε I) (some b) (Matrix.SpecialLinearGroup.toGL A) := by
  funext j
  rcases j with _ | b'
  · rw [Pi.mulSingle_eq_of_ne (Option.some_ne_none b).symm]
    exact resBlockHom_leviEHom h hε (Finset.mem_coe.mpr hI.mem) (hI.le b.1 b.2).2 A hA
  · by_cases hbb : b' = b
    · subst hbb
      rw [Pi.mulSingle_eq_same]
      exact eBlockHom_leviEHom_self h hε b'.2 (hI.le b'.1 b'.2).1
        ((hI.le b'.1 b'.2).2.trans (Nat.le_add_right t s)) A hA
    · rw [Pi.mulSingle_eq_of_ne (by simpa using hbb)]
      exact eBlockHom_leviEHom_of_ne h hε b'.2 b.2 (hI.le b'.1 b'.2).1 (hI.le b.1 b.2).1
        ((hI.le b'.1 b'.2).2.trans (Nat.le_add_right t s))
        ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s))
        (fun he => hbb (Subtype.ext he.symm)) A hA

theorem uniLeviHom_leviResHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (B : hypSU h s ε)
    (hB : leviResHom h hε t B ∈ flagStabilizer h (t + s) ε ↑I) :
    uniLeviHom h hε hI ⟨_, hB⟩ =
      Pi.mulSingle (M := uniBlockGroup K s ε I) none (B : GL (HypIndex s ε) K) := by
  funext j
  rcases j with _ | b
  · rw [Pi.mulSingle_eq_same]
    exact resBlockHom_leviResHom h hε (Finset.mem_coe.mpr hI.mem) B hB
  · rw [Pi.mulSingle_eq_of_ne (Option.some_ne_none b)]
    exact eBlockHom_leviResHom h hε hI b.2 B hB

theorem pi_uniBlockSub_le_range (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) h I) ≤ (uniLeviHom h hε hI).range := by
  classical
  rw [Subgroup.pi_le_iff]
  rintro (_ | b)
  · rintro _ ⟨B, hB, rfl⟩
    have hmem := leviResHom_mem_flagStabilizer h hε t (I := ↑I) (fun c hc => (hI.le c hc).2)
      ⟨B, hB⟩
    exact ⟨⟨_, hmem⟩, uniLeviHom_leviResHom h hε hI ⟨B, hB⟩ hmem⟩
  · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
    have hbr := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
    have hmem := leviEHom_mem_flagStabilizer h hε (a := predCut I b.1) hbr (I := ↑I)
      (fun c hc => (hI.le c hc).2.trans (Nat.le_add_right t s))
      (fun c hc => by
        by_cases hcb : c < b.1
        · exact Or.inl (le_predCut hc hcb)
        · exact Or.inr (not_lt.mp hcb)) A
    exact ⟨⟨_, hmem⟩, uniLeviHom_leviEHom h hε hI b A hmem⟩

theorem commutator_range_le_pi (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    ⁅(uniLeviHom (s := s) h hε hI).range, (uniLeviHom (s := s) h hε hI).range⁆ ≤
      Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) h I) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def]
  rintro _ ⟨z, hz, rfl⟩
  refine (Subgroup.mem_pi _).mpr fun j _ => ?_
  rcases j with _ | b
  · have hdet := Abelianization.commutator_subset_ker
      (Matrix.GeneralLinearGroup.det.comp (resBlockHom h hε (Finset.mem_coe.mpr hI.mem))) hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hdet
    refine mem_hypSU.mpr ⟨resBlock_gram h hε (Finset.mem_coe.mpr hI.mem) z, ?_⟩
    have := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    exact this
  · have hdet := Abelianization.commutator_subset_ker
      (Matrix.GeneralLinearGroup.det.comp (eBlockHom h hε b.2 (hI.le b.1 b.2).1
        ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))) hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hdet
    change _ ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →* _).range
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet

end CFSG.AGLEmbedding.LeviBlock
