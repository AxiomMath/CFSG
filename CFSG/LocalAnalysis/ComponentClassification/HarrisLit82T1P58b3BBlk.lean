module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BA4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOComm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOSign
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthArith
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

namespace P58b3

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

abbrev tBlockP (I : Finset (Fin d)) : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
  ((oIsoBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _)

theorem blockP_le_tBlockP (I : Finset (Fin d)) : blockP K hw I ≤ tBlockP hw I :=
  map_mono fun _ hg => oBlock_le_oIsoBlock hw I hg

theorem tBlockP_le_centralizer (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) :
    tBlockP hw I ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _) := by
  rintro _ ⟨g, hg, rfl⟩
  replace hg : (g : GL (Fin d) K) ∈ oIsoBlock K hw I := hg
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact commute_sign_of_mem hw J I hI hg

theorem projH_injective_of_odd (h2 : (2 : K) ≠ 0) (hd : Odd d) :
    Function.Injective (projH (matrixDerived (oQ (diagGL hw)))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hs : g ∈ (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ (diagGL hw))) := by
    rwa [← QuotientGroup.eq_one_iff]
  rw [mem_subgroupOf] at hs
  obtain ⟨c, hc⟩ := hs
  have hdet := det_eq_one_of_mem_commutator g.2
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    (matrixDerived_le_isometryGroup hw h2 g.2)
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagGL] at hiso
  have hc2 : (c : K) * c = 1 := by
    set k : Fin d := ⟨0, hd.pos⟩
    have h := congrFun (congrFun hiso k) k
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
      at h
    have h' : (c : K) * c * w k = 1 * w k := by linear_combination h
    exact mul_right_cancel₀ (hw k) h'
  have hc1 : (c : K) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hdet
    exact hdet
  apply Subtype.ext
  rw [← hc, show c = 1 from Units.ext hc1, map_one]
  rfl

theorem eq_one_of_mem_tBlockP_of_mem_compl (h2 : (2 : K) ≠ 0) (hd : Odd d)
    {I : Finset (Fin d)} {r : StatedProj (matrixDerived (oQ (diagGL hw)))}
    (h₁ : r ∈ tBlockP hw I) (h₂ : r ∈ tBlockP hw Iᶜ) : r = 1 := by
  obtain ⟨B, hB, rfl⟩ := h₁
  obtain ⟨B', hB', hBB'⟩ := h₂
  have he : B' = B := projH_injective_of_odd hw h2 hd hBB'
  subst he
  replace hB : (B' : GL (Fin d) K) ∈ oIsoBlock K hw I := hB
  replace hB' : (B' : GL (Fin d) K) ∈ oIsoBlock K hw Iᶜ := hB'
  have h1 : B' = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hi : i ∈ I
    · have := ((mem_oIsoBlock_iff hw).1 hB').2 i j (Or.inl (by simpa using hi))
      rw [this]
      simp [Matrix.one_apply]
    · have := ((mem_oIsoBlock_iff hw).1 hB).2 i j (Or.inl hi)
      rw [this]
      simp [Matrix.one_apply]
  rw [h1, map_one]

theorem projH_sign_not_mem_tBlockP_compl (hK : ringChar K ≠ 2) (hd : Odd d) {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty) :
    projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∉ tBlockP hw Jᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rintro ⟨B, hB, hBe⟩
  have he : B = ⟨signGL K J, hJ⟩ := projH_injective_of_odd hw h2 hd hBe
  replace hB : (B : GL (Fin d) K) ∈ oIsoBlock K hw Jᶜ := hB
  have hS : signGL K J ∈ oIsoBlock K hw Jᶜ := by
    rw [he] at hB
    exact hB
  obtain ⟨i, hi⟩ := hJne
  have h := ((mem_oIsoBlock_iff hw).1 hS).2 i i (Or.inl (by simpa using hi))
  rw [coe_signGL, signMat_apply_self, ite_eq_left hi, ite_eq_left rfl] at h
  exact h2 (by linear_combination -h)

omit hw in
theorem pow_apply_of_isolated {I : Finset (Fin d)} {B : Matrix (Fin d) (Fin d) K} {c : K}
    (hB : ∀ i ∈ I, ∀ j, B i j = if i = j then c else 0) (k : ℕ) :
    ∀ i ∈ I, ∀ j, (B ^ k) i j = if i = j then c ^ k else 0 := by
  induction k with
  | zero =>
    intro i _ j
    simp [Matrix.one_apply]
  | succ k ih =>
    intro i hi j
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih i hi]
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [ite_eq_right (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl, hB i hi j]
    split_ifs <;> ring

theorem mem_tBlockP_compl_of_commute [Finite K] (hK : ringChar K ≠ 2) (hd : Odd d)
    (hker : OKer (oQ (diagGL hw))) {J I : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I))
    {r : StatedProj (matrixDerived (oQ (diagGL hw)))}
    (hrx : r ∈ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hrc : ∀ y ∈ blockP K hw I, r * y = y * r) (hro : Odd (orderOf r)) :
    r ∈ tBlockP hw Iᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨B, rfl⟩ := projH_surjective r
  have hBiso : (B : GL (Fin d) K) ∈ matrixIsometries (oQ (diagGL hw)) :=
    matrixDerived_le_isometries _ B.2
  have hκ : oκ _ (linPair (B : GL (Fin d) K) hBiso) =
      conjProjH (matrixDerived (oQ (diagGL hw))) ⟨B, B.2⟩ := oκ_linPair_eq_conj hBiso B.2
  have hfix : ∀ y ∈ blockP K hw I, oκ _ (linPair (B : GL (Fin d) K) hBiso) y = y := by
    intro y hy
    rw [hκ, MonoidHom.comp_apply, MulAut.conj_apply]
    change projH _ B * y * (projH _ B)⁻¹ = y
    rw [hrc y hy, mul_inv_cancel_right]
  have ht : oκ _ (linPair (B : GL (Fin d) K) hBiso) (projH _ ⟨signGL K J, hJ⟩) =
      projH _ ⟨signGL K J, hJ⟩ := by
    rw [hκ, MonoidHom.comp_apply, MulAut.conj_apply]
    change projH _ B * _ * (projH _ B)⁻¹ = _
    rw [mem_centralizer_singleton_iff.mp hrx, mul_inv_cancel_right]
  obtain ⟨-, c, hc⟩ := GSThmB.QPUCl.kappa_scalar_on_block hK hw hker hJ hI hIc hNF hq hfix ht
  simp only [linPair_left] at hc
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    (matrixDerived_le_isometryGroup hw h2 B.2)
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := by
    rcases hNF with ⟨I₀, hI₀, hI₀3, -, -⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    exact ⟨a, hI₀ ha⟩
  have hc2 : (c : K) * c = 1 := by
    have h := congrFun (congrFun hiso i₀) i₀
    rw [coe_diagGL, Matrix.mul_apply] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_apply_eq] at h
    have hcol : ∀ l, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) l i₀ =
        if i₀ = l then (c : K) else 0 :=
      fun l => (hc i₀ hi₀ l).2
    rw [Finset.sum_eq_single i₀ (fun l _ hl => by rw [hcol l, ite_eq_right (Ne.symm hl)]; ring)
      (fun h => absurd (Finset.mem_univ _) h), hcol i₀, ite_eq_left rfl] at h
    have h' : (c : K) * c * w i₀ = 1 * w i₀ := by linear_combination h
    exact mul_right_cancel₀ (hw i₀) h'
  have hBm : B ^ orderOf (projH _ B) = 1 := by
    apply projH_injective_of_odd hw h2 hd
    rw [map_pow, pow_orderOf_eq_one, map_one]
  have hcm : (c : K) ^ orderOf (projH _ B) = 1 := by
    have h := pow_apply_of_isolated (B := ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
      (fun i hi j => (hc i hi j).1) (orderOf (projH _ B)) i₀ hi₀ i₀
    rw [ite_eq_left rfl] at h
    rw [← h]
    have e : (((B ^ orderOf (projH _ B) : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^
          orderOf (projH _ B) := by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    rw [← e, hBm]
    simp
  have hc1 : (c : K) = 1 := by
    obtain ⟨k, hk⟩ := hro
    rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hcm
    exact hcm
  refine ⟨B, ?_, rfl⟩
  show (B : GL (Fin d) K) ∈ oIsoBlock K hw Iᶜ
  rw [mem_oIsoBlock_iff]
  refine ⟨matrixDerived_le_isometryGroup hw h2 B.2, fun i j hij => ?_⟩
  rcases hij with hi | hj
  · have hi' : i ∈ I := by simpa using hi
    rw [(hc i hi' j).1, hc1]
  · have hj' : j ∈ I := by simpa using hj
    rw [(hc j hj' i).2, hc1]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem le_tBlockP_compl_of_isSubnormal [Finite K] (hK : ringChar K ≠ 2) (hd : Odd d)
    (hker : OKer (oQ (diagGL hw))) {J I : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I))
    {R : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hRx : R ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR : (R.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hRs : Group.IsSolvable R) (hodd : R ≤ closure {y | y ∈ R ∧ Odd (orderOf y)}) :
    R ≤ tBlockP hw Iᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set C := centralizer ({projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw)))} : Set
    (StatedProj (matrixDerived (oQ (diagGL hw))))) with hC
  have hPC : blockP K hw I ≤ C := blockP_le_centralizer hw J I hI hJ
  have hcomp : CFSG.IsComponent ((blockP K hw I).subgroupOf C) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hPC).symm hq,
      isSubnormal_blockP hw hK J I hI hJ⟩
  have hRs' : Group.IsSolvable (R.subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hRx).toMonoidHom)
      (subgroupOfEquivOfLe hRx).injective
  have hcomm := (LocalCores.component_solvable_centralizer hRs' hR).1 _ hcomp
  have hrc : ∀ r ∈ R, ∀ y ∈ blockP K hw I, r * y = y * r := by
    intro r hr y hy
    have h := Subgroup.commutator_mem_commutator
      (show (⟨y, hPC hy⟩ : ↥C) ∈ (blockP K hw I).subgroupOf C from mem_subgroupOf.mpr hy)
      (show (⟨r, hRx hr⟩ : ↥C) ∈ R.subgroupOf C from mem_subgroupOf.mpr hr)
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact (congrArg Subtype.val h).symm
  refine hodd.trans (closure_le _ |>.mpr ?_)
  rintro y ⟨hyR, hyo⟩
  exact mem_tBlockP_compl_of_commute hw hK hd hker hJ hI hIc hNF hq (hRx hyR) (hrc y hyR) hyo

theorem eq_one_of_mem_tBlockP_of_card_le_two [Finite K] (h3 : Nat.card K = 3)
    {I : Finset (Fin d)} (hI2 : I.card ≤ 2) {r : StatedProj (matrixDerived (oQ (diagGL hw)))}
    (hr : r ∈ tBlockP hw I) (hro : Odd (orderOf r)) : r = 1 := by
  obtain ⟨B, hB, rfl⟩ := hr
  replace hB : (B : GL (Fin d) K) ∈ oIsoBlock K hw I := hB
  obtain ⟨hBI, hBs⟩ := (mem_oIsoBlock_iff hw).1 hB
  have hBR := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hBI
  rw [coe_diagGL] at hBR
  set D : Matrix (Fin d) (Fin d) K := ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ with hD
  have hsim : D * diagonal w * Dᵀ = diagonal fun x => 1 * w x := by
    rw [hD, Matrix.transpose_transpose, hBR]
    simp
  have hD8 : D ^ 8 = 1 := by
    refine pow_eight_of_blocks h3 hw one_ne_zero hsim fun x => ?_
    by_cases hx : x ∈ I
    · refine ⟨I, hx, ?_, fun y z hyz => ?_⟩
      · have : 0 < I.card := Finset.card_pos.2 ⟨x, hx⟩
        omega
      · rw [hD, Matrix.transpose_apply]
        by_cases hy : y ∈ I
        · have hz : z ∉ I := hyz.1 hy
          have hzy : z ≠ y := fun h => hz (by rw [h]; exact hy)
          rw [hBs z y (Or.inl hz), ite_eq_right hzy]
        · have hz : z ∈ I := by
            by_contra hz
            exact hy (hyz.2 hz)
          have hzy : z ≠ y := fun h => hy (by rw [← h]; exact hz)
          rw [hBs z y (Or.inr hy), ite_eq_right hzy]
    · refine ⟨{x}, Finset.mem_singleton_self x, Or.inl (Finset.card_singleton x),
        fun y z hyz => ?_⟩
      rw [hD, Matrix.transpose_apply]
      by_cases hy : y = x
      · have hz : z ≠ x := fun h => hyz.1 (by rw [hy]; exact Finset.mem_singleton_self x)
          (by rw [h]; exact Finset.mem_singleton_self x)
        rw [hy, hBs z x (Or.inr hx), ite_eq_right hz]
      · have hz : z = x := by
          by_contra hz
          exact hy (Finset.mem_singleton.1 (hyz.2 (by simpa using hz)))
        rw [hz, hBs x y (Or.inl hx), ite_eq_right (fun h => hy h.symm)]
  have hB8 : B ^ 8 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    have h := congrArg Matrix.transpose hD8
    rw [Matrix.transpose_pow, hD, Matrix.transpose_transpose, Matrix.transpose_one] at h
    exact h
  have h8 : projH _ B ^ 8 = 1 := by rw [← map_pow, hB8, map_one]
  have hdvd : orderOf (projH _ B) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · rw [hk] at hro
      exact absurd hro (by
        rw [Nat.not_odd_iff_even]
        exact (Nat.even_pow.2 ⟨even_two, h.ne'⟩))
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

open Burgoyne.PSL (isoOrthGL trans_commutator isQuasisimple_trans map_commutator_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial
  (orthogonal_low_dimensional_fixed_derived_component_coverage)

omit hw in
theorem isQuasisimple_omegaR_of_five_le [Finite K] (hK : ringChar K ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (R : GL (Fin n) K) (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    IsQuasisimple (Burgoyne.C.omegaR R) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  set e := isoOrthGL hK R hR with he
  have hquasi : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) →
      IsQuasisimple (Burgoyne.C.omegaR R) := fun hq => by
    have h := isQuasisimple_trans e hq
    rwa [trans_commutator] at h
  by_cases hT : ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact hquasi (CatalogueBOrthogonal.derived_quasisimple Q h2 hQnd hT3.ge hTQ)
  have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQnd
    (by rw [hdim]; omega) hT
  rw [hdim] at hcases
  rcases hcases with h | h | h | h
  · omega
  · omega
  · obtain ⟨-, -, -, -, -, h5c, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inl ⟨hodd, Or.inr (Or.inr (by rw [hdim]; exact h))⟩)
    obtain ⟨-, -, -, -, -, -, hq⟩ := h5c hodd (by rw [hdim]; exact h)
    exact hquasi hq
  · obtain ⟨-, -, -, -, -, -, h6c⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inr (Or.inl ⟨hodd, by rw [hdim]; exact h, hT⟩))
    obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h6c hodd (by rw [hdim]; exact h) hT
    exact hquasi hq

theorem isQuasisimple_blockP_of_five_le [Finite K] (hK : ringChar K ≠ 2) {I : Finset (Fin d)}
    (hI5 : 5 ≤ I.card) (hIc : Iᶜ.Nonempty) : IsQuasisimple (blockP K hw I) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at e
  exact LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_omegaR_of_five_le hK hI5
    (diagGL (wRes_ne_zero hw I)) (diagGL_transpose (wRes_ne_zero hw I)))

@[expose] def OddGen (Y : Type*) [Group Y] : Prop :=
  closure {y : Y | Odd (orderOf y)} = ⊤

omit hw in
theorem OddGen.of_surjective {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] {f : Y →* Y'}
    (hf : Function.Surjective f) (h : OddGen Y) : OddGen Y' := by
  rw [OddGen, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ closure {y : Y | Odd (orderOf y)} := h ▸ mem_top x
  have hmap : (closure {y : Y | Odd (orderOf y)}).map f ≤ closure {y : Y' | Odd (orderOf y)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨z, hz, rfl⟩
    exact subset_closure (Odd.of_dvd_nat hz (orderOf_map_dvd f z))
  exact hmap ⟨x, hx, rfl⟩

omit hw in
theorem OddGen.le_closure {G : Type*} [Group G] {R : Subgroup G} (h : OddGen ↥R) :
    R ≤ closure {y | y ∈ R ∧ Odd (orderOf y)} := by
  intro r hr
  have hr' : (⟨r, hr⟩ : ↥R) ∈ closure {y : ↥R | Odd (orderOf y)} := h ▸ mem_top _
  have hmap : (closure {y : ↥R | Odd (orderOf y)}).map R.subtype ≤
      closure {y | y ∈ R ∧ Odd (orderOf y)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨z, hz, rfl⟩
    exact subset_closure ⟨z.2, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩
  exact hmap ⟨⟨r, hr⟩, hr', rfl⟩

omit hw in
theorem exists_odd_orderOf_lift_of_finite {Y Y' : Type*} [Group Y] [Finite Y] [Group Y']
    {f : Y →* Y'} (hf : Function.Surjective f) {u : Y'} (hu : Odd (orderOf u)) :
    ∃ g : Y, f g = u ∧ Odd (orderOf g) := by
  obtain ⟨g, rfl⟩ := hf u
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hdvd : 2 ^ a ∣ orderOf g := ⟨m, hn⟩
  have hga : orderOf (g ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hcop : (2 ^ a).Coprime (orderOf (f g)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hu)
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(g ^ 2 ^ a) ^ b, ?_, ?_⟩
  · rw [map_pow, map_pow, hb]
  · rw [← hga] at hm
    exact Odd.of_dvd_nat hm (orderOf_pow_dvd _)

omit hw in
theorem OddGen.of_quotient {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) (h : OddGen (Y ⧸ N)) : OddGen Y := by
  set H := closure {y : Y | Odd (orderOf y)} with hH
  have hNH : N ≤ H := fun n hn => subset_closure (Odd.of_dvd_nat hN (by
    rw [← Subgroup.orderOf_mk n hn]
    exact _root_.orderOf_dvd_natCard _))
  have hmap : H.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff, ← h, closure_le]
    intro u hu
    obtain ⟨g, rfl, hg⟩ := exists_odd_orderOf_lift_of_finite (QuotientGroup.mk'_surjective N) hu
    exact ⟨g, subset_closure hg, rfl⟩
  rw [OddGen, eq_top_iff]
  intro y _
  have hy : QuotientGroup.mk' N y ∈ H.map (QuotientGroup.mk' N) := hmap ▸ mem_top _
  obtain ⟨h', hh', he⟩ := hy
  have h1 : h'⁻¹ * y ∈ N := QuotientGroup.eq.1 he
  have h2 : y = h' * (h'⁻¹ * y) := by group
  rw [h2]
  exact mul_mem hh' (hNH h1)

omit hw in
theorem oddGen_sl23 : OddGen SL(2, ZMod 3) := by
  rw [OddGen, eq_top_iff,
    ← LieType.HighestRoot.closure_orderOf_three_eq_top_of_mulEquiv card_zmod_three
      (MulEquiv.refl SL(2, ZMod 3))]
  exact closure_mono fun y hy => by
    change orderOf y = 3 at hy
    change Odd (orderOf y)
    rw [hy]
    decide

omit hw in
theorem oddGen_psl23 : OddGen PSL(2, ZMod 3) :=
  oddGen_sl23.of_surjective (QuotientGroup.mk'_surjective _)

omit hw in
theorem mem_leftRightImage_of_odd {g : DeterminantIsometries K} (hg : Odd (orderOf g)) :
    g ∈ leftRightImage K := by
  have h1 : orderOf (QuotientGroup.mk' (leftRightImage K) g) ∣ orderOf g := orderOf_map_dvd _ g
  have h2 : orderOf (QuotientGroup.mk' (leftRightImage K) g) ∣ 2 :=
    (_root_.orderOf_dvd_natCard _).trans leftRightImage_index_dvd_two
  have h3 : orderOf (QuotientGroup.mk' (leftRightImage K) g) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hg) h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

omit hw in
theorem exists_central_involution_of_normal_four [Finite K] (hK : Nat.card K = 3) {m : ℕ}
    (hm : m = 4) (R : GL (Fin m) K) (hR : (R : Matrix (Fin m) (Fin m) K)ᵀ = R)
    (hq : ¬ IsQuasisimple (Burgoyne.C.omegaR R)) {Y : Type*} [Group Y] [Finite Y]
    (φ : Y ≃* ↥(CatalogueBGraphForm.isometryGroup m K R)) {M : Subgroup Y} [M.Normal]
    {H : Subgroup ↥M} (hH : H.IsSubnormal) (hodd : OddGen ↥H) {r : ↥M} (hr : r ∈ H)
    (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∃ s ∈ H, (∀ h ∈ H, s * h = h * s) ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hodd' : Odd (Nat.card K) := by rw [hK]; decide
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK2 R hR
  have hdim : Module.finrank K (Fin m → K) = 4 := by rw [Module.finrank_fin_fun, hm]
  set e₁ := isoOrthGL hK2 R hR with he₁
  obtain ⟨S, hS2, hSQ⟩ : ∃ S : Submodule K (Fin m → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, Q x = 0 := by
    by_contra hS
    obtain ⟨-, -, -, -, h4n, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
      Q hQnd (Or.inl ⟨hodd', Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, -, -, -, -, -, -, -, hq'⟩ := h4n hodd' hdim hS
    apply hq
    have h := isQuasisimple_trans e₁ hq'
    rwa [trans_commutator] at h
  obtain ⟨-, e₂, -, -, -⟩ := split_four_determinant_form_isometry Q hQnd hdim S hS2 hSQ
  set Φ : Y ≃* DeterminantIsometries K := φ.trans (e₁.symm.trans e₂) with hΦ
  set H' : Subgroup (DeterminantIsometries K) := (H.map M.subtype).map Φ.toMonoidHom with hH'
  have hHY : (H.map M.subtype).IsSubnormal := by
    refine IsSubnormal.trans (map_subtype_le _) ?_ (Subgroup.Normal.isSubnormal inferInstance)
    rw [show (H.map M.subtype).subgroupOf M = H from
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _]
    exact hH
  have hH's : H'.IsSubnormal := hHY.map Φ.surjective
  have hH'C : H' ≤ leftRightImage K := by
    have hcl := (hodd.of_surjective (f := ((H.equivMapOfInjective M.subtype
      M.subtype_injective).trans ((H.map M.subtype).equivMapOfInjective Φ.toMonoidHom
        Φ.injective)).toMonoidHom) (MulEquiv.surjective _)).le_closure
    refine hcl.trans (closure_le _ |>.mpr ?_)
    rintro y ⟨-, hy⟩
    exact mem_leftRightImage_of_odd hy
  have hrm : Φ (r : Y) ∈ H' := ⟨r, ⟨r, hr, rfl⟩, rfl⟩
  obtain ⟨s', ⟨s, hs, rfl⟩, hs'⟩ := rhoL_neg_one_mem hK hH'C hH's.subgroupOf hrm
    (by rw [← map_pow, ← Subgroup.coe_pow, hr3, Subgroup.coe_one, map_one])
    (fun h => hr1 (by
      apply M.subtype_injective
      apply Φ.injective
      rw [map_one, map_one]
      exact h))
  have hs'' : Φ (s : Y) = rhoL (-1 : SL(2, K)) := hs'
  refine ⟨s, hs, fun h _ => ?_, ?_⟩
  · apply M.subtype_injective
    apply Φ.injective
    simp only [map_mul, Subgroup.coe_subtype]
    rw [hs'']
    exact (mem_center_iff.mp rhoL_neg_one_mem_center _).symm
  · rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq Φ, hs'', orderOf_rhoL_neg_one h2]

theorem exists_central_involution_of_le_tBlockP [Finite K] (hK : Nat.card K = 3) (hd : Odd d)
    {I : Finset (Fin d)} (hI4 : I.card = 4) (hIc : Iᶜ.Nonempty)
    (hq : ¬ IsQuasisimple (blockP K hw I))
    {H : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} (hHI : H ≤ tBlockP hw I)
    (hH : (H.subgroupOf (tBlockP hw I)).IsSubnormal) (hodd : OddGen ↥H) {r} (hr : r ∈ H)
    (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∃ s ∈ H, (∀ h ∈ H, s * h = h * s) ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  set A := (oIsoBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) with hA
  set M₂ : Subgroup ↥(oIsoBlock K hw I) :=
    (matrixDerived (oQ (diagGL hw))).subgroupOf (oIsoBlock K hw I) with hM₂
  have hM₂n : M₂.Normal := by
    have hΩn : ((matrixDerived (oQ (diagGL hw))).subgroupOf
        (CatalogueBGraphForm.isometryGroup d K (diagGL hw))).Normal := by
      rw [matrixDerived_oQ h2 _ (diagGL_transpose hw), ← Subgroup.map_subtype_commutator,
        show ((commutator ↥(CatalogueBGraphForm.isometryGroup d K (diagGL hw))).map
          (CatalogueBGraphForm.isometryGroup d K (diagGL hw)).subtype).subgroupOf
            (CatalogueBGraphForm.isometryGroup d K (diagGL hw)) =
          commutator ↥(CatalogueBGraphForm.isometryGroup d K (diagGL hw)) from
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _]
      infer_instance
    exact normal_subgroupOf_of_le hΩn (matrixDerived_le_isometryGroup hw h2) (oIsoBlock_le hw I)
  let ψ₁ : ↥A ≃* ↥(tBlockP hw I) := A.equivMapOfInjective _ (projH_injective_of_odd hw h2 hd)
  let ψ₂ : ↥A ≃* ↥(oIsoBlock K hw I ⊓ matrixDerived (oQ (diagGL hw))) :=
    (A.equivMapOfInjective (matrixDerived (oQ (diagGL hw))).subtype
      (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _))
  let ψ₃ : ↥M₂ ≃* ↥(oIsoBlock K hw I ⊓ matrixDerived (oQ (diagGL hw))) :=
    (M₂.equivMapOfInjective _ (oIsoBlock K hw I).subtype_injective).trans
      (MulEquiv.subgroupCongr ((subgroupOf_map_subtype _ _).trans (inf_comm _ _)))
  let ψ : ↥(tBlockP hw I) ≃* ↥M₂ := (ψ₁.symm.trans ψ₂).trans ψ₃.symm
  set H₃ : Subgroup ↥M₂ := (H.subgroupOf (tBlockP hw I)).map ψ.toMonoidHom with hH₃
  have hHe : ↥H ≃* ↥H₃ := (subgroupOfEquivOfLe hHI).symm.trans
    ((H.subgroupOf (tBlockP hw I)).equivMapOfInjective _ ψ.injective)
  obtain ⟨eP⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at eP
  have hq' : ¬ IsQuasisimple (Burgoyne.C.omegaR (diagGL (wRes_ne_zero hw I))) := fun h =>
    hq (LocalCores.isQuasisimple_of_mulEquiv eP.symm h)
  set r₀ : ↥(tBlockP hw I) := ⟨r, hHI hr⟩ with hr₀
  have hr₀1 : r₀ ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
  obtain ⟨s₀, hs₀, hs₀c, hs₀2⟩ := exists_central_involution_of_normal_four hK hI4
    (diagGL (wRes_ne_zero hw I)) (diagGL_transpose (wRes_ne_zero hw I)) hq'
    (oIsoBlockEquiv hw I).symm (M := M₂) (H := H₃) (hH.map ψ.surjective)
    (hodd.of_surjective (f := hHe.toMonoidHom) hHe.surjective) (r := ψ r₀)
    (Subgroup.mem_map_of_mem ψ.toMonoidHom (mem_subgroupOf.mpr hr))
    (by rw [← map_pow, show r₀ ^ 3 = 1 from Subtype.ext (by simpa using hr3), map_one])
    (fun h => hr₀1 (ψ.injective (h.trans (map_one ψ).symm)))
  obtain ⟨t, ht, rfl⟩ := hs₀
  refine ⟨t, mem_subgroupOf.mp ht, fun h hh => ?_, ?_⟩
  · have hc := hs₀c (ψ ⟨h, hHI hh⟩) ⟨⟨h, hHI hh⟩, mem_subgroupOf.mpr hh, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (ψ.injective hc)
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ]
    exact hs₀2

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
