module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_eq compInd
  compInd_mul_apply mul_compInd_apply compInd_apply commute_compInd_iff commute_signMat_iff
  isSubnormal_subgroupOf_of_normalizes)
open scoped commutatorElement

section RingBlock

variable {A : Type*} [Ring A] {c : A}

abbrev blkL (c B : A) : A := B * (1 - c) + c

theorem one_sub_mul_self (hc : c * c = c) : (1 - c) * c = 0 := by
  rw [sub_mul, one_mul, hc, sub_self]

theorem mul_one_sub_self (hc : c * c = c) : c * (1 - c) = 0 := by
  rw [mul_sub, mul_one, hc, sub_self]

theorem one_sub_mul_one_sub (hc : c * c = c) : (1 - c) * (1 - c) = 1 - c := by
  rw [mul_sub, mul_one, one_sub_mul_self hc, sub_zero]

theorem comm_one_sub {B : A} (hB : B * c = c * B) : B * (1 - c) = (1 - c) * B := by
  rw [mul_sub, sub_mul, mul_one, one_mul, hB]

theorem idem_rules (hc : c * c = c) :
    (∀ X : A, (1 - c) * ((1 - c) * X) = (1 - c) * X) ∧ (∀ X : A, (1 - c) * (c * X) = 0) ∧
      (∀ X : A, c * ((1 - c) * X) = 0) ∧ (∀ X : A, c * (c * X) = c * X) := by
  refine ⟨fun X => ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · rw [← mul_assoc, one_sub_mul_one_sub hc]
  · rw [← mul_assoc, one_sub_mul_self hc, zero_mul]
  · rw [← mul_assoc, mul_one_sub_self hc, zero_mul]
  · rw [← mul_assoc, hc]

theorem comm_rules {B : A} (hB : B * c = c * B) :
    (∀ X : A, (1 - c) * (B * X) = B * ((1 - c) * X)) ∧ (∀ X : A, c * (B * X) = B * (c * X)) ∧
      (1 - c) * B = B * (1 - c) ∧ c * B = B * c := by
  have e1 : (1 - c) * B = B * (1 - c) := (comm_one_sub hB).symm
  refine ⟨fun X => by rw [← mul_assoc, e1, mul_assoc], fun X => by rw [← mul_assoc, ← hB,
    mul_assoc], e1, hB.symm⟩

theorem blkL_mul (hc : c * c = c) {B B' : A} (hB' : B' * c = c * B') :
    blkL c B * blkL c B' = blkL c (B * B') := by
  obtain ⟨r1, r2, r3, r4⟩ := idem_rules hc
  obtain ⟨s1, s2, s3, s4⟩ := comm_rules hB'
  simp only [blkL, add_mul, mul_add, mul_assoc, s1, s2, 
    one_sub_mul_one_sub hc, one_sub_mul_self hc, mul_one_sub_self hc, hc, mul_zero, add_zero,
    zero_add]

theorem blkL_one : blkL c (1 : A) = 1 := by simp [blkL]

theorem blkL_mul_blkL_one_sub (hc : c * c = c) {B : A} (hB : B * c = c * B) :
    blkL c B * blkL (1 - c) B = B := by
  obtain ⟨r1, r2, r3, r4⟩ := idem_rules hc
  obtain ⟨s1, s2, s3, s4⟩ := comm_rules hB
  simp only [blkL, sub_sub_cancel, add_mul, mul_add, mul_assoc, s1, s2, 
    one_sub_mul_one_sub hc, one_sub_mul_self hc, mul_one_sub_self hc, hc, mul_zero, add_zero,
    zero_add]
  rw [← mul_add, add_sub_cancel, mul_one]

theorem blkL_comm (hc : c * c = c) {B B' : A} (hB : B * c = c * B) (hB' : B' * c = c * B') :
    blkL c B * blkL (1 - c) B' = blkL (1 - c) B' * blkL c B := by
  obtain ⟨r1, r2, r3, r4⟩ := idem_rules hc
  obtain ⟨s1, s2, s3, s4⟩ := comm_rules hB
  obtain ⟨t1, t2, t3, t4⟩ := comm_rules hB'
  simp only [blkL, sub_sub_cancel, add_mul, mul_add, mul_assoc, s1, s2, 
    t1, t2, one_sub_mul_one_sub hc, one_sub_mul_self hc, mul_one_sub_self hc, hc,
    mul_zero, add_zero, zero_add]
  abel

theorem blkL_iso (hc : c * c = c) {D B BT : A} (hDc : D * c = c * D) (hBc : B * c = c * B)
    (hBTc : BT * c = c * BT) (hBR : BT * D * B = D) :
    ((1 - c) * BT + c) * D * blkL c B = D := by
  obtain ⟨r1, r2, r3, r4⟩ := idem_rules hc
  obtain ⟨s1, s2, s3, s4⟩ := comm_rules hBc
  obtain ⟨t1, t2, t3, t4⟩ := comm_rules hBTc
  obtain ⟨u1, u2, u3, u4⟩ := comm_rules hDc
  have hBR' : ∀ X, BT * (D * (B * X)) = D * X := fun X => by
    rw [← mul_assoc, ← mul_assoc, hBR]
  simp only [blkL, add_mul, mul_add, mul_assoc, s1, s2, t3, 
    u3, u4, one_sub_mul_one_sub hc, one_sub_mul_self hc, mul_one_sub_self hc, hc,
    mul_zero, add_zero, zero_add, hBR']
  rw [← mul_add, sub_add_cancel, mul_one]

end RingBlock

variable {K : Type} [Field K] {d : ℕ}

theorem compInd_mul_self (J : Finset (Fin d)) : compInd K J * compInd K J = compInd K J := by
  rw [compInd, diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem compInd_compl (J : Finset (Fin d)) : compInd K Jᶜ = 1 - compInd K J := by
  ext i j
  rw [compInd_apply, Matrix.sub_apply, compInd_apply, Matrix.one_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ J
  · subst hij; simp [hi]
  · subst hij; simp [hi]
  · simp [hij]
  · simp [hij]

theorem compInd_transpose (J : Finset (Fin d)) : (compInd K J)ᵀ = compInd K J := by
  rw [compInd, diagonal_transpose]

theorem inv_mul_comm_of_mul_comm {B : GL (Fin d) K} {c : Matrix (Fin d) (Fin d) K}
    (hB : (B : Matrix (Fin d) (Fin d) K) * c = c * B) :
    ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * c =
      c * ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have e1 : ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 : (B : Matrix (Fin d) (Fin d) K) * ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * c
      = ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * c *
        ((B : Matrix (Fin d) (Fin d) K) * ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
        rw [e2, Matrix.mul_one]
    _ = ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((B : Matrix (Fin d) (Fin d) K) * c) *
        ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [hB]; simp only [Matrix.mul_assoc]
    _ = c * ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

@[expose] def blkLGL {c : Matrix (Fin d) (Fin d) K} (hc : c * c = c) (B : GL (Fin d) K)
    (hB : (B : Matrix (Fin d) (Fin d) K) * c = c * B) : GL (Fin d) K :=
  ⟨blkL c (B : Matrix (Fin d) (Fin d) K), blkL c ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
    by rw [blkL_mul hc (inv_mul_comm_of_mul_comm hB), ← Units.val_mul, mul_inv_cancel,
      Units.val_one, blkL_one],
    by rw [blkL_mul hc hB, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, blkL_one]⟩

theorem coe_blkLGL {c : Matrix (Fin d) (Fin d) K} (hc : c * c = c) (B : GL (Fin d) K)
    (hB : (B : Matrix (Fin d) (Fin d) K) * c = c * B) :
    ((blkLGL hc B hB : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkL c (B : Matrix (Fin d) (Fin d) K) := rfl

theorem blkLGL_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
    {B : GL (Fin d) K} (hBI : B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hB : (B : Matrix (Fin d) (Fin d) K) * compInd K J = compInd K J * B) :
    blkLGL (compInd_mul_self J) B hB ∈ oIsoBlock K hw J := by
  set c := compInd K J with hcdef
  have hc : c * c = c := compInd_mul_self J
  have hcT : cᵀ = c := compInd_transpose J
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL] at hBI
  refine ⟨?_, ?_, ?_⟩
  · rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL, coe_blkLGL]
    have hDc : diagonal w * c = c * diagonal w := by
      rw [hcdef, compInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext i
      ring
    have hBT : (B : Matrix (Fin d) (Fin d) K)ᵀ * c = c * (B : Matrix (Fin d) (Fin d) K)ᵀ := by
      have := congrArg Matrix.transpose hB
      rwa [transpose_mul, transpose_mul, hcT, eq_comm] at this
    have hT : (blkL c (B : Matrix (Fin d) (Fin d) K))ᵀ =
        (1 - c) * (B : Matrix (Fin d) (Fin d) K)ᵀ + c := by
      rw [blkL, transpose_add, transpose_mul, transpose_sub, transpose_one, hcT]
    rw [hT]
    exact blkL_iso hc hDc hB hBT hBI
  · change c * blkL c (B : Matrix (Fin d) (Fin d) K) = c
    rw [blkL, mul_add, ← mul_assoc, ← hB, mul_assoc, mul_one_sub_self hc, mul_zero, zero_add, hc]
  · change blkL c (B : Matrix (Fin d) (Fin d) K) * c = c
    rw [blkL, add_mul, mul_assoc, one_sub_mul_self hc, mul_zero, zero_add, hc]

theorem exists_block_mul_of_commute (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) {B : GL (Fin d) K}
    (hBI : B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hB : B * signGL K J = signGL K J * B) :
    ∃ B₁ ∈ oIsoBlock K hw J, ∃ B₂ ∈ oIsoBlock K hw Jᶜ, B = B₁ * B₂ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hBm : signMat K J * (B : Matrix (Fin d) (Fin d) K) = (B : Matrix (Fin d) (Fin d) K) *
      signMat K J := by
    have := congrArg Units.val hB
    rw [Units.val_mul, Units.val_mul, coe_signGL] at this
    exact this.symm
  have hc : (B : Matrix (Fin d) (Fin d) K) * compInd K J = compInd K J * B :=
    ((commute_signMat_iff h2 J _).1 hBm).symm
  have hc' : (B : Matrix (Fin d) (Fin d) K) * compInd K Jᶜ = compInd K Jᶜ * B := by
    rw [compInd_compl, mul_sub, sub_mul, mul_one, one_mul, hc]
  refine ⟨blkLGL (compInd_mul_self J) B hc, blkLGL_mem_oIsoBlock hw J hBI hc,
    blkLGL (compInd_mul_self Jᶜ) B hc', blkLGL_mem_oIsoBlock hw Jᶜ hBI hc', ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_blkLGL, coe_blkLGL, compInd_compl]
  exact (blkL_mul_blkL_one_sub (compInd_mul_self J) hc).symm

theorem commute_of_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {g h : GL (Fin d) K} (hg : g ∈ oIsoBlock K hw J) (hh : h ∈ oIsoBlock K hw Jᶜ) :
    g * h = h * g := by
  obtain ⟨-, hg1, hg2⟩ := hg
  obtain ⟨-, hh1, hh2⟩ := hh
  set c := compInd K J with hcdef
  have hc : c * c = c := compInd_mul_self J
  rw [compInd_compl] at hh1 hh2
  have hG : (g : Matrix (Fin d) (Fin d) K) = blkL c g := by
    rw [blkL, mul_sub, mul_one, hg2, sub_add_cancel]
  have hH : (h : Matrix (Fin d) (Fin d) K) = blkL (1 - c) h := by
    have e := hh2
    rw [mul_sub, mul_one] at e
    rw [blkL, sub_sub_cancel]
    calc (h : Matrix (Fin d) (Fin d) K) = ((h : Matrix (Fin d) (Fin d) K) -
          (h : Matrix (Fin d) (Fin d) K) * c) + (h : Matrix (Fin d) (Fin d) K) * c := by abel
      _ = (h : Matrix (Fin d) (Fin d) K) * c + (1 - c) := by rw [e]; abel
  have hGc : (g : Matrix (Fin d) (Fin d) K) * c = c * g := by rw [hg1, hg2]
  have hHc : (h : Matrix (Fin d) (Fin d) K) * c = c * h := by
    have e1 : (1 - c) * (h : Matrix (Fin d) (Fin d) K) = (h : Matrix (Fin d) (Fin d) K) * (1 - c) :=
      by rw [hh1, hh2]
    rw [sub_mul, mul_sub, one_mul, mul_one] at e1
    calc (h : Matrix (Fin d) (Fin d) K) * c
        = (h : Matrix (Fin d) (Fin d) K) - ((h : Matrix (Fin d) (Fin d) K) -
          (h : Matrix (Fin d) (Fin d) K) * c) := by abel
      _ = c * h := by rw [← e1]; abel
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hG, hH]
  exact blkL_comm hc hGc hHc

theorem commutatorElement_mul_mul {G : Type*} [Group G] {M N : Subgroup G}
    (hMN : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m) {a a' b b' : G} (ha : a ∈ M) (ha' : a' ∈ M)
    (hb : b ∈ N) (hb' : b' ∈ N) : ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  set φ := MonoidHom.noncommCoprod M.subtype N.subtype
    (fun m n => (hMN m m.2 n n.2 : Commute (m : G) n)) with hφ
  have h1 : φ ⁅((⟨a, ha⟩ : M), (⟨b, hb⟩ : N)), ((⟨a', ha'⟩ : M), (⟨b', hb'⟩ : N))⁆ =
      ⁅a * b, a' * b'⁆ := by
    rw [map_commutatorElement]
    rfl
  have h2 : ⁅((⟨a, ha⟩ : M), (⟨b, hb⟩ : N)), ((⟨a', ha'⟩ : M), (⟨b', hb'⟩ : N))⁆ =
      (⁅(⟨a, ha⟩ : M), ⟨a', ha'⟩⁆, ⁅(⟨b, hb⟩ : N), ⟨b', hb'⟩⁆) := by
    refine Prod.ext ?_ ?_
    · exact map_commutatorElement (MonoidHom.fst M N) _ _
    · exact map_commutatorElement (MonoidHom.snd M N) _ _
  rw [← h1, h2]
  rfl

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem oBlock_le_matrixDerived (h2 : (2 : K) ≠ 0) (J : Finset (Fin d)) :
    oBlock K hw J ≤ matrixDerived (oQ (diagGL hw)) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
  exact oBlock_le hw J

theorem matrixDerived_le_isometryGroup (h2 : (2 : K) ≠ 0) :
    matrixDerived (oQ (diagGL hw)) ≤ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
  exact commutator_le_self _

variable (K) in
abbrev blockP (J : Finset (Fin d)) : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
  ((oBlock K hw J).subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _)

theorem commute_sign_of_mem_oIsoBlock {J : Finset (Fin d)} {g : GL (Fin d) K}
    (hg : g ∈ oIsoBlock K hw J) : g * signGL K J = signGL K J * g := by
  obtain ⟨-, hg1, hg2⟩ := hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_signGL, signMat_eq, mul_sub, sub_mul, mul_one, one_mul,
    Matrix.mul_smul, Matrix.smul_mul, hg1, hg2]

theorem commutator_centralizer_sign_le (hK : ringChar K ≠ 2) (J : Finset (Fin d))
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) :
    ⁅centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw)))),
        centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw))))⁆ ≤
      (oBlock K hw J ⊔ oBlock K hw Jᶜ).subgroupOf (matrixDerived (oQ (diagGL hw))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [commutator_le]
  intro B hB B' hB'
  rw [mem_subgroupOf]
  have hc : ∀ {C : matrixDerived (oQ (diagGL hw))},
      C ∈ centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw)))) →
      (C : GL (Fin d) K) * signGL K J = signGL K J * C := by
    intro C hC
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hC)
  obtain ⟨B₁, hB₁, B₂, hB₂, hBe⟩ := exists_block_mul_of_commute hK hw J
    (matrixDerived_le_isometryGroup hw h2 B.2) (hc hB)
  obtain ⟨B₁', hB₁', B₂', hB₂', hBe'⟩ := exists_block_mul_of_commute hK hw J
    (matrixDerived_le_isometryGroup hw h2 B'.2) (hc hB')
  have hcomm : ∀ m ∈ oIsoBlock K hw J, ∀ n ∈ oIsoBlock K hw Jᶜ, m * n = n * m :=
    fun m hm n hn => commute_of_mem_oIsoBlock hw hm hn
  change ⁅(B : GL (Fin d) K), (B' : GL (Fin d) K)⁆ ∈ _
  rw [hBe, hBe', commutatorElement_mul_mul hcomm hB₁ hB₁' hB₂ hB₂']
  exact mul_mem (mem_sup_left (commutator_mem_commutator hB₁ hB₁'))
    (mem_sup_right (commutator_mem_commutator hB₂ hB₂'))

theorem le_blockP_sup_of_perfect (hK : ringChar K ≠ 2) (J : Finset (Fin d))
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hL : L ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _)) (hperf : ⁅L, L⁆ = L) :
    L ≤ blockP K hw J ⊔ blockP K hw Jᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine (le_map_commutator_of_perfect _ hL hperf).trans ?_
  refine (map_mono (commutator_centralizer_sign_le hw hK J hJ)).trans ?_
  rw [subgroupOf_sup (oBlock_le_matrixDerived hw h2 J) (oBlock_le_matrixDerived hw h2 Jᶜ),
    Subgroup.map_sup]

theorem signGL_eq_compl_mul (J : Finset (Fin d)) :
    signGL K J = signGL K Jᶜ * GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
  apply Units.ext
  rw [Units.val_mul, coe_signGL, coe_signGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  simp only [signMat, diagonal_mul_diagonal, diagonal_apply, Finset.mem_compl]
  split_ifs <;> simp

theorem commute_sign_of_mem (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ) {g : GL (Fin d) K}
    (hg : g ∈ oIsoBlock K hw I) : g * signGL K J = signGL K J * g := by
  rcases hI with rfl | rfl
  · exact commute_sign_of_mem_oIsoBlock hw hg
  · have h := commute_sign_of_mem_oIsoBlock hw hg
    rw [signGL_eq_compl_mul, ← mul_assoc, h, mul_assoc, mul_assoc, (commute_scalar _ _).eq]

theorem commute_compInd_of_commute_sign (hK : ringChar K ≠ 2) (J I : Finset (Fin d))
    (hI : I = J ∨ I = Jᶜ) {B : GL (Fin d) K} (hB : B * signGL K J = signGL K J * B) :
    compInd K I * (B : Matrix (Fin d) (Fin d) K) =
      (B : Matrix (Fin d) (Fin d) K) * compInd K I := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hBm : signMat K J * (B : Matrix (Fin d) (Fin d) K) = (B : Matrix (Fin d) (Fin d) K) *
      signMat K J := by
    have := congrArg Units.val hB
    rw [Units.val_mul, Units.val_mul, coe_signGL] at this
    exact this.symm
  have hc := (commute_signMat_iff h2 J _).1 hBm
  rcases hI with rfl | rfl
  · exact hc
  · rw [compInd_compl, sub_mul, mul_sub, one_mul, mul_one, hc]

theorem blockP_le_centralizer (J I : Finset (Fin d))
    (hI : I = J ∨ I = Jᶜ) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) :
    blockP K hw I ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _) := by
  rintro _ ⟨g, hg, rfl⟩
  replace hg : (g : GL (Fin d) K) ∈ oBlock K hw I := hg
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact commute_sign_of_mem hw J I hI (oBlock_le_oIsoBlock hw _ hg)

theorem isSubnormal_blockP (hK : ringChar K ≠ 2) (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) :
    ((blockP K hw I).subgroupOf
      (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨-, hnorm⟩ := normal_map_of_normalizes (⟨signGL K J, hJ⟩ : matrixDerived _)
    (M := centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw))))) le_rfl
    (by
      rintro B ⟨z, hz, hBz⟩ m hm
      rw [mem_centralizer_singleton_iff] at hm ⊢
      exact conj_mem_centralizer_of_central hz hBz hm)
  refine isSubnormal_subgroupOf_of_normalizes
    (C := (centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw))))).map
      (projH _)) ?_ ?_ (Normal.isSubnormal hnorm)
  · refine map_mono fun g hg => ?_
    replace hg : (g : GL (Fin d) K) ∈ oBlock K hw I := hg
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (commute_sign_of_mem hw J I hI (oBlock_le_oIsoBlock hw _ hg))
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨g, hg, rfl⟩
    replace hg : (g : GL (Fin d) K) ∈ oBlock K hw I := hg
    have hBI := matrixDerived_le_isometryGroup hw h2 B.2
    have hBc : (B : GL (Fin d) K) * signGL K J = signGL K J * B :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hB)
    refine ⟨B * g * B⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    change ((B * g * B⁻¹ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) ∈ oBlock K hw I
    exact conj_mem_oBlock hw hBI (commute_compInd_of_commute_sign hK J I hI hBc) hg

theorem projH_injOn_oBlock {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    {g : matrixDerived (oQ (diagGL hw))}
    (hg : g ∈ (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))))
    (h1 : projH _ g = 1) : g = 1 := by
  rw [mem_subgroupOf] at hg
  have hs : g ∈ (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ (diagGL hw))) := by
    rwa [← QuotientGroup.eq_one_iff]
  rw [mem_subgroupOf] at hs
  obtain ⟨c, hc⟩ := hs
  obtain ⟨k, hk⟩ := hIc
  have hgI := ((mem_oIsoBlock_iff hw).1 (oBlock_le_oIsoBlock hw _ hg)).2 k k
    (Or.inl (Finset.mem_compl.1 hk))
  simp only [↓reduceIte] at hgI
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at hgI
  apply Subtype.ext
  rw [← hc, show c = 1 from Units.ext hgI, map_one]
  rfl

theorem nonempty_blockP_equiv {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty) (h2 : (2 : K) ≠ 0) :
    Nonempty (blockP K hw I ≃* oBlock K hw I) := by
  set M := (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) with hM
  have hinj : Function.Injective ((projH (matrixDerived (oQ (diagGL hw)))).comp M.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (projH_injOn_oBlock hw hIc g.2 hg)
  have hrange : ((projH (matrixDerived (oQ (diagGL hw)))).comp M.subtype).range =
      blockP K hw I := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
    (subgroupOfEquivOfLe (oBlock_le_matrixDerived hw h2 I))⟩

end CFSG.ComponentClassification.Burgoyne.C
