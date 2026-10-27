module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.TBLit CFSG.Blueprint
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd signMat_mul_self even_card_pair
  commute_signMat_iff)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (hu : UnitaryFieldData p f K) {n : ℕ}

omit [Field K] in
theorem compInd_map {F : Type} [Field F] (φ : F →+* F) (J : Finset (Fin n)) :
    (compInd F J).map φ = compInd F J := by
  ext i j
  rw [map_apply, compInd, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ J <;> simp [hi]
  · simp [hij]

theorem blkL_unitary {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : (M.map hu.bar)ᵀ * M = 1) (hMc : M * compInd K J = compInd K J * M) :
    ((blkL (compInd K J) M).map hu.bar)ᵀ * blkL (compInd K J) M = 1 := by
  set c := compInd K J with hcdef
  have hc : c * c = c := compInd_mul_self J
  have hcT : cᵀ = c := compInd_transpose J
  have hcb : c.map hu.bar = c := compInd_map hu.bar J
  have hMb : M.map hu.bar * c = c * M.map hu.bar := by
    have := congrArg (fun X => X.map hu.bar) hMc
    simpa only [Matrix.map_mul, hcb] using this
  have hMT : (M.map hu.bar)ᵀ * c = c * (M.map hu.bar)ᵀ := by
    have := congrArg Matrix.transpose hMb
    rwa [transpose_mul, transpose_mul, hcT, eq_comm] at this
  have hmap : (blkL c M).map hu.bar = M.map hu.bar * (1 - c) + c := by
    change hu.bar.mapMatrix (M * (1 - c) + c) = _
    rw [map_add, map_mul, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hcb]
  have hT : ((blkL c M).map hu.bar)ᵀ = (1 - c) * (M.map hu.bar)ᵀ + c := by
    rw [hmap, transpose_add, transpose_mul, transpose_sub, transpose_one, hcT]
  rw [hT]
  have := blkL_iso hc (D := 1) (by rw [Matrix.one_mul, Matrix.mul_one]) hMc hMT
    (by rw [Matrix.mul_one, hM])
  rwa [Matrix.mul_one] at this

include hu in
theorem commutator_le_uBlock_sup {C : Subgroup (StatedSU n (p ^ f) K)} (J : Finset (Fin n))
    (hC : ∀ g ∈ C, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J =
      compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ⁅C, C⁆ ≤ uBlock p f K J ⊔ uBlock p f K Jᶜ := by
  have hc := compInd_mul_self (K := K) J
  have hc' : (1 - compInd K J) * (1 - compInd K J) = 1 - compInd K J := one_sub_mul_one_sub hc
  have hcom' : ∀ {u : StatedSU n (p ^ f) K}, u ∈ C →
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - compInd K J) =
        (1 - compInd K J) * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro u hu'
    rw [mul_sub, sub_mul, mul_one, one_mul, hC u hu']
  have hU : ∀ u : StatedSU n (p ^ f) K,
      ((((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map hu.bar)ᵀ *
        ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun u =>
    ((mem_unitarySU_iff hu).1 u.2).2
  have hinv : ∀ u : StatedSU n (p ^ f) K, ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((u⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun u =>
    by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [commutator_le]
  intro g hg h hh
  have hgh : ⁅g, h⁆ ∈ C := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  set M := ((⁅g, h⁆ : StatedSU n (p ^ f) K) : GL (Fin n) K) with hMdef
  have hMm : (M : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((h⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hMdef, commutatorElement_def]
    rfl
  have hMc : (M : Matrix (Fin n) (Fin n) K) * compInd K J = compInd K J * M := hC _ hgh
  have hd₁ : (blkL (compInd K J) (M : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hMm]
    exact det_blkL_commutator hc (hC _ hh) (hC _ (inv_mem hg)) (hC _ (inv_mem hh)) (hinv g)
      (hinv h)
  have hd₂ : (blkL (1 - compInd K J) (M : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hMm]
    exact det_blkL_commutator hc' (hcom' hh) (hcom' (inv_mem hg)) (hcom' (inv_mem hh))
      (hinv g) (hinv h)
  have hMc' : (M : Matrix (Fin n) (Fin n) K) * compInd K Jᶜ = compInd K Jᶜ * M := by
    rw [compInd_compl, mul_sub, sub_mul, mul_one, one_mul, hMc]
  set u₁ := uSUmk hu _ hd₁ (blkL_unitary hu (hU _) hMc)
  have hd₂' : (blkL (compInd K Jᶜ) (M : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [compInd_compl]
    exact hd₂
  set u₂ := uSUmk hu _ hd₂' (blkL_unitary hu (hU _) hMc')
  have hmem : ∀ {I : Finset (Fin n)} {u : StatedSU n (p ^ f) K},
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blkL (compInd K I) M →
      (M : Matrix (Fin n) (Fin n) K) * compInd K I = compInd K I * M → u ∈ uBlock p f K I := by
    intro I u hu' hMI
    have hcI := compInd_mul_self (K := K) I
    refine ⟨?_, ?_⟩
    · rw [hu', blkL, mul_add, ← mul_assoc, ← hMI, mul_assoc, mul_one_sub_self hcI, mul_zero,
        zero_add, hcI]
    · rw [hu', blkL, add_mul, mul_assoc, one_sub_mul_self hcI, mul_zero, zero_add, hcI]
  have hgu : ⁅g, h⁆ = u₁ * u₂ := by
    apply Subtype.ext
    apply Units.ext
    change (M : Matrix (Fin n) (Fin n) K) = blkL (compInd K J) M * blkL (compInd K Jᶜ) M
    rw [compInd_compl]
    exact (blkL_mul_blkL_one_sub hc hMc).symm
  rw [hgu]
  exact mul_mem (mem_sup_left (hmem rfl hMc)) (mem_sup_right (hmem rfl hMc'))

theorem uBlock_mono {I₁ I₂ : Finset (Fin n)} (hI : I₁ ⊆ I₂) :
    uBlock p f K I₁ ≤ uBlock p f K I₂ := by
  intro g hg
  rw [mem_uBlock_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun hi h' => hi (hI h')) fun hj h' => hj (hI h'))

include hu in
theorem subsingleton_statedSU_of_le_one {m : ℕ} (hm : m ≤ 1) :
    Subsingleton (StatedSU m (p ^ f) K) := by
  constructor
  intro a b
  apply Subtype.ext
  apply Units.ext
  ext i j
  interval_cases m
  · exact i.elim0
  · fin_cases i
    fin_cases j
    have ha := ((mem_unitarySU_iff hu).1 a.2).1
    have hb := ((mem_unitarySU_iff hu).1 b.2).1
    rw [det_fin_one] at ha hb
    exact ha.trans hb.symm

@[expose] def statedSUCongr {m m' : ℕ} (hm : m = m') :
    StatedSU m (p ^ f) K ≃* StatedSU m' (p ^ f) K := by
  subst hm
  exact MulEquiv.refl _

@[expose] def uBlockProjEquiv {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    uBlock p f K I ≃* (uBlock p f K I).map (projH (StatedSU n (p ^ f) K)) :=
  (MonoidHom.ofInjective (f := (projH (StatedSU n (p ^ f) K)).comp (uBlock p f K I).subtype)
    (by
      rw [injective_iff_map_eq_one]
      intro g hg
      exact Subtype.ext (eq_one_of_mem_uBlock_scalars hk g.2
        ((QuotientGroup.eq_one_iff _).1 hg)))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))

@[expose] def uSignSU {a b : Fin n} (hab : a ≠ b) : StatedSU n (p ^ f) K :=
  uSUmk hu (signMat K {a, b})
    (by rw [PSL.det_signMat, (even_card_pair hab).neg_one_pow])
    (by rw [map_signMat, signMat, diagonal_transpose, ← signMat, signMat_mul_self])

theorem coe_uSignSU {a b : Fin n} (hab : a ≠ b) :
    (((uSignSU hu hab : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      signMat K {a, b} := rfl

theorem uSignSU_mem_uBlock {a b : Fin n} (hab : a ≠ b) :
    uSignSU hu hab ∈ uBlock p f K {a, b} := by
  rw [mem_uBlock_iff]
  intro i j hij
  rw [coe_uSignSU, signMat, diagonal_apply]
  by_cases hij' : i = j
  · subst hij'
    have hi : i ∉ ({a, b} : Finset (Fin n)) := by tauto
    simp [hi]
  · simp [hij']

theorem orderOf_projH_uSignSU (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    orderOf (projH (StatedSU n (p ^ f) K) (uSignSU hu hab)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_two]
    have : uSignSU hu hab * uSignSU hu hab = 1 :=
      Subtype.ext (Units.ext (by
        change signMat K {a, b} * signMat K {a, b} = 1
        exact signMat_mul_self _))
    rw [this, map_one]
  · intro h1
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := PSL.exists_not_mem_pair hn a b
    have hm : ∀ i, ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i i = signMat K {a, b} i i := fun i => by rw [hc]; rfl
    have ha := hm a
    have hk' := hm k
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, signMat,
      diagonal_apply_eq] at ha hk'
    rw [ite_eq_left (by simp)] at ha
    rw [ite_eq_right hk] at hk'
    rw [ha] at hk'
    exact h2 (by linear_combination -hk')

variable [Finite K]

include hu in
theorem blockOK_uBlock (hp2 : p ≠ 2) (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (e₂ : StatedSU 2 (p ^ f) K ≃* SL(2, F)) {I : Finset (Fin n)}
    {k : Fin n} (hk : k ∉ I) : BlockOK F ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := hu.prime.two_le
    exact hp2 (by omega)
  set e := uBlockProjEquiv (K := K) (p := p) (f := f) hk with he
  have hq3 : 3 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hu.prime.odd_of_ne_two hp2).pow
    have : 2 ≤ p ^ f := le_trans hu.prime.two_le (Nat.le_self_pow (by have := hu.one_le; omega) p)
    obtain ⟨j, hj⟩ := hodd
    omega
  have eI : ∀ {m : ℕ} (hm : I.card = m), (uBlock p f K I).map (projH (StatedSU n (p ^ f) K)) ≃*
      StatedSU m (p ^ f) K := fun hm =>
    (e.symm.trans (uBlockEquiv hu I).symm).trans (statedSUCongr hm)
  by_cases h1 : I.card ≤ 1
  · left
    have := subsingleton_statedSU_of_le_one hu (K := K) h1
    have : Subsingleton ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) :=
      (eI rfl).injective.subsingleton
    infer_instance
  by_cases h23 : I.card = 2 ∧ p ^ f = 3
  · left
    have hs : Group.IsSolvable SL(2, F) := isSolvable_SL_two_of_card_three (by rw [hF, h23.2])
    have e3 := (eI h23.1).trans e₂
    exact Group.isSolvable_of_isSolvable_injective (f := e3.toMonoidHom) e3.injective
  right
  have hI2 : 2 ≤ I.card := by omega
  have hq : 3 ≤ I.card ∨ 5 ≤ p ^ f := by
    by_contra hcon
    push Not at hcon
    have hodd : Odd (p ^ f) := (hu.prime.odd_of_ne_two hp2).pow
    obtain ⟨j, hj⟩ := hodd
    exact h23 ⟨by omega, by omega⟩
  have hqs : IsQuasisimple ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) :=
    LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_uBlock hu hp2 hI2 hq)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
  have hsub : ({a, b} : Finset (Fin n)) ⊆ I := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ha
    · rw [Finset.mem_singleton.1 hy]
      exact hb
  refine ⟨hqs, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    have hdvd := Subgroup.card_dvd_of_le (uBlock_mono (p := p) (f := f) (K := K) hsub)
    rwa [Nat.card_congr ((uBlockEquiv hu ({a, b} : Finset (Fin n))).symm.trans
      ((statedSUCongr (Finset.card_pair hab)).trans e₂)).toEquiv] at hdvd
  · by_cases h3 : I.card = 2
    · exact Or.inr ⟨(eI h3).trans e₂⟩
    · left
      obtain ⟨c, hc, hcab⟩ : ∃ c ∈ I, c ∉ ({a, b} : Finset (Fin n)) := by
        by_contra hcon
        push Not at hcon
        have := Finset.card_le_card (fun y hy => hcon y hy : I ⊆ {a, b})
        rw [Finset.card_pair hab] at this
        omega
      have hca : c ≠ a := fun h' => hcab (h' ▸ by simp)
      have hcb : c ≠ b := fun h' => hcab (h' ▸ by simp)
      have hbc : b ≠ c := Ne.symm hcb
      have hsub' : ({b, c} : Finset (Fin n)) ⊆ I := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hb
        · rw [Finset.mem_singleton.1 hy]
          exact hc
      refine ⟨_, ⟨_, uBlock_mono hsub (uSignSU_mem_uBlock hu hab), rfl⟩,
        _, ⟨_, uBlock_mono hsub' (uSignSU_mem_uBlock hu hbc), rfl⟩,
        orderOf_projH_uSignSU hu h2 hn hab, orderOf_projH_uSignSU hu h2 hn hbc, ?_, ?_⟩
      · rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        apply Units.ext
        change signMat K {a, b} * signMat K {b, c} = signMat K {b, c} * signMat K {a, b}
        exact O.signMat_mul_comm _ _
      · intro h'
        rw [projH_eq_projH_iff] at h'
        obtain ⟨z, hz⟩ := h'
        have hzz : ∀ y, ((GeneralLinearGroup.scalar (Fin n) z : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) y y = (signMat K {a, b} * signMat K {b, c}) y y := by
          intro y
          rw [hz]
          change ((((uSignSU hu hab)⁻¹ * uSignSU hu hbc : StatedSU n (p ^ f) K) :
            GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y y = _
          have hinv : (uSignSU hu hab)⁻¹ = uSignSU hu hab :=
            inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext (by
              change signMat K {a, b} * signMat K {a, b} = 1
              exact signMat_mul_self _)))
          rw [hinv]
          rfl
        have h_a := hzz a
        have h_b := hzz b
        rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, signMat, signMat,
          diagonal_mul_diagonal, diagonal_apply_eq] at h_a h_b
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ite_true,
          hab, Ne.symm hab, hca.symm, or_false, ite_false] at h_a h_b
        simp only [mul_one, mul_neg, neg_neg] at h_a h_b
        exact h2 (by linear_combination h_a - h_b)

include hu in
theorem psu_split_false (hp2 : p ≠ 2) (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (e₂ : StatedSU 2 (p ^ f) K ≃* SL(2, F)) {J : Finset (Fin n)}
    {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) {l : K} (hl : l ≠ 0) {A : StatedSU n (p ^ f) K}
    (hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J)
    {R₁ R₂ : Subgroup (StatedProj (StatedSU n (p ^ f) K))} {r m : ℕ} [Fact r.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ r m) : False := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := hu.prime.two_le
    exact hp2 (by omega)
  have hcent : ∀ g : StatedSU n (p ^ f) K, g ∈ centralizer ({A} : Set _) ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J =
        compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro g
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h' := congrArg (fun u : StatedSU n (p ^ f) K =>
        ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg
      simp only [Subgroup.coe_mul, Units.val_mul] at h'
      rw [hA, Matrix.mul_smul, Matrix.smul_mul] at h'
      exact ((commute_signMat_iff h2 J _).1 (smul_right_injective _ hl h').symm).symm
    · intro hg
      apply Subtype.ext
      apply Units.ext
      change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hA, Matrix.mul_smul, Matrix.smul_mul,
        ((commute_signMat_iff h2 J _).2 hg.symm).symm]
  have hZ := scalars_subgroupOf_le_center (H := StatedSU n (p ^ f) K)
  have hsub : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      (uBlock p f K I).map (QuotientGroup.mk' _) ≤
          centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSU n (p ^ f) K))) ∧
        (((uBlock p f K I).map (QuotientGroup.mk' _)).subgroupOf
          (centralizer ({QuotientGroup.mk' _ A} :
            Set (StatedProj (StatedSU n (p ^ f) K))))).IsSubnormal := by
    intro I hI
    refine isSubnormal_map_mk hZ A (fun g hg => (hcent g).2 ?_) ?_
    · exact commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg) |>.symm
    · intro B hB g hg
      have hBc := (hcent B).1 hB
      have hBI : compInd K I * ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I :=
        commute_compInd_of_or hI hBc.symm
      refine conj_mem_uBlock (D := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (Di := (((B⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ?_ ?_ hBI hg rfl
      · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hperf : ∀ L : Subgroup (StatedProj (StatedSU n (p ^ f) K)),
      L ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) → ⁅L, L⁆ = L →
      L ≤ (uBlock p f K J).map (QuotientGroup.mk' _) ⊔
        (uBlock p f K Jᶜ).map (QuotientGroup.mk' _) := by
    intro L hL hp
    refine (le_map_commutator_of_perfect_mk hZ A hL hp).trans ?_
    rw [← Subgroup.map_sup]
    exact map_mono (commutator_le_uBlock_sup hu J fun g hg => (hcent g).1 hg)
  have haJ : a ∉ Jᶜ := by simpa using ha
  exact propCData_false_of_blocks hC (F := F) (hsub (Or.inl rfl)).1 (hsub (Or.inr rfl)).1
    (hsub (Or.inl rfl)).2 (hsub (Or.inr rfl)).2 hperf (blockOK_uBlock hu hp2 hn hF e₂ hb)
    (blockOK_uBlock hu hp2 hn hF e₂ haJ)

theorem psu_paired_false (hp2 : p ≠ 2) {m : ℕ} (hm : 2 ≤ m) {l : K} (hl : l ≠ 0)
    (hN : hu.norm l = -1) {A : StatedSU (m + m) (p ^ f) K}
    (hA : ((A : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) = prA m l)
    {R₁ R₂ : Subgroup (StatedProj (StatedSU (m + m) (p ^ f) K))} {r m' : ℕ} [Fact r.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ r m') : False := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := hu.prime.two_le
    exact hp2 (by omega)
  have hZ := scalars_subgroupOf_le_center (H := StatedSU (m + m) (p ^ f) K)
  set L₀ := (prSLHom (m := m) hu h2 hl hN).range with hL₀
  have hcent : ∀ g : StatedSU (m + m) (p ^ f) K, g ∈ centralizer ({A} : Set _) →
      prA m l * ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l := by
    intro g hg
    have h' := congrArg (fun u : StatedSU (m + m) (p ^ f) K =>
      ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K))
      (mem_centralizer_singleton_iff.1 hg)
    simp only [Subgroup.coe_mul, Units.val_mul, hA] at h'
    exact h'.symm
  have hcomm : ⁅centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)),
      centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K))⁆ ≤ L₀ := by
    rw [commutator_le]
    intro g hg h hh
    have hgh : ⁅g, h⁆ ∈ centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
    refine mem_range_prSLHom hu h2 hl hN (hcent _ hgh) ?_
    have hblk : ∀ {u : StatedSU (m + m) (p ^ f) K},
        u ∈ centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)) →
        ∃ G G' : Matrix (Fin m) (Fin m) K,
          prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
            fromBlocks G 0 0 G' := by
      intro u hu'
      obtain ⟨G, G', hG⟩ := exists_prPhi_of_commute h2 hl (hcent u hu').symm
      exact ⟨G, G', by rw [hG, prEv_prPhi h2 hl]⟩
    obtain ⟨G₁, G₁', e₁⟩ := hblk hg
    obtain ⟨G₂, G₂', e₂⟩ := hblk hh
    obtain ⟨G₃, G₃', e₃⟩ := hblk (inv_mem hg)
    obtain ⟨G₄, G₄', e₄⟩ := hblk (inv_mem hh)
    have hinv : ∀ {u : StatedSU (m + m) (p ^ f) K} {G G' H H' : Matrix (Fin m) (Fin m) K},
        prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          fromBlocks G 0 0 G' →
        prEv m l (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) = fromBlocks H 0 0 H' → G * H = 1 := by
      intro u G G' H H' eG eH
      have e1 : ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
          (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
            Matrix (Fin (m + m)) (Fin (m + m)) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one]
      have := congrArg (prEv m l) e1
      rw [prEv_mul h2 hl, eG, eH, prEv_one h2 hl, fromBlocks_multiply, ← fromBlocks_one] at this
      simpa using (fromBlocks_inj.1 this).1
    have h13 := hinv e₁ e₃
    have h24 := hinv e₂ e₄
    have hm4 : ((⁅g, h⁆ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) =
        (g : GL (Fin (m + m)) K) * (h : GL (Fin (m + m)) K) *
          ((g⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) *
          ((h⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) := by
      rw [commutatorElement_def]
      rfl
    rw [hm4, Units.val_mul, Units.val_mul, Units.val_mul, prEv_mul h2 hl, prEv_mul h2 hl,
      prEv_mul h2 hl, e₁, e₂, e₃, e₄]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      toBlocks_fromBlocks₁₁, det_mul]
    have d13 : G₁.det * G₃.det = 1 := by rw [← det_mul, h13, det_one]
    have d24 : G₂.det * G₄.det = 1 := by rw [← det_mul, h24, det_one]
    linear_combination G₂.det * G₄.det * d13 + d24
  have hK4 : 4 ≤ Nat.card K := by
    rw [hu.card_eq_sq]
    have := hu.prime.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by have := hu.one_le; omega) p
    nlinarith
  have hLq : IsQuasisimple L₀ := isQuasisimple_range_prSLHom hu h2 hl hN hm hK4
  set φ := (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
    (StatedSU (m + m) (p ^ f) K))).comp L₀.subtype with hφ
  have hφr : φ.range = L₀.map (QuotientGroup.mk' _) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  have hN' : Group.IsSolvable (L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
        (StatedSU (m + m) (p ^ f) K)))) ∨
      IsQuasisimple (L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
        (StatedSU (m + m) (p ^ f) K)))) := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hLq φ with h' | h'
    · left
      rw [← hφr, h']
      infer_instance
    · right
      rwa [← hφr]
  have hNH : L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
      (StatedSU (m + m) (p ^ f) K))) ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) := by
    rintro _ ⟨g, ⟨G, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change prPhi m l G (prDual hu G) * ((A : GL (Fin (m + m)) K) : Matrix _ _ K) =
      ((A : GL (Fin (m + m)) K) : Matrix _ _ K) * prPhi m l G (prDual hu G)
    rw [hA]
    exact (prPhi_commute_prA h2 hl _ _).symm
  exact propCData_false_of_layer hC hNH
    (fun L hL hp => (le_map_commutator_of_perfect_mk hZ A hL hp).trans (map_mono hcomm)) hN'

include hu in
theorem exists_statedSU_two_equiv : ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = p ^ f ∧ Nonempty (StatedSU 2 (p ^ f) K ≃* SL(2, F)) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have hK := hu.card_eq_sq
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  exact ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield hK,
    ⟨((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU hK 2)).symm⟩⟩

include hu in
theorem psu_propC_false (hp2 : p ≠ 2) (hn : 3 ≤ n) {x : StatedProj (StatedSU n (p ^ f) K)}
    {R₁ R₂ : Subgroup (StatedProj (StatedSU n (p ^ f) K))} {r m : ℕ} [Fact r.Prime]
    (hC : PropCData x R₁ R₂ r m) : False := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := hu.prime.two_le
    exact hp2 (by omega)
  obtain ⟨F, _, _, hF, ⟨e₂⟩⟩ := exists_statedSU_two_equiv hu
  obtain ⟨A, rfl⟩ := projH_surjective x
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map hu.bar)ᵀ * Am = 1 := ((mem_unitarySU_iff hu).1 A.2).2
  have hx2 : projH _ (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← hC.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 hx2
  have hAA : Am * Am = (c : K) • 1 := by
    have e : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Am * Am := by
      rw [hc]
      rfl
    rw [← e, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hN : hu.norm (c : K) = 1 := by
    have e : ((Am * Am).map hu.bar)ᵀ * (Am * Am) = 1 := by
      rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
        Matrix.one_mul, hU]
    rw [hAA] at e
    have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [Matrix.mul_apply, Matrix.one_apply] at e1
    rw [UnitaryFieldData.norm, mul_comm]
    simpa [Matrix.smul_apply, Matrix.one_apply] using e1
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one hu hp2 hN
  have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
  have hNl : hu.norm l * hu.norm l = 1 := by
    rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
    ring
  have hA'2 : (l⁻¹ • Am) * (l⁻¹ • Am) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  have hmap : (l⁻¹ • Am).map hu.bar = hu.bar l⁻¹ • Am.map hu.bar := by
    ext i j
    simp [map_mul]
  have he : Am = l • (l⁻¹ • Am) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have htr : ∀ {Hm : Matrix (Fin n) (Fin n) K} (hHU : (Hm.map hu.bar)ᵀ * Hm = 1),
      PropCData (projH _ (⟨(uGL hu Hm hHU)⁻¹ * A * (uGL hu Hm hHU)⁻¹⁻¹,
        uConjSU_mem hu ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩ A⟩ : StatedSU n (p ^ f) K))
        (R₁.map (uConjAut hu (by omega) ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩).toMonoidHom)
        (R₂.map (uConjAut hu (by omega) ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩).toMonoidHom) r m := by
    intro Hm hHU
    have := hC.map (uConjAut hu (by omega) ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩)
    rwa [uConjAut_proj] at this
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = 1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
    obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form hu h2 hU' hA'2
    have hconj : (Hm.map hu.bar)ᵀ * Am * Hm = l • signMat K J := by
      rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
        Matrix.one_mul]
    have hHH : Hm * (Hm.map hu.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
    have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
        by_cases hne : J.Nonempty
        · obtain ⟨a, ha⟩ := hne
          refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hcon a ha i]
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          refine ⟨1, one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hne]
      have e : Am = (l * s) • 1 := by
        calc Am = Hm * ((Hm.map hu.bar)ᵀ * Am * Hm) * (Hm.map hu.bar)ᵀ := by
              simp only [← Matrix.mul_assoc, hHH, Matrix.one_mul]
              rw [Matrix.mul_assoc, hHH, Matrix.mul_one]
          _ = (l * s) • 1 := by
              rw [hconj, hsJ, smul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
      have hsc : A ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) := by
        refine ⟨Units.mk0 (l * s) (mul_ne_zero hl0 hs), Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar]
        change _ = Am
        rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        rfl
      have h1 : projH (StatedSU n (p ^ f) K) A = 1 := (QuotientGroup.eq_one_iff _).2 hsc
      have := hC.orderOf_eq
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    obtain ⟨a, ha, b, hb⟩ := hJ
    refine psu_split_false hu hp2 hn hF e₂ ha hb hl0 ?_ (htr hHU)
    change (Hm.map hu.bar)ᵀ * Am * Hm = _
    exact hconj
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = -1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_neg, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = -1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi,
        neg_one_smul]
    obtain ⟨m', rfl⟩ := exists_half_of_antiunitary hu h2 hU' hA'2
    have hm : 2 ≤ m' := by omega
    obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form hu h2 hU' hA'2 hl0 hN1
    refine psu_paired_false hu hp2 hm hl0 hN1 ?_ (htr hHU)
    change (Hm.map hu.bar)ᵀ * Am * Hm = _
    rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]

theorem burgoynePropC_PSU {X : Type} [Group X] [Finite X] (hX : IsM4 X) {n' p' f' : ℕ}
    (hp2' : p' ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSU n' p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have hu : UnitaryFieldData p' f' K := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
    have hout := (UnitaryHigher.unitary_classical_model_schreier hmod).2
    obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab hout θ
      hC.orderOf_eq hC.le₁ hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
    exact psu_propC_false hu hp2' hn hC'
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.C
