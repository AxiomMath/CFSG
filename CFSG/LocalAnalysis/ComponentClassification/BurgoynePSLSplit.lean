module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def signGL (J : Finset (Fin n)) : GL (Fin n) K :=
  ⟨signMat K J, signMat K J, signMat_mul_self J, signMat_mul_self J⟩

theorem coe_signGL (J : Finset (Fin n)) :
    ((signGL K J : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = signMat K J :=
  rfl

@[expose] def blockScalarGL (J : Finset (Fin n)) (α β : Kˣ) : GL (Fin n) K :=
  ⟨diagonal fun i => if i ∈ J then (α : K) else β,
    diagonal fun i => if i ∈ J then ((α⁻¹ : Kˣ) : K) else ((β⁻¹ : Kˣ) : K),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; split_ifs <;> simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; split_ifs <;> simp⟩

theorem coe_blockScalarGL (J : Finset (Fin n)) (α β : Kˣ) :
    ((blockScalarGL J α β : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => if i ∈ J then (α : K) else β :=
  rfl

theorem compInd_compl (J : Finset (Fin n)) : compInd K Jᶜ = 1 - compInd K J := by
  ext i j
  rw [compInd, compInd, Matrix.sub_apply, one_apply, diagonal_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ J <;> simp [hi]
  · simp [hij]

theorem commute_compInd_compl {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (h : compInd K J * M = M * compInd K J) : compInd K Jᶜ * M = M * compInd K Jᶜ := by
  rw [compInd_compl, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]

theorem coordBlock_le_slCentralizer (h2 : (2 : K) ≠ 0) {J I : Finset (Fin n)}
    (hI : I = J ∨ I = Jᶜ) : coordBlock K I ≤ slCentralizer (signGL K J) := by
  intro g hg
  rw [mem_slCentralizer, coe_signGL]
  have hc : compInd K J * (g : Matrix (Fin n) (Fin n) K) = g * compInd K J := by
    rcases hI with rfl | rfl
    · exact commute_compInd_of_mem hg
    · have := commute_compInd_compl (commute_compInd_of_mem hg)
      rwa [compl_compl] at this
  exact ((commute_signMat_iff h2 J _).2 hc).symm

theorem normalizes_coordBlock (h2 : (2 : K) ≠ 0) {J I : Finset (Fin n)} (hI : I = J ∨ I = Jᶜ) :
    ∀ h ∈ slCentralizer (signGL K J), ∀ g ∈ coordBlock K I, h * g * h⁻¹ ∈ coordBlock K I := by
  intro h hh g hg
  have hh' := mem_slCentralizer.1 hh
  rw [coe_signGL] at hh'
  have hcJ : compInd K J * (h : Matrix (Fin n) (Fin n) K) = h * compInd K J :=
    (commute_signMat_iff h2 J _).1 hh'.symm
  have hcI : compInd K I * (h : Matrix (Fin n) (Fin n) K) = h * compInd K I := by
    rcases hI with rfl | rfl
    · exact hcJ
    · exact commute_compInd_compl hcJ
  have hD1 : (h : Matrix (Fin n) (Fin n) K) *
      ((h⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hD2 : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (h : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  exact conj_mem_coordBlock hD1 hD2 hcI hg
    (by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul])

theorem fieldAut_proj_transvection {i j : Fin n} (hij : i ≠ j) (τ : K ≃+* K) (c : K) :
    fieldAut n K τ (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
      proj n K (Matrix.SpecialLinearGroup.transvection hij (τ c)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext k l
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp

theorem eq_one_and_commute_of_fix_transvections {p : ℕ} [Fact p.Prime] [CharP K p]
    {i j : Fin n} (hij : i ≠ j) {D : GL (Fin n) K} {τ : K ≃+* K}
    (h : ∀ c : K, (conjAut n K D * fieldAut n K τ)
      (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
        proj n K (Matrix.SpecialLinearGroup.transvection hij c)) :
    τ = 1 ∧ (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
      single i j 1 * (D : Matrix (Fin n) (Fin n) K) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ c : K, M * single i j (τ c) * Mi = single i j c := by
    intro c
    have h1 := h c
    rw [MulAut.mul_apply, fieldAut_proj_transvection, conjAut_proj] at h1
    have h3 := eq_of_proj_eq_of_pow_char (p := p)
      (by rw [← map_pow, transvection_pow_char, map_one]) (transvection_pow_char hij c) h1
    have h4 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K)) h3
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.SpecialLinearGroup.transvection_coe] at h4
    have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M] at h4
    exact add_left_cancel h4
  have hτ : ∀ c, τ c = c := by
    intro c
    have e1 := key 1
    rw [map_one] at e1
    have e2 := key c
    have : single i j (τ c) = (τ c) • single i j (1 : K) := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, e1, smul_single, smul_eq_mul, mul_one] at e2
    have := congrFun (congrFun e2 i) j
    simpa using this
  refine ⟨RingEquiv.ext hτ, ?_⟩
  have e1 := key 1
  rw [map_one] at e1
  calc M * single i j 1 = M * single i j 1 * Mi * M := by
        rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
    _ = single i j 1 * M := by rw [e1]

theorem coordBlock_mono {I₁ I₂ : Finset (Fin n)} (h : I₁ ⊆ I₂) :
    coordBlock K I₁ ≤ coordBlock K I₂ := by
  intro g hg
  rw [mem_coordBlock_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun hi h' => hi (h h')) fun hj h' => hj (h h'))

theorem conjProj_coordBlock_injective' {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) :
    Function.Injective ((conjProj n K).comp (coordBlock K I).subtype) := by
  intro g h e
  exact Subtype.ext (proj_injOn_coordBlock hk g.2 h.2 (hinj e))

@[expose] def blockImageEquiv {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) :
    coordBlock K I ≃* (coordBlock K I).map (conjProj n K) :=
  (MonoidHom.ofInjective (conjProj_coordBlock_injective' hk hinj)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))

theorem isQuasisimple_blockImage [Finite K] {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (hI : 2 ≤ I.card) (hq : 3 ≤ I.card ∨ 4 ≤ Nat.card K) :
    IsQuasisimple ((coordBlock K I).map (conjProj n K)) :=
  LocalCores.isQuasisimple_of_mulEquiv (blockImageEquiv hk hinj) (isQuasisimple_coordBlock hI hq)

theorem even_card_blockImage [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {I : Finset (Fin n)} (hI : 2 ≤ I.card) :
    Even (Nat.card ((coordBlock K I).map (conjProj n K))) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hI
  have hsub : ({i, j} : Finset (Fin n)) ⊆ I := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton.1 hx]
      exact hj
  have hmem : pairInvolution K hij ∈ (coordBlock K I).map (conjProj n K) :=
    ⟨_, coordBlock_mono hsub (signSL_mem_coordBlock _ _), rfl⟩
  rw [even_iff_two_dvd, ← orderOf_pairInvolution hK hn hinj hij]
  exact Subgroup.orderOf_dvd_natCard _ hmem

theorem commute_of_odd_conjAut [Finite K] (hn : 3 ≤ n)
    {D D₀ : GL (Fin n) K} (hsq : ∃ ν : Kˣ, D₀ * D₀ = GeneralLinearGroup.scalar (Fin n) ν)
    (hodd : Odd (orderOf (conjAut n K D)))
    (hc : conjAut n K D * conjAut n K D₀ = conjAut n K D₀ * conjAut n K D) : D * D₀ = D₀ * D := by
  have hsc : ∀ (c : Kˣ) (Z : GL (Fin n) K), Commute (GeneralLinearGroup.scalar (Fin n) c) Z :=
    fun c Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
  have h1 : conjAut n K (D * D₀ * D⁻¹ * D₀⁻¹) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h1
  set L := GeneralLinearGroup.scalar (Fin n) l with hL
  have hLc : ∀ Z : GL (Fin n) K, Commute L Z := hsc l
  have hDD : D * D₀ * D⁻¹ = L * D₀ := by rw [hl, inv_mul_cancel_right]
  have hcentral : ∀ (S Z : GL (Fin n) K), (∀ W, Commute S W) → Z * S * Z⁻¹ = S := fun S Z h => by
    rw [(h Z).eq.symm, mul_inv_cancel_right]
  obtain ⟨ν, hν⟩ := hsq
  have hL2 : L * L = 1 := by
    have e1 : (L * D₀) * (L * D₀) = (L * L) * (D₀ * D₀) := by
      rw [mul_assoc L D₀, ← mul_assoc D₀ L, ← (hLc D₀).eq]
      group
    have e2 : (L * D₀) * (L * D₀) = D * (D₀ * D₀) * D⁻¹ := by
      rw [← hDD]
      group
    rw [e2, hν, hcentral _ D (hsc ν), ← hν] at e1
    exact mul_right_cancel (e1.symm.trans (one_mul _).symm)
  have hpow : ∀ k : ℕ, D ^ k * D₀ * (D ^ k)⁻¹ = L ^ k * D₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc D ^ (k + 1) * D₀ * (D ^ (k + 1))⁻¹ = D * (D ^ k * D₀ * (D ^ k)⁻¹) * D⁻¹ := by
            rw [pow_succ']
            group
        _ = D * (L ^ k * D₀) * D⁻¹ := by rw [ih]
        _ = L ^ k * (D * D₀ * D⁻¹) := by
            rw [← mul_assoc, ← ((Commute.pow_left (hLc D) k).eq)]
            group
        _ = L ^ (k + 1) * D₀ := by rw [hDD, ← mul_assoc, pow_succ]
  obtain ⟨-, μ, hμ⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (D ^ orderOf (conjAut n K D)) 1
    (by rw [map_one, mul_one, map_pow, pow_orderOf_eq_one])
  have hLm : L ^ orderOf (conjAut n K D) = 1 := by
    have e := hpow (orderOf (conjAut n K D))
    rw [← hμ] at e
    have : GeneralLinearGroup.scalar (Fin n) μ * D₀ * (GeneralLinearGroup.scalar (Fin n) μ)⁻¹ =
        D₀ := by rw [(hsc μ D₀).eq, mul_inv_cancel_right]
    rw [this] at e
    exact mul_right_cancel (e.symm.trans (one_mul _).symm)
  obtain ⟨k, hk⟩ := hodd
  have hL1 : L = 1 := by
    have e : L ^ orderOf (conjAut n K D) = L * (L * L) ^ k := by
      rw [hk, pow_succ', pow_mul, pow_two]
    rw [hLm, hL2, one_pow, mul_one] at e
    exact e.symm
  rw [hL1, one_mul] at hDD
  calc D * D₀ = D * D₀ * D⁻¹ * D := by group
    _ = D₀ * D := by rw [hDD]

theorem commutator_mem_oddCoreIn {G : Type} [Group G] {B : Subgroup G} {t y c : G}
    (hy : y ∈ oddCoreIn B t) (hc : c ∈ B ⊓ centralizer ({t} : Set G)) :
    y * c * y⁻¹ * c⁻¹ ∈ oddCoreIn B t := by
  obtain ⟨y', hy', rfl⟩ := hy
  set c' : ↥(B ⊓ centralizer ({t} : Set G)) := ⟨c, hc⟩
  refine ⟨y' * (c' * y'⁻¹ * c'⁻¹), mul_mem hy' ((pPrimeCore_normal (p := 2)).conj_mem _
    (inv_mem hy') c'), ?_⟩
  simp [c', mul_assoc]

theorem mem_of_mem_oddCoreIn {G : Type} [Group G] {B : Subgroup G} {t y : G}
    (hy : y ∈ oddCoreIn B t) : y ∈ B ⊓ centralizer ({t} : Set G) := by
  obtain ⟨y', -, rfl⟩ := hy
  exact y'.2

theorem split_oddCoreIn [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) {y : MulAut (projectiveSL n K)}
    (hy : y ∈ oddCoreIn B (conjAut n K (signGL K J))) :
    ∃ α β : Kˣ, y = conjAut n K (blockScalarGL J α β) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hyBC := mem_of_mem_oddCoreIn hy
  have hcard : Nat.card K = 3 ∨ 4 ≤ Nat.card K := by
    have hodd' := FiniteField.odd_card_of_char_ne_two hK
    rw [← Nat.card_eq_fintype_card] at hodd'
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2' : Nat.card K ≠ 2 := fun h => by rw [h] at hodd'; norm_num at hodd'
    omega
  have hmiss : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → ∃ k, k ∉ I := by
    rintro I (rfl | rfl)
    · exact ⟨b, hb⟩
    · exact ⟨a, by simpa using ha⟩
  have hcomp : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → 2 ≤ I.card →
      (3 ≤ I.card ∨ 4 ≤ Nat.card K) → ∀ g ∈ coordBlock K I, y (proj n K g) = proj n K g := by
    intro I hI h2I hq g hg
    obtain ⟨k, hk⟩ := hmiss hI
    exact apply_proj_eq_of_commute hinj (commute_oddCoreIn_of_component hn hB (signGL K J)
      (coordBlock_le_slCentralizer h2 hI) (normalizes_coordBlock h2 hI)
      (isQuasisimple_blockImage hk hinj h2I hq) (even_card_blockImage hK hn hinj h2I) hy hg)
  have htr : ∀ {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j), i ∈ I → j ∈ I → ∀ c : K,
      Matrix.SpecialLinearGroup.transvection hij c ∈ coordBlock K I := by
    intro I i j hij hi hj c
    rw [mem_coordBlock_iff]
    intro k l hkl
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
    have : ¬ (i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      tauto
    simp [this]
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hτ : τ = 1 := by
    rcases hcard with h3 | h4
    · exact ringEquiv_eq_one_of_prime_card (h3 ▸ Nat.prime_three) τ
    · have hsum : J.card + Jᶜ.card = n := by
        rw [Finset.card_compl, Fintype.card_fin]
        have := Finset.card_le_univ J
        rw [Fintype.card_fin] at this
        omega
      obtain ⟨I, hI, h2I⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ 2 ≤ I.card := by
        by_cases hJ : 2 ≤ J.card
        · exact ⟨J, Or.inl rfl, hJ⟩
        · exact ⟨Jᶜ, Or.inr rfl, by omega⟩
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h2I
      exact (eq_one_and_commute_of_fix_transvections (p := p) hij fun c =>
        hcomp hI h2I (Or.inr h4) _ (htr hij hi hj c)).1
  subst hτ
  rw [map_one, mul_one] at hodd hyBC hy ⊢
  have hcD : D * signGL K J = signGL K J * D := by
    refine commute_of_odd_conjAut hn ⟨1, ?_⟩ hodd (mem_centralizer_singleton_iff.1 hyBC.2)
    rw [map_one]
    exact Units.ext (signMat_mul_self J)
  have hcJ : compInd K J * (D : Matrix (Fin n) (Fin n) K) = D * compInd K J := by
    have := congrArg Units.val hcD
    rw [Units.val_mul, Units.val_mul, coe_signGL] at this
    exact (commute_signMat_iff h2 J _).1 this.symm
  have hcI : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      compInd K I * (D : Matrix (Fin n) (Fin n) K) = D * compInd K I := by
    rintro I (rfl | rfl)
    · exact hcJ
    · exact commute_compInd_compl hcJ
  have hE : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → ∀ {i j : Fin n} (hij : i ≠ j), i ∈ I →
      j ∈ I → (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
        single i j 1 * (D : Matrix (Fin n) (Fin n) K) := by
    intro I hI i j hij hi hj
    have h2I : 2 ≤ I.card := Finset.one_lt_card.2 ⟨i, hi, j, hj, hij⟩
    by_cases hq : 3 ≤ I.card ∨ 4 ≤ Nat.card K
    · exact (eq_one_and_commute_of_fix_transvections (p := p) (τ := 1) hij fun c =>
        hcomp hI h2I hq _ (htr hij hi hj c)).2
    · push Not at hq
      have h3 : Nat.card K = 3 := by omega
      have hIij : I = {i, j} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hi
          · rw [Finset.mem_singleton.1 hx]
            exact hj
        · rw [Finset.card_pair hij]
          omega
      subst hIij
      refine three_block_commute h3 hij (hcI hI) fun x hx => ?_
      obtain ⟨hle, -⟩ := isSubnormal_map_conjProj hn hB (signGL K J)
        (coordBlock_le_slCentralizer h2 hI) (normalizes_coordBlock h2 hI)
      have hxC : conjProj n K x ∈ B ⊓ centralizer ({conjAut n K (signGL K J)} : Set _) :=
        hle ⟨x, hx, rfl⟩
      have hmem := commutator_mem_oddCoreIn hy hxC
      rw [conjAut_mul_conjProj_mul_inv, ← map_inv, ← map_mul] at hmem
      have hz : CatalogueBHigherLinearAction.slConjugation n K D x * x⁻¹ ∈ coordBlock K {i, j} :=
        mul_mem (conj_mem_coordBlock (Di := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
          (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) (hcI hI) hx
          (CatalogueBHigherLinearAction.slConjugation_matrix n K D x)) (inv_mem hx)
      have ho := odd_orderOf_of_mem_oddCoreIn hmem
      obtain ⟨k, hk⟩ := hmiss hI
      have e := orderOf_injective _ (conjProj_coordBlock_injective' hk hinj)
        (⟨_, hz⟩ : coordBlock K {i, j})
      rw [Subgroup.orderOf_mk] at e
      rw [← e]
      exact ho
  have hblk : ∀ k l, (k ∈ J ↔ l ∉ J) → (D : Matrix (Fin n) (Fin n) K) k l = 0 :=
    (commute_compInd_iff J _).1 hcJ
  have hsame : ∀ k l, k ≠ l → (k ∈ J ↔ l ∈ J) →
      (D : Matrix (Fin n) (Fin n) K) k l = 0 ∧
        (D : Matrix (Fin n) (Fin n) K) k k = (D : Matrix (Fin n) (Fin n) K) l l := by
    intro k l hkl hkJ
    obtain ⟨I, hI, hk, hl⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ k ∈ I ∧ l ∈ I := by
      by_cases hk : k ∈ J
      · exact ⟨J, Or.inl rfl, hk, hkJ.1 hk⟩
      · exact ⟨Jᶜ, Or.inr rfl, Finset.mem_compl.2 hk,
          Finset.mem_compl.2 fun h => hk (hkJ.2 h)⟩
    obtain ⟨e1, e2, -⟩ := commute_single_apply (hE hI hkl.symm hl hk)
    exact ⟨e2 k hkl, e1⟩
  set α₀ := (D : Matrix (Fin n) (Fin n) K) a a with hα₀
  set β₀ := (D : Matrix (Fin n) (Fin n) K) b b with hβ₀
  have hdiag : (D : Matrix (Fin n) (Fin n) K) = diagonal fun k => if k ∈ J then α₀ else β₀ := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      rw [diagonal_apply_eq]
      by_cases hk : k ∈ J
      · simp only [hk, ↓reduceIte]
        by_cases hka : k = a
        · rw [hka]
        · exact (hsame k a hka (iff_of_true hk ha)).2
      · simp only [hk, ↓reduceIte]
        by_cases hkb : k = b
        · rw [hkb]
        · exact (hsame k b hkb (iff_of_false hk hb)).2
    · rw [diagonal_apply_ne _ hkl]
      by_cases hkJ : (k ∈ J ↔ l ∈ J)
      · exact (hsame k l hkl hkJ).1
      · exact hblk k l (by tauto)
  have hdet : IsUnit (D : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  rw [hdiag, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff] at hdet
  have hα : α₀ ≠ 0 := by simpa [ha] using hdet a (Finset.mem_univ a)
  have hβ : β₀ ≠ 0 := by simpa [hb] using hdet b (Finset.mem_univ b)
  refine ⟨Units.mk0 α₀ hα, Units.mk0 β₀ hβ, ?_⟩
  congr 1
  apply Units.ext
  rw [coe_blockScalarGL, hdiag]
  rfl

theorem compInd_commute_diagonal (J : Finset (Fin n)) (d : Fin n → K) :
    compInd K J * diagonal d = diagonal d * compInd K J := by
  rw [compInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  ring

theorem split_propAConclusionIn [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J)
    {Y : Subgroup (MulAut (projectiveSL n K))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut n K (signGL K J))) :
    PropAConclusionIn B (conjAut n K (signGL K J)) Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  set t := conjAut n K (signGL K J) with ht
  have hcore := fun {y} (hy : y ∈ oddCoreIn B t) => split_oddCoreIn hK hn hinj hB ha hb hy
  have h4 : 4 ≤ Nat.card K := by
    by_contra h4
    have h3 : Nat.card K = 3 := by
      have hodd' := FiniteField.odd_card_of_char_ne_two hK
      rw [← Nat.card_eq_fintype_card] at hodd'
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2' : Nat.card K ≠ 2 := fun h => by rw [h] at hodd'; norm_num at hodd'
      omega
    apply hY
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨α, β, rfl⟩ := hcore (hYO hy)
    have hsq : ∀ γ : Kˣ, (γ : K) * γ = 1 := by
      intro γ
      have := FiniteField.pow_card_sub_one_eq_one (γ : K) γ.ne_zero
      rw [← Nat.card_eq_fintype_card, h3] at this
      simpa [pow_two] using this
    have h1 : conjAut n K (blockScalarGL J α β) ^ 2 = 1 := by
      rw [← map_pow]
      have : blockScalarGL J α β ^ 2 = 1 := by
        apply Units.ext
        rw [pow_two, Units.val_mul, coe_blockScalarGL, diagonal_mul_diagonal, Units.val_one,
          ← diagonal_one]
        congr 1
        ext i
        split_ifs <;> simp [hsq]
      rw [this, map_one]
    have hodd := odd_orderOf_of_mem_oddCoreIn (hYO hy)
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    have : orderOf (conjAut n K (blockScalarGL J α β)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 this
  have hSB : pairSlice K a b ≤ B := pairSlice_le_range.trans hB
  have hu := orderOf_pairInvolution hK hn hinj hab
  obtain ⟨p', f, hp', hp'2, hf, ⟨e⟩⟩ := exists_sl_galoisField (K := K) hK
  refine propAConclusionIn_of_core ?_ hY hYO
    (hB ⟨_, rfl⟩) hu hSB (pairSlice_le_centralizer hab)
    (pairSlice_isPComponent hK hn hinj h4 hB hab)
    ⟨p', f, hp', hp'2, hf, ⟨(pairSliceEquivSL hn hinj hab).trans e⟩⟩
    (center_pairSlice hn hinj hab)
    (conjAut_mem_normalizer_pairSlice (by rw [coe_signGL]; exact compInd_commute_diagonal _ _))
    ?_ ?_ ?_
  ·
    apply orderOf_eq_prime
    · rw [ht, ← map_pow, pow_two]
      have : signGL K J * signGL K J = 1 := Units.ext (signMat_mul_self J)
      rw [this, map_one]
    · intro h1
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (signGL K J) 1
        (by rw [map_one, mul_one]; exact h1)
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [coe_signGL] at e
      have ea := congrFun (congrFun e a) a
      have eb := congrFun (congrFun e b) b
      simp only [GeneralLinearGroup.scalar, signMat, diagonal_apply_eq, ha, hb,
        ↓reduceIte, Units.coe_map] at ea eb
      have ea' : (c : K) = -1 := by simpa using ea
      have eb' : (c : K) = 1 := by simpa using eb
      rw [ea'] at eb'
      have eb := eb'
      exact h2 (by linear_combination -eb)
  ·
    by_contra hall
    push Not at hall
    have := (pairBlock_of_commute (p := p) hinj hab fun x hx => (hall x hx)).1
    rw [coe_signGL, signMat, diagonal_apply_eq, diagonal_apply_eq] at this
    simp only [ha, hb, ↓reduceIte] at this
    exact h2 (by linear_combination -this)
  ·
    intro y hy
    obtain ⟨α, β, rfl⟩ := hcore hy
    exact conjAut_mem_normalizer_pairSlice
      (by rw [coe_blockScalarGL]; exact compInd_commute_diagonal _ _)
  ·
    intro y hy hcomm
    obtain ⟨α, β, rfl⟩ := hcore hy
    have := (pairBlock_of_commute (p := p) hinj hab hcomm).1
    rw [coe_blockScalarGL, diagonal_apply_eq, diagonal_apply_eq] at this
    simp only [ha, hb, ↓reduceIte] at this
    have hαβ : α = β := Units.ext this
    subst hαβ
    have : blockScalarGL J α α = GeneralLinearGroup.scalar (Fin n) α := by
      apply Units.ext
      rw [coe_blockScalarGL]
      ext i j
      rw [diagonal_apply]
      simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, diagonal_apply]
    rw [this, conjAut_scalar]

end CFSG.ComponentClassification.Burgoyne.PSL