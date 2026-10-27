module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexBlockOK
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure (exists_pow_eq_of_pow_eq ringAut_comm)
open scoped Pointwise commutatorElement

theorem uniActsInnerly_of_levi_data_index
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (Q : Subgroup K) (hQ : Q = coverSub ρ P)
    {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOK (H j) (S j))
    (hZ : ∀ (j : ι) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (φ : MulAut ↥Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) {a : Y}
    (hcompat : ∀ x : ↥Q,
      (MulAut.conjNormal a : MulAut ↥L) (ρ (x : K)) * (ρ ((φ x : ↥Q) : K))⁻¹ ∈
        Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ perfectJoin P, a ^ (3 ^ m) * w = w * a ^ (3 ^ m))
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  classical
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let π : (∀ j, G j) →* ∀ i : Fin (Nat.card ι), G (e.symm i) :=
    MonoidHom.pi fun i => Pi.evalMonoidHom G (e.symm i)
  have hπinj : Function.Injective π := by
    intro x y hxy
    funext j
    obtain ⟨i, rfl⟩ := e.symm.surjective j
    exact congrFun hxy i
  have hπsingle : ∀ (i : Fin (Nat.card ι)) (y : G (e.symm i)),
      π (Pi.mulSingle (e.symm i) y) = Pi.mulSingle (M := fun i => G (e.symm i)) i y := by
    intro i y
    funext i'
    by_cases hi : i' = i
    · subst hi
      change Pi.mulSingle (e.symm i') y (e.symm i') = _
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · change Pi.mulSingle (e.symm i) y (e.symm i') = _
      rw [Pi.mulSingle_eq_of_ne (e.symm.injective.ne hi), Pi.mulSingle_eq_of_ne hi]
  have hker' : (π.comp β).ker = β.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one π, hπinj.eq_iff]
  have hS' : Subgroup.pi Set.univ (fun i => S (e.symm i)) ≤ (π.comp β).range := by
    rw [Subgroup.pi_le_iff]
    rintro i _ ⟨y, hy, rfl⟩
    have hmem : Pi.mulSingle (e.symm i) y ∈ Subgroup.pi Set.univ S := by
      refine (Subgroup.mem_pi _).mpr fun j _ => ?_
      by_cases hj : j = e.symm i
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact hy
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
    obtain ⟨x, hx⟩ := hS hmem
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, hx, hπsingle]
    rfl
  have hc' : ⁅(π.comp β).range, (π.comp β).range⁆ ≤
      Subgroup.pi Set.univ (fun i => S (e.symm i)) := by
    rw [MonoidHom.range_comp, ← Subgroup.map_commutator]
    rintro _ ⟨z, hz, rfl⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact (Subgroup.mem_pi _).mp (hc hz) (e.symm i) trivial
  refine actsInnerly_of_levi_data hPL ρ hρ hker Q hQ (G := fun i => G (e.symm i))
    (fun i => S (e.symm i)) (fun i => H (e.symm i)) (π.comp β) (hker' ▸ h2) hS' hc'
    (fun i => hqs _) (fun i hq => hblock _ hq) (fun i E hES hE hcard x hρx hx => ?_) φ (π g)
    (fun i => hg _) (fun x => ?_) hcompat hpow hrk
  · obtain ⟨y, hy, hyx⟩ := hx
    refine hZ (e.symm i) E hES hE hcard x hρx ⟨y, hy, hπinj ?_⟩
    change π (Pi.mulSingle (e.symm i) y) = π (β x)
    rw [hπsingle]
    exact hyx
  · rw [MonoidHom.comp_apply, hφ, map_mul, map_mul, map_inv]
    rfl

section Conj

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {r ε : ℕ}

theorem uniConj_mem_hypSU {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (y : hypSU h r ε) : A * (y : GL (HypIndex r ε) K) * A⁻¹ ∈ hypSU h r ε := by
  have h1 : A * (y : GL (HypIndex r ε) K) * A⁻¹ ∈ hypUnitary h r ε :=
    (hypUnitary h r ε).mul_mem ((hypUnitary h r ε).mul_mem hA (mem_hypUnitary.2 y.2.1))
      ((hypUnitary h r ε).inv_mem hA)
  refine ⟨mem_hypUnitary.1 h1, ?_⟩
  show ((A * (y : GL (HypIndex r ε) K) * A⁻¹ : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1
  rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, mul_inv_cancel_comm,
    GeneralLinearGroup.val_det_apply]
  exact y.2.2

@[expose] def uniConjSU (A : GL (HypIndex r ε) K) (hA : A ∈ hypUnitary h r ε) :
    MulAut (hypSU h r ε) where
  toFun y := ⟨A * (y : GL (HypIndex r ε) K) * A⁻¹, uniConj_mem_hypSU hA y⟩
  invFun y := ⟨A⁻¹ * (y : GL (HypIndex r ε) K) * A, by
    simpa using uniConj_mem_hypSU ((hypUnitary h r ε).inv_mem hA) y⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem uniConjSU_coe (A : GL (HypIndex r ε) K) (hA : A ∈ hypUnitary h r ε) (y : hypSU h r ε) :
    ((uniConjSU A hA y : hypSU h r ε) : GL (HypIndex r ε) K) =
      A * (y : GL (HypIndex r ε) K) * A⁻¹ :=
  rfl

end Conj

section Diag

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def uniDiagGL (d : ι → Kˣ) : GL ι K where
  val := diagonal fun i => (d i : K)
  inv := diagonal fun i => (((d i)⁻¹ : Kˣ) : K)
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem uniDiagGL_val (d : ι → Kˣ) :
    ((uniDiagGL d : GL ι K) : Matrix ι ι K) = diagonal fun i => (d i : K) :=
  rfl

theorem uniDiagGL_inv_val (d : ι → Kˣ) :
    (((uniDiagGL d : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) =
      diagonal fun i => (((d i)⁻¹ : Kˣ) : K) :=
  rfl

theorem uniDiagGL_inv (d : ι → Kˣ) : (uniDiagGL d : GL ι K)⁻¹ = uniDiagGL (d⁻¹) :=
  Units.ext rfl

theorem uniDiagGL_det (d : ι → Kˣ) :
    GeneralLinearGroup.det (uniDiagGL d : GL ι K) = ∏ i, d i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, uniDiagGL_val, Matrix.det_diagonal, Units.coe_prod]

theorem uniDiagGL_conj_apply (d : ι → Kˣ) (x : GL ι K) (i j : ι) :
    ((uniDiagGL d * x * (uniDiagGL d)⁻¹ : GL ι K) : Matrix ι ι K) i j =
      (d i : K) * (x : Matrix ι ι K) i j * (((d j)⁻¹ : Kˣ) : K) := by
  rw [Units.val_mul, Units.val_mul, uniDiagGL_val, uniDiagGL_inv_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

theorem uniDiagGL_conj_submatrix {ι' : Type} [Fintype ι'] [DecidableEq ι'] (d : ι → Kˣ)
    (x : GL ι K) (φ : ι' → ι) :
    ((uniDiagGL d * x * (uniDiagGL d)⁻¹ : GL ι K) : Matrix ι ι K).submatrix φ φ =
      ((uniDiagGL (d ∘ φ) : GL ι' K) : Matrix ι' ι' K) * (x : Matrix ι ι K).submatrix φ φ *
        (((uniDiagGL (d ∘ φ))⁻¹ : GL ι' K) : Matrix ι' ι' K) := by
  ext i j
  rw [Matrix.submatrix_apply, uniDiagGL_conj_apply, uniDiagGL_val, uniDiagGL_inv_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

end Diag

section Torus

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {r ε : ℕ}

@[expose] noncomputable def uniTorusUnits (h : UnitaryFieldData 2 f K) {r ε : ℕ} (a : Fin r → Kˣ) :
    HypIndex r ε → Kˣ
  | .inl i => a i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (Units.map (h.bar : K →* K) (a i))⁻¹

theorem uniTorusUnits_coe (a : Fin r → Kˣ) (x : HypIndex r ε) :
    ((uniTorusUnits h a x : Kˣ) : K) = torusEntries h a (1 : Fin ε → Kˣ) x := by
  rcases x with i | k | i
  · rfl
  · simp [uniTorusUnits, torusEntries]
  · simp [uniTorusUnits, torusEntries]

theorem uniDiagGL_torus_mem_hypUnitary (a : Fin r → Kˣ) :
    (uniDiagGL (uniTorusUnits h a : HypIndex r ε → Kˣ) : GL (HypIndex r ε) K) ∈
      hypUnitary h r ε := by
  rw [mem_hypUnitary, uniDiagGL_val]
  have : (fun x : HypIndex r ε => ((uniTorusUnits h a x : Kˣ) : K)) =
      torusEntries h a (1 : Fin ε → Kˣ) := funext (uniTorusUnits_coe a)
  rw [this]
  exact diagonal_torusEntries_isometry h a (fun k => by simp [UnitaryFieldData.norm])

theorem prod_uniTorusUnits (a : Fin r → Kˣ) :
    ∏ x : HypIndex r ε, uniTorusUnits h a x =
      (∏ i, a i) * ∏ i, (Units.map (h.bar : K →* K) (a i))⁻¹ := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp [uniTorusUnits]

theorem uniHilbert90 (h : UnitaryFieldData 2 f K) {δ : Kˣ} (hδ : h.norm (δ : K) = 1) :
    ∃ a₀ : Kˣ, a₀ * (Units.map (h.bar : K →* K) a₀)⁻¹ = δ := by
  haveI : CharP K 2 := h.charP
  by_cases hδ1 : δ = 1
  · exact ⟨1, by simp [hδ1]⟩
  · have hδ0 : (δ : K) ≠ 0 := δ.ne_zero
    have hbar : h.bar (δ : K) = (δ : K)⁻¹ := by
      rw [UnitaryFieldData.norm] at hδ
      exact eq_inv_of_mul_eq_one_right hδ
    have hx : (1 + (δ : K)) ≠ 0 := by
      intro h0
      apply hδ1
      have : (1 : K) = (δ : K) := CharTwo.add_eq_zero.1 h0
      exact Units.ext this.symm
    refine ⟨Units.mk0 (1 + (δ : K)) hx, Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.coe_map,
      MonoidHom.coe_coe, map_add, map_one, hbar]
    have h1 : (1 + (δ : K)⁻¹) = (1 + (δ : K)) * (δ : K)⁻¹ := by
      rw [add_mul, one_mul, mul_inv_cancel₀ hδ0, add_comm]
    rw [h1, mul_inv, inv_inv, mul_inv_cancel_left₀ hx]

end Torus

section FlagDiag

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {r ε : ℕ}

theorem uniDiagGL_smul_posFlag (d : HypIndex r ε → Kˣ) (c : ℕ) :
    (uniDiagGL d : GL (HypIndex r ε) K) • posFlag r ε K c = posFlag r ε K c := by
  refine smul_eq_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
  · intro a ha
    rw [uniDiagGL_val, mulVec_diagonal, hv a ha, mul_zero]
  · intro a ha
    rw [uniDiagGL_inv_val, mulVec_diagonal, hv a ha, mul_zero]

theorem uniDiag_conj_mem_flagStabilizer (hε : ε ≤ 1) {I : Set ℕ} (hIr : ∀ c ∈ I, c ≤ r)
    (d : HypIndex r ε → Kˣ) {D : GL (HypIndex r ε) K} (hDd : D = uniDiagGL d)
    (hD : D ∈ hypUnitary h r ε) {x : hypSU h r ε} (hx : x ∈ flagStabilizer h r ε I) :
    uniConjSU D hD x ∈ flagStabilizer h r ε I := by
  subst hDd
  rw [mem_flagStabilizer] at hx ⊢
  intro i hi
  have hF : hypFlag h r ε i = posFlag r ε K i :=
    hypFlag_eq_posFlag h hε (by have := hIr i hi; omega)
  have hx' := hx i hi
  rw [hF] at hx' ⊢
  rw [Subgroup.smul_def] at hx' ⊢
  change (uniDiagGL d * (x : GL (HypIndex r ε) K) * (uniDiagGL d)⁻¹) • posFlag r ε K i =
    posFlag r ε K i
  have h1 : (uniDiagGL d : GL (HypIndex r ε) K)⁻¹ • posFlag r ε K i = posFlag r ε K i := by
    rw [uniDiagGL_inv]
    exact uniDiagGL_smul_posFlag _ _
  rw [mul_smul, mul_smul, h1, hx', uniDiagGL_smul_posFlag]

end FlagDiag

section Torus3

variable {f : ℕ} {K : Type} [Field K]

theorem uniElemAbelian_range {G : Type*} [Group G] {C : Type*} [CommGroup C] {r : ℕ}
    (hC3 : ∀ x : C, x ^ 3 = 1) (hC : Nat.card C = 3) (σ : (Fin r → C) →* G)
    (hσ : Function.Injective σ) : IsElemAbelian 3 σ.range ∧ Nat.card σ.range = 3 ^ r := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm x z]
  · obtain ⟨x, rfl⟩ := hy
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply]
      exact hC3 (x i)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hσ).toEquiv, Nat.card_fun, hC, Nat.card_fin]

theorem uniExists_cyclic_three (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ C : Subgroup Kˣ, Nat.card C = 3 ∧ ∀ x ∈ C, h.norm (x : K) = 1 := by
  haveI : Finite K := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul]
    have : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    rw [this]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  refine ⟨Subgroup.zpowers ω, by rw [Nat.card_zpowers, hω], fun x hx => ?_⟩
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hω3,
      _root_.one_zpow]
  have hxq : x ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [hm, pow_mul, hx3, one_pow]
  rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hxq, Units.val_one]

theorem uniLinTorusVec_mem {n r : ℕ} (C : Subgroup Kˣ) (t : Fin r → C) (i : Fin n) :
    linTorusVec (n := n) (fun j => (t j : Kˣ)) i ∈ C := by
  unfold linTorusVec
  split_ifs with h1 h2
  · exact (t ⟨i, h1⟩).2
  · exact C.inv_mem (C.prod_mem fun j _ => (t j).2)
  · exact C.one_mem

theorem uniLinTorus_mem_unitarySU (h : UnitaryFieldData 2 f K) {n r : ℕ} (hn : r + 1 ≤ n)
    (C : Subgroup Kˣ) (hC : ∀ x ∈ C, h.norm (x : K) = 1) (t : Fin r → C) :
    (SpecialLinearGroup.toGL (linTorus K r hn (fun i => (t i : Kˣ))) : GL (Fin n) K) ∈
      unitarySU 2 f K n := by
  rw [mem_unitarySU_iff h]
  refine ⟨(linTorus K r hn (fun i => (t i : Kˣ))).2, ?_⟩
  have hmat : ((SpecialLinearGroup.toGL (linTorus K r hn (fun i => (t i : Kˣ))) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal fun i => (linTorusVec (n := n)
        (fun j => (t j : Kˣ)) i : K) := rfl
  rw [hmat, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  have := hC _ (uniLinTorusVec_mem C t i)
  rw [UnitaryFieldData.norm] at this
  rw [mul_comm]
  exact this

@[expose] noncomputable def uniTorusStd (h : UnitaryFieldData 2 f K) {n r : ℕ} (hn : r + 1 ≤ n)
    (C : Subgroup Kˣ) (hC : ∀ x ∈ C, h.norm (x : K) = 1) : (Fin r → C) →* unitarySU 2 f K n :=
  ((SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).comp
    ((linTorus K r hn).comp (Pi.monoidHom fun i => C.subtype.comp
      (Pi.evalMonoidHom (fun _ => C) i)))).codRestrict _
    (fun t => uniLinTorus_mem_unitarySU h hn C hC t)

theorem coe_uniTorusStd (h : UnitaryFieldData 2 f K) {n r : ℕ} (hn : r + 1 ≤ n)
    (C : Subgroup Kˣ) (hC : ∀ x ∈ C, h.norm (x : K) = 1) (t : Fin r → C) :
    (((uniTorusStd h hn C hC t : unitarySU 2 f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
        diagonal fun i => (linTorusVec (n := n) (fun j => (t j : Kˣ)) i : K) :=
  rfl

theorem uniTorusStd_injective (h : UnitaryFieldData 2 f K) {n r : ℕ} (hn : r + 1 ≤ n)
    (C : Subgroup Kˣ) (hC : ∀ x ∈ C, h.norm (x : K) = 1) :
    Function.Injective (uniTorusStd h hn C hC) := by
  intro a b hab
  have h1 : (SpecialLinearGroup.toGL (linTorus K r hn (fun i => (a i : Kˣ))) : GL (Fin n) K) =
      SpecialLinearGroup.toGL (linTorus K r hn (fun i => (b i : Kˣ))) :=
    congrArg Subtype.val hab
  have h2 := linTorus_injective hn (SpecialLinearGroup.toGL_injective h1)
  funext i
  exact Subtype.ext (congrFun h2 i)

theorem uniTorusStd_eq_one_of_scalar (h : UnitaryFieldData 2 f K) {n r : ℕ} (hn : r + 2 ≤ n)
    (C : Subgroup Kˣ) (hC : ∀ x ∈ C, h.norm (x : K) = 1) (t : Fin r → C) (c : Kˣ)
    (hc : (((uniTorusStd h (by omega : r + 1 ≤ n) C hC t : unitarySU 2 f K n) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K)) : t = 1 := by
  rw [coe_uniTorusStd] at hc
  have hr1 : r + 1 < n := by omega
  have hc1 : (c : K) = 1 := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) K => A ⟨r + 1, hr1⟩ ⟨r + 1, hr1⟩) hc
    simp only [diagonal_apply_eq, scalar_apply] at this
    have e : (linTorusVec (n := n) (fun j => (t j : Kˣ)) ⟨r + 1, hr1⟩ : K) = 1 := by
      simp [linTorusVec]
    rw [e] at this
    exact this.symm
  funext j
  have hjn : (j : ℕ) < n := by have := j.isLt; omega
  have := congrArg (fun A : Matrix (Fin n) (Fin n) K => A ⟨j, hjn⟩ ⟨j, hjn⟩) hc
  simp only [diagonal_apply_eq, scalar_apply, hc1] at this
  have e : (linTorusVec (n := n) (fun j => (t j : Kˣ)) ⟨j, hjn⟩ : K) = (t j : Kˣ) := by
    simp [linTorusVec, j.isLt]
  rw [e] at this
  exact Subtype.ext (Units.ext (by simpa using this))

end Torus3

section Rank

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem uniExists_elemAbelian_nine_su {s ε : ℕ} (hm : 3 ≤ 2 * s + ε) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (GL (HypIndex s ε) K), E ≤ hypSU h s ε ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  haveI : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := s) (ε := ε) h
  obtain ⟨C, hCcard, hCnorm⟩ := uniExists_cyclic_three h h3
  have hC3 : ∀ x : C, x ^ 3 = 1 := fun x => by
    have := pow_card_eq_one' (G := C) (x := x)
    rwa [hCcard] at this
  let τ := uniTorusStd h (by omega : 2 + 1 ≤ 2 * s + ε) C hCnorm
  let σ : (Fin 2 → C) →* GL (HypIndex s ε) K :=
    (hypSU h s ε).subtype.comp
      (((hypTransport h hR).symm : unitarySU 2 f K (2 * s + ε) ≃* hypSU h s ε).toMonoidHom.comp τ)
  have hσ : Function.Injective σ :=
    Subtype.val_injective.comp ((hypTransport h hR).symm.injective.comp
      (uniTorusStd_injective h _ C hCnorm))
  obtain ⟨hE, hcard⟩ := uniElemAbelian_range hC3 hCcard σ hσ
  refine ⟨σ.range, ?_, hE, by rw [hcard]; norm_num⟩
  rintro _ ⟨t, rfl⟩
  exact ((hypTransport h hR).symm (τ t)).2

theorem uniFour_le_pRank {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {r ε : ℕ}
    (hn : 6 ≤ 2 * r + ε) (h3 : 3 ∣ 2 ^ f + 1) (ρ : hypSU h r ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h r ε) : 4 ≤ Open.pRank 3 L := by
  haveI : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  obtain ⟨C, hCcard, hCnorm⟩ := uniExists_cyclic_three h h3
  have hC3 : ∀ x : C, x ^ 3 = 1 := fun x => by
    have := pow_card_eq_one' (G := C) (x := x)
    rwa [hCcard] at this
  let τ := uniTorusStd h (by omega : 4 + 1 ≤ 2 * r + ε) C hCnorm
  let σ : (Fin 4 → C) →* hypSU h r ε :=
    ((hypTransport h hR).symm : unitarySU 2 f K (2 * r + ε) ≃* hypSU h r ε).toMonoidHom.comp τ
  let Ψ : (Fin 4 → C) →* Y := L.subtype.comp (ρ.comp σ)
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ρ (σ t) = 1 := Subtype.ext ht
    have h2 : σ t ∈ hypScalars h r ε := (hZ _).1 (h1 ▸ Subgroup.one_mem _)
    have h4 := (mem_hypScalars_iff_transport hR (σ t)).1 h2
    have e : hypTransport h hR (σ t) = τ t := MulEquiv.apply_symm_apply _ _
    rw [e] at h4
    obtain ⟨c, -, -, hc⟩ := h4
    exact uniTorusStd_eq_one_of_scalar h (by omega : 4 + 2 ≤ 2 * r + ε) C hCnorm t c
      (by rw [hc]; rfl)
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm a b)
    (fun x => funext fun i => hC3 (x i)) (k := 4) ?_ Ψ hinj ?_
  · rw [Nat.card_fun, hCcard, Nat.card_fin]
  · rintro _ ⟨t, rfl⟩
    exact (ρ (σ t)).2

end Rank

section GU

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem uniNorm_det_eq_one {r ε : ℕ} {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) :
    h.norm ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).det) = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.1 hA)
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have hJ := det_hypGram_ne_zero (r := r) (ε := ε) (K := K)
  rw [UnitaryFieldData.norm, mul_comm]
  have h2 : (h.bar (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det) * (hypGram r ε K).det =
        1 * (hypGram r ε K).det := by
    linear_combination h1
  exact mul_right_cancel₀ hJ h2

theorem uniNorm_eq_one_of_scalar {r ε : ℕ} (hr : 1 ≤ r) {c : Kˣ}
    (hc : (GeneralLinearGroup.scalar (HypIndex r ε) c : GL (HypIndex r ε) K) ∈
      hypUnitary h r ε) : h.norm (c : K) = 1 := by
  have h1 := mem_hypUnitary.1 hc
  rw [GeneralLinearGroup.coe_scalar, scalar_gram] at h1
  have h2 := congrFun (congrFun h1 (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
  simpa [hypGram_apply] using h2

theorem uniExists_pow_eq_normOne (h : UnitaryFieldData 2 f K) {m k : ℕ}
    (hm : ¬ 3 ∣ Nat.gcd m (2 ^ f + 1)) {d u : Kˣ} (hd : h.norm (d : K) = 1)
    (hu : h.norm (u : K) = 1) (hdu : d ^ (3 ^ k) = u ^ m) :
    ∃ μ : Kˣ, h.norm (μ : K) = 1 ∧ μ ^ m = d := by
  haveI : Finite K := h.finite
  let Z : Subgroup Kˣ := (powMonoidHom (2 ^ f + 1) : Kˣ →* Kˣ).ker
  have hZmem : ∀ x : Kˣ, x ∈ Z ↔ h.norm (x : K) = 1 := fun x => by
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
    simp [Z, MonoidHom.mem_ker]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf γ = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hγq : γ ^ (2 ^ f + 1) = 1 := by
    have h1 := MonoidHom.mem_ker.1 γ.2
    exact Subtype.ext (by simpa using h1)
  have hcard : Nat.card Z ∣ 2 ^ f + 1 := hord ▸ orderOf_dvd_of_pow_eq_one hγq
  have hn : ¬ 3 ∣ Nat.gcd m (Nat.card Z) := fun h3 =>
    hm (h3.trans (Nat.gcd_dvd_gcd_of_dvd_right m hcard))
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq (Z := Z) Nat.prime_three hn (k := k)
    (d := ⟨d, (hZmem d).2 hd⟩) (u := ⟨u, (hZmem u).2 hu⟩) (Subtype.ext hdu)
  exact ⟨μ, (hZmem _).1 μ.2, congrArg Subtype.val hμ⟩

theorem uniScalar_mem_hypUnitary {r ε : ℕ} {c : Kˣ} (hc : h.norm (c : K) = 1) :
    (GeneralLinearGroup.scalar (HypIndex r ε) c : GL (HypIndex r ε) K) ∈ hypUnitary h r ε := by
  rw [mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram, hc, one_smul]

theorem uniDet_scalar {r ε : ℕ} (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (HypIndex r ε) c : GL (HypIndex r ε) K) =
      c ^ (2 * r + ε) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
    Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, card_hypIndex,
    Units.val_pow_eq_pow_val]

end GU

section Centralizer

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def uniX0 : HypIndex 1 0 := Sum.inl 0

@[expose] def uniX1 : HypIndex 1 0 := Sum.inr (Sum.inr 0)

theorem uniHyp10_cases (a : HypIndex 1 0) : a = uniX0 ∨ a = uniX1 := by
  rcases a with i | k | i
  · left
    simp [uniX0, Subsingleton.elim i 0]
  · exact k.elim0
  · right
    simp [uniX1, Subsingleton.elim i 0]

theorem uniX0_ne_uniX1 : uniX0 ≠ uniX1 := by simp [uniX0, uniX1]

theorem uniTransvection_01_gram [CharP K 2] :
    ((transvection uniX0 uniX1 (1 : K)).map h.bar)ᵀ * hypGram 1 0 K *
      transvection uniX0 uniX1 (1 : K) = hypGram 1 0 K := by
  ext a b
  simp only [transvection, Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp [uniX0, uniX1, Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  rcases uniHyp10_cases a with rfl | rfl <;> rcases uniHyp10_cases b with rfl | rfl <;>
    simp [uniX0, uniX1, hypPartner, CharTwo.add_self_eq_zero]

theorem uniTransvection_10_gram [CharP K 2] :
    ((transvection uniX1 uniX0 (1 : K)).map h.bar)ᵀ * hypGram 1 0 K *
      transvection uniX1 uniX0 (1 : K) = hypGram 1 0 K := by
  ext a b
  simp only [transvection, Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp [uniX0, uniX1, Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  rcases uniHyp10_cases a with rfl | rfl <;> rcases uniHyp10_cases b with rfl | rfl <;>
    simp [uniX0, uniX1, hypPartner, CharTwo.add_self_eq_zero]

theorem uniCommute_transvection_of_one {n : Type*} [Fintype n] [DecidableEq n] {R : Type*}
    [CommRing R] {i j : n} {G : Matrix n n R} (h1 : Commute (transvection i j (1 : R)) G)
    (c : R) : Commute (transvection i j c) G := by
  have : transvection i j c = 1 + c • (transvection i j (1 : R) - 1) := by
    simp [transvection, Matrix.smul_single]
  rw [this]
  exact (Commute.one_left G).add_left ((h1.sub_left (Commute.one_left G)).smul_left c)

theorem uniScalar_of_commute_two {g : GL (HypIndex 1 0) K}
    (hcU : Commute (transvection uniX0 uniX1 (1 : K))
      (g : Matrix (HypIndex 1 0) (HypIndex 1 0) K))
    (hcL : Commute (transvection uniX1 uniX0 (1 : K))
      (g : Matrix (HypIndex 1 0) (HypIndex 1 0) K)) :
    ∃ c : Kˣ, g = GeneralLinearGroup.scalar (HypIndex 1 0) c := by
  have hall : ∀ t : TransvectionStruct (HypIndex 1 0) K,
      Commute t.toMatrix (g : Matrix (HypIndex 1 0) (HypIndex 1 0) K) := by
    rintro ⟨i, j, hij, c⟩
    change Commute (transvection i j c) _
    rcases uniHyp10_cases i with rfl | rfl <;> rcases uniHyp10_cases j with rfl | rfl
    · exact absurd rfl hij
    · exact uniCommute_transvection_of_one hcU c
    · exact uniCommute_transvection_of_one hcL c
    · exact absurd rfl hij
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_transvectionStruct hall
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply Units.ne_zero g
    rw [← hc]
    simp
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, ← hc]
  rfl

theorem uniScalar_of_centralizes (h : UnitaryFieldData 2 f K) {s ε : ℕ} (hε : ε ≤ 1)
    (hm : 2 ≤ 2 * s + ε) {g : GL (HypIndex s ε) K} (hg : g ∈ hypUnitary h s ε)
    (hc : ∀ y ∈ hypSU h s ε, g * y * g⁻¹ = y) :
    ∃ c : Kˣ, g = GeneralLinearGroup.scalar (HypIndex s ε) c := by
  by_cases h3 : 3 ≤ 2 * s + ε
  · have hr : 1 ≤ s := by omega
    let x : semilinearSimilitudes h s ε :=
      ⟨⟨g, RingEquiv.refl K⟩, 1, one_ne_zero, map_one _, by
        simpa using mem_hypUnitary.1 hg⟩
    have hΦ : semilinearAutHom h hr hε x = 1 := by
      refine MulEquiv.ext fun z => ?_
      induction z using QuotientGroup.induction_on with
      | H y =>
        change semilinearAutHom h hr hε x (hypProj h s ε y) = hypProj h s ε y
        rw [semilinearAutHom_apply]
        congr 1
        refine Subtype.ext ?_
        change g * glAut (RingEquiv.refl K) (y : GL (HypIndex s ε) K) * g⁻¹ = y
        have h1 : glAut (RingEquiv.refl K) (y : GL (HypIndex s ε) K) = y :=
          congrArg (fun φ : MulAut (GL (HypIndex s ε) K) => φ (y : GL (HypIndex s ε) K))
            (map_one glAut)
        rw [h1]
        exact hc y y.2
    obtain ⟨-, c, hc'⟩ := (semilinearAutHom_eq_one_iff h hr hε h3 x).1 hΦ
    exact ⟨c, hc'⟩
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    haveI : CharP K 2 := h.charP
    have hcomm : ∀ (M : Matrix (HypIndex 1 0) (HypIndex 1 0) K) (hM : M.det ≠ 0)
        (hgram : (M.map h.bar)ᵀ * hypGram 1 0 K * M = hypGram 1 0 K) (hdet : M.det = 1),
        Commute M (g : Matrix (HypIndex 1 0) (HypIndex 1 0) K) := by
      intro M hM hgram hdet
      have hmem : GeneralLinearGroup.mkOfDetNeZero M hM ∈ hypSU h 1 0 := ⟨hgram, hdet⟩
      have h1 := hc _ hmem
      have h2 : g * GeneralLinearGroup.mkOfDetNeZero M hM =
          GeneralLinearGroup.mkOfDetNeZero M hM * g := mul_inv_eq_iff_eq_mul.1 h1
      exact (congrArg (fun z : GL (HypIndex 1 0) K => (z : Matrix (HypIndex 1 0) (HypIndex 1 0) K))
        h2).symm
    refine uniScalar_of_commute_two (hcomm _ ?_ uniTransvection_01_gram ?_)
      (hcomm _ ?_ uniTransvection_10_gram ?_)
    · rw [det_transvection_of_ne _ _ uniX0_ne_uniX1]
      exact one_ne_zero
    · exact det_transvection_of_ne _ _ uniX0_ne_uniX1 _
    · rw [det_transvection_of_ne _ _ uniX0_ne_uniX1.symm]
      exact one_ne_zero
    · exact det_transvection_of_ne _ _ uniX0_ne_uniX1.symm _

end Centralizer

section BlockGU

variable {f : ℕ} {K : Type} [Field K]

theorem uniExists_ne_of_isQuasisimple {G : Type*} [Group G] (hq : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G, a ≠ b := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  obtain ⟨x, y, hxy⟩ :=
    (IsSimpleGroup.toNontrivial (G := G ⧸ Subgroup.center G)).exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

theorem blockOK_gu_su (h : UnitaryFieldData 2 f K) {s ε : ℕ} (hε : ε ≤ 1)
    (hq : CFSG.Open.IsQuasisimple ↥(hypSU h s ε)) :
    BlockOK (hypUnitary h s ε) (hypSU h s ε) := by
  classical
  haveI : Finite K := h.finite
  have hm2 : 2 ≤ 2 * s + ε := by
    by_contra hlt
    have hs0 : s = 0 := by omega
    subst hs0
    have := subsingleton_hypSU_zero h hε
    obtain ⟨a, b, hab⟩ := uniExists_ne_of_isQuasisimple hq
    exact hab (Subsingleton.elim a b)
  intro g hg _ k hk
  by_cases hdiv : 3 ∣ Nat.gcd (2 * s + ε) (2 ^ f + 1)
  · right
    have h3m : 3 ∣ 2 * s + ε := hdiv.trans (Nat.gcd_dvd_left _ _)
    exact uniExists_elemAbelian_nine_su (by have := Nat.le_of_dvd (by omega) h3m; omega)
      (hdiv.trans (Nat.gcd_dvd_right _ _))
  · left
    have hr : 1 ≤ s := by omega
    have hgk : g ^ (3 ^ k) ∈ hypUnitary h s ε := pow_mem hg _
    obtain ⟨c, hc⟩ := uniScalar_of_centralizes h hε hm2 hgk hk
    have hcn : h.norm (c : K) = 1 := uniNorm_eq_one_of_scalar hr (hc ▸ hgk)
    have hδ : h.norm ((GeneralLinearGroup.det g : Kˣ) : K) = 1 := by
      rw [GeneralLinearGroup.val_det_apply]
      exact uniNorm_det_eq_one hg
    have hdu : (GeneralLinearGroup.det g : Kˣ) ^ (3 ^ k) = c ^ (2 * s + ε) := by
      rw [← map_pow, hc, uniDet_scalar]
    obtain ⟨μ, hμn, hμ⟩ := uniExists_pow_eq_normOne h hdiv hδ hcn hdu
    have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμn, inv_one]
    have hp1 : (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) ∈
        hypUnitary h s ε := mul_mem (uniScalar_mem_hypUnitary hμ'n) hg
    have hdetp : GeneralLinearGroup.det
        (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) = 1 := by
      rw [map_mul, uniDet_scalar, inv_pow, hμ, inv_mul_cancel]
    have hpS : (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) ∈
        hypSU h s ε := by
      refine ⟨mem_hypUnitary.1 hp1, ?_⟩
      rw [← GeneralLinearGroup.val_det_apply, hdetp, Units.val_one]
    refine ⟨_, hpS, fun y _ => ?_⟩
    have hgp : g = GeneralLinearGroup.scalar (HypIndex s ε) μ *
        (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hc' := (commute_scalar μ (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g * y *
      (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹)).eq
    calc g * y * g⁻¹ = (GeneralLinearGroup.scalar (HypIndex s ε) μ *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)) * y *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g))⁻¹ := by rw [← hgp]
      _ = GeneralLinearGroup.scalar (HypIndex s ε) μ *
          ((GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) * y *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹) *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ)⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) * y *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹ := by
          rw [← hc']
          group

end BlockGU

section Cover

theorem uniCenter_le_of_compParab {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) : (z : Y) ∈ P := by
  obtain ⟨-, T, ⟨hTL, -, -⟩, hN⟩ := hCP.parab
  refine hN ⟨z.2, ?_⟩
  show (z : Y) ∈ Subgroup.normalizer (T : Set Y)
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have hc : ∀ t' ∈ L, (z : Y) * t' = t' * z := fun t' ht' =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨t', ht'⟩).symm
  constructor
  · intro ht
    have := hc t (hTL ht)
    rw [this, mul_inv_cancel_right]
    exact ht
  · intro ht
    have htL : t ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem z.2) (hTL ht)) z.2
      simpa [mul_assoc] using this
    have := hc t htL
    rwa [this, mul_inv_cancel_right] at ht

theorem uniMem_of_normalizes_coverSub {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) {K : Type} [Group K] (ρ : K →* ↥L) (hρs : Function.Surjective ρ)
    {Q : Subgroup K} (hQ : Q = (P.subgroupOf L).comap ρ) {s : K}
    (hs : ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) : s ∈ Q := by
  have hmemQ : ∀ x : K, x ∈ Q ↔ ((ρ x : ↥L) : Y) ∈ P := fun x => by
    rw [hQ]
    rfl
  have hN : ((ρ s : ↥L) : Y) ∈ Subgroup.normalizer (P : Set Y) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨x, hx⟩ := hρs ⟨p, hCP.parab.1 hp⟩
    have hxQ : x ∈ Q := (hmemQ x).2 (by rw [hx]; exact hp)
    have h1 := (hmemQ _).1 (hs x hxQ)
    simpa [map_mul, map_inv, hx] using h1
  exact (hmemQ s).2
    (CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo
      hCP.parab (ρ s).2 hN)

end Cover

section LeviData

variable {f t s ε : ℕ} {K : Type} [Field K]

@[expose] noncomputable def uniBlockH (h : UnitaryFieldData 2 f K) (s ε : ℕ) (I : Finset ℕ) :
    (j : Option ↥I) → Subgroup (uniBlockGroup K s ε I j)
  | none => hypUnitary h s ε
  | some _ => ⊤

theorem uniLeviHom_mem_H (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (x : ↥(flagStabilizer h (t + s) ε ↑I)) (j : Option ↥I) :
    uniLeviHom h hε hI x j ∈ uniBlockH h s ε I j := by
  rcases j with _ | b
  · exact mem_hypUnitary.2 (resBlock_gram h hε (Finset.mem_coe.mpr hI.mem) x)
  · exact Subgroup.mem_top _

theorem uniBlockOK (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (j : Option ↥I)
    (hq : CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) h I j)) :
    BlockOK (uniBlockH h s ε I j) (uniBlockSub (s := s) (ε := ε) h I j) := by
  haveI : Finite K := h.finite
  rcases j with _ | b
  · exact blockOK_gu_su h hε hq
  · have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq)
    exact blockOK_gl_sl _ hm

theorem uniBlockSub_subsingleton_of_card_three (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : IsTopCut I t) (hn : 2 * (t + s) + ε = 3) (j : Option ↥I) :
    Subsingleton ↥(uniBlockSub (s := s) (ε := ε) h I j) := by
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hs0 : s = 0 := by omega
  rcases j with _ | b
  · subst hs0
    exact subsingleton_hypSU_zero h hε
  · have hb := hI.le b.1 b.2
    have hm : b.1 - predCut I b.1 < 2 := by omega
    have : Subsingleton (SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K) :=
      subsingleton_specialLinear_of_lt_two hm
    exact (slEquivToGLRange (K := K) (b.1 - predCut I b.1)).surjective.subsingleton

theorem uniHZ {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (ρ : hypSU h (t + s) ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε)
    (hrank3 : Open.pRank 3 L ≤ 3) (j : Option ↥I)
    (E : Subgroup (uniBlockGroup K s ε I j))
    (hES : E ≤ uniBlockSub (s := s) (ε := ε) h I j) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) (x : ↥(flagStabilizer h (t + s) ε ↑I))
    (hρx : ρ (x : hypSU h (t + s) ε) = 1)
    (hβx : uniLeviHom h hε hI x ∈ E.map (MonoidHom.mulSingle (uniBlockGroup K s ε I) j)) :
    x = 1 := by
  classical
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hxs : (x : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε :=
    (hZ _).1 (by rw [hρx]; exact Subgroup.one_mem _)
  by_cases h3 : 3 ∣ Nat.gcd (2 * (t + s) + ε) (2 ^ f + 1)
  · exfalso
    have h3q : 3 ∣ 2 ^ f + 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h3n : 3 ∣ 2 * (t + s) + ε := h3.trans (Nat.gcd_dvd_left _ _)
    by_cases hn6 : 6 ≤ 2 * (t + s) + ε
    · have := uniFour_le_pRank hn6 h3q ρ hZ
      omega
    · have hn3 : 2 * (t + s) + ε = 3 := by omega
      have hsub := uniBlockSub_subsingleton_of_card_three h hε hI hn3 j
      have hsE : Subsingleton E := ⟨fun a b => Subtype.ext (Subtype.mk.inj
        (Subsingleton.elim (⟨a.1, hES a.2⟩ : ↥(uniBlockSub (s := s) (ε := ε) h I j))
          ⟨b.1, hES b.2⟩))⟩
      have := Finite.card_le_one_iff_subsingleton.2 hsE
      omega
  · have hxord : orderOf (x : hypSU h (t + s) ε) ∣ Nat.gcd (2 * (t + s) + ε) (2 ^ f + 1) := by
      rw [← card_hypScalars h (by omega)]
      exact Subgroup.orderOf_dvd_natCard _ hxs
    have hβ3 : (uniLeviHom h hε hI x) ^ 3 = 1 := by
      obtain ⟨y, hy, hyx⟩ := hβx
      rw [← hyx, ← map_pow, hE.2 y hy, map_one]
    have hβ1 : uniLeviHom h hε hI x = 1 := by
      by_contra hne
      have hord3 : orderOf (uniLeviHom h hε hI x) = 3 := orderOf_eq_prime hβ3 hne
      have h3x : 3 ∣ orderOf x := hord3 ▸ orderOf_map_dvd _ x
      rw [← Subgroup.orderOf_coe] at h3x
      exact h3 (h3x.trans hxord)
    have hker : x ∈ (uniLeviHom h hε hI).ker := hβ1
    obtain ⟨n, hn⟩ := isPGroup_ker_uniLeviHom h hε hI ⟨x, hker⟩
    have hx2 : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hdvd2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx2
    have hdvdq : orderOf x ∣ 2 ^ f + 1 := by
      rw [← Subgroup.orderOf_coe]
      exact hxord.trans (Nat.gcd_dvd_right _ _)
    have hcop : Nat.Coprime (2 ^ n) (2 ^ f + 1) := by
      apply Nat.Coprime.pow_left
      have hodd : Odd (2 ^ f + 1) :=
        (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
      exact Nat.coprime_two_left.2 hodd
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdq)

@[expose] noncomputable def uniDiagBlocks {I : Finset ℕ} (hI : IsTopCut I t)
    (d : HypIndex (t + s) ε → Kˣ) : ∀ j : Option ↥I, uniBlockGroup K s ε I j
  | none => uniDiagGL (d ∘ resIdx t)
  | some b => uniDiagGL (d ∘ eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))

theorem uniLeviHom_conj_diag (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (d : HypIndex (t + s) ε → Kˣ) {D : GL (HypIndex (t + s) ε) K}
    (hDd : D = uniDiagGL d) (hD : D ∈ hypUnitary h (t + s) ε)
    (x : ↥(flagStabilizer h (t + s) ε ↑I))
    (hy : uniConjSU D hD x ∈ flagStabilizer h (t + s) ε ↑I) :
    uniLeviHom h hε hI ⟨uniConjSU D hD x, hy⟩ =
      uniDiagBlocks hI d * uniLeviHom h hε hI x * (uniDiagBlocks hI d)⁻¹ := by
  subst hDd
  funext j
  rcases j with _ | b
  · apply Units.ext
    rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_mul]
    simp only [uniLeviHom_none, coe_resBlockHom, uniDiagBlocks]
    exact uniDiagGL_conj_submatrix d (x : hypSU h (t + s) ε) (resIdx t)
  · apply Units.ext
    rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_mul]
    simp only [uniLeviHom_some, coe_eBlockHom, uniDiagBlocks]
    exact uniDiagGL_conj_submatrix d (x : hypSU h (t + s) ε)
      (eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))

theorem uniDiagGL_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    (uniDiagGL (fun _ : ι => (1 : Kˣ)) : GL ι K) = 1 :=
  Units.ext (by simp [uniDiagGL_val])

theorem uniActsInnerly_of_compat
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (ρ : hypSU h (t + s) ε →* ↥L) (hρs : Function.Surjective ρ)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer h (t + s) ε ↑I)
    (hrank3 : Open.pRank 3 L ≤ 3)
    {A : GL (HypIndex (t + s) ε) K} (hA : A ∈ hypUnitary h (t + s) ε) {a : Y}
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hcm : ∀ y : hypSU h (t + s) ε, (MulAut.conjNormal a : MulAut ↥L) (ρ y) *
      (ρ (uniConjSU A hA y))⁻¹ ∈ Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ perfectJoin P, a ^ (3 ^ m) * w = w * a ^ (3 ^ m))
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  classical
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hr : 0 < t + s := by omega
  have hIr : ∀ c ∈ (↑I : Set ℕ), c ≤ t + s := fun c hc =>
    (hI.le c hc).2.trans (Nat.le_add_right t s)
  set Q := flagStabilizer h (t + s) ε ↑I with hQdef
  have hmemQ : ∀ x : hypSU h (t + s) ε, x ∈ Q ↔ ((ρ x : ↥L) : Y) ∈ P := fun x => by
    rw [← hcomap]
    rfl
  have hQA : ∀ x ∈ Q, uniConjSU A hA x ∈ Q := by
    intro x hx
    rw [hmemQ] at hx ⊢
    have h1 := hcm x
    have h2 : ρ (uniConjSU A hA x) = ((MulAut.conjNormal a : MulAut ↥L) (ρ x) *
        (ρ (uniConjSU A hA x))⁻¹)⁻¹ * (MulAut.conjNormal a : MulAut ↥L) (ρ x) := by group
    rw [h2]
    exact P.mul_mem (uniCenter_le_of_compParab hCP (Subgroup.inv_mem _ h1))
      ((Subgroup.mem_normalizer_iff.1 haN _).1 hx)
  set δ : Kˣ := GeneralLinearGroup.det A with hδ
  have hδn : h.norm (δ : K) = 1 := by
    rw [hδ, GeneralLinearGroup.val_det_apply]
    exact uniNorm_det_eq_one hA
  obtain ⟨a₀, ha₀⟩ := uniHilbert90 h hδn
  let i₀ : Fin (t + s) := ⟨0, hr⟩
  let a' : Fin (t + s) → Kˣ := fun i => if i = i₀ then a₀ else 1
  let d : HypIndex (t + s) ε → Kˣ := uniTorusUnits h a'
  let D : GL (HypIndex (t + s) ε) K := uniDiagGL d
  have hDd : D = uniDiagGL d := rfl
  have hD : D ∈ hypUnitary h (t + s) ε := uniDiagGL_torus_mem_hypUnitary a'
  have hdetD : GeneralLinearGroup.det D = δ := by
    rw [hDd, uniDiagGL_det]
    show ∏ x : HypIndex (t + s) ε, uniTorusUnits h a' x = δ
    rw [prod_uniTorusUnits]
    have e1 : ∏ i, a' i = a₀ := by simp [a']
    have e2 : ∏ i, (Units.map (h.bar : K →* K) (a' i))⁻¹ =
        (Units.map (h.bar : K →* K) a₀)⁻¹ := by
      simp [a', apply_ite]
    rw [e1, e2]
    exact ha₀
  have hD' : D⁻¹ ∈ hypUnitary h (t + s) ε := (hypUnitary h (t + s) ε).inv_mem hD
  have hs₀ : A * D⁻¹ ∈ hypSU h (t + s) ε := by
    refine ⟨mem_hypUnitary.1 ((hypUnitary h (t + s) ε).mul_mem hA hD'), ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hdetD, mul_inv_cancel,
      Units.val_one]
  let s₁ : hypSU h (t + s) ε := ⟨A * D⁻¹, hs₀⟩
  have hAs : A = (s₁ : GL (HypIndex (t + s) ε) K) * D := by
    simp [s₁]
  have hdQ : ∀ x ∈ Q, uniConjSU D hD x ∈ Q := fun x hx =>
    uniDiag_conj_mem_flagStabilizer hε hIr d hDd hD hx
  have hdQ' : ∀ x ∈ Q, uniConjSU D⁻¹ hD' x ∈ Q := fun x hx =>
    uniDiag_conj_mem_flagStabilizer hε hIr d⁻¹ (uniDiagGL_inv d) hD' hx
  have hs₁N : ∀ x ∈ Q, s₁ * x * s₁⁻¹ ∈ Q := by
    intro x hx
    have e : s₁ * x * s₁⁻¹ = uniConjSU A hA (uniConjSU D⁻¹ hD' x) :=
      Subtype.ext (by simp [s₁, uniConjSU_coe, mul_assoc])
    rw [e]
    exact hQA _ (hdQ' x hx)
  have hs₁Q : s₁ ∈ Q := uniMem_of_normalizes_coverSub hCP ρ hρs hcomap.symm hs₁N
  let φ₀ : ↥Q →* ↥Q := ((uniConjSU A hA).toMonoidHom.comp Q.subtype).codRestrict Q
    fun x => hQA x x.2
  have hφinj : Function.Injective φ₀ := fun x y hxy =>
    Subtype.ext ((uniConjSU A hA).injective (congrArg Subtype.val hxy))
  have hφsurj : Function.Surjective φ₀ := Finite.injective_iff_surjective.1 hφinj
  let φ : MulAut ↥Q := MulEquiv.ofBijective φ₀ ⟨hφinj, hφsurj⟩
  have hφval : ∀ x : ↥Q, ((φ x : ↥Q) : hypSU h (t + s) ε) =
      uniConjSU A hA (x : hypSU h (t + s) ε) := fun x => rfl
  let g : ∀ j : Option ↥I, uniBlockGroup K s ε I j :=
    uniLeviHom h hε hI ⟨s₁, hs₁Q⟩ * uniDiagBlocks hI d
  have hdres : (d ∘ resIdx t : HypIndex s ε → Kˣ) = fun _ => 1 := by
    funext y
    have hne : ∀ i : Fin s, (Fin.natAdd t i : Fin (t + s)) ≠ i₀ := fun i hi => by
      have := congrArg Fin.val hi
      simp [i₀] at this
      omega
    rcases y with i | k | i
    · simp [d, uniTorusUnits, resIdx, a', hne i]
    · simp [d, uniTorusUnits, resIdx]
    · simp [d, uniTorusUnits, resIdx, a', hne i]
  have hg : ∀ j, g j ∈ uniBlockH h s ε I j := by
    intro j
    rcases j with _ | b
    · have h1 := uniLeviHom_mem_H h hε hI ⟨s₁, hs₁Q⟩ none
      have h2 : uniDiagBlocks hI d none = 1 := by
        change uniDiagGL (d ∘ resIdx t) = 1
        rw [hdres]
        exact uniDiagGL_one
      show uniLeviHom h hε hI ⟨s₁, hs₁Q⟩ none * uniDiagBlocks hI d none ∈ _
      rw [h2, mul_one]
      exact h1
    · exact Subgroup.mem_top _
  have hφ : ∀ x : ↥Q, uniLeviHom h hε hI (φ x) = g * uniLeviHom h hε hI x * g⁻¹ := by
    intro x
    have hxD := hdQ x x.2
    have e1 : φ x = ⟨s₁, hs₁Q⟩ * ⟨uniConjSU D hD x, hxD⟩ * ⟨s₁, hs₁Q⟩⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [hφval, uniConjSU_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hAs]
      group
    rw [e1, map_mul, map_mul, map_inv, uniLeviHom_conj_diag h hε hI d hDd hD x hxD]
    simp only [g]
    group
  have hker : ρ.ker ≤ Subgroup.center (hypSU h (t + s) ε) := fun y hy =>
    normOneScalars_le_center h _ _
      ((hZ y).1 (by rw [MonoidHom.mem_ker.1 hy]; exact Subgroup.one_mem _))
  exact uniActsInnerly_of_levi_data_index hCP.parab.1 ρ hρs hker Q hcomap.symm
    (G := uniBlockGroup K s ε I) (uniBlockSub (s := s) (ε := ε) h I) (uniBlockH h s ε I)
    (uniLeviHom h hε hI) (isPGroup_ker_uniLeviHom h hε hI) (pi_uniBlockSub_le_range h hε hI)
    (commutator_range_le_pi h hε hI) (fun j => (uniBlockSub_facts h hε hI j).1)
    (fun j hq => uniBlockOK h hε j hq)
    (fun j E hES hE hcard x hρx hβx => uniHZ h hε hI ρ hZ hrank3 j E hES hE hcard x hρx hβx)
    φ g hg hφ (fun x => hcm x) hpow hrk

end LeviData

section Data

theorem exists_uniCover_std
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (hC : IsLieOf IdxTwistedA (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Field K) (f t s ε : ℕ) (h : UnitaryFieldData 2 f K)
      (ρ : hypSU h (t + s) ε →* ↥L) (I : Finset ℕ),
      ε ≤ 1 ∧ IsTopCut I t ∧ 3 ≤ 2 * (t + s) + ε ∧ ¬(2 * (t + s) + ε = 3 ∧ 2 ^ f = 2) ∧
        Function.Surjective ρ ∧
        (∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) ∧
        (P.subgroupOf L).comap ρ = flagStabilizer h (t + s) ε ↑I := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, hK, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hd e
  have hdim : 3 ≤ 2 * (t + s) + ε ∧ ¬(2 * (t + s) + ε = 3 ∧ 2 ^ f = 2) := by
    obtain ⟨d', hv⟩ := d
    cases d' with
    | twistedA r₀ q =>
      obtain ⟨hqc, hn⟩ := hq r₀ q rfl
      have hqp : q.p = 2 := hd
      have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r₀ q hv e
      rw [hqp] at hc
      obtain ⟨⟨-, -, hn3, hnq⟩, -⟩ := hc
      have hqe : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hqp]
      simp only [ne_eq, Prod.mk.injEq] at hnq
      refine ⟨by omega, fun ⟨h1, h2⟩ => hnq ⟨by omega, ?_⟩⟩
      rw [← hqe, hqc]
      exact h2
    | _ => exact hd.elim
  have hmem : ∀ y : hypSU h (t + s) ε, y ∈ (P.subgroupOf L).comap ρ ↔
      g⁻¹ * y * g ∈ flagStabilizer h (t + s) ε ↑I := by
    intro y
    rw [hJ, mem_flagStabilizer]
    refine forall₂_congr fun i _ => ?_
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine ⟨K, hK, f, t, s, ε, h, ρ.comp (MulAut.conj g).toMonoidHom, I, hε, hI, hdim.1, hdim.2,
    hρ.comp (MulAut.conj g).surjective, fun y => ?_, ?_⟩
  · rw [MonoidHom.comp_apply]
    change ρ (MulAut.conj g y) ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε
    rw [hZ]
    constructor
    · intro hy
      have := (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hy g⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hy
      have := (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hy g
      simpa [MulAut.conj_apply] using this
  · ext y
    have h1 : y ∈ (P.subgroupOf L).comap (ρ.comp (MulAut.conj g).toMonoidHom) ↔
        (MulAut.conj g y : hypSU h (t + s) ε) ∈ (P.subgroupOf L).comap ρ := Iff.rfl
    rw [h1, hmem]
    have : g⁻¹ * (MulAut.conj g y : hypSU h (t + s) ε) * g = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]

end Data

theorem leviInnOn_unitary :
    LeviInnOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk
  haveI := hLn
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, hε, hI, -, -, hρs, hZ, hcomap⟩ := exists_uniCover_std hCP hC
  haveI : Finite K := h.finite
  intro l hl k hcomm
  have hlL : l ∈ L := hCP.parab.1 hl
  obtain ⟨x₀, hx₀⟩ := hρs ⟨l, hlL⟩
  have hA : (x₀ : GL (HypIndex (t + s) ε) K) ∈ hypUnitary h (t + s) ε :=
    mem_hypUnitary.2 x₀.2.1
  refine uniActsInnerly_of_compat hCP h hε hI ρ hρs hZ hcomap
    (hrank 3 Nat.prime_three (by norm_num)) hA (a := l) (Subgroup.le_normalizer hl)
    (fun y => ?_) ⟨k, fun w hw => ?_⟩ hrk
  · have e : uniConjSU (x₀ : GL (HypIndex (t + s) ε) K) hA y = x₀ * y * x₀⁻¹ := rfl
    have e2 : ρ (uniConjSU (x₀ : GL (HypIndex (t + s) ε) K) hA y) =
        (MulAut.conjNormal l : MulAut ↥L) (ρ y) := by
      rw [e, map_mul, map_mul, map_inv, hx₀]
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    rw [e2, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact commutatorElement_eq_one_iff_mul_comm.1 (hcomm w hw)

section Diagonal

theorem uniPCentral_map {Γ Δ C : Type*} [Group Γ] [Group Δ] [Group C] (Φ : Γ →* Δ)
    (hΦ : Function.Surjective Φ) (ψ : Γ →* C) (hC : ∀ x y : C, x * y = y * x) {p : ℕ} :
    PCentral p (ψ.ker.map Φ) := by
  refine ⟨Subgroup.Normal.map inferInstance Φ hΦ, fun α _ γ => ?_⟩
  obtain ⟨x, rfl⟩ := hΦ α
  obtain ⟨y, rfl⟩ := hΦ γ
  refine ⟨⁅y, x⁆, ?_, map_commutatorElement Φ y x⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 (hC _ _)]

theorem uniPCentral_comap_of_mulEquiv {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ'] (ψ : Γ ≃* Γ')
    {D : Subgroup Γ'} (hD : PCentral p D) : PCentral p (D.comap ψ.toMonoidHom) := by
  haveI := hD.1
  refine ⟨inferInstance, fun α ⟨k, hk⟩ γ => ?_⟩
  have h1 : ψ α ^ (p ^ k) ∈ D := by
    rw [← map_pow]
    exact hk
  have h2 := hD.2 (ψ α) ⟨k, h1⟩ (ψ γ)
  rw [Subgroup.mem_comap]
  simpa only [MulEquiv.coe_toMonoidHom, map_commutatorElement] using h2

variable {f r ε : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
  {Y : Type} [Group Y] {L : Subgroup Y}

@[expose] noncomputable def uniCoverEquiv (ρ : hypSU h r ε →* ↥L) (hρ : Function.Surjective ρ)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h r ε) :
    hypPSU h r ε ≃* ↥L ⧸ Subgroup.center ↥L :=
  let ρ' : hypSU h r ε →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp ρ
  have hker : hypScalars h r ε = ρ'.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ]
  have hs : Function.Surjective ρ' := (QuotientGroup.mk'_surjective _).comp hρ
  (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective ρ' hs)

theorem uniCoverEquiv_hypProj (ρ : hypSU h r ε →* ↥L) (hρ : Function.Surjective ρ)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h r ε) (y : hypSU h r ε) :
    uniCoverEquiv ρ hρ hZ (hypProj h r ε y) = (QuotientGroup.mk (ρ y) : ↥L ⧸ Subgroup.center ↥L) :=
  rfl

end Diagonal

theorem fieldIndexOn_unitary :
    FieldIndexOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  obtain ⟨K, hK, f, t, s, ε, h, ρ, I, hε, hI, hn3, hnq, hρs, hZ, hcomap⟩ :=
    exists_uniCover_std hCP hC
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hr : 1 ≤ t + s := by omega
  obtain ⟨θ, hθ⟩ : ∃ θ : hypPSU h (t + s) ε ≃* ↥L ⧸ Subgroup.center ↥L,
      ∀ y, θ (hypProj h (t + s) ε y) = (QuotientGroup.mk (ρ y) : ↥L ⧸ Subgroup.center ↥L) :=
    ⟨uniCoverEquiv ρ hρs hZ, uniCoverEquiv_hypProj ρ hρs hZ⟩
  let ψ : ↥(semilinearSimilitudes h (t + s) ε) →* (K ≃+* K) :=
    (SemidirectProduct.rightHom).comp (semilinearSimilitudes h (t + s) ε).subtype
  have hΦs : Function.Surjective (semilinearAutHom h hr hε) :=
    semilinearAutHom_surjective_of_admissible h hr hε hn3 hnq
  have hDpc : PCentral 3 (ψ.ker.map (semilinearAutHom h hr hε)) :=
    uniPCentral_map _ hΦs ψ (ringAut_comm K)
  have hD : PCentral 3 ((ψ.ker.map (semilinearAutHom h hr hε)).comap
      (MulAut.congr θ.symm).toMonoidHom) :=
    uniPCentral_comap_of_mulEquiv (MulAut.congr θ.symm) hDpc
  refine fieldIndex_core hD ha3 hout fun hmem => ?_
  obtain ⟨x₀, hx₀k, hx₀⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hmem)
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h hr hε hn3 x₀
  have hA : (x : SemiGL (HypIndex (t + s) ε) K).left ∈ hypUnitary h (t + s) ε := hxU
  have hr0 : (x₀ : SemiGL (HypIndex (t + s) ε) K).right = 1 := by
    have := MonoidHom.mem_ker.1 hx₀k
    simpa [ψ] using this
  have hxr1 : (x : SemiGL (HypIndex (t + s) ε) K).right = 1 := hxr.trans hr0
  have hcm : ∀ y : hypSU h (t + s) ε, (MulAut.conjNormal a : MulAut ↥L) (ρ y) *
      (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y))⁻¹ ∈
        Subgroup.center ↥L := by
    intro y
    have h1 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        hypProj h (t + s) ε (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y) := by
      rw [semilinearAutHom_apply]
      congr 1
      apply Subtype.ext
      change (x : SemiGL (HypIndex (t + s) ε) K).left *
        glAut (x : SemiGL (HypIndex (t + s) ε) K).right (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹ =
        (x : SemiGL (HypIndex (t + s) ε) K).left * (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹
      rw [hxr1, map_one]
      rfl
    have h2 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        θ.symm (convAut L a (θ (hypProj h (t + s) ε y))) := by
      rw [hxΦ, hx₀]
      rfl
    have h4 : θ (hypProj h (t + s) ε
        (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) =
          convAut L a (QuotientGroup.mk (ρ y)) := by
      rw [← h1, h2, θ.apply_symm_apply, hθ]
    rw [hθ] at h4
    have h5 : (QuotientGroup.mk (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) :
        ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk ((MulAut.conjNormal a : MulAut ↥L) (ρ y)) := h4
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 h5.symm
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact uniActsInnerly_of_compat hCP h hε hI ρ hρs hZ hcomap
    (hrank 3 Nat.prime_three (by norm_num)) hA haN hcm
    ⟨k, fun w _ => by rw [hak, one_mul, mul_one]⟩ hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
