module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealEigen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealKey
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniBlock
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniLine

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.K155X

section Triple

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section FieldTransport

variable {n d : ℕ} {E : Type} [Field E]

theorem u6r_mem_gramSU_map_iff (h : UnitaryFieldData 2 f K)
    (hE : UnitaryFieldData 2 (f * d) E) (α : K ≃+* E)
    (hbar : ∀ k : K, hE.bar (α k) = α (h.bar k)) (M : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.map α M ∈ gramSU hE (idGram E n) ↔
      M ∈ gramSU h (idGram K n) := by
  rw [mem_gramSU, mem_gramSU]
  simp only [idGram, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have hcoe : ∀ (N : GL (Fin n) K),
      ((Matrix.GeneralLinearGroup.map α N : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (N : Matrix (Fin n) (Fin n) K).map α := by
    intro N
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  have hmap : ∀ (N : GL (Fin n) K),
      ((((Matrix.GeneralLinearGroup.map α N : GL (Fin n) E) :
            Matrix (Fin n) (Fin n) E).map hE.bar)ᵀ *
          ((Matrix.GeneralLinearGroup.map α N : GL (Fin n) E) :
            Matrix (Fin n) (Fin n) E)) =
        ((((N : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          (N : Matrix (Fin n) (Fin n) K))).map α := by
    intro N
    rw [hcoe N]
    rw [show (((N : Matrix (Fin n) (Fin n) K).map α).map hE.bar) =
        ((N : Matrix (Fin n) (Fin n) K).map h.bar).map α by
      ext i j
      simp [hbar]]
    rw [← Matrix.transpose_map]
    simp only [Matrix.map_mul, Matrix.map_one, Matrix.mul_one]
  constructor
  · rintro ⟨hunit, hdet⟩
    have hunit' : ((M : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        (M : Matrix (Fin n) (Fin n) K) = 1 := by
      apply Matrix.map_injective α.injective
      change (((M : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        (M : Matrix (Fin n) (Fin n) K)).map α = (1 : Matrix (Fin n) (Fin n) K).map α
      rw [← hmap M, hunit]
      simp
    refine ⟨hunit', ?_⟩
    have hdet' : α (Matrix.det (M : Matrix (Fin n) (Fin n) K)) = 1 := by
      have h := hdet
      rw [hcoe M] at h
      change Matrix.det ((α : K →+* E).mapMatrix (M : Matrix (Fin n) (Fin n) K)) = 1 at h
      rw [← RingHom.map_det] at h
      exact h
    exact α.injective (by simpa using hdet')
  · rintro ⟨hunit, hdet⟩
    have hunit' : (((Matrix.GeneralLinearGroup.map α M : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E).map hE.bar)ᵀ *
        ((Matrix.GeneralLinearGroup.map α M : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) = 1 := by
      rw [hmap M, hunit]
      simp
    refine ⟨hunit', ?_⟩
    rw [hcoe M]
    change Matrix.det ((α : K →+* E).mapMatrix (M : Matrix (Fin n) (Fin n) K)) = 1
    rw [← RingHom.map_det, hdet, map_one]

end FieldTransport

section Action

variable {E : Type} [Field E] [Algebra K E] {W : Type*} [AddCommGroup W] [Module K W]
  [Module E W] [IsScalarTower K E W]

theorem u6r_algEquiv_smul (α : K ≃ₐ[K] E) (c : K) (v : W) : (α c) • v = c • v := by
  have h : α c = algebraMap K E c := by simpa using α.commutes c
  rw [h, IsScalarTower.algebraMap_smul]

variable {n : ℕ}

theorem u6r_toLin'_apply_basis (e : Module.Basis (Fin n) E W) (M : GL (Fin n) E) (k : Fin n) :
    ((Matrix.GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup E W) :
        Module.End E W) (e k) = ∑ i, (M : Matrix (Fin n) (Fin n) E) i k • e i := by
  have hsingle : e.equivFun (e k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  rw [CFSG.LocalAnalysis.ComponentInitial.toLin'_apply_eq, hsingle,
    Matrix.mulVec_single_one, Module.Basis.equivFun_symm_apply]
  simp only [Matrix.col_apply]

end Action

theorem u6r_tr_map_fixSub {Y : Type*} [Group Y] {η ε : MulAut Y} (hc : ε * η = η * ε) :
    (Lemma510Ns.fixSub η).map ε.toMonoidHom = Lemma510Ns.fixSub η := by
  ext y
  simp only [Subgroup.mem_map, Lemma510Ns.mem_fixSub, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : (ε * η) x = (η * ε) x := by rw [hc]
    simp only [MulAut.mul_apply] at h1
    rw [← h1, hx]
  · intro hy
    refine ⟨ε.symm y, ?_, by simp⟩
    have h1 : (ε * η) (ε.symm y) = (η * ε) (ε.symm y) := by rw [hc]
    simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply, hy] at h1
    have h2 := congrArg ε.symm h1
    simpa using h2

theorem u6r_tr_kappa_cube {B D : GL (Fin 6) K} (hB3 : B ^ 3 = 1) {κ : Kˣ}
    (hDB : D * B * D⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) : κ ^ 3 = 1 := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 6) (κ ^ 3) = 1 := by
    have e1 : (D * B * D⁻¹) ^ 3 = 1 := by rw [conj_pow, hB3, mul_one, mul_inv_cancel]
    rw [hDB, (commute_scalar κ B).symm.mul_pow, hB3, mul_one, ← map_pow] at e1
    exact e1
  have h2 := congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K) 0 0) h1
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h2
  exact Units.ext (by simpa using h2)

theorem u6r_tr_comm (B D : primeFormUnitary h (idGram K 6)) {κ : Kˣ}
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) :
    primeFormConjHom h (idGram K 6) D * primeFormConjHom h (idGram K 6) B =
      primeFormConjHom h (idGram K 6) B * primeFormConjHom h (idGram K 6) D := by
  have hS : primeFormConjHom h (idGram K 6) (D * B * D⁻¹ * B⁻¹) = 1 := by
    refine (CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.conj_eq_one_iff h (by norm_num) _).2 ⟨κ, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hDB, mul_inv_cancel_right]
  simp only [map_mul, map_inv] at hS
  calc primeFormConjHom h (idGram K 6) D * primeFormConjHom h (idGram K 6) B
      = (primeFormConjHom h (idGram K 6) D * primeFormConjHom h (idGram K 6) B *
          (primeFormConjHom h (idGram K 6) D)⁻¹ * (primeFormConjHom h (idGram K 6) B)⁻¹) *
          primeFormConjHom h (idGram K 6) B * primeFormConjHom h (idGram K 6) D := by group
    _ = primeFormConjHom h (idGram K 6) B * primeFormConjHom h (idGram K 6) D := by
      rw [hS, one_mul]

theorem u6r_four_le (hf : Odd f) (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B)
    {H : Subgroup (primeFormP h (idGram K 6))}
    (hH : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B)) H) :
    4 ≤ 2 ^ f := by
  have hap : (B : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) := by
    rw [map_one]
    exact hB3
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  obtain ⟨⟨⟨b, hb⟩, hgood⟩, -⟩ := u6r_exists_block B H hH
  obtain ⟨c, hc3, rfl⟩ := u6r_primaryFactor_eq B hB3 hb
  have h2 := hgood.2 (u6r_dualPoly h hf hc3)
  have hm := u6r_multiplicity_eq_two B D hB3 hκ1 hDB hc3
  change (primaryMultiplicity ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (X - C c), 2 ^ (f * (X - C c : K[X]).natDegree)) ∉
    ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) at h2
  rw [hm, natDegree_X_sub_C, mul_one] at h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or] at h2
  have hf2 : 2 ≤ 2 ^ f := by
    have := h.one_le
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  by_contra hlt
  have h23 : 2 ^ f = 2 ∨ 2 ^ f = 3 := by omega
  rcases h23 with h' | h'
  · exact h2.1 ⟨trivial, h'⟩
  · exact h2.2.1 ⟨trivial, h'⟩

theorem u6r_triple (hf : Odd f) (hf4 : 4 ≤ 2 ^ f) (B D : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1) {κ : Kˣ} (hκ1 : κ ≠ 1)
    (hDB : (D : GL (Fin 6) K) * B * (D : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ * B) :
    ∃ H₁ H₂ H₃ : Subgroup (primeFormP h (idGram K 6)),
      (∀ H : Subgroup (primeFormP h (idGram K 6)),
        GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B)) H ↔
          (H = H₁ ∨ H = H₂ ∨ H = H₃)) ∧
      H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
      (∀ H : Subgroup (primeFormP h (idGram K 6)), (H = H₁ ∨ H = H₂ ∨ H = H₃) →
        IsTypeL2 (2 ^ f) (barOf 3 H)) ∧
      H₁.map (primeFormConjHom h (idGram K 6) D).toMonoidHom = H₂ ∧
      H₂.map (primeFormConjHom h (idGram K 6) D).toMonoidHom = H₃ ∧
      H₃.map (primeFormConjHom h (idGram K 6) D).toMonoidHom = H₁ := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  have hap : (B : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) := by
    rw [map_one]
    exact hB3
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  have hκ3 : κ ^ 3 = 1 := u6r_tr_kappa_cube hB3 hDB
  set w : K := ((κ⁻¹ : Kˣ) : K) with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← Units.val_pow_eq_pow_val, inv_pow, hκ3, inv_one, Units.val_one]
  have hw1 : w ≠ 1 := by
    intro h1
    apply hκ1
    have : (κ⁻¹ : Kˣ) = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    exact inv_eq_one.1 this
  have hw0 : w ≠ 0 := Units.ne_zero _
  let N : K → Subgroup ↥(gramSU h (idGram K 6)) := fun d =>
    (specialBlock (idForm h 6) (t6psub_toLin B) (X - C d)).comap (t6psuh_toLinSU h 6)
  let ι : ∀ d : K, d ^ 3 = 1 → t6psub_Idx h 6 B := fun d hd =>
    ⟨⟨X - C d, u6r_mem_primaryFactors_of_cycle B D hB3 hκ1 hDB hd⟩,
      u6r_isGoodBlock hf4 B D hB3 hκ1 hDB hd⟩
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6) with hπ
  have hq : ∀ d (hd : d ^ 3 = 1), CFSG.IsQuasisimple ↥(N d) := fun d hd =>
    t6psub_isQuasisimple_block B H (ι d hd)
  have hperfN : ∀ d (hd : d ^ 3 = 1), ⁅N d, N d⁆ = N d := fun d hd =>
    Subgroup.isPerfect_iff.1 (hq d hd).1
  have hT : ∀ d (hd : d ^ 3 = 1), IsTypeL2 (2 ^ f) ↥((N d).map π) := by
    intro d hd
    have h1 := u6r_isTypeL2_block B H (ι d hd) (u6r_dualPoly h hf hd)
      (u6r_multiplicity_eq_two B D hB3 hκ1 hDB hd)
    have h2 : (2 : ℕ) ^ (f * ((ι d hd).1 : K[X]).natDegree) = 2 ^ f := by
      show 2 ^ (f * (X - C d : K[X]).natDegree) = 2 ^ f
      rw [natDegree_X_sub_C, mul_one]
    rw [h2] at h1
    exact h1
  have hcomp : ∀ d (hd : d ^ 3 = 1),
      GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B)) ((N d).map π) :=
    fun d hd => u6r_block_comp B H (ι d hd) (hT d hd)
  have hall : ∀ H' : Subgroup (primeFormP h (idGram K 6)),
      GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B)) H' →
        ∃ c : K, c ^ 3 = 1 ∧ H' = (N c).map π := by
    intro H' hH'
    obtain ⟨⟨⟨b, hb⟩, hg⟩, hi'⟩ := u6r_exists_block B H hH'
    obtain ⟨c, hc3, rfl⟩ := u6r_primaryFactor_eq B hB3 hb
    exact ⟨c, hc3, u6r_eq_block B H hH' ⟨⟨X - C c, hb⟩, hg⟩ hi' (hT c hc3)⟩
  have hNne : ∀ d (hd : d ^ 3 = 1), ∃ g ∈ N d, g ≠ 1 := by
    intro d hd
    haveI : Nontrivial ↥(N d) := nontrivial_of_isQuasisimple' (isQuasisimple_open (hq d hd))
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(N d))
    exact ⟨x, x.2, fun h1 => hx (Subtype.ext h1)⟩
  have hdist : ∀ d e (hd : d ^ 3 = 1) (he : e ^ 3 = 1), (N d).map π = (N e).map π → d = e := by
    intro d e hd he hde
    by_contra hne
    have hle : N d ≤ N e := u6r_le_of_map_le π u6r_ker_le_center (hperfN d hd) (le_of_eq hde)
    obtain ⟨g, hg, hg1⟩ := hNne d hd
    have h1 : t6psub_actSU h 6 1 g ∈ N e := by
      simp only [map_one, MulAut.one_apply]
      exact hle hg
    have hDB1 : ((1 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) * B *
        ((1 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) * B := by
      simp
    refine hg1 (u6r_supp hf B 1 hB3 hDB1 hd he (fun heq => hne ?_) hg h1)
    simp only [inv_one, Units.val_one, one_mul] at heq
    exact heq.symm
  have hfixmap := u6r_tr_map_fixSub (u6r_tr_comm B D hDB)
  have hDcomp : ∀ H' : Subgroup (primeFormP h (idGram K 6)),
      GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B)) H' →
        GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) B))
          (H'.map (primeFormConjHom h (idGram K 6) D).toMonoidHom) := by
    intro H' hH'
    have hk : (primeFormConjHom h (idGram K 6) D).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).2 (primeFormConjHom h (idGram K 6) D).injective
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map Nat.prime_three
      (primeFormConjHom h (idGram K 6) D).toMonoidHom
      (by rw [hk, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right 3) hH'
    rwa [hfixmap] at h1
  have hmapD : ∀ d, ((N d).map π).map (primeFormConjHom h (idGram K 6) D).toMonoidHom =
      ((N d).map (t6psub_actSU h 6 D).toMonoidHom).map π := by
    intro d
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hrot : ∀ d (hd : d ^ 3 = 1),
      ((N d).map π).map (primeFormConjHom h (idGram K 6) D).toMonoidHom = (N (w * d)).map π := by
    intro d hd
    obtain ⟨c, hc3, hc⟩ := hall _ (hDcomp _ (hcomp d hd))
    have hce : c = w * d := by
      by_contra hne
      have hperf : ⁅(N d).map (t6psub_actSU h 6 D).toMonoidHom,
          (N d).map (t6psub_actSU h 6 D).toMonoidHom⁆ =
            (N d).map (t6psub_actSU h 6 D).toMonoidHom := by
        rw [← Subgroup.map_commutator, hperfN d hd]
      have hle : (N d).map (t6psub_actSU h 6 D).toMonoidHom ≤ N c :=
        u6r_le_of_map_le π u6r_ker_le_center hperf (by rw [← hmapD, hc])
      obtain ⟨g, hg, hg1⟩ := hNne d hd
      exact hg1 (u6r_supp hf B D hB3 hDB hd hc3 hne hg (hle ⟨g, hg, rfl⟩))
    rw [hc, hce]
  have h1c : (1 : K) ^ 3 = 1 := one_pow 3
  have hwwc : (w * w) ^ 3 = 1 := by rw [mul_pow, hw3, one_mul]
  refine ⟨(N 1).map π, (N w).map π, (N (w * w)).map π, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H'
    constructor
    · intro hH'
      obtain ⟨c, hc3, rfl⟩ := hall H' hH'
      rcases u6r_cube_root_cases hw3 hw1 hc3 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [sq]))
    · rintro (rfl | rfl | rfl)
      · exact hcomp 1 h1c
      · exact hcomp w hw3
      · exact hcomp (w * w) hwwc
  · intro heq
    exact hw1 (hdist 1 w h1c hw3 heq).symm
  · intro heq
    have h1 := hdist 1 (w * w) h1c hwwc heq
    apply hw1
    calc w = w * (w * w) := by rw [← h1, mul_one]
      _ = w ^ 3 := by ring
      _ = 1 := hw3
  · intro heq
    have h1 := hdist w (w * w) hw3 hwwc heq
    apply hw1
    have h2 : w * 1 = w * w := by rw [mul_one]; exact h1
    exact (mul_left_cancel₀ hw0 h2).symm
  · rintro H' (rfl | rfl | rfl)
    · exact u6r_isTypeL2_barOf (isQuasisimple_open (u6r_block_quasisimple B H (ι 1 h1c))) (hT 1 h1c)
    · exact u6r_isTypeL2_barOf (isQuasisimple_open (u6r_block_quasisimple B H (ι w hw3))) (hT w hw3)
    · exact u6r_isTypeL2_barOf (isQuasisimple_open (u6r_block_quasisimple B H (ι (w * w) hwwc)))
        (hT (w * w) hwwc)
  · rw [hrot 1 h1c, mul_one]
  · exact hrot w hw3
  · rw [hrot (w * w) hwwc]
    congr 2
    calc w * (w * w) = w ^ 3 := by ring
      _ = 1 := hw3

theorem u6r_scalar_eq_one_of_normalizes_component
    {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (hf : Odd f) (B D : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1) {κ : Kˣ}
    (hDB : (D : GL (Fin n) K) * B * (D : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) κ * B)
    (JP : Subgroup (primeFormP h (idGram K n)))
    (hJP : CFSG.Open.IsComponentOf JP
      (fixSubgroup (primeFormConjHom h (idGram K n) B)))
    (hN : ∀ z ∈ JP, primeFormConjHom h (idGram K n) D z ∈ JP) : κ = 1 := by
  classical
  have hap : (B : GL (Fin n) K) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [map_one]
    exact hB3
  have H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  obtain ⟨a, ha⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.exists_good_block_of_component
      (h := h) (n := n) hq B rfl H JP hJP
  let N : Subgroup ↥(gramSU h (idGram K n)) := t6psub_block B a
  let π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  have hJP_eq : JP = N.map π := by
    rw [ha]
    rfl
  have hqN : CFSG.IsQuasisimple N := t6psub_isQuasisimple_block B H a
  have hNperf : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.1 hqN.1
  have hleJP : JP.map (primeFormConjHom h (idGram K n) D).toMonoidHom ≤ JP := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hN w hw
  have hleNπ : (N.map π).map (primeFormConjHom h (idGram K n) D).toMonoidHom ≤ N.map π := by
    simpa only [hJP_eq] using hleJP
  have hmap : (N.map (t6psub_actSU h n D).toMonoidHom).map π =
      (N.map π).map (primeFormConjHom h (idGram K n) D).toMonoidHom := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨x, hxN, rfl⟩ := hz
      exact ⟨π x, ⟨x, hxN, rfl⟩, (t6psub_hact D x).symm⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨x, hxN, rfl⟩ := hz
      exact ⟨t6psub_actSU h n D x, ⟨x, hxN, rfl⟩, t6psub_hact D x⟩
  have hproj : (N.map (t6psub_actSU h n D).toMonoidHom).map π ≤ N.map π := by
    rw [hmap]
    exact hleNπ
  have hM : ⁅N.map (t6psub_actSU h n D).toMonoidHom,
      N.map (t6psub_actSU h n D).toMonoidHom⁆ =
      N.map (t6psub_actSU h n D).toMonoidHom := by
    rw [← Subgroup.map_commutator, hNperf]
  have hleN : N.map (t6psub_actSU h n D).toMonoidHom ≤ N :=
    u6r_le_of_map_le π u6r_ker_le_center hM hproj
  haveI : Nontrivial ↥N :=
    nontrivial_of_isQuasisimple' (isQuasisimple_open hqN)
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥N)
  let g : ↥(gramSU h (idGram K n)) := x
  have hgN : g ∈ N := x.2
  have hg1 : g ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hDgN : t6psub_actSU h n D g ∈ N := hleN ⟨g, hgN, rfl⟩
  by_contra hκ1
  obtain ⟨c, hc3, hc_eq⟩ := u6r_primaryFactor_eq B hB3 a.1.2
  have hne : c ≠ ((κ⁻¹ : Kˣ) : K) * c := by
    intro h
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0] at hc3
      norm_num at hc3
    have h1 : (1 : K) = ((κ⁻¹ : Kˣ) : K) := by
      have h2 : (1 : K) * c = ((κ⁻¹ : Kˣ) : K) * c := by
        rw [one_mul]
        exact h
      exact mul_right_cancel₀ hc0 h2
    exact hκ1 (inv_eq_one.mp (Units.ext h1.symm))
  have hg' : g ∈ (specialBlock (idForm h n) (t6psub_toLin B) (X - C c)).comap
      (t6psuh_toLinSU h n) := by
    change g ∈ (specialBlock (idForm h n) (t6psub_toLin B) (a.1 : K[X])).comap
      (t6psuh_toLinSU h n) at hgN
    rwa [hc_eq] at hgN
  have hDg' : t6psub_actSU h n D g ∈
      (specialBlock (idForm h n) (t6psub_toLin B) (X - C c)).comap
        (t6psuh_toLinSU h n) := by
    change t6psub_actSU h n D g ∈
      (specialBlock (idForm h n) (t6psub_toLin B) (a.1 : K[X])).comap
        (t6psuh_toLinSU h n) at hDgN
    rwa [hc_eq] at hDgN
  exact hg1 (u6r_supp hf B D hB3 hDB hc3 hc3 hne hg' hDg')

theorem u6r_commute_of_normalizes_component
    {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (hf : Odd f) (hn : 3 ≤ n) (B D : primeFormUnitary h (idGram K n))
    (hB3 : (B : GL (Fin n) K) ^ 3 = 1)
    (hcomm : primeFormConjHom h (idGram K n) D * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) D)
    (JP : Subgroup (primeFormP h (idGram K n)))
    (hJP : CFSG.Open.IsComponentOf JP
      (fixSubgroup (primeFormConjHom h (idGram K n) B)))
    (hN : ∀ z ∈ JP, primeFormConjHom h (idGram K n) D z ∈ JP) :
    (D : GL (Fin n) K) * (B : GL (Fin n) K) =
      (B : GL (Fin n) K) * (D : GL (Fin n) K) := by
  obtain ⟨ζ, hζ⟩ := u6r_comm_scalar hn B D hcomm
  have hζ1 : ζ = 1 :=
    u6r_scalar_eq_one_of_normalizes_component hf B D hB3 hζ JP hJP hN
  have hDB : (D : GL (Fin n) K) * (B : GL (Fin n) K) * (D : GL (Fin n) K)⁻¹ =
      (B : GL (Fin n) K) := by
    rw [hζ, hζ1, map_one, one_mul]
  calc (D : GL (Fin n) K) * (B : GL (Fin n) K)
      = ((D : GL (Fin n) K) * (B : GL (Fin n) K) * (D : GL (Fin n) K)⁻¹) *
          (D : GL (Fin n) K) := by group
    _ = (B : GL (Fin n) K) * (D : GL (Fin n) K) := by rw [hDB]

theorem u6r_a2_block_of_normalizes_component
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (hf : Odd f)
    (B g₁ g₂ : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1)
    (hBns : ¬ ∃ c : Kˣ,
      (B : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (JP : Subgroup (primeFormP h (idGram K 6)))
    (hJP : CFSG.Open.IsComponentOf JP
      (fixSubgroup (primeFormConjHom h (idGram K 6) B)))
    (κ : Kˣ) (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (h12 : (g₁ : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) *
        (g₁ : GL (Fin 6) K)⁻¹ * (g₂ : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (h1B : primeFormConjHom h (idGram K 6) g₁ *
        primeFormConjHom h (idGram K 6) B =
      primeFormConjHom h (idGram K 6) B *
        primeFormConjHom h (idGram K 6) g₁)
    (h2B : primeFormConjHom h (idGram K 6) g₂ *
        primeFormConjHom h (idGram K 6) B =
      primeFormConjHom h (idGram K 6) B *
        primeFormConjHom h (idGram K 6) g₂)
    (hN1 : ∀ z ∈ JP, primeFormConjHom h (idGram K 6) g₁ z ∈ JP)
    (hN2 : ∀ z ∈ JP, primeFormConjHom h (idGram K 6) g₂ z ∈ JP) :
    ∃ (a : t6psub_Idx h 6 B) (c : K),
      c ^ 3 = 1 ∧
      (a.1 : K[X]) = X - C c ∧
      primaryMultiplicity
        ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (a.1 : K[X]) = 3 ∧
      (a.1 : K[X]).natDegree = 1 ∧
      dualPoly h.bar (a.1 : K[X]) = (a.1 : K[X]) ∧
      Module.finrank K (primaryComponent
        ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c)) = 3 ∧
      JP = ((specialBlock (idForm h 6) (t6psub_toLin B) (X - C c)).comap
        (t6psuh_toLinSU h 6)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) ∧
      3 ≤ 2 ^ f := by
  classical
  have h13 : (g₁ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₁ : GL (Fin 6) K) :=
    u6r_commute_of_normalizes_component hf (by norm_num) B g₁ hB3 h1B JP hJP hN1
  have h23 : (g₂ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) :=
    u6r_commute_of_normalizes_component hf (by norm_num) B g₂ hB3 h2B JP hJP hN2
  have hap : (B : GL (Fin 6) K) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) := by
    rw [map_one]
    exact hB3
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  obtain ⟨a, hJa⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.exists_good_block_of_component
      (h := h) (n := 6) (t6psuh_hq h) B rfl H JP hJP
  obtain ⟨c, hc3, hac⟩ := u6r_primaryFactor_eq B hB3 a.1.2
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc3
    norm_num at hc3
  have hdeg : (a.1 : K[X]).natDegree = 1 := by
    rw [hac, natDegree_X_sub_C]
  have hself : dualPoly h.bar (a.1 : K[X]) = (a.1 : K[X]) := by
    rw [hac]
    exact u6r_dualPoly h hf hc3
  let x : Module.End K (Fin 6 → K) :=
    ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K))
  let W : Submodule K (Fin 6 → K) := primaryComponent x (X - C c)
  have hW_eq : W = LinearMap.ker
      (Matrix.toLin' ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) -
        c • (LinearMap.id : (Fin 6 → K) →ₗ[K] (Fin 6 → K))) := by
    change primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (X - C c) = _
    ext v
    change v ∈ primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K
      (Fin 6 → K)) : Module.End K (Fin 6 → K)) (X - C c) ↔ _
    rw [u6r_mem_primaryComponent_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hWmem : ∀ v : Fin 6 → K,
      v ∈ W ↔ ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v = c • v := by
    intro v
    rw [hW_eq, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Matrix.toLin'_apply]
  have hW_ne_top : W ≠ ⊤ := by
    intro hWtop
    have hMv : ∀ v : Fin 6 → K,
        ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v = c • v := by
      intro v
      have hv : v ∈ W := by rw [hWtop]; trivial
      exact (hWmem v).1 hv
    have hMscalar : ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.scalar (Fin 6) c := eq_scalar_of_mulVec_eq_smul hMv
    refine hBns ⟨Units.mk0 c hc0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hMscalar
  have hfinW : Module.finrank K W =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.eigenDim
        ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c := by
    rw [hW_eq]
    rfl
  have hdiv : 3 ∣ Module.finrank K W := by
    rw [hfinW]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.three_dvd_eigenDim
      (g₁ : GL (Fin 6) K) (g₂ : GL (Fin 6) K) (B : GL (Fin 6) K)
      κ hκ3 hκ1 h12 h13 h23 c
  have hfinWlt : Module.finrank K W < 6 := by
    have h := Submodule.finrank_lt hW_ne_top
    simpa only [Module.finrank_fin_fun] using h
  have hfinmult : Module.finrank K W =
      (X - C c : K[X]).natDegree * primaryMultiplicity x (X - C c) := by
    haveI : Fact (Irreducible (X - C c : K[X])) := ⟨irreducible_X_sub_C c⟩
    exact finrank_primaryComponent x (X - C c)
  have hfinmult' : Module.finrank K W = primaryMultiplicity x (X - C c) := by
    rw [hfinmult, natDegree_X_sub_C, one_mul]
  have hge2 : 2 ≤ Module.finrank K W := by
    have h := a.2.1
    rw [hac] at h
    change 2 ≤ primaryMultiplicity x (X - C c) at h
    rwa [← hfinmult'] at h
  obtain ⟨k, hk⟩ := hdiv
  have hfinW3 : Module.finrank K W = 3 := by omega
  have hmult3 : primaryMultiplicity
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (a.1 : K[X]) = 3 := by
    rw [hac, ← hfinmult']
    exact hfinW3
  have hfinC : Module.finrank K (primaryComponent
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (X - C c)) = 3 := by
    change Module.finrank K W = 3
    exact hfinW3
  have hq3 : 3 ≤ 2 ^ f := by
    have h := (isGoodBlock_numeric (t6psuh_hq h) hself a.2).2 hmult3
    rwa [hdeg, mul_one] at h
  have hJP_eq : JP = (t6psub_block B a).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) := by
    rw [hJa]
    rfl
  have hJout : JP = ((specialBlock (idForm h 6) (t6psub_toLin B) (X - C c)).comap
      (t6psuh_toLinSU h 6)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) := by
    simpa only [t6psub_block, hac] using hJP_eq
  exact ⟨a, c, hc3, hac, hmult3, hdeg, hself, hfinC, hJout, hq3⟩

theorem u6r_natural_embedding_of_a2_block
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (B : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1)
    {a : t6psub_Idx h 6 B} {c : K}
    (hac : (a.1 : K[X]) = X - C c)
    (hself : dualPoly h.bar (a.1 : K[X]) = (a.1 : K[X]))
    (hm : primaryMultiplicity
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (a.1 : K[X]) = 3)
    (JP : Subgroup (primeFormP h (idGram K 6)))
    (hJ : JP = ((specialBlock (idForm h 6) (t6psub_toLin B) (X - C c)).comap
        (t6psuh_toLinSU h 6)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))) :
    ∃ (U : Matrix (Fin 6) (Fin 3) K) (L : Matrix (Fin 3) (Fin 6) K)
      (ε : Matrix (Fin 6) (Fin 6) K)
      (j : gramSU h (idGram K 3) →* gramSU h (idGram K 6)),
      Function.Injective j ∧
      L = Matrix.transpose (U.map h.bar) ∧
      L * U = 1 ∧
      U * L = ε ∧
      Matrix.transpose (ε.map h.bar) = ε ∧
      LinearMap.range U.mulVecLin =
        primaryComponent ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c) ∧
      ε.mulVecLin = primaryProjection
        ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (X - C c) ∧
      (∀ P : gramSU h (idGram K 3),
        (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)) ∧
      j.range = (specialBlock (idForm h 6) (t6psub_toLin B) (X - C c)).comap
        (t6psuh_toLinSU h 6) ∧
      j.range.map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) = JP := by
  classical
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hdeg : (a.1 : K[X]).natDegree = 1 := by rw [hac, natDegree_X_sub_C]
  have hap : (B : GL (Fin 6) K) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) := by
    rw [map_one]
    exact hB3
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (by norm_num) hap
  obtain ⟨hE, hbarE, hsmul, Hf, hHfsymm, hHfsep, htrace, ⟨e, he⟩, φ, hφ, hdet⟩ :=
    (selfDualPrimaryBlock H a.1 hself).unitaryForm
  let x : Module.End K (Fin 6 → K) :=
    ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K))
  let W : Submodule K (Fin 6 → K) := primaryComponent x (a.1 : K[X])
  let E := AdjoinRoot (a.1 : K[X])
  have hne : (a.1 : K[X]) ≠ 0 := (Fact.out : Irreducible (a.1 : K[X])).ne_zero
  have hfinE : Module.finrank K E = 1 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  haveI : Module.Free K E := Module.Free.of_basis (AdjoinRoot.powerBasis hne).basis
  let α : K ≃ₐ[K] E := AlgEquiv.ofBijective (Algebra.ofId K E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinE)
  have hbarα : ∀ k : K, hE.bar (α k) = α (h.bar k) := by
    intro k
    rw [hbarE, hdeg, pow_one, h.bar_apply, map_pow]
  let e3 : Module.Basis (Fin 3) E W := e.reindex (finCongr hm)
  have he3 : ∀ i j : Fin 3, Hf (e3 i) (e3 j) = if i = j then 1 else 0 := by
    intro i j
    have hi : e3 i = e (finCongr hm.symm i) := by simp [e3, Module.Basis.reindex_apply]
    have hj : e3 j = e (finCongr hm.symm j) := by simp [e3, Module.Basis.reindex_apply]
    rw [hi, hj, he]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne' : finCongr hm.symm i ≠ finCongr hm.symm j := fun h =>
        hij ((finCongr hm.symm).injective h)
      simp [hij, hne']
  have horth : ∀ i j : Fin 3,
      idForm h 6 ((e3 i : W) : Fin 6 → K) ((e3 j : W) : Fin 6 → K) =
        if i = j then 1 else 0 := by
    intro i j
    have ht := htrace (e3 i) (e3 j) (1 : E)
    simp only [one_mul, one_smul] at ht
    rw [← ht, he3 i j]
    have hite : (if i = j then (1 : E) else 0) =
        algebraMap K E (if i = j then (1 : K) else 0) := by
      split_ifs <;> simp
    rw [hite, Algebra.trace_algebraMap, hfinE, one_smul]
  let U : Matrix (Fin 6) (Fin 3) K := Matrix.of fun i j => ((e3 j : W) : Fin 6 → K) i
  let L : Matrix (Fin 3) (Fin 6) K := (U.map h.bar)ᵀ
  let ε : Matrix (Fin 6) (Fin 6) K := U * L
  have hidForm_eq : ∀ x y : Fin 6 → K,
      idForm h 6 x y = ∑ i, h.bar (x i) * y i := by
    intro x y
    rw [idForm, gramForm_apply]
    have h1 : (idGram K 6 : Matrix (Fin 6) (Fin 6) K) *ᵥ y = y := by
      simpa [idGram] using Matrix.one_mulVec y
    rw [h1]
    rfl
  have hidFormU : ∀ (j : Fin 3) (v : Fin 6 → K),
      idForm h 6 ((e3 j : W) : Fin 6 → K) v = ∑ i, h.bar (U i j) * v i := by
    intro j v
    rw [hidForm_eq]
    rfl
  have hLU : L * U = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : ∀ i, L j i = h.bar (U i j) := by intro i; simp [L]
    simp only [h1]
    rw [show ∑ i, h.bar (U i j) * U i k =
        idForm h 6 ((e3 j : W) : Fin 6 → K) ((e3 k : W) : Fin 6 → K) from by
      rw [hidForm_eq]; rfl, horth j k]
  have hLmul : ∀ v : Fin 6 → K, L.mulVecLin v = fun j => ∑ i, h.bar (U i j) * v i := by
    intro v
    ext j
    change (((U.map h.bar)ᵀ *ᵥ v) j) = ∑ i, h.bar (U i j) * v i
    rw [Matrix.mulVec_transpose]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hLzero : ∀ (b : K[X]) (hb : b ∈ primaryFactors x) (hbne : b ≠ (a.1 : K[X]))
      (v : Fin 6 → K) (hv : v ∈ primaryComponent x b), L.mulVecLin v = 0 := by
    intro b hb hbne v hv
    rw [hLmul]
    funext j
    have h0 : idForm h 6 ((e3 j : W) : Fin 6 → K) v = 0 := by
      refine orthogonal_of_ne_dualPoly (H := H) (x := t6psub_toLin B) (B := idForm h 6)
        a.1.2 hb ?_ (e3 j).2 hv
      rw [hself]
      exact hbne
    change ∑ i, h.bar (((e3 j : W) : Fin 6 → K) i) * v i = 0
    rw [← hidForm_eq ((e3 j : W) : Fin 6 → K) v, h0]
  have hαsymm : ∀ (c' : E) (w : W), (α.symm.toRingEquiv c') • w = c' • w := by
    intro c' w
    have hc : c' = algebraMap K E (α.symm c') := by
      have h : α (α.symm c') = algebraMap K E (α.symm c') := by
        simpa using α.commutes (α.symm c')
      rw [α.apply_symm_apply] at h
      exact h
    show (α.symm c') • w = c' • w
    have hαmap : algebraMap K E (α.symm c') = α (α.symm c') := by
      rw [α.apply_symm_apply]
      exact hc.symm
    rw [hc, IsScalarTower.algebraMap_smul, hαmap, α.symm_apply_apply]
  let e3K : Module.Basis (Fin 3) K W := e3.mapCoeffs α.symm.toRingEquiv hαsymm
  have he3K : ∀ j, e3K j = e3 j := fun j =>
    Module.Basis.mapCoeffs_apply e3 α.symm.toRingEquiv hαsymm j
  have hLsingle : ∀ k : Fin 3,
      L.mulVecLin ((e3 k : W) : Fin 6 → K) = Pi.single k 1 := by
    intro k
    rw [hLmul]
    funext j
    change ∑ i, h.bar (((e3 j : W) : Fin 6 → K) i) *
        (((e3 k : W) : Fin 6 → K) i) =
      (Pi.single k (1 : K) : Fin 3 → K) j
    rw [← hidForm_eq ((e3 j : W) : Fin 6 → K) ((e3 k : W) : Fin 6 → K), horth j k]
    simp [Pi.single_apply, eq_comm]
  have hUcol : ∀ k : Fin 3, U *ᵥ (Pi.single k (1 : K)) = ((e3 k : W) : Fin 6 → K) := by
    intro k
    rw [Matrix.mulVec_single_one]
    ext i
    rfl
  have h_on_basis : ∀ k : Fin 3,
      U.mulVecLin (L.mulVecLin ((e3 k : W) : Fin 6 → K)) = ((e3 k : W) : Fin 6 → K) := by
    intro k
    change U *ᵥ (L *ᵥ ((e3 k : W) : Fin 6 → K)) = ((e3 k : W) : Fin 6 → K)
    have hLk : L *ᵥ ((e3 k : W) : Fin 6 → K) = Pi.single k 1 := by
      have := hLsingle k
      rwa [Matrix.mulVecLin_apply] at this
    rw [hLk, hUcol k]
  have hULW : ∀ v : W,
      U.mulVecLin (L.mulVecLin (v : Fin 6 → K)) = (v : Fin 6 → K) := by
    intro v
    have hv : (v : Fin 6 → K) =
        ∑ j : Fin 3, e3K.repr v j • ((e3K j : W) : Fin 6 → K) := by
      have h := congrArg Subtype.val (e3K.sum_repr v).symm
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
    calc U.mulVecLin (L.mulVecLin (v : Fin 6 → K))
        = ∑ j : Fin 3, e3K.repr v j •
            U.mulVecLin (L.mulVecLin ((e3K j : W) : Fin 6 → K)) := by
          rw [hv]
          simp only [map_sum, map_smul]
      _ = ∑ j : Fin 3, e3K.repr v j • ((e3K j : W) : Fin 6 → K) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [he3K j, h_on_basis j]
      _ = (v : Fin 6 → K) := by simpa using hv.symm
  have hεproj : ε.mulVecLin = primaryProjection x (a.1 : K[X]) := by
    refine ext_primaryComponent H.squarefree (M := Fin 6 → K) fun b hb v hv => ?_
    by_cases hba : b = (a.1 : K[X])
    · subst hba
      have h1 : ε.mulVecLin v = U.mulVecLin (L.mulVecLin v) := by
        rw [show ε.mulVecLin = (U * L).mulVecLin from rfl, Matrix.mulVecLin_mul]
        rfl
      rw [h1, hULW ⟨v, hv⟩, primaryProjection_of_mem H.squarefree a.1.2 hv]
    · have hLv : L.mulVecLin v = 0 := hLzero b hb hba v hv
      have h1 : ε.mulVecLin v = 0 := by
        rw [show ε.mulVecLin = (U * L).mulVecLin from rfl, Matrix.mulVecLin_mul]
        simp [hLv]
      rw [h1, primaryProjection_of_mem_ne H.squarefree a.1.2 hb hba hv]
  have hεadj : Matrix.transpose (ε.map h.bar) = ε := by
    have hLmap : L.map h.bar = (U : Matrix (Fin 6) (Fin 3) K)ᵀ := by
      change (((U.map h.bar)ᵀ).map h.bar) = (U : Matrix (Fin 6) (Fin 3) K)ᵀ
      rw [Matrix.transpose_map]
      congr 1
      ext i j
      simp [h.bar_bar]
    calc Matrix.transpose (ε.map h.bar)
        = Matrix.transpose ((U * L).map h.bar) := rfl
      _ = Matrix.transpose ((U.map h.bar) * (L.map h.bar)) := by rw [Matrix.map_mul]
      _ = Matrix.transpose (L.map h.bar) * Matrix.transpose (U.map h.bar) := by
            rw [Matrix.transpose_mul]
      _ = ((U : Matrix (Fin 6) (Fin 3) K)ᵀ)ᵀ * (U.map h.bar)ᵀ := by rw [hLmap]
      _ = U * (U.map h.bar)ᵀ := by rw [Matrix.transpose_transpose]
      _ = ε := rfl
  have hεrange : LinearMap.range ε.mulVecLin = W := by
    rw [hεproj]
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact primaryProjection_mem H.squarefree a.1.2 w
    · intro hv
      exact ⟨v, primaryProjection_of_mem H.squarefree a.1.2 hv⟩
  have hrangeU : LinearMap.range U.mulVecLin = W := by
    have hle1 : LinearMap.range ε.mulVecLin ≤ LinearMap.range U.mulVecLin := by
      rw [show ε.mulVecLin = (U * L).mulVecLin from rfl, Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    have hle2 : LinearMap.range U.mulVecLin ≤ W := by
      rw [Matrix.range_mulVecLin]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      have hcol : U.col j = ((e3 j : W) : Fin 6 → K) := by
        ext i
        rfl
      rw [hcol]
      exact (e3 j).2
    exact le_antisymm hle2 (hεrange ▸ hle1)
  let T := Matrix.GeneralLinearGroup.toLin' e3
  let donorMap : GL (Fin 3) E →* LinearMap.GeneralLinearGroup K (Fin 6 → K) :=
    (l154BlockExt H.squarefree a.1).comp T.toMonoidHom
  let jGL : GL (Fin 3) K →* LinearMap.GeneralLinearGroup K (Fin 6 → K) :=
    donorMap.comp (Matrix.GeneralLinearGroup.map (α : K →+* E))
  have hmapinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin 3) (α : K →+* E)) := by
    intro x y hxy
    ext i j
    exact (α : K →+* E).injective (by
      simpa [Matrix.GeneralLinearGroup.map_apply] using
        congrArg (fun z : GL (Fin 3) E => ((z : Matrix (Fin 3) (Fin 3) E) i j)) hxy)
  have hjGLinj : Function.Injective jGL :=
    (l154BlockExt_injective H.squarefree a.1).comp (T.injective.comp hmapinj)
  have hformula : ∀ P : GL (Fin 3) K,
      (jGL P : Module.End K (Fin 6 → K)) =
        (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin := by
    intro P
    refine ext_primaryComponent H.squarefree (M := Fin 6 → K) fun b hb v hv => ?_
    by_cases hba : b = (a.1 : K[X])
    · subst hba
      have hLHS : ∀ k : Fin 3,
          (jGL P : Module.End K (Fin 6 → K)) ((e3 k : W) : Fin 6 → K) =
          ∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) K) i k • ((e3 i : W) : Fin 6 → K) := by
        intro k
        rw [show jGL P =
            l154BlockExt H.squarefree a.1
              (T (Matrix.GeneralLinearGroup.map (α : K →+* E) P)) from rfl]
        rw [l154BlockExt_apply_self H.squarefree a.1 _ _ (e3 k).2]
        change ((T (Matrix.GeneralLinearGroup.map (α : K →+* E) P) : Module.End E W)
            ⟨(e3 k : W), (e3 k).2⟩ : Fin 6 → K) = _
        have hTk : ((T (Matrix.GeneralLinearGroup.map (α : K →+* E) P) : Module.End E W)
            (e3 k) : W) = ∑ i, (P : Matrix (Fin 3) (Fin 3) K) i k • e3 i := by
          dsimp only [T]
          rw [u6r_toLin'_apply_basis e3
            (Matrix.GeneralLinearGroup.map (α : K →+* E) P) k]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (Matrix.GeneralLinearGroup.map (α : K →+* E) P :
                Matrix (Fin 3) (Fin 3) E) i k = α ((P : Matrix (Fin 3) (Fin 3) K) i k) from by
            simp [Matrix.GeneralLinearGroup.map_apply]]
          exact u6r_algEquiv_smul α ((P : Matrix (Fin 3) (Fin 3) K) i k) (e3 i)
        have hTkV := congrArg Subtype.val hTk
        simpa using hTkV
      have hRHS : ∀ k : Fin 3,
          (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin
            ((e3 k : W) : Fin 6 → K) =
          ∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) K) i k • ((e3 i : W) : Fin 6 → K) := by
        intro k
        have hεk : ε.mulVecLin ((e3 k : W) : Fin 6 → K) = ((e3 k : W) : Fin 6 → K) := by
          rw [hεproj]
          exact primaryProjection_of_mem H.squarefree a.1.2 (e3 k).2
        have hUcolsum : U *ᵥ ((P : Matrix (Fin 3) (Fin 3) K).col k) =
            ∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) K) i k • ((e3 i : W) : Fin 6 → K) := by
          ext i
          simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, U, Matrix.of_apply,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        calc (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin
              ((e3 k : W) : Fin 6 → K)
            = (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)) *ᵥ
                ((e3 k : W) : Fin 6 → K) := rfl
          _ = (U * (P : Matrix (Fin 3) (Fin 3) K) * L) *ᵥ ((e3 k : W) : Fin 6 → K) +
                (1 - ε) *ᵥ ((e3 k : W) : Fin 6 → K) := by
              rw [Matrix.add_mulVec]
          _ = U *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ (L *ᵥ ((e3 k : W) : Fin 6 → K))) +
                (1 *ᵥ ((e3 k : W) : Fin 6 → K) - ε *ᵥ ((e3 k : W) : Fin 6 → K)) := by
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.sub_mulVec]
          _ = U *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single k 1) +
                (((e3 k : W) : Fin 6 → K) - ε *ᵥ ((e3 k : W) : Fin 6 → K)) := by
              have hLk : L *ᵥ ((e3 k : W) : Fin 6 → K) = Pi.single k 1 := by
                have := hLsingle k
                rwa [Matrix.mulVecLin_apply] at this
              rw [hLk, Matrix.one_mulVec]
          _ = U *ᵥ ((P : Matrix (Fin 3) (Fin 3) K).col k) +
                (((e3 k : W) : Fin 6 → K) - ((e3 k : W) : Fin 6 → K)) := by
              have hεkv : ε *ᵥ ((e3 k : W) : Fin 6 → K) = ((e3 k : W) : Fin 6 → K) := by
                have := hεk
                rwa [Matrix.mulVecLin_apply] at this
              rw [Matrix.mulVec_single_one, hεkv]
          _ = ∑ i : Fin 3, (P : Matrix (Fin 3) (Fin 3) K) i k • ((e3 i : W) : Fin 6 → K) := by
              rw [hUcolsum, sub_self, add_zero]
      have hvsum : (v : Fin 6 → K) =
          ∑ k : Fin 3, e3K.repr ⟨v, hv⟩ k • ((e3 k : W) : Fin 6 → K) := by
        have h := congrArg (fun w : W => (w : Fin 6 → K)) (e3K.sum_repr ⟨v, hv⟩)
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        simpa only [he3K] using h.symm
      have hjsum : (jGL P : Module.End K (Fin 6 → K)) v =
          ∑ k : Fin 3, e3K.repr ⟨v, hv⟩ k •
            (jGL P : Module.End K (Fin 6 → K)) ((e3 k : W) : Fin 6 → K) := by
        conv_lhs => rw [hvsum]
        simp only [map_sum, map_smul]
      have hMsum : (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin v =
          ∑ k : Fin 3, e3K.repr ⟨v, hv⟩ k •
            (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin
              ((e3 k : W) : Fin 6 → K) := by
        conv_lhs => rw [hvsum]
        simp only [map_sum, map_smul]
      calc (jGL P : Module.End K (Fin 6 → K)) v
          = ∑ k : Fin 3, e3K.repr ⟨v, hv⟩ k •
              (jGL P : Module.End K (Fin 6 → K)) ((e3 k : W) : Fin 6 → K) := hjsum
        _ = ∑ k : Fin 3, e3K.repr ⟨v, hv⟩ k •
              (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin
                ((e3 k : W) : Fin 6 → K) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hLHS k, hRHS k]
        _ = (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin v := hMsum.symm
      rfl
    · have hne : (⟨b, hb⟩ : primaryFactors x) ≠ a.1 := fun h => hba (congrArg Subtype.val h)
      have hLHS : (jGL P : Module.End K (Fin 6 → K)) v = v := by
        rw [show jGL P =
            l154BlockExt H.squarefree a.1
              (T (Matrix.GeneralLinearGroup.map (α : K →+* E) P)) from rfl]
        exact l154BlockExt_apply_ne H.squarefree a.1 _ ⟨b, hb⟩ hne v hv
      have hRHS : (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin v = v := by
        have hLv : L.mulVecLin v = 0 := hLzero b hb hba v hv
        have hεv : ε.mulVecLin v = 0 := by
          rw [hεproj, primaryProjection_of_mem_ne H.squarefree a.1.2 hb hba hv]
        have hLv' : L *ᵥ v = 0 := by
          rwa [Matrix.mulVecLin_apply] at hLv
        have hεv' : ε *ᵥ v = 0 := by
          have := hεv
          rwa [Matrix.mulVecLin_apply] at this
        have h1 : (U * (P : Matrix (Fin 3) (Fin 3) K) * L) *ᵥ v = 0 := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hLv']
          simp
        have h2 : (1 - ε) *ᵥ v = v := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hεv', sub_zero]
        calc (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)).mulVecLin v
            = (U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)) *ᵥ v := rfl
          _ = (U * (P : Matrix (Fin 3) (Fin 3) K) * L) *ᵥ v + (1 - ε) *ᵥ v := by
              rw [Matrix.add_mulVec]
          _ = v := by rw [h1, h2, zero_add]
      rw [hLHS, hRHS]
  have hmatGL : ∀ P : GL (Fin 3) K,
      ((Matrix.GeneralLinearGroup.toLin.symm (jGL P) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
        U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε) := by
    intro P
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
    rw [show Matrix.mulVecLin (((Matrix.GeneralLinearGroup.toLin.symm (jGL P) :
            GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
          Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm (jGL P)) from
        (Matrix.GeneralLinearGroup.coe_toLin _).symm,
      MulEquiv.apply_symm_apply, hformula P]
  have hfield : gramSU hE (idGram E 3) =
      (gramSU h (idGram K 3)).map (Matrix.GeneralLinearGroup.map (α : K →+* E)) := by
    ext Q
    constructor
    · intro hQ
      let M : GL (Fin 3) K := Matrix.GeneralLinearGroup.map (α.symm : E ≃+* K) Q
      have hmapQM : Matrix.GeneralLinearGroup.map (α : K ≃+* E) M = Q := by
        ext i j
        simp [M, Matrix.GeneralLinearGroup.map_apply]
      have hM : M ∈ gramSU h (idGram K 3) :=
        (u6r_mem_gramSU_map_iff (h := h) (hE := hE) (α := (α : K ≃+* E)) hbarα M).mp
          (by rwa [hmapQM])
      exact ⟨M, hM, hmapQM⟩
    · rintro ⟨M, hM, rfl⟩
      exact (u6r_mem_gramSU_map_iff (h := h) (hE := hE) (α := (α : K ≃+* E)) hbarα M).mpr hM
  have hdonor : specialBlock (idForm h 6) (t6psub_toLin B) (a.1 : K[X]) =
      (gramSU hE (idGram E 3)).map donorMap := by
    have h := CFSG.LocalAnalysis.GLTheoremA.K155X.specialBlock_eq_map_l154BlockExt
      (hK := h) (B := idForm h 6) (x := t6psub_toLin B)
      H.squarefree a.1 hself e3 he3 φ hφ
    rw [h]
    rw [CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU hE]
  have hImg : specialBlock (idForm h 6) (t6psub_toLin B) (a.1 : K[X]) =
      (gramSU h (idGram K 3)).map jGL := by
    rw [hdonor, hfield, Subgroup.map_map]
  have hmem : ∀ P ∈ gramSU h (idGram K 3),
      Matrix.GeneralLinearGroup.toLin.symm (jGL P) ∈ gramSU h (idGram K 6) := by
    intro P hP
    have hsp : jGL P ∈ specialBlock (idForm h 6) (t6psub_toLin B) (a.1 : K[X]) := by
      rw [hImg]
      exact ⟨P, hP, rfl⟩
    have hu : jGL P ∈ sesqUnitaryGroup (idForm h 6) :=
      (Subgroup.mem_inf.mp (specialBlock_le_unitaryCentralizer hsp)).1
    have hdetP : (P : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_gramSU.mp hP).2
    have hdetM : ((Matrix.GeneralLinearGroup.toLin.symm (jGL P) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [hmatGL P]
      have hM : U * (P : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε) =
          1 + U * ((P : Matrix (Fin 3) (Fin 3) K) - 1) * L := by
        rw [show ε = U * L from rfl]
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        abel
      rw [hM, Matrix.det_one_add_mul_comm (U * ((P : Matrix (Fin 3) (Fin 3) K) - 1)) L,
        ← Matrix.mul_assoc, hLU, Matrix.one_mul]
      have hPsub : (1 : Matrix (Fin 3) (Fin 3) K) +
          ((P : Matrix (Fin 3) (Fin 3) K) - 1) = (P : Matrix (Fin 3) (Fin 3) K) := by
        abel
      rw [hPsub, hdetP]
    rw [mem_gramSU_iff_isometry]
    refine ⟨?_, hdetM⟩
    intro x y
    have hxy := hu x y
    change idForm h 6
        (((Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.toLin.symm (jGL P)) :
            LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) x)
        (((Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.toLin.symm (jGL P)) :
            LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) y) =
      idForm h 6 x y
    rw [MulEquiv.apply_symm_apply]
    exact hxy
  let j : gramSU h (idGram K 3) →* gramSU h (idGram K 6) :=
    { toFun := fun P => ⟨Matrix.GeneralLinearGroup.toLin.symm (jGL (P : GL (Fin 3) K)),
        hmem (P : GL (Fin 3) K) P.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro P Q
        apply Subtype.ext
        simp }
  have hj : Function.Injective j := by
    intro P Q hPQ
    have hgl : (j P : GL (Fin 6) K) = (j Q : GL (Fin 6) K) := congrArg Subtype.val hPQ
    have hlm := congrArg (Matrix.GeneralLinearGroup.toLin) hgl
    have : jGL (P : GL (Fin 3) K) = jGL (Q : GL (Fin 3) K) := by
      simpa [j, MulEquiv.apply_symm_apply] using hlm
    exact Subtype.ext (hjGLinj this)
  have hjformula : ∀ P : gramSU h (idGram K 3),
      (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε) := by
    intro P
    exact hmatGL (P : GL (Fin 3) K)
  have htoLinj : ∀ P : gramSU h (idGram K 3),
      t6psuh_toLinSU h 6 (j P) = jGL (P : GL (Fin 3) K) := by
    intro P
    simpa [j, t6psuh_toLinSU, MulEquiv.apply_symm_apply]
  have hrangej : j.range = (specialBlock (idForm h 6) (t6psub_toLin B) (a.1 : K[X])).comap
      (t6psuh_toLinSU h 6) := by
    ext g
    constructor
    · rintro ⟨P, rfl⟩
      rw [Subgroup.mem_comap, htoLinj P, hImg]
      exact ⟨P, P.2, rfl⟩
    · intro hg
      rw [Subgroup.mem_comap, hImg] at hg
      obtain ⟨P, hP, hPj⟩ := hg
      refine ⟨⟨P, hP⟩, ?_⟩
      apply t6psuh_toLinSU_injective
      rw [htoLinj ⟨P, hP⟩]
      exact hPj
  have hJa : JP = ((specialBlock (idForm h 6) (t6psub_toLin B) (a.1 : K[X])).comap
      (t6psuh_toLinSU h 6)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) := by
    simpa only [← hac] using hJ
  have hjmap : j.range.map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) = JP := by
    rw [hrangej, ← hJa]
  refine ⟨U, L, ε, j, hj, rfl, hLU, rfl, hεadj, ?_, ?_, hjformula, ?_, hjmap⟩
  · simpa only [← hac] using hrangeU
  · simpa only [← hac] using hεproj
  · simpa only [← hac] using hrangej


section Position

theorem u6r_specialUnitary_position_of_natural_embedding
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (B : primeFormUnitary h (idGram K 6)) (c d : K)
    (U : Matrix (Fin 6) (Fin 3) K) (L : Matrix (Fin 3) (Fin 6) K)
    (ε : Matrix (Fin 6) (Fin 6) K)
    (j : gramSU h (idGram K 3) →* gramSU h (idGram K 6))
    (hL : L = Matrix.transpose (U.map h.bar))
    (hLU : L * U = 1)
    (hUL : U * L = ε)
    (hformula : ∀ P : gramSU h (idGram K 3),
      (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
        U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε))
    (hBdec : ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      c • ε + d • (1 - ε)) :
    ∃ T : gramSU h (idGram K 6), ∃ V : Matrix (Fin 6) (Fin 3) K,
      (∀ i k, (((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) i ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k)) = U i k) ∧
      (∀ i k, (((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) i ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k)) = V i k) ∧
      Matrix.transpose (V.map h.bar) * V = 1 ∧
      Matrix.transpose (U.map h.bar) * V = 0 ∧
      ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) =
        Matrix.diagonal ![c, c, c, d, d, d] ∧
      ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * ε *
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) =
        Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
          (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K)) ∧
      ∀ P : gramSU h (idGram K 3),
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ :
            GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) *
          ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K)) =
          Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
            (Matrix.fromBlocks (((P : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)) (0 : Matrix (Fin 3) (Fin 3) K)
              (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  have hUorth : Matrix.transpose (U.map h.bar) * U = 1 := by
    rw [← hL, hLU]
  obtain ⟨T0, hTU0⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo.exists_gramSU_with_columns
      h (by norm_num : 0 < 3) U hUorth
  let T : gramSU h (idGram K 6) := T0
  have hTU : ((T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).submatrix id (Fin.castAdd 3) = U := by
    simpa [T] using hTU0
  let Tm : Matrix (Fin 6) (Fin 6) K := ((T : gramSU h (idGram K 6)) : GL (Fin 6) K)
  let Tadj : Matrix (Fin 6) (Fin 6) K := Matrix.transpose (Tm.map h.bar)
  have hTU' : ∀ i k, Tm i ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k)) = U i k := by
    intro i k
    have h := congrFun (congrFun hTU i) k
    rw [finSumFinEquiv_apply_left]
    simpa [Tm, Matrix.submatrix_apply] using h
  let V : Matrix (Fin 6) (Fin 3) K := Matrix.of fun i k => Tm i ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k))
  have hTV : ∀ i k, Tm i ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k)) = V i k := fun i k => rfl
  have hTunit : Tadj * Tm = 1 := by
    have h := (mem_gramSU.mp T.2).1
    simpa [Tadj, Tm, idGram] using h
  have hTmTadj : Tm * Tadj = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := Tadj) (B := Tm) (Equiv.refl _)).mp hTunit
  have hTinv : ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Tadj := by
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_eq_right_inv hTmTadj]
  have hUV : Matrix.transpose (U.map h.bar) * V = 0 := by
    ext k l
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) K =>
      M ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k)) ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr l))) hTunit
    simp only [Tadj, Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, hTU', hTV] at h
    simpa [Tadj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hTU', hTV] using h
  have hVV : Matrix.transpose (V.map h.bar) * V = 1 := by
    ext k l
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) K =>
      M ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k)) ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr l))) hTunit
    simp only [Tadj, Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, hTV] at h
    simpa [Tadj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hTV,
      Matrix.one_apply] using h
  let BL : Matrix (Fin 6) (Fin 3) K := Matrix.of fun i k =>
    if i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k) then 1 else 0
  let BR : Matrix (Fin 6) (Fin 3) K := Matrix.of fun i k =>
    if i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k) then 1 else 0
  let C : Matrix (Fin 3) (Fin 6) K := Matrix.of fun k j =>
    if j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k) then 1 else 0
  let blockMat : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 3) (Fin 3) K →
      Matrix (Fin 6) (Fin 6) K := fun A B =>
    Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (Matrix.fromBlocks A (0 : Matrix (Fin 3) (Fin 3) K)
        (0 : Matrix (Fin 3) (Fin 3) K) B)
  have hblock_add : ∀ A B A' B' : Matrix (Fin 3) (Fin 3) K,
      blockMat A B + blockMat A' B' = blockMat (A + A') (B + B') := by
    intro A B A' B'
    change (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)) (Matrix.fromBlocks A 0 0 B) +
      (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)) (Matrix.fromBlocks A' 0 0 B') =
      (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)) (Matrix.fromBlocks (A + A') 0 0 (B + B'))
    rw [← (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)).map_add, Matrix.fromBlocks_add]
    simp
  have hblock_smul : ∀ (a : K) (A B : Matrix (Fin 3) (Fin 3) K),
      a • blockMat A B = blockMat (a • A) (a • B) := by
    intro a A B
    change a • (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)) (Matrix.fromBlocks A 0 0 B) =
      (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)) (Matrix.fromBlocks (a • A) 0 0 (a • B))
    rw [← (Matrix.reindexLinearEquiv K K (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)).map_smul, Matrix.fromBlocks_smul]
    simp
  have hblock_one : blockMat (1 : Matrix (Fin 3) (Fin 3) K)
      (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
    change Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) K) 0 0
        (1 : Matrix (Fin 3) (Fin 3) K)) = 1
    rw [Matrix.fromBlocks_one]
    change (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K).submatrix
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm = 1
    exact Matrix.submatrix_one (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm.injective
  have hTmBL : Tm * BL = U := by
    ext i k
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k))]
    · simp [BL, hTU']
    · intro j _ hj
      simp [BL, hj]
    · intro h
      simp at h
  have hTmBR : Tm * BR = V := by
    ext i k
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k))]
    · simp [BR, hTV]
    · intro j _ hj
      simp [BR, hj]
    · intro h
      simp at h
  have hTadjU : Tadj * U = BL := by
    calc Tadj * U = Tadj * (Tm * BL) := by rw [hTmBL]
      _ = (Tadj * Tm) * BL := by rw [Matrix.mul_assoc]
      _ = BL := by rw [hTunit, Matrix.one_mul]
  have hTadjV : Tadj * V = BR := by
    calc Tadj * V = Tadj * (Tm * BR) := by rw [hTmBR]
      _ = (Tadj * Tm) * BR := by rw [Matrix.mul_assoc]
      _ = BR := by rw [hTunit, Matrix.one_mul]
  have hLTm : L * Tm = C := by
    ext k j
    rcases hj : ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm j) with l | l
    · have hjl : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl l) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hjl, Matrix.mul_apply]
      simp only [hTU']
      rw [← Matrix.mul_apply, hLU, Matrix.one_apply]
      simp [C, hjl, eq_comm]
    · have hjl : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr l) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hjl, Matrix.mul_apply]
      simp only [hTV]
      rw [← Matrix.mul_apply, hL, hUV]
      simp [C, hjl]
  have hBLPC : ∀ P : Matrix (Fin 3) (Fin 3) K, BL * P * C = blockMat P 0 := by
    intro P
    ext i j
    rcases hi : ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm i) with a | a <;>
      rcases hj : ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm j) with b | b
    · have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl a) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) i]
        rw [hi]
      have hjb : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl b) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hia, hjb]
      simp [BL, C, blockMat, Matrix.reindex_apply, Matrix.mul_apply,
        Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
    · have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl a) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) i]
        rw [hi]
      have hjb : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr b) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hia, hjb]
      simp [BL, C, blockMat, Matrix.reindex_apply, Matrix.mul_apply,
        Finset.sum_ite_eq', Finset.mem_univ]
    · have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr a) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) i]
        rw [hi]
      have hjb : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl b) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hia, hjb]
      simp [BL, C, blockMat, Matrix.reindex_apply, Matrix.mul_apply,
        Finset.sum_ite_eq', Finset.mem_univ]
    · have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr a) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) i]
        rw [hi]
      have hjb : j = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr b) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) j]
        rw [hj]
      rw [hia, hjb]
      simp [BL, C, blockMat, Matrix.reindex_apply, Matrix.mul_apply,
        Finset.sum_ite_eq', Finset.mem_univ]
  have hBLC : BL * C = blockMat 1 0 := by
    simpa using hBLPC 1
  have hsplit : blockMat (1 : Matrix (Fin 3) (Fin 3) K) 0 +
      blockMat 0 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hblock_add]
    simpa using hblock_one
  have hdiagFun : (Sum.elim (fun _ : Fin 3 => c) (fun _ : Fin 3 => d)) ∘
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm =
      (fun i : Fin 6 => if i.val < 3 then c else d) := by
    funext i
    rcases hi : (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).symm i with a | a
    · rw [Function.comp_apply, hi]
      have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl a) := by
        rw [← hi, Equiv.apply_symm_apply]
      rw [hia, finSumFinEquiv_apply_left, Fin.val_castAdd, if_pos a.isLt]
      rfl
    · rw [Function.comp_apply, hi]
      have hia : i = (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr a) := by
        rw [← hi, Equiv.apply_symm_apply]
      rw [hia, finSumFinEquiv_apply_right, Fin.val_natAdd, if_neg (by omega)]
      rfl
  have hvec : ![c, c, c, d, d, d] =
      (fun i : Fin 6 => if i.val < 3 then c else d) := by
    funext i
    fin_cases i <;> rfl
  have hdiag : blockMat (c • (1 : Matrix (Fin 3) (Fin 3) K))
      (d • (1 : Matrix (Fin 3) (Fin 3) K)) = Matrix.diagonal ![c, c, c, d, d, d] := by
    change Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
        (Matrix.fromBlocks (c • (1 : Matrix (Fin 3) (Fin 3) K))
          (0 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K)
          (d • (1 : Matrix (Fin 3) (Fin 3) K))) =
      Matrix.diagonal ![c, c, c, d, d, d]
    have hfrom : Matrix.fromBlocks (c • (1 : Matrix (Fin 3) (Fin 3) K))
        (0 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K)
        (d • (1 : Matrix (Fin 3) (Fin 3) K)) =
        Matrix.diagonal (Sum.elim (fun _ : Fin 3 => c) (fun _ : Fin 3 => d)) := by
      ext i j
      rcases i with a | a <;> rcases j with b | b <;>
        simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [hfrom, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv, hdiagFun, ← hvec]
  have hεU : ε * U = U := by
    calc ε * U = (U * L) * U := by rw [hUL]
      _ = U * (L * U) := by rw [Matrix.mul_assoc]
      _ = U := by rw [hLU, Matrix.mul_one]
  have hεV : ε * V = 0 := by
    calc ε * V = (U * L) * V := by rw [hUL]
      _ = U * (L * V) := by rw [Matrix.mul_assoc]
      _ = U * (Matrix.transpose (U.map h.bar) * V) := by rw [hL]
      _ = 0 := by rw [hUV, Matrix.mul_zero]
  have hTmεTm : Tadj * ε * Tm = blockMat 1 0 := by
    calc Tadj * ε * Tm = Tadj * (ε * Tm) := by rw [Matrix.mul_assoc]
      _ = (Tadj * U) * (L * Tm) := by
          rw [← hUL]
          simp only [Matrix.mul_assoc]
      _ = (Tadj * (Tm * BL)) * (L * Tm) := by rw [hTmBL]
      _ = (Tadj * Tm) * BL * (L * Tm) := by
          congr 1
          rw [Matrix.mul_assoc]
      _ = BL * (L * Tm) := by rw [hTunit, Matrix.one_mul]
      _ = BL * C := by rw [hLTm]
      _ = blockMat 1 0 := hBLC
  have hsub : (1 : Matrix (Fin 6) (Fin 6) K) - blockMat 1 0 = blockMat 0 1 := by
    rw [sub_eq_iff_eq_add, add_comm, hsplit]
  have hTm1mεTm : Tadj * (1 - ε) * Tm = blockMat 0 1 := by
    calc Tadj * (1 - ε) * Tm = (Tadj * (1 - ε)) * Tm := rfl
      _ = (Tadj * 1 - Tadj * ε) * Tm := by rw [Matrix.mul_sub]
      _ = (Tadj - Tadj * ε) * Tm := by rw [Matrix.mul_one]
      _ = Tadj * Tm - (Tadj * ε) * Tm := by rw [Matrix.sub_mul]
      _ = 1 - Tadj * ε * Tm := by rw [hTunit, Matrix.mul_assoc]
      _ = 1 - blockMat 1 0 := by rw [hTmεTm]
      _ = blockMat 0 1 := hsub
  have hTmBdec : Tadj * (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * Tm =
      blockMat (c • (1 : Matrix (Fin 3) (Fin 3) K))
        (d • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    calc Tadj * (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * Tm
        = Tadj * (c • ε + d • (1 - ε)) * Tm := by rw [hBdec]
      _ = c • (Tadj * ε * Tm) + d • (Tadj * (1 - ε) * Tm) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
      _ = c • blockMat 1 0 + d • blockMat 0 1 := by
          rw [hTmεTm, hTm1mεTm]
      _ = blockMat (c • 1) (d • 1) := by
          rw [hblock_smul, hblock_smul, hblock_add]
          congr 1 <;> simp
  have hTmj : ∀ P : gramSU h (idGram K 3),
      Tadj * (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * Tm =
        blockMat ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 := by
    intro P
    calc Tadj * (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) * Tm
        = Tadj * (U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L +
            (1 - ε)) * Tm := by rw [hformula P]
      _ = blockMat ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 := by
          calc Tadj * (U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L +
                (1 - ε)) * Tm
              = (Tadj * U) * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (L * Tm) +
                  Tadj * (1 - ε) * Tm := by
                simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
            _ = BL * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C +
                  blockMat 0 1 := by rw [hTadjU, hLTm, hTm1mεTm]
            _ = blockMat ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 +
                  blockMat 0 1 := by rw [hBLPC]
            _ = blockMat ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 := by
                rw [hblock_add]
                simp
  refine ⟨T, V, hTU', hTV, hVV, hUV, ?_, ?_, ?_⟩
  · simpa [hTinv, Tm] using hTmBdec.trans hdiag
  · simpa [hTinv, Tm, blockMat] using hTmεTm
  · intro P
    simpa [hTinv, Tm, blockMat] using hTmj P

  noncomputable local instance decEqU6rPosition : DecidableEq K := Classical.decEq K

theorem u6r_three_plus_three_of_normalizes_component
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (hf : Odd f)
    (B g₁ g₂ : primeFormUnitary h (idGram K 6))
    (hB3 : (B : GL (Fin 6) K) ^ 3 = 1)
    (hBns : ¬ ∃ c : Kˣ,
      (B : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (JP : Subgroup (primeFormP h (idGram K 6)))
    (hJP : CFSG.Open.IsComponentOf JP
      (fixSubgroup (primeFormConjHom h (idGram K 6) B)))
    (κ : Kˣ) (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (h12 : (g₁ : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) *
        (g₁ : GL (Fin 6) K)⁻¹ * (g₂ : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (h1B : primeFormConjHom h (idGram K 6) g₁ *
        primeFormConjHom h (idGram K 6) B =
      primeFormConjHom h (idGram K 6) B *
        primeFormConjHom h (idGram K 6) g₁)
    (h2B : primeFormConjHom h (idGram K 6) g₂ *
        primeFormConjHom h (idGram K 6) B =
      primeFormConjHom h (idGram K 6) B *
        primeFormConjHom h (idGram K 6) g₂)
    (hN1 : ∀ z ∈ JP, primeFormConjHom h (idGram K 6) g₁ z ∈ JP)
    (hN2 : ∀ z ∈ JP, primeFormConjHom h (idGram K 6) g₂ z ∈ JP) :
    ∃ (a : t6psub_Idx h 6 B) (c d : K)
      (U : Matrix (Fin 6) (Fin 3) K) (L : Matrix (Fin 3) (Fin 6) K)
      (ε : Matrix (Fin 6) (Fin 6) K)
      (j : gramSU h (idGram K 3) →* gramSU h (idGram K 6))
      (T : gramSU h (idGram K 6)) (V : Matrix (Fin 6) (Fin 3) K),
      (a.1 : K[X]) = X - C c ∧
      c ^ 3 = 1 ∧
      primaryMultiplicity
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (a.1 : K[X]) = 3 ∧
      (a.1 : K[X]).natDegree = 1 ∧
      dualPoly h.bar (a.1 : K[X]) = (a.1 : K[X]) ∧
      d ^ 3 = 1 ∧ d ≠ c ∧
      primaryFactors
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) = {X - C c, X - C d} ∧
      Module.finrank K (primaryComponent
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C c)) = 3 ∧
      Module.finrank K (primaryComponent
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C d)) = 3 ∧
      IsCompl
        (primaryComponent
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C c))
        (primaryComponent
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C d)) ∧
      (∀ v ∈ primaryComponent
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C c),
        ∀ w ∈ primaryComponent
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C d),
        idForm h 6 v w = 0) ∧
      primaryProjection
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C c) +
      primaryProjection
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C d) = 1 ∧
      (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) =
        c • primaryProjection
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C c) +
        d • primaryProjection
          (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
            Module.End K (Fin 6 → K))) (X - C d) ∧
      Function.Injective j ∧
      L = Matrix.transpose (U.map h.bar) ∧
      L * U = 1 ∧
      U * L = ε ∧
      Matrix.transpose (ε.map h.bar) = ε ∧
      LinearMap.range U.mulVecLin = primaryComponent
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C c) ∧
      ε.mulVecLin = primaryProjection
        (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K))) (X - C c) ∧
      (∀ P : gramSU h (idGram K 3),
        (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) =
          U * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * L + (1 - ε)) ∧
      j.range = (specialBlock (idForm h 6) (t6psub_toLin B) (X - C c)).comap
        (t6psuh_toLinSU h 6) ∧
      j.range.map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)) = JP ∧
      (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c • ε + d • (1 - ε)) ∧
      (∀ i k, (((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) i
          ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k)) = U i k) ∧
      (∀ i k, (((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) i
          ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k)) = V i k) ∧
      Matrix.transpose (V.map h.bar) * V = 1 ∧
      Matrix.transpose (U.map h.bar) * V = 0 ∧
      ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *
        (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) =
        Matrix.diagonal ![c, c, c, d, d, d] ∧
      ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) * ε *
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) =
        Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
          (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
          (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K)
            (0 : Matrix (Fin 3) (Fin 3) K) (0 : Matrix (Fin 3) (Fin 3) K)) ∧
      (∀ P : gramSU h (idGram K 3),
        ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) *
          (((j P : gramSU h (idGram K 6)) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) *
          ((((T : gramSU h (idGram K 6)) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K)) =
          Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
            (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
            (Matrix.fromBlocks (((P : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)) (0 : Matrix (Fin 3) (Fin 3) K)
              (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K))) ∧
      3 ≤ 2 ^ f := by
  classical
  obtain ⟨a, c, hc3, hac, hmult3, hdeg, hself, hfinC, hJPout, hq3⟩ :=
    u6r_a2_block_of_normalizes_component hf B g₁ g₂ hB3 hBns JP hJP κ hκ3 hκ1 h12 h1B h2B hN1 hN2
  have h13 : (g₁ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₁ : GL (Fin 6) K) :=
    u6r_commute_of_normalizes_component hf (by norm_num : 3 ≤ 6) B g₁ hB3 h1B JP hJP hN1
  have h23 : (g₂ : GL (Fin 6) K) * (B : GL (Fin 6) K) =
      (B : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) :=
    u6r_commute_of_normalizes_component hf (by norm_num : 3 ≤ 6) B g₂ hB3 h2B JP hJP hN2
  obtain ⟨d, hd3, hdne, hF, hfinD, hcompl, horth, _, _, hproj, hop⟩ :=
    u6r_complement_of_cubic_scalar_commutator hf B g₁ g₂ hB3 κ hκ3 hκ1 h12 h13 h23
      c hc3 hfinC
  obtain ⟨U, L, ε, j, hj, hL, hLU, hUL, hεadj, hrangeU, hεproj, hformula, hrangej, hjmap⟩ :=
    u6r_natural_embedding_of_a2_block B hB3 hac hself hmult3 JP hJPout
  have hxLin : (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K))) =
      Matrix.toLin' (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
    change (Matrix.GeneralLinearGroup.toLin (B : GL (Fin 6) K) :
        (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Matrix.toLin' (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']
  have hπd : primaryProjection
      (((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K))) (X - C d) = 1 - ε.mulVecLin := by
    rw [eq_sub_iff_add_eq, hεproj, add_comm, hproj]
  have hεLin : Matrix.toLin' ε = ε.mulVecLin := Matrix.toLin'_apply' ε
  have hBdec : (((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      c • ε + d • (1 - ε) := by
    apply Matrix.toLin'.injective
    rw [map_add, map_smul, map_smul, map_sub, Matrix.toLin'_one, hεLin, ← hxLin]
    rw [hop, hπd, hεproj]
    rfl
  obtain ⟨T, V, hTU, hTV, hVV, hUV, hBconj, hεconj, hjconj⟩ :=
    u6r_specialUnitary_position_of_natural_embedding B c d U L ε j
      hL hLU hUL hformula hBdec
  exact ⟨a, c, d, U, L, ε, j, T, V, hac, hc3, hmult3, hdeg, hself,
    hd3, hdne, hF, hfinC, hfinD, hcompl, horth, hproj, hop,
    hj, hL, hLU, hUL, hεadj, hrangeU, hεproj, hformula, hrangej, hjmap,
    hBdec, hTU, hTV, hVV, hUV, hBconj, hεconj, hjconj, hq3⟩


end Position

end Triple

end CFSG.HardMathSupport.Dickson.Sec6.I1431
