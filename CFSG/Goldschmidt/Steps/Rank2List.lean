module

public import CFSG.Goldschmidt.Statements
public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11Data
import CFSG.Timmesfeld.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
import CFSG.CharacterTheory.Semidihedral.InvolutionFusion

public section

namespace CFSG.Goldschmidt

namespace Rank2List

open Matrix CFSG.Assembly.LowTwoRank

section Generic

variable {G : Type*} [Group G]

theorem not_isMulCommutative_omega1 [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hxy : x * y ≠ y * x)
    (S : Sylow 2 G) : ¬ IsMulCommutative (Omega1 (S : Subgroup G)) := by
  intro hcomm
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hΩ : ∀ z ∈ P, z ^ 2 = 1 → g * z * g⁻¹ ∈ Omega1 (S : Subgroup G) := by
    intro z hz hz2
    refine Subgroup.subset_closure ⟨?_, by rw [conj_pow, hz2, mul_one, mul_inv_cancel]⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (Q : Subgroup G) (hPQ hz)
  have h := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hΩ x hx hx2⟩ ⟨_, hΩ y hy hy2⟩)
  apply hxy
  simp only [Subgroup.coe_mul] at h
  have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    simpa only [mul_assoc, inv_mul_cancel_left] using h
  simpa using h'

theorem not_isMulCommutative_omega1_of_injective [Finite G] {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {x y : H} {k : ℕ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hk : (x * y) ^ 2 ^ k = 1) (hxy : x * y ≠ y * x) (S : Sylow 2 G) :
    ¬ IsMulCommutative (Omega1 (S : Subgroup G)) := by
  have hx' : φ x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hy' : φ y ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have hk' : (φ x * φ y) ^ 2 ^ k = 1 := by rw [← map_mul, ← map_pow, hk, map_one]
  refine not_isMulCommutative_omega1
    (CFSG.Timmesfeld.isPGroup_two_closure_pair (by rw [← sq, hx']) (by rw [← sq, hy']) hk')
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hx' hy' ?_ S
  rw [← map_mul, ← map_mul]
  exact fun h => hxy (hφ h)

theorem isConj_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (h : ∀ x y : H, orderOf x = 2 → orderOf y = 2 → IsConj x y) (x y : G) (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  have hxy := h (e x) (e y) (by rw [MulEquiv.orderOf_eq, hx]) (by rw [MulEquiv.orderOf_eq, hy])
  simpa using MonoidHom.map_isConj e.symm.toMonoidHom hxy

theorem isConj_of_forall_isConj {c : G} (h : ∀ x : G, orderOf x = 2 → IsConj x c) (x y : G)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (h x hx).trans (h y hy).symm

theorem isInvolution_of_orderOf {x : G} (hx : orderOf x = 2) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x := by
  refine ⟨fun h => ?_, by rw [← hx, pow_orderOf_eq_one]⟩
  rw [h, orderOf_one] at hx
  exact absurd hx (by norm_num)

end Generic

@[expose] def Concl (G : Type) [Group G] : Prop :=
  (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (Omega1 (S : Subgroup G))

theorem sixteen_dvd_sq_sub_one {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q ^ 2 - 1 := by
  have h16 : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
  have hq2 : q ^ 2 % 16 = 1 := by
    rcases h16 with h | h | h | h <;> simp [Nat.pow_mod, h]
  omega

theorem psl2_concl (G : Type) [Group G] [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h8 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7)
    (hM : StatedClassicalModel G .PSL 2 p f) : Concl G := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  let φ : G ≃* CFSG.GorensteinWalter.PSL2 K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  refine ⟨isConj_of_mulEquiv φ fun x y hx hy => ?_, fun S => ?_⟩
  · obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hKodd
      x y (isInvolution_of_orderOf hx) (isInvolution_of_orderOf hy)
    exact isConj_iff.mpr ⟨g, hg⟩
  · obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 (CFSG.GorensteinWalter.PSL2 K)))
    obtain ⟨m, hm, ⟨eS⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hKodd S₀
    have h8G : 2 ^ 3 ∣ Nat.card (CFSG.GorensteinWalter.PSL2 K) := by
      rw [CFSG.GorensteinWalter.psl2_card_formula K hKodd]
      obtain ⟨c, hc⟩ := sixteen_dvd_sq_sub_one (hK ▸ h8)
      rw [hc, show Nat.card K * (16 * c) = 2 * (8 * (Nat.card K * c)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
      exact Dvd.intro _ rfl
    have h8S := S₀.pow_dvd_card_of_pow_dvd_card h8G
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card, ← pow_succ'] at h8S
    have hm2 : 2 ≤ m := by
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8S
      omega
    have hne : (1 : ZMod (2 ^ m)) ≠ -1 := by
      intro h
      have h11 : (1 : ZMod (2 ^ m)) + 1 = 0 :=
        calc (1 : ZMod (2 ^ m)) + 1 = 1 + -1 := by rw [← h]
          _ = 0 := add_neg_cancel 1
      have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
        rw [Nat.cast_two]
        rwa [one_add_one_eq_two] at h11
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      omega
    refine not_isMulCommutative_omega1_of_injective
      (φ.symm.toMonoidHom.comp ((S₀ : Subgroup _).subtype.comp eS.symm.toMonoidHom))
      (φ.symm.injective.comp (Subtype.val_injective.comp eS.symm.injective))
      (x := DihedralGroup.sr 0) (y := DihedralGroup.sr 1) (k := m)
      (by rw [sq, DihedralGroup.sr_mul_self]) (by rw [sq, DihedralGroup.sr_mul_self]) ?_ ?_ S
    · rw [DihedralGroup.sr_mul_sr, sub_zero, DihedralGroup.r_one_pow, Nat.cast_pow,
        Nat.cast_ofNat, ← Nat.cast_ofNat (R := ZMod (2 ^ m)), ← Nat.cast_pow, ZMod.natCast_self]
      rfl
    · rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr, sub_zero, zero_sub, Ne,
        DihedralGroup.r.injEq]
      exact hne

section LinearThree

open CFSG.Wreathed.OddLinearThreeCentralizerCore

variable {F : Type} [Field F]

@[expose] def negDiagMat : Matrix (Fin 3) (Fin 3) F := diagonal ![-1, -1, 1]

theorem det_negDiagMat : (negDiagMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [negDiagMat, det_diagonal, Fin.prod_univ_three]
  simp

@[expose] def negDiagSL : SL3 F := ⟨negDiagMat, det_negDiagMat⟩

theorem isConj_negDiagSL [Finite F] (hF : Odd (Nat.card F)) {z : SL3 F} (hz : orderOf z = 2) :
    IsConj negDiagSL z := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero F hF
  set a : Module.End F (Fin 3 → F) := (matrixAction F z).toLinearMap with ha
  obtain ⟨hm, hp⟩ := matrixAction_finrank F hF z hz
  have hc : IsCompl (minusSpace a) (plusSpace a) :=
    involution_spaces_isCompl h2 a (matrixAction_involutive F z hz)
  let bm := Module.finBasisOfFinrankEq F (minusSpace a) hm
  let bp := Module.finBasisOfFinrankEq F (plusSpace a) hp
  let b₀ := (bm.prod bp).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let d₀ : Fin 2 ⊕ Fin 1 → F := Sum.elim (fun _ => -1) (fun _ => 1)
  have hb₀ : ∀ i, a (b₀ i) = d₀ i • b₀ i := by
    rintro (i | i)
    · have hmem : b₀ (Sum.inl i) ∈ minusSpace a := by
        simp [b₀, Module.Basis.map_apply, Module.Basis.prod_apply]
      exact Module.End.mem_eigenspace_iff.mp hmem
    · have hmem : b₀ (Sum.inr i) ∈ plusSpace a := by
        simp [b₀, Module.Basis.map_apply, Module.Basis.prod_apply]
      exact Module.End.mem_eigenspace_iff.mp hmem
  let b := b₀.reindex finSumFinEquiv
  have hd : ∀ j : Fin 3, d₀ (finSumFinEquiv.symm j) = ![-1, -1, 1] j := by
    intro j
    fin_cases j <;> rfl
  have hb : ∀ j : Fin 3, (z : Matrix (Fin 3) (Fin 3) F) *ᵥ b j =
      (![-1, -1, 1] : Fin 3 → F) j • b j := by
    intro j
    have h := hb₀ (finSumFinEquiv.symm j)
    rw [hd j] at h
    rw [Module.Basis.reindex_apply]
    change Matrix.SpecialLinearGroup.toLin' z _ = _ at h
    rwa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] at h
  set U : Matrix (Fin 3) (Fin 3) F := (Pi.basisFun F (Fin 3)).toMatrix b with hU
  have hUij : ∀ i j, U i j = b j i := fun i j => by
    rw [hU, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hUdet : U.det ≠ 0 := by
    have h := (Pi.basisFun F (Fin 3)).isUnit_det b
    rw [Module.Basis.det_apply] at h
    exact h.ne_zero
  have hzU : (z : Matrix (Fin 3) (Fin 3) F) * U = U * diagonal ![-1, -1, 1] := by
    ext i j
    rw [mul_diagonal, hUij, Matrix.mul_apply]
    have h := congrFun (hb j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [hUij]
    rw [h, mul_comm]
  set D : Matrix (Fin 3) (Fin 3) F := diagonal ![U.det⁻¹, 1, 1] with hD
  have hdet : (U * D).det = 1 := by
    rw [det_mul, hD, det_diagonal, Fin.prod_univ_three]
    simp [hUdet]
  have hzUD : (z : Matrix (Fin 3) (Fin 3) F) * (U * D) = U * D * negDiagMat := by
    rw [← Matrix.mul_assoc, hzU, Matrix.mul_assoc, Matrix.mul_assoc, negDiagMat, hD,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  set c : SL3 F := ⟨U * D, hdet⟩ with hc
  have hct : c * negDiagSL = z * c := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact hzUD.symm
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [hct, mul_inv_cancel_right]

theorem psl3_isConj [Finite F] (hF : Odd (Nat.card F))
    {t : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F} (ht : orderOf t = 2) :
    IsConj t (QuotientGroup.mk' (Subgroup.center (SL3 F)) negDiagSL) := by
  obtain ⟨z, ⟨hz, rfl⟩, -⟩ := unique_involution_lift F (Subgroup.center (SL3 F)) le_rfl t ht
  exact (MonoidHom.map_isConj _ (isConj_negDiagSL hF hz)).symm

end LinearThree

section Dihedral

variable {K : Type} [Field K]

@[expose] def d8MatA : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

@[expose] def d8MatB : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem d8MatA_mul_self : d8MatA * d8MatA = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d8MatA, Matrix.mul_apply, Fin.sum_univ_three]

theorem d8MatB_mul_self : d8MatB * d8MatB = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d8MatB, Matrix.mul_apply, Fin.sum_univ_three]

theorem d8Mat_mul_sq :
    d8MatA * d8MatB * (d8MatA * d8MatB) = (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d8MatA, d8MatB, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def d8GLA : GL (Fin 3) K := ⟨d8MatA, d8MatA, d8MatA_mul_self, d8MatA_mul_self⟩

@[expose] def d8GLB : GL (Fin 3) K := ⟨d8MatB, d8MatB, d8MatB_mul_self, d8MatB_mul_self⟩

theorem det_d8MatA : (d8MatA : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [d8MatA, det_fin_three]

theorem det_d8MatB : (d8MatB : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [d8MatB, det_fin_three]

theorem d8GLA_mem_statedSL : (d8GLA : GL (Fin 3) K) ∈ StatedSL 3 K :=
  Subgroup.subset_closure det_d8MatA

theorem d8GLB_mem_statedSL : (d8GLB : GL (Fin 3) K) ∈ StatedSL 3 K :=
  Subgroup.subset_closure det_d8MatB

theorem d8GLA_mem_statedSU {q : ℕ} (hq : Odd q) : (d8GLA : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  have hmap : (d8MatA : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = d8MatA := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d8MatA, hq.neg_one_pow, zero_pow hq0]
  have htr : (d8MatA : Matrix (Fin 3) (Fin 3) K)ᵀ = d8MatA := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine Subgroup.subset_closure ⟨det_d8MatA, ?_⟩
  change (d8MatA.map (· ^ q))ᵀ * d8MatA = 1
  rw [hmap, htr, d8MatA_mul_self]

theorem d8GLB_mem_statedSU {q : ℕ} (hq : Odd q) : (d8GLB : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  have hmap : (d8MatB : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = d8MatB := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d8MatB, hq.neg_one_pow, zero_pow hq0]
  have htr : (d8MatB : Matrix (Fin 3) (Fin 3) K)ᵀ = d8MatB := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine Subgroup.subset_closure ⟨det_d8MatB, ?_⟩
  change (d8MatB.map (· ^ q))ᵀ * d8MatB = 1
  rw [hmap, htr, d8MatB_mul_self]

theorem statedProj_d8 (h2 : (2 : K) ≠ 0) {Hg : Subgroup (GL (Fin 3) K)} (hA : d8GLA ∈ Hg)
    (hB : d8GLB ∈ Hg) :
    (QuotientGroup.mk ⟨d8GLA, hA⟩ : StatedProj Hg) ^ 2 = 1 ∧
      (QuotientGroup.mk ⟨d8GLB, hB⟩ : StatedProj Hg) ^ 2 = 1 ∧
      ((QuotientGroup.mk ⟨d8GLA, hA⟩ : StatedProj Hg) * QuotientGroup.mk ⟨d8GLB, hB⟩) ^ 2 ^ 2 = 1 ∧
      (QuotientGroup.mk ⟨d8GLA, hA⟩ : StatedProj Hg) * QuotientGroup.mk ⟨d8GLB, hB⟩ ≠
        QuotientGroup.mk ⟨d8GLB, hB⟩ * QuotientGroup.mk ⟨d8GLA, hA⟩ := by
  set a : Hg := ⟨d8GLA, hA⟩ with ha
  set b : Hg := ⟨d8GLB, hB⟩ with hb
  have haa : a * a = 1 := Subtype.ext (Units.ext d8MatA_mul_self)
  have hbb : b * b = 1 := Subtype.ext (Units.ext d8MatB_mul_self)
  have hcoe : (((a * b) * (a * b) : Hg) : GL (Fin 3) K) =
      (⟨diagonal ![-1, -1, 1], diagonal ![-1, -1, 1], by
        rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
        by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩ :
        GL (Fin 3) K) :=
    Units.ext d8Mat_mul_sq
  have hcc : (a * b) * (a * b) * ((a * b) * (a * b)) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hcoe]
    change diagonal ![-1, -1, 1] * diagonal ![-1, -1, 1] = (1 : Matrix (Fin 3) (Fin 3) K)
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hne : (QuotientGroup.mk ((a * b) * (a * b)) : StatedProj Hg) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range]
    rintro ⟨c, hc⟩
    rw [hcoe] at hc
    have e0 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have e2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at e0 e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at e0 e2
    exact h2 (by linear_combination e0 - e2)
  have hX : (a : StatedProj Hg) * a = 1 := by rw [← QuotientGroup.mk_mul, haa, QuotientGroup.mk_one]
  have hY : (b : StatedProj Hg) * b = 1 := by rw [← QuotientGroup.mk_mul, hbb, QuotientGroup.mk_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, sq, haa, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, sq, hbb, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, show 2 ^ 2 = 2 + 2 from rfl, pow_add, sq,
      hcc, QuotientGroup.mk_one]
  · intro h
    apply hne
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    calc (a : StatedProj Hg) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [h]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hX, hY, one_mul]

end Dihedral

theorem psl3_concl (G : Type) [Group G] [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : StatedClassicalModel G .PSL 3 p f) : Concl G := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hKodd
  refine ⟨isConj_of_mulEquiv (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm)
    (isConj_of_forall_isConj fun x hx => psl3_isConj hKodd hx), fun S => ?_⟩
  obtain ⟨hx, hy, hk, hxy⟩ := statedProj_d8 h2 d8GLA_mem_statedSL d8GLB_mem_statedSL
  exact not_isMulCommutative_omega1_of_injective e.symm.toMonoidHom e.symm.injective hx hy hk hxy S

theorem psu3_concl (G : Type) [Group G] [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hM : StatedClassicalModel G .PSU 3 p f) : Concl G := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K p := hU.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  refine ⟨isConj_of_mulEquiv
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm)
    (isConj_of_forall_isConj fun x hx =>
      CFSG.RankThree.Classical.isConj_unitaryProj_unitaryInvT hU hp2 hx), fun S => ?_⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hx, hy, hk, hxy⟩ := statedProj_d8 h2 (d8GLA_mem_statedSU hq) (d8GLB_mem_statedSU hq)
  exact not_isMulCommutative_omega1_of_injective e.symm.toMonoidHom e.symm.injective hx hy hk hxy S

@[expose] def a7X : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

@[expose] def a7Y : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 4 5, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

theorem a7_pair : a7X ^ 2 = 1 ∧ a7Y ^ 2 = 1 ∧ (a7X * a7Y) ^ 2 ^ 2 = 1 ∧ a7X * a7Y ≠ a7Y * a7X := by
  decide +kernel

theorem a7_concl
    (G : Type) [Group G] [Finite G] (e : G ≃* alternatingGroup (Fin 7)) :
    Concl G := by
  refine ⟨isConj_of_mulEquiv e fun x y hx hy => ?_, fun S => ?_⟩
  · obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.aSeven_involutions_conjugate x y
      (isInvolution_of_orderOf hx) (isInvolution_of_orderOf hy)
    exact isConj_iff.mpr ⟨g, hg⟩
  · obtain ⟨hx, hy, hk, hxy⟩ := a7_pair
    exact not_isMulCommutative_omega1_of_injective e.symm.toMonoidHom e.symm.injective hx hy hk
      hxy S

section M11

open CFSG.QuasithinUnique.Unc25M11

@[expose] def m11SylowTwo : Subgroup CFSG.Blueprint.NativeSporadic.M11 where
  carrier := {x | (x : Equiv.Perm (Fin 11)) ∈ P0L}
  one_mem' := one_mem_P0L
  mul_mem' := fun {x y} hx hy => mul_mem_P0L (x : Equiv.Perm (Fin 11)) hx y hy
  inv_mem' := fun {x} hx => inv_mem_P0L (x : Equiv.Perm (Fin 11)) hx

theorem card_m11SylowTwo : Nat.card m11SylowTwo = 16 := by
  have h := CFSG.Sporadic.Schreier.card_eq_length
    (fun x : CFSG.Blueprint.NativeSporadic.M11 => x ∈ m11SylowTwo)
    (fun x => (x : Equiv.Perm (Fin 11))) Subtype.val_injective P0L P0L_nodup ?_
  · rw [P0L_length] at h
    exact h
  · intro y
    constructor
    · intro hy
      obtain ⟨i, -, j, -, rfl⟩ := mem_P0L_iff.mp hy
      exact ⟨⟨sa ^ i * sb ^ j, Subgroup.mul_mem _ (Subgroup.pow_mem _ (pw_mem _) i)
        (Subgroup.pow_mem _ (pw_mem _) j)⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx

@[expose] def m11ConjWords : List (List ℕ) :=
  [[], [1, 1, 0, 1, 0, 1, 1], [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1, 1, 0]]

theorem m11_invsP0_conj_check :
    invsP0.all (fun u => m11ConjWords.any fun l => decide (pw l * u * (pw l)⁻¹ = sb)) = true := by
  decide +kernel

theorem m11_invsP0_conj {u : Equiv.Perm (Fin 11)} (hu : u ∈ invsP0) :
    ∃ l : List ℕ, pw l * u * (pw l)⁻¹ = sb := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp (List.all_eq_true.mp m11_invsP0_conj_check u hu)
  exact ⟨l, of_decide_eq_true hl⟩

theorem m11_isConj_sb
    (t : CFSG.Blueprint.NativeSporadic.M11) (ht : orderOf t = 2) :
    IsConj t ⟨sb, pw_mem _⟩ := by
  have hP : IsPGroup 2 m11SylowTwo :=
    IsPGroup.of_card (n := 4) (by rw [card_m11SylowTwo]; norm_num)
  have hindex : m11SylowTwo.index = 495 := by
    have h := m11SylowTwo.card_mul_index
    rw [card_m11SylowTwo, CFSG.Semidihedral.GL2Recognition.card_nativeM11] at h
    omega
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨y, hty⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow
    (hP.toSylow (by rw [hindex]; decide)) t hpt
  have hy2 : orderOf (y : CFSG.Blueprint.NativeSporadic.M11) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hty
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hyinv : ((y : CFSG.Blueprint.NativeSporadic.M11) : Equiv.Perm (Fin 11)) ∈ invsP0 := by
    refine List.mem_filter.mpr ⟨y.2, decide_eq_true ⟨fun h1 => ?_, ?_⟩⟩
    · have h1' : (y : CFSG.Blueprint.NativeSporadic.M11) = 1 := Subtype.ext h1
      rw [h1', orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · have h := pow_orderOf_eq_one (y : CFSG.Blueprint.NativeSporadic.M11)
      rw [hy2, sq] at h
      exact congrArg Subtype.val h
  obtain ⟨l, hl⟩ := m11_invsP0_conj hyinv
  refine hty.trans (isConj_iff.mpr ⟨⟨pw l, pw_mem l⟩, Subtype.ext ?_⟩)
  simpa using hl

theorem m11_pair : sb ^ 2 = 1 ∧ (sa ^ 2 * sb) ^ 2 = 1 ∧ (sb * (sa ^ 2 * sb)) ^ 2 ^ 2 = 1 ∧
    sb * (sa ^ 2 * sb) ≠ sa ^ 2 * sb * sb := by
  decide +kernel

theorem m11_concl
    (G : Type) [Group G] [Finite G] (e : G ≃* StatedM11) : Concl G := by
  let e' : G ≃* CFSG.Blueprint.NativeSporadic.M11 := e.trans
    (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)
  refine ⟨isConj_of_mulEquiv e' (isConj_of_forall_isConj m11_isConj_sb), fun S => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := m11_pair
  have hsa : sa ∈ CFSG.Blueprint.NativeSporadic.M11 := pw_mem _
  have hsb : sb ∈ CFSG.Blueprint.NativeSporadic.M11 := pw_mem _
  refine not_isMulCommutative_omega1_of_injective e'.symm.toMonoidHom e'.symm.injective
    (x := ⟨sb, hsb⟩) (y := ⟨sa ^ 2 * sb, mul_mem (pow_mem hsa 2) hsb⟩) (k := 2)
    (Subtype.ext h1) (Subtype.ext h2) (Subtype.ext h3) (fun h => h4 (congrArg Subtype.val h)) S

end M11

end Rank2List

open Rank2List

theorem N15 : S_N15 := by
  intro G _ _ _ hG
  rcases hG with ⟨p, f, hp, hp2, hf, h8, hM⟩ | ⟨p, f, hp, hp2, -, hM⟩ | ⟨p, f, hp, hp2, hf, hM⟩ |
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact psl2_concl G hp hp2 hf h8 hM
  · exact psl3_concl G hp hp2 hM
  · exact psu3_concl G hp hp2 hf hM
  · exact a7_concl G e
  · exact m11_concl G e

end CFSG.Goldschmidt
