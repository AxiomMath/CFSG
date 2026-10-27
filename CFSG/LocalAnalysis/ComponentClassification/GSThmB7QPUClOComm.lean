module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOCommA
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOInnerNF
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOMinA

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL compInd
  commute_signMat_iff commute_compInd_iff)
open scoped commutatorElement

theorem kappa_scalar_on_block {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {d : ℕ}
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (_hker : OKer (oQ (diagGL hw)))
    {J I : Finset (Fin d)} (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty) (hNF : BlockNF w I)
    (hq : IsQuasisimple (Burgoyne.C.blockP K hw I)) {g : similarityPairs (oQ (diagGL hw))}
    (hfix : ∀ x ∈ Burgoyne.C.blockP K hw I, oκ _ g x = x)
    (ht : oκ _ g (projH _ ⟨signGL K J, hJ⟩) = projH _ ⟨signGL K J, hJ⟩) :
    g.val.right = 1 ∧ ∃ c : Kˣ, ∀ i ∈ I, ∀ j : Fin d,
      (g.val.left : Matrix (Fin d) (Fin d) K) i j = (if i = j then (c : K) else 0) ∧
      (g.val.left : Matrix (Fin d) (Fin d) K) j i = (if i = j then (c : K) else 0) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF
  have hle := Burgoyne.C.oBlock_le_matrixDerived hw h2 I
  have hperf : ⁅(oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))),
      (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw)))⁆ =
      (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) := by
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL hw))).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle,
      commutator_oBlock_eq hw h2 hIc hq]
  have hfix' : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      (g.val.left : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map g.val.right *
        ((g.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X := fun X hX =>
    kappa_eq_of_fix g hperf (fun Y hY => hfix _ ⟨Y, hY, rfl⟩) (X := ⟨X, hle hX⟩)
      (mem_subgroupOf.2 hX)
  set D := g.val.left with hDdef
  have hDinv : ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hS : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j → (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
      signMat K {i, j} * D := by
    intro i hi j hj hij
    have e := hfix' _ (signGL_pair_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj))
    rw [coe_signGL, map_signMat_field] at e
    calc (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
        (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} *
          (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D) := by
            rw [hDinv, Matrix.mul_one]
      _ = signMat K {i, j} * D := by rw [← Matrix.mul_assoc, e]
  have hiso₀ : ∀ x y, x ≠ y → (x ∈ I₀ ∨ y ∈ I₀) → (D : Matrix (Fin d) (Fin d) K) x y = 0 :=
    fun x y hxy hxI => offDiag_eq_zero_of_commute_sign_on h2 hI₀3 hS hxy hxI
  have hisoA : ∀ x ∈ I₀, ∀ y, y ≠ x → (D : Matrix (Fin d) (Fin d) K) y x = 0 ∧
      (D : Matrix (Fin d) (Fin d) K) x y = 0 := fun x hx y hy =>
    ⟨hiso₀ y x hy (Or.inr hx), hiso₀ x y (Ne.symm hy) (Or.inl hx)⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
  obtain ⟨b, hb, hba, -⟩ := exists_mem_ne_ne hI₀3 a a
  obtain ⟨c, hc, hca, hcb⟩ := exists_mem_ne_ne hI₀3 a b
  have hwab : w a = w b := hI₀w a ha b hb
  have hwac : w a = w c := hI₀w a ha c hc
  have hτ : g.val.right = 1 := by
    have hfa : ∀ x : K, x ≠ 1 → g.val.right (2 * x ^ 2 - 1) = 2 * x ^ 2 - 1 := by
      intro x hx1
      obtain ⟨y, z, hyz⟩ := exists_sq_add_sq_eq hK (1 - x ^ 2)
      set v : Fin d → K := x • Pi.single a 1 + y • Pi.single b 1 + z • Pi.single c 1 with hv
      have hva : v a = x := by
        simp [hv, Ne.symm hba, Ne.symm hca]
      have hQv : bil w v v = w a := by
        simp only [hv, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right,
          bil_single_self, bil_single_ne w hba, bil_single_ne w hca, bil_single_ne w hcb,
          bil_single_ne w (Ne.symm hba), bil_single_ne w (Ne.symm hca),
          bil_single_ne w (Ne.symm hcb)]
        linear_combination (w a) * hyz - y ^ 2 * hwab - z ^ 2 * hwac
      have hav : bil w (Pi.single a 1) v = x * w a := by
        simp only [hv, bil_add_right, bil_smul_right, bil_single_self,
          bil_single_ne w (Ne.symm hba), bil_single_ne w (Ne.symm hca)]
        ring
      have hQ' : bil w (Pi.single a 1 - v) (Pi.single a 1 - v) ≠ 0 := by
        rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_comm w v (Pi.single a 1), hav, hQv,
          bil_single_self]
        have e : w a - x * w a - (x * w a - w a) = 2 * w a * (1 - x) := by ring
        rw [e]
        exact mul_ne_zero (mul_ne_zero h2 (hw a)) (sub_ne_zero.2 (Ne.symm hx1))
      have hsupp : ∀ i, i ∉ I → (Pi.single a 1 - v : Fin d → K) i = 0 := by
        intro i hi
        have hia : i ≠ a := fun h => hi (h ▸ hI₀ ha)
        have hib : i ≠ b := fun h => hi (h ▸ hI₀ hb)
        have hic : i ≠ c := fun h => hi (h ▸ hI₀ hc)
        simp [hv, hia, hib, hic]
      have hX := commutator_mem_commutator (reflGL_mem_oIsoBlock hw (hI₀ ha))
        (reflGLv_mem_oIsoBlock hw hQ' hsupp)
      have e := congrFun (congrFun (hfix' _ hX) a) a
      rw [conj_apply_diag_of_isolated (fun y hy => (hisoA a ha y hy).2)
        (fun y hy => (hisoA a ha y hy).1), Matrix.map_apply, coe_comm_reflGL h2 (hw a) hQv hQ',
        signMat_mul_reflM_apply, hQv, hva] at e
      have hval : 2 / w a * (x * (w a * x)) - 1 = 2 * x ^ 2 - 1 := by
        rw [show 2 / w a * (x * (w a * x)) = 2 * x ^ 2 * (w a / w a) by ring, div_self (hw a),
          mul_one]
      rwa [hval] at e
    have hsq : ∀ x : K, g.val.right (x ^ 2) = x ^ 2 := by
      intro x
      by_cases hx1 : x = 1
      · rw [hx1, one_pow, map_one]
      have e := hfa x hx1
      rw [map_sub, map_mul, map_one, map_ofNat] at e
      have e' : (2 : K) * (g.val.right (x ^ 2) - x ^ 2) = 0 := by linear_combination e
      exact sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_left h2)
    refine RingEquiv.ext fun y => ?_
    have hy : ((y + 1) / 2) ^ 2 - ((y - 1) / 2) ^ 2 = y := by
      have h4 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      linear_combination y * (2 * 2⁻¹ + 1) * h4
    change g.val.right y = y
    rw [← hy, map_sub, hsq, hsq]
  have hDΩ : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * X = X * D := by
    intro X hX
    have e := hfix' X hX
    have e2 : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map ⇑g.val.right = X := by
      rw [hτ]
      ext
      rfl
    rw [e2] at e
    calc (D : Matrix (Fin d) (Fin d) K) * X =
        (D : Matrix (Fin d) (Fin d) K) * X *
          (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D) := by
            rw [hDinv, Matrix.mul_one]
      _ = X * D := by rw [← Matrix.mul_assoc, e]
  have hDaa : (D : Matrix (Fin d) (Fin d) K) a a ≠ 0 := by
    intro h0
    have hcol : (D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single a 1 = 0 := by
      rw [mulVec_single_of_isolated (fun y hy => (hisoA a ha y hy).1), h0, zero_smul]
    have h1 : ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
        ((D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single a 1) = 0 := by
      rw [hcol, mulVec_zero]
    rw [mulVec_mulVec, hDinv, one_mulVec] at h1
    have h1' := congrFun h1 a
    simp at h1'
  have hDS : (D : Matrix (Fin d) (Fin d) K) * signMat K J = signMat K J * D := by
    rw [kappa_proj, projH_eq_projH_iff] at ht
    obtain ⟨c', hc'⟩ := mem_subgroupOf.1 ht
    have hconj : ((matrixDerivedConjugation _ g ⟨signGL K J, hJ⟩ :
        matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) = D * signGL K J * D⁻¹ := by
      rw [matrixDerivedConjugation_val, hτ, map_one, MulAut.one_apply]
      try rfl
    have hc'' : GeneralLinearGroup.scalar (Fin d) c' =
        (D * signGL K J * D⁻¹)⁻¹ * signGL K J := by
      rw [← hconj]
      exact hc'
    have e3 : signGL K J = D * signGL K J * D⁻¹ * GeneralLinearGroup.scalar (Fin d) c' := by
      rw [hc'', mul_inv_cancel_left]
    have e2 : signGL K J * D = GeneralLinearGroup.scalar (Fin d) c' * (D * signGL K J) := by
      calc signGL K J * D =
          D * signGL K J * D⁻¹ * GeneralLinearGroup.scalar (Fin d) c' * D := by
            rw [← e3]
        _ = D * signGL K J * D⁻¹ * (D * GeneralLinearGroup.scalar (Fin d) c') := by
            rw [(commute_scalar c' D).eq]
            group
        _ = D * signGL K J * GeneralLinearGroup.scalar (Fin d) c' := by group
        _ = GeneralLinearGroup.scalar (Fin d) c' * (D * signGL K J) :=
            (commute_scalar c' (D * signGL K J)).eq
    have e4 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) a a) e2
    simp only [Units.val_mul, coe_signGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      signMat, diagonal_mul, mul_diagonal] at e4
    have hs0 : (if a ∈ J then (-1 : K) else 1) ≠ 0 := by
      split_ifs
      · exact neg_ne_zero.2 one_ne_zero
      · exact one_ne_zero
    have hc1 : (c' : K) = 1 := by
      have e5 : (if a ∈ J then (-1 : K) else 1) * (D : Matrix (Fin d) (Fin d) K) a a *
          ((c' : K) - 1) = 0 := by linear_combination -e4
      rcases mul_eq_zero.1 e5 with h | h
      · exact absurd h (mul_ne_zero hs0 hDaa)
      · exact sub_eq_zero.1 h
    have hc1' : c' = 1 := Units.ext hc1
    rw [hc1', map_one, one_mul] at e2
    have e6 := congrArg Units.val e2
    rw [Units.val_mul, Units.val_mul, coe_signGL] at e6
    exact e6.symm
  have hblock : ∀ x y, (x ∈ J ↔ y ∉ J) → (D : Matrix (Fin d) (Fin d) K) x y = 0 :=
    (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS.symm)
  have hisoI : ∀ x ∈ I, ∀ y, y ≠ x → (D : Matrix (Fin d) (Fin d) K) y x = 0 ∧
      (D : Matrix (Fin d) (Fin d) K) x y = 0 := by
    intro x hx y hyx
    by_cases hx0 : x ∈ I₀
    · exact hisoA x hx0 y hyx
    by_cases hy0 : y ∈ I₀
    · exact ⟨hiso₀ y x hyx (Or.inl hy0), hiso₀ x y (Ne.symm hyx) (Or.inr hy0)⟩
    have hyI : y ∉ I := fun hyI => hyx (hns y hyI x hx hy0 hx0)
    have hxy : (x ∈ J ↔ y ∉ J) := by
      rcases hI with rfl | rfl
      · exact ⟨fun _ => hyI, fun _ => hx⟩
      · simp only [Finset.mem_compl] at hx hyI ⊢
        tauto
    exact ⟨hblock y x (by tauto), hblock x y hxy⟩
  have hDe : ∀ i ∈ I, (D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single i 1 =
      (D : Matrix (Fin d) (Fin d) K) i i • Pi.single i 1 := fun i hi =>
    mulVec_single_of_isolated fun y hy => (hisoI i hi y hy).1
  have hcyc : ∀ {x y z : Fin d}, x ∈ I → y ∈ I → z ∈ I → x ≠ y → x ≠ z → y ≠ z →
      w x = w y → w y = w z →
      (D : Matrix (Fin d) (Fin d) K) z z = (D : Matrix (Fin d) (Fin d) K) x x := by
    intro x y z hx hy hz hxy hxz hyz hwxy hwyz
    have hu : bil w (Pi.single x 1 - Pi.single y 1) (Pi.single x 1 - Pi.single y 1) ≠ 0 := by
      rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_single_self, bil_single_self,
        bil_single_ne w hxy, bil_single_ne w (Ne.symm hxy), ← hwxy]
      have e : w x - 0 - (0 - w x) = 2 * w x := by ring
      rw [e]
      exact mul_ne_zero h2 (hw x)
    have hv : bil w (Pi.single y 1 - Pi.single z 1) (Pi.single y 1 - Pi.single z 1) ≠ 0 := by
      rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_single_self, bil_single_self,
        bil_single_ne w hyz, bil_single_ne w (Ne.symm hyz), ← hwyz]
      have e : w y - 0 - (0 - w y) = 2 * w y := by ring
      rw [e]
      exact mul_ne_zero h2 (hw y)
    have hsub : ∀ {p q : Fin d}, p ∈ I → q ∈ I → ∀ i, i ∉ I →
        (Pi.single p 1 - Pi.single q 1 : Fin d → K) i = 0 := by
      intro p q hp hq i hi
      have hip : i ≠ p := fun h => hi (h ▸ hp)
      have hiq : i ≠ q := fun h => hi (h ▸ hq)
      simp [hip, hiq]
    have hY := commutator_mem_commutator (reflGLv_mem_oIsoBlock hw hu (hsub hx hy))
      (reflGLv_mem_oIsoBlock hw hv (hsub hy hz))
    have hYa := comm_reflM_three_mulVec h2 hxy hxz hyz hwxy hwyz hu hv
    have e : (D : Matrix (Fin d) (Fin d) K) *ᵥ
        (((⁅reflGLv w hu, reflGLv w hv⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          Pi.single x 1) =
        ((⁅reflGLv w hu, reflGLv w hv⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          ((D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single x 1) := by
      rw [mulVec_mulVec, mulVec_mulVec, hDΩ _ hY]
    rw [hYa, hDe z hz, hDe x hx, mulVec_smul, hYa] at e
    have e' := congrFun e z
    simpa using e'
  have hconst : ∀ i ∈ I,
      (D : Matrix (Fin d) (Fin d) K) i i = (D : Matrix (Fin d) (Fin d) K) a a := by
    have hI₀c : ∀ i ∈ I₀,
        (D : Matrix (Fin d) (Fin d) K) i i = (D : Matrix (Fin d) (Fin d) K) a a := by
      intro i hi
      by_cases hia : i = a
      · rw [hia]
      obtain ⟨b', hb', hb'a, hb'i⟩ := exists_mem_ne_ne hI₀3 a i
      exact hcyc (hI₀ ha) (hI₀ hb') (hI₀ hi) (Ne.symm hb'a) (Ne.symm hia) hb'i
        (hI₀w a ha b' hb') (hI₀w b' hb' i hi)
    intro i hi
    by_cases hi0 : i ∈ I₀
    · exact hI₀c i hi0
    have hia : i ≠ a := fun h => hi0 (h ▸ ha)
    have hib : i ≠ b := fun h => hi0 (h ▸ hb)
    have hic : i ≠ c := fun h => hi0 (h ▸ hc)
    by_cases hwi : w i = w a
    · exact hcyc (hI₀ ha) (hI₀ hb) hi (Ne.symm hba) (Ne.symm hia) (Ne.symm hib) hwab
        (by rw [← hwab, hwi])
    have hm : (w a - w i) * (w a)⁻¹ ≠ 0 :=
      mul_ne_zero (sub_ne_zero.2 (Ne.symm hwi)) (inv_ne_zero (hw a))
    obtain ⟨β, γ, hβγ⟩ := exists_sq_add_sq_eq hK ((w a - w i) * (w a)⁻¹)
    have hβγ' : w a * (β ^ 2 + γ ^ 2) = w a - w i := by
      have hinv : w a * (w a)⁻¹ = 1 := mul_inv_cancel₀ (hw a)
      linear_combination (w a) * hβγ + (w a - w i) * hinv
    set u : Fin d → K := β • Pi.single b 1 + γ • Pi.single c 1 + Pi.single i 1 with hu
    have hQu : bil w u u = w a := by
      simp only [hu, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right,
        bil_single_self, bil_single_ne w hcb, bil_single_ne w (Ne.symm hcb),
        bil_single_ne w hib, bil_single_ne w (Ne.symm hib), bil_single_ne w hic,
        bil_single_ne w (Ne.symm hic)]
      linear_combination hβγ' - β ^ 2 * hwab - γ ^ 2 * hwac
    have huI : ∀ k, k ∉ I → u k = 0 := by
      intro k hk
      have hkb : k ≠ b := fun h => hk (h ▸ hI₀ hb)
      have hkc : k ≠ c := fun h => hk (h ▸ hI₀ hc)
      have hki : k ≠ i := fun h => hk (h ▸ hi)
      simp [hu, hkb, hkc, hki]
    have hau : bil w (Pi.single a 1) u = 0 := by
      simp only [hu, bil_add_right, bil_smul_right, bil_single_ne w (Ne.symm hba),
        bil_single_ne w (Ne.symm hca), bil_single_ne w (Ne.symm hia)]
      ring
    have hv : bil w (Pi.single a 1 - u) (Pi.single a 1 - u) ≠ 0 := by
      rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_comm w u (Pi.single a 1), hau, hQu,
        bil_single_self]
      have e : w a - 0 - (0 - w a) = 2 * w a := by ring
      rw [e]
      exact mul_ne_zero h2 (hw a)
    have hDa := commute_signMat_single_of_isolated h2 (fun y hy => hisoA a ha y hy)
    have hcomm := commute_reflM_of_mix hw h2 (fun X hX => hDΩ X hX) (hI₀ ha) hDa huI hQu hv
    obtain ⟨κ, hκ⟩ := exists_smul_of_commute_reflM h2 w (by rw [hQu]; exact hw a) hcomm
    have hDu : (D : Matrix (Fin d) (Fin d) K) *ᵥ u =
        (β * (D : Matrix (Fin d) (Fin d) K) b b) • Pi.single b 1 +
          (γ * (D : Matrix (Fin d) (Fin d) K) c c) • Pi.single c 1 +
          (D : Matrix (Fin d) (Fin d) K) i i • Pi.single i 1 := by
      rw [hu, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hDe b (hI₀ hb), hDe c (hI₀ hc),
        hDe i hi, smul_smul, smul_smul]
    rw [hDu] at hκ
    have ki := congrFun hκ i
    have kb := congrFun hκ b
    have kc := congrFun hκ c
    simp only [hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hib, Pi.single_eq_of_ne hic, Pi.single_eq_of_ne (Ne.symm hib),
      Pi.single_eq_of_ne (Ne.symm hic), Pi.single_eq_of_ne hcb, Pi.single_eq_of_ne (Ne.symm hcb),
      mul_one, mul_zero, add_zero, zero_add] at ki kb kc
    have hbb := hI₀c b hb
    have hcc := hI₀c c hc
    by_cases hβ : β = 0
    · have hγ : γ ≠ 0 := by
        intro hγ
        exact hm (by linear_combination -hβγ + β * hβ + γ * hγ)
      have : (D : Matrix (Fin d) (Fin d) K) c c = κ := by
        have e : γ * ((D : Matrix (Fin d) (Fin d) K) c c - κ) = 0 := by linear_combination kc
        exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hγ)
      linear_combination ki - this + hcc
    · have : (D : Matrix (Fin d) (Fin d) K) b b = κ := by
        have e : β * ((D : Matrix (Fin d) (Fin d) K) b b - κ) = 0 := by linear_combination kb
        exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hβ)
      linear_combination ki - this + hbb
  refine ⟨hτ, Units.mk0 _ hDaa, fun i hi j => ?_⟩
  rw [Units.val_mk0]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    exact ⟨hconst i hi, hconst i hi⟩
  · rw [ite_eq_right hij]
    exact ⟨(hisoI i hi j (Ne.symm hij)).2, (hisoI i hi j (Ne.symm hij)).1⟩

end CFSG.ComponentClassification.GSThmB.QPUCl
