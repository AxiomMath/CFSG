module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthPc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOddJ
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlPc

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL)
open CFSG.ComponentClassification.GSThmB.X10Orth (sign01_pi4 sign02_pi4 kronI_diag_pi4_ne
  pi4_permMatrix_sq commutator_perm4 pi4 projH_sq_of_scalar projH_comm_of_scalar projH_ne_one
  signGL_ne_scalar pairSet_props pairSet_symmDiff symmDiff_pair_pair signGL_mul_signGL)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem exists_e8_isoCent_pc (hK : ringChar K ≠ 2) {c : K} {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K}
    (hRm : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {A : GL (Fin (2 * n)) K}
    (hgA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    ∃ X Y Z : GL (Fin (2 * n)) K,
      X ∈ (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) ∧
      Y ∈ (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) ∧
      Z ∈ (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) ∧
      ∀ (hXH : X ∈ matrixDerived (oQ R)) (hYH : Y ∈ matrixDerived (oQ R))
        (hZH : Z ∈ matrixDerived (oQ R)),
        X10Orth.E8Triple (projH _ (⟨X, hXH⟩ : matrixDerived (oQ R))) (projH _ ⟨Y, hYH⟩)
          (projH _ ⟨Z, hZH⟩) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsign : ∀ i i' : Fin n, i ≠ i' → signGL K (pairSet {i, i'}) ∈
      (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) :=
    fun i i' hii' => X10Orth.kron_signPair_mem hRm hgA hii'
  rcases Nat.lt_or_ge 4 n with h5 | h4
  ·
    set i₀ : Fin n := ⟨0, by omega⟩
    set i₁ : Fin n := ⟨1, by omega⟩
    set i₂ : Fin n := ⟨2, by omega⟩
    set i₃ : Fin n := ⟨3, by omega⟩
    have hd : ∀ a b : Fin n, (a : ℕ) ≠ b → a ≠ b := fun a b hab h' => hab (by rw [h'])
    have h01 := hd i₀ i₁ (by simp [i₀, i₁])
    have h02 := hd i₀ i₂ (by simp [i₀, i₂])
    have h03 := hd i₀ i₃ (by simp [i₀, i₃])
    have h12 := hd i₁ i₂ (by simp [i₁, i₂])
    have h13 := hd i₁ i₃ (by simp [i₁, i₃])
    have h23 := hd i₂ i₃ (by simp [i₂, i₃])
    exact ⟨_, _, _, hsign _ _ h01, hsign _ _ h02, hsign _ _ h03,
      fun hX hY hZ => X10Orth.e8Triple_kron_sign h2 h5 h01 h02 h03 h12 h13 h23 hX hY hZ⟩
  ·
    obtain rfl : n = 4 := by omega
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
    set τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    set W := kronGL K 4 ⁅permGL K 4 σ, permGL K 4 τ⁆ with hWdef
    have hWm : (W : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (pi4.permMatrix K) := by
      rw [hWdef, coe_kronGL, coe_commutator_permGL, commutator_perm4]
    have hW := X10Orth.kron_perm_mem (K := K) hRm hgA σ τ
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h12 : (1 : Fin 4) ≠ 2 := by decide
    refine ⟨_, _, _, hsign _ _ h01, hsign _ _ h02, hW, fun hX hY hZ => ?_⟩
    have hXm : ((signGL K (pairSet ({0, 1} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 1}) := by
      rw [coe_signGL, kronI_signMat]
    have hYm : ((signGL K (pairSet ({0, 2} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 2}) := by
      rw [coe_signGL, kronI_signMat]
    have hsq : ∀ T : Finset (Fin (2 * 4)), signGL K T * signGL K T = 1 := fun T =>
      Units.ext (by rw [Units.val_mul, coe_signGL, signMat_mul_self, Units.val_one])
    have hWW : W * W = 1 := Units.ext (by
      rw [Units.val_mul, hWm, ← map_mul, pi4_permMatrix_sq, map_one, Units.val_one])
    have hXW : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 * (W * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hXm, hWm, ← map_mul, ← map_mul, sign01_pi4]
    have hYW : signGL K (pairSet ({0, 2} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (W * signGL K (pairSet {0, 2})) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hYm, hWm, ← map_mul, ← map_mul,
        sign02_pi4, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_neg, Units.val_one,
        ← Matrix.smul_one_eq_diagonal, neg_one_smul, Matrix.neg_mul, Matrix.one_mul, map_neg]
    have hXY : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * signGL K (pairSet {0, 2}) =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 *
          (signGL K (pairSet {0, 2}) * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul, signGL_mul_signGL, signGL_mul_signGL, symmDiff_comm]
    have hne_d : ∀ (v : Fin 4 → K) (Z : matrixDerived (oQ R)),
        ((Z : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          kronI K 4 (diagonal v * pi4.permMatrix K) → projH _ Z ≠ 1 := fun v Z hZ =>
      projH_ne_one fun c' hc' => kronI_diag_pi4_ne v c' (by rw [← hZ, hc'])
    have hsgn : ∀ (T : Finset (Fin 4)) (Z : matrixDerived (oQ R)), T.Nonempty → Tᶜ.Nonempty →
        (Z : GL (Fin (2 * 4)) K) = signGL K (pairSet T) → projH _ Z ≠ 1 :=
      fun T Z h1 h1' hZ => projH_ne_one fun c' hc' => signGL_ne_scalar h2
        (pairSet_props ⟨h1, h1'⟩).1 (pairSet_props ⟨h1, h1'⟩).2 c' (hZ.symm.trans hc')
    have hone : GeneralLinearGroup.scalar (Fin (2 * 4)) (1 : Kˣ) = 1 := map_one _
    refine ⟨projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hWW),
      projH_comm_of_scalar 1 hXY, projH_comm_of_scalar 1 hXW, projH_comm_of_scalar (-1) hYW,
      hsgn {0, 1} _ (by decide) ⟨2, by decide⟩ rfl, hsgn {0, 2} _ (by decide) ⟨1, by decide⟩ rfl,
      hne_d (fun _ => 1) _ (by rw [hWm, diagonal_one, Matrix.one_mul]), ?_, ?_, ?_, ?_⟩
    · rw [← map_mul]
      refine hsgn {1, 2} _ (by decide) ⟨0, by decide⟩ ?_
      change signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) = _
      rw [signGL_mul_signGL, ← pairSet_symmDiff, symmDiff_pair_pair h01 h02 h12]
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hXm, hWm, ← map_mul]
      rfl
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hYm, hWm, ← map_mul]
      rfl
    · rw [← map_mul, ← map_mul]
      refine hne_d ((fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) *
        fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, Units.val_mul, hXm, hYm, hWm, ← map_mul, ← map_mul, signMat, signMat,
        diagonal_mul_diagonal]
      rfl

variable [Finite K]

theorem false_of_x_pc (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ f)
    {m : ℕ} (hm : 4 ≤ m) {R : GL (Fin (2 * m)) K}
    (hR : (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ = R) {A : matrixDerived (oQ R)}
    (hA2 : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
      ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = -1)
    {J : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hJC : J ≤ centralizer ({projH _ A} : Set (StatedProj (matrixDerived (oQ R)))))
    (hJc : IsPComponent 2 (J.subgroupOf
      (centralizer ({projH _ A} : Set (StatedProj (matrixDerived (oQ R)))))))
    (hJ8 : ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ X10Orth.E8Triple u v w) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hAI : (A : GL (Fin (2 * m)) K) ∈ matrixIsometries (oQ R) :=
    matrixDerived_le_isometries _ A.2
  have hARR : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R *
      ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = R := by
    have := hAI
    rw [matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup] at this
    exact this
  have hA2' : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
      ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = (-1 : K) • 1 := by
    rw [hA2, neg_one_smul]
  have hAR : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
        ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)) := by
    set M := ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) with hM
    calc Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)
        = Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) * (M * -M) := by
          rw [Matrix.mul_neg, hA2, neg_neg, Matrix.mul_one]
      _ = (-1 : K) • ((R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) * M) := by
          rw [← Matrix.mul_assoc (Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)) M (-M), hARR,
            Matrix.mul_neg, neg_one_smul]
  obtain ⟨H, hgram, hAH⟩ := exists_pc_basis hK hR (neg_ne_zero.2 one_ne_zero) hA2' hAR
    (fun _ => 1) (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * m) K H * R * H :=
    ⟨_, rfl⟩
  have hgramR : (H : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R * H = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = blkDiag m (wMat 1 (-(-1))) := by
    rw [← hgramR, hgram]
    simp only [one_smul]
    rfl
  have hR₁s : (R₁ : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ = R₁ := by
    rw [hR₁m, blkDiag_transpose, wMat, diagonal_transpose]
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR (g := linPair _ hAI) rfl
  set Θ := oTransport H⁻¹ 1 hS with hΘ
  set A₁ := derivedTransport H⁻¹ 1 hS A with hA₁
  have hAm : ((A₁ : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) =
      blkDiag m (jMat (-1)) := by
    rw [hA₁, coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
    exact inv_mul_mul_eq hAH
  have hxA : Θ (projH _ A) = projH _ A₁ := by rw [hΘ, oTransport_proj]
  set J₁ := J.map Θ.toMonoidHom with hJ₁
  have hJ₁C : J₁ ≤ centralizer ({projH _ A₁} : Set (StatedProj (matrixDerived (oQ R₁)))) := by
    rw [← hxA, ← CatFactsSp4.map_centralizer_singleton]
    exact map_mono hJC
  have hJ₁c : IsPComponent 2 (J₁.subgroupOf
      (centralizer ({projH _ A₁} : Set (StatedProj (matrixDerived (oQ R₁)))))) := by
    have := CatFactsSp4.isPComponent_map_subgroupOf 2 Θ hJC hJc
    rwa [CatFactsSp4.map_centralizer_singleton, hxA] at this
  set Z := isoCent R₁ (A₁ : GL (Fin (2 * m)) K) with hZ
  have hq := C.isQuasisimple_isoCent_pc hK hℓ hKc (neg_ne_zero.2 one_ne_zero) (by omega) hR₁m hAm
  have hZΩ : ⁅Z, Z⁆ ≤ matrixDerived (oQ R₁) := by
    rw [matrixDerived_oQ h2 R₁ hR₁s]
    exact commutator_mono inf_le_left inf_le_left
  set N := ((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R₁))).map (projH _) with hN
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := C.commutator_eq_of_isPComponent hJ₁C hJ₁c
  have hJ₁N : J₁ ≤ N := by
    refine (C.le_map_commutator_of_perfect A₁ hJ₁C hJ₁p).trans (map_mono ?_)
    rw [commutator_le]
    intro B hB B' hB'
    rw [mem_subgroupOf]
    have hZB : ∀ {C : matrixDerived (oQ R₁)}, C ∈ centralizer ({A₁} : Set _) →
        (C : GL (Fin (2 * m)) K) ∈ Z := by
      intro C hC
      refine ⟨?_, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hC))⟩
      have := matrixDerived_le_isometries (oQ R₁) C.2
      rwa [matrixIsometries_oQ h2 R₁ hR₁s] at this
    exact commutator_mem_commutator (hZB hB) (hZB hB')
  have hNC : N ≤ centralizer ({projH _ A₁} : Set (StatedProj (matrixDerived (oQ R₁)))) := by
    rintro _ ⟨g, hg, rfl⟩
    replace hg : (g : GL (Fin (2 * m)) K) ∈ ⁅Z, Z⁆ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgZ : (g : GL (Fin (2 * m)) K) ∈ Z := commutator_le_self _ hg
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgZ).2
  have hNq : IsQuasisimple N := by
    set φ := (projH (matrixDerived (oQ R₁))).comp
      (((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R₁))).subtype.comp
        (subgroupOfEquivOfLe hZΩ).symm.toMonoidHom) with hφ
    have hφr : φ.range = N := by
      rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
        (subgroupOfEquivOfLe hZΩ).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq φ with h | h
    · exfalso
      rw [hφr] at h
      rw [h, le_bot_iff] at hJ₁N
      exact C.ne_bot_of_isPComponent hJ₁C hJ₁c hJ₁N
    · rwa [hφr] at h
  have heq : J₁ = N := C.eq_of_le_of_isQuasisimple hJ₁N hNC hJ₁c hNq
  obtain ⟨X, Y, W, hX, hY, hW, hT⟩ := exists_e8_isoCent_pc hK hm hR₁m hAm
  have hin : ∀ (V : GL (Fin (2 * m)) K) (hV : V ∈ ⁅Z, Z⁆),
      projH _ (⟨V, hZΩ hV⟩ : matrixDerived (oQ R₁)) ∈ J₁ := fun V hV => by
    rw [heq]
    exact ⟨⟨V, hZΩ hV⟩, mem_subgroupOf.2 hV, rfl⟩
  have hT' := hT (hZΩ hX) (hZΩ hY) (hZΩ hW)
  obtain ⟨u, hu, hu'⟩ := hin X hX
  obtain ⟨v, hv, hv'⟩ := hin Y hY
  obtain ⟨w, hw, hw'⟩ := hin W hW
  refine hJ8 u hu v hv w hw (X10Orth.E8Triple.comap (φ := Θ.toMonoidHom) Θ.injective ?_)
  rw [hu', hv', hw']
  exact hT'

end CFSG.ComponentClassification.GSThmB.Orth516
