module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5Mat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Lift

variable {k : Type} [Field k]

theorem exists_lift_sq_eq_one_of_odd {n : ℕ} (hn : Odd n) {t : projectiveSL n k} (ht : t ^ 2 = 1) :
    ∃ U : SpecialLinearGroup (Fin n) k, proj n k U = t ∧ U ^ 2 = 1 := by
  obtain ⟨U₀, rfl⟩ := proj_surjective n k t
  have hs : U₀ ^ 2 ∈ scalars n k := by
    rw [← proj_eq_one_iff, map_pow, ht]
  obtain ⟨c, hcn, hcU⟩ := mem_scalars.1 hs
  refine ⟨U₀ ^ n, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hn
    calc proj n k (U₀ ^ n) = (proj n k U₀ ^ 2) ^ m * proj n k U₀ := by
          rw [map_pow, ← pow_mul, ← pow_succ, ← hm]
      _ = proj n k U₀ := by rw [ht, one_pow, one_mul]
  · have h : ((U₀ ^ 2) ^ n : SpecialLinearGroup (Fin n) k) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hcU, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
        ← Units.val_pow_eq_pow_val, hcn, Units.val_one, map_one]
    rw [← pow_mul, mul_comm n 2, pow_mul, h]

theorem mul_comm_of_conjAut_proj_eq_of_odd {n : ℕ} (hn : Odd n) {M : GL (Fin n) k}
    {U : SpecialLinearGroup (Fin n) k} (hU2 : U ^ 2 = 1)
    (hfix : LinearFlag.conjAut n k M (proj n k U) = proj n k U) :
    M * Matrix.SpecialLinearGroup.toGL U = Matrix.SpecialLinearGroup.toGL U * M := by
  rw [conjAut_proj, proj_eq_proj_iff] at hfix
  obtain ⟨c, hcn, hc⟩ := mem_scalars.1 hfix
  set W := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n k M U with hW
  have hWm : Matrix.SpecialLinearGroup.toGL W = M * Matrix.SpecialLinearGroup.toGL U * M⁻¹ := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hW, coe_slConjugation, Units.val_mul,
      Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hWU : Matrix.SpecialLinearGroup.toGL (W⁻¹ * U) = GeneralLinearGroup.scalar (Fin n) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, GeneralLinearGroup.coe_scalar]
  set u := Matrix.SpecialLinearGroup.toGL U with hu
  set s := GeneralLinearGroup.scalar (Fin n) c with hs
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, ← sq, hU2, map_one]
  have hUWs : u = M * u * M⁻¹ * s := by
    rw [← hWU, map_mul, map_inv, ← hWm, mul_inv_cancel_left]
  have hsc : ∀ g : GL (Fin n) k, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute c g
  have hs2 : s * s = 1 := by
    have h1 : u * u = (M * u * M⁻¹) * (M * u * M⁻¹) * (s * s) := by
      conv_lhs => rw [hUWs]
      rw [show M * u * M⁻¹ * s * (M * u * M⁻¹ * s) = M * u * M⁻¹ * (s * (M * u * M⁻¹)) * s by
        group]
      rw [hsc (M * u * M⁻¹)]
      group
    have h2 : (M * u * M⁻¹) * (M * u * M⁻¹) = 1 := by
      calc (M * u * M⁻¹) * (M * u * M⁻¹) = M * (u * u) * M⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [h2, one_mul, hu2] at h1
    exact h1.symm
  have hsn : s ^ n = 1 := by
    rw [hs, ← map_pow, hcn, map_one]
  have hs1 : s = 1 := by
    obtain ⟨m, hm⟩ := hn
    have key : s ^ n = (s ^ 2) ^ m * s := by rw [← pow_mul, ← pow_succ, ← hm]
    rw [hsn, sq, hs2, one_pow, one_mul] at key
    exact key.symm
  rw [hs1, mul_one] at hUWs
  calc M * u = M * u * M⁻¹ * M := by group
    _ = u * M := by rw [← hUWs]

end Lift

section Diag

variable {F : Type} [Field F]

theorem diagonal_mul_comm_of_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {d e : ι → F}
    (he : ∀ i j, d i = d j → e i = e j) {N : Matrix ι ι F}
    (h : diagonal d * N = N * diagonal d) : diagonal e * N = N * diagonal e := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : d i = d j
  · rw [he i j hij, mul_comm]
  · rw [apply_eq_zero_of_diagonal_mul_comm h hij, mul_zero, zero_mul]

theorem diagonal_mul_comm_of_mem_coordBlockSL {n : ℕ} {d : Fin n → F} {J : Finset (Fin n)}
    (hJ : ∀ i ∈ J, ∀ j ∈ J, d i = d j) {B : SpecialLinearGroup (Fin n) F}
    (hB : B ∈ coordBlockSL F J) :
    diagonal d * (B : Matrix (Fin n) (Fin n) F) = (B : Matrix (Fin n) (Fin n) F) * diagonal d := by
  rw [mem_coordBlockSL_iff] at hB
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hi : i ∈ J
  · by_cases hj : j ∈ J
    · rw [hJ i hi j hj, mul_comm]
    · rw [hB i j (Or.inr hj)]
      split_ifs with hij
      · subst hij
        ring
      · ring
  · rw [hB i j (Or.inl hi)]
    split_ifs with hij
    · subst hij
      ring
    · ring

theorem exists_sl_subfield_eq {n : ℕ} {F₀ : Subfield F} {Z : SpecialLinearGroup (Fin n) F}
    (hZ : ∀ i j, (Z : Matrix (Fin n) (Fin n) F) i j ∈ F₀) :
    ∃ Z₀ : SpecialLinearGroup (Fin n) F₀, SpecialLinearGroup.map F₀.subtype Z₀ = Z := by
  let A : Matrix (Fin n) (Fin n) F₀ := fun i j => ⟨(Z : Matrix (Fin n) (Fin n) F) i j, hZ i j⟩
  have hA : F₀.subtype.mapMatrix A = (Z : Matrix (Fin n) (Fin n) F) := rfl
  have hdet : A.det = 1 := by
    apply Subtype.val_injective
    change F₀.subtype A.det = F₀.subtype 1
    rw [map_one, RingHom.map_det, hA]
    exact Z.2
  refine ⟨⟨A, hdet⟩, ?_⟩
  ext i j
  rfl

end Diag

section Block

variable {k : Type} [Field k] [Finite k]

theorem glaPLayer_ne_bot_of_diagonal_block [CharP k 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : k ≃+* k} (hpk₀ : p ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {X : GL (Fin p) k} {d : Fin p → k} (hX : (X : Matrix (Fin p) (Fin p) k) = diagonal d)
    {a a' c : Fin p} (haa' : a ≠ a') (hda : d a = d a') (hdc : d c ≠ d a) :
    GLAPLayer p (fixSubgroup (fieldAut p k σ) ⊓ fixSubgroup (LinearFlag.conjAut p k X)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set k₀ := semilinearFixedSubfield σ with hk₀def
  have hσk₀ : ∀ x ∈ k₀, σ x = x := fun x hx => RingHom.mem_eqLocusField.mp hx
  have hk₀4 : 4 ≤ Nat.card k₀ := by
    have h1 : 1 < Nat.card k₀ := Finite.one_lt_card
    have h2 : p ≤ Nat.card k₀ - 1 := Nat.le_of_dvd (by omega) hpk₀
    have h3 : 2 ≤ p := hp.two_le
    omega
  have hcard : Fintype.card (Fin p) < 2 * p := by
    rw [Fintype.card_fin]
    have := hp.pos
    omega
  have hd0 : ∀ l, d l ≠ 0 := by
    intro l h0
    have hdet : (X : Matrix (Fin p) (Fin p) k).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    apply hdet
    rw [hX, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ l) h0
  set J : Finset (Fin p) := Finset.univ.filter fun l => d l = d a with hJ
  have hmemJ : ∀ l, l ∈ J ↔ d l = d a := fun l => by simp [hJ]
  have haJ : a ∈ J := (hmemJ a).2 rfl
  have ha'J : a' ∈ J := (hmemJ a').2 hda.symm
  have hcJ : c ∉ J := fun h => hdc ((hmemJ c).1 h)
  have hJ2 : 2 ≤ J.card := by
    calc 2 = ({a, a'} : Finset (Fin p)).card := (Finset.card_pair haa').symm
      _ ≤ J.card := Finset.card_le_card (by
          intro l hl
          rcases Finset.mem_insert.1 hl with rfl | hl
          · exact haJ
          · rw [Finset.mem_singleton.1 hl]
            exact ha'J)
  have hdJ : ∀ i ∈ J, ∀ j ∈ J, d i = d j := fun i hi j hj =>
    ((hmemJ i).1 hi).trans ((hmemJ j).1 hj).symm
  have hιapp : ∀ (g : SpecialLinearGroup (Fin p) k₀) i j,
      ((SpecialLinearGroup.map k₀.subtype g : SpecialLinearGroup (Fin p) k) :
        Matrix (Fin p) (Fin p) k) i j = ((g : Matrix (Fin p) (Fin p) k₀) i j : k) :=
    fun g i j => rfl
  have hιinj : Function.Injective
      (SpecialLinearGroup.map k₀.subtype : SpecialLinearGroup (Fin p) k₀ →* _) := by
    intro g g' h
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have := congrArg (fun A : SpecialLinearGroup (Fin p) k => (A : Matrix (Fin p) (Fin p) k) i j) h
    simp only [hιapp] at this
    exact Subtype.val_injective this
  have hιJ : ∀ g ∈ coordBlockSL k₀ J, SpecialLinearGroup.map k₀.subtype g ∈ coordBlockSL k J := by
    intro g hg
    rw [mem_coordBlockSL_iff] at hg ⊢
    intro i j hij
    rw [hιapp, hg i j hij]
    split_ifs <;> simp
  have hσι : ∀ g : SpecialLinearGroup (Fin p) k₀,
      SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map k₀.subtype g) =
        SpecialLinearGroup.map k₀.subtype g := by
    intro g
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hσk₀ _ ((g : Matrix (Fin p) (Fin p) k₀) i j).2
  set ψ : ↥(coordBlockSL k₀ J) →* projectiveSL p k :=
    (proj p k).comp ((SpecialLinearGroup.map k₀.subtype).comp (coordBlockSL k₀ J).subtype)
    with hψdef
  have hψ : ∀ g, ψ g = proj p k (SpecialLinearGroup.map k₀.subtype (g : SpecialLinearGroup (Fin p) k₀)) :=
    fun g => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hψ, proj_eq_one_iff] at hg
    obtain ⟨ν, -, hν⟩ := mem_scalars.1 hg
    have hgc := mem_coordBlockSL_iff.1 g.2 c c (Or.inl hcJ)
    have hν1 : (ν : k) = 1 := by
      have h := congrFun (congrFun hν c) c
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hιapp, hgc, if_pos rfl] at h
      simpa using h.symm
    have hι1 : SpecialLinearGroup.map k₀.subtype (g : SpecialLinearGroup (Fin p) k₀) = 1 := by
      ext i j
      rw [hν, hν1, map_one, Matrix.SpecialLinearGroup.coe_one]
    apply Subtype.ext
    exact hιinj (hι1.trans (map_one _).symm)
  have hXB : ∀ B ∈ coordBlockSL k J, (X : Matrix (Fin p) (Fin p) k) * (B : Matrix (Fin p) (Fin p) k) =
      (B : Matrix (Fin p) (Fin p) k) * X := by
    intro B hB
    rw [hX]
    exact diagonal_mul_comm_of_mem_coordBlockSL hdJ hB
  have hLH : ψ.range ≤ fixSubgroup (fieldAut p k σ) ⊓ fixSubgroup (LinearFlag.conjAut p k X) := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSubgroup, hψ, fieldAut_proj, hσι]
    · rw [mem_fixSubgroup, hψ, conjAut_proj]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, hXB _ (hιJ _ g.2), Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hN : (ψ.range.subgroupOf
      (fixSubgroup (fieldAut p k σ) ⊓ fixSubgroup (LinearFlag.conjAut p k X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLH]
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y₁, rfl⟩ := proj_surjective p k y
    have hyσ := (Subgroup.mem_inf.1 hy).1
    have hyX := (Subgroup.mem_inf.1 hy).2
    rw [mem_fixSubgroup] at hyσ hyX
    rw [conjAut_proj, proj_eq_proj_iff] at hyX
    obtain ⟨ν, hνp, hν⟩ := mem_scalars.1 hyX
    have hY : (Y₁ : Matrix (Fin p) (Fin p) k) =
        (ν : k) • ((X : Matrix (Fin p) (Fin p) k) * (Y₁ : Matrix (Fin p) (Fin p) k) *
          ((X⁻¹ : GL (Fin p) k) : Matrix (Fin p) (Fin p) k)) := by
      set W := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation p k X Y₁
        with hW
      calc (Y₁ : Matrix (Fin p) (Fin p) k) =
            ((W * (W⁻¹ * Y₁) : SpecialLinearGroup (Fin p) k) : Matrix (Fin p) (Fin p) k) := by
            rw [mul_inv_cancel_left]
        _ = (W : Matrix (Fin p) (Fin p) k) * scalar (Fin p) (ν : k) := by
            rw [Matrix.SpecialLinearGroup.coe_mul, hν]
        _ = _ := by
            rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
              hW, coe_slConjugation]
    have hYX : (Y₁ : Matrix (Fin p) (Fin p) k) * diagonal d =
        (ν : k) • (diagonal d * (Y₁ : Matrix (Fin p) (Fin p) k)) := by
      rw [← hX]
      conv_lhs => rw [hY]
      simp only [Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    have hν1 : (ν : k) = 1 := by
      by_contra hne
      have hνp' : (ν : k) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, hνp, Units.val_one]
      have hdet : IsUnit (Y₁ : Matrix (Fin p) (Fin p) k).det := by
        rw [Y₁.2]
        exact isUnit_one
      exact haa' (injective_of_mul_diagonal_eq_smul hp hcard hd0 hνp' hne hdet hYX hda)
    have hYd : diagonal d * (Y₁ : Matrix (Fin p) (Fin p) k) =
        (Y₁ : Matrix (Fin p) (Fin p) k) * diagonal d := by
      rw [hYX, hν1, one_smul]
    have hYP : compIndicator k J * (Y₁ : Matrix (Fin p) (Fin p) k) =
        (Y₁ : Matrix (Fin p) (Fin p) k) * compIndicator k J := by
      rw [compIndicator]
      refine diagonal_mul_comm_of_fiber (fun i j hij => ?_) hYd
      simp only [hmemJ, hij]
    rw [fieldAut_proj, proj_eq_proj_iff] at hyσ
    set w := (SpecialLinearGroup.map σ.toRingHom Y₁)⁻¹ * Y₁ with hw
    have hwc : w ∈ Subgroup.center (SpecialLinearGroup (Fin p) k) := by
      rw [← scalars_eq_center p k]
      exact hyσ
    set B := SpecialLinearGroup.map k₀.subtype (g : SpecialLinearGroup (Fin p) k₀) with hB
    set Z := Y₁ * B * Y₁⁻¹ with hZ
    have hσY : SpecialLinearGroup.map σ.toRingHom Y₁ = Y₁ * w⁻¹ := by
      rw [hw, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    have hZσ : SpecialLinearGroup.map σ.toRingHom Z = Z := by
      have hwB : w⁻¹ * B = B * w⁻¹ :=
        ((Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hwc)) B).symm
      rw [hZ, map_mul, map_mul, map_inv, hσY, hB, hσι, ← hB]
      calc Y₁ * w⁻¹ * B * (Y₁ * w⁻¹)⁻¹ = Y₁ * (w⁻¹ * B) * w * Y₁⁻¹ := by group
        _ = Y₁ * (B * w⁻¹) * w * Y₁⁻¹ := by rw [hwB]
        _ = Y₁ * B * Y₁⁻¹ := by group
    have hZJ : Z ∈ coordBlockSL k J := conj_mem_coordBlockSL hYP (hιJ _ g.2)
    have hZmem : ∀ i j, (Z : Matrix (Fin p) (Fin p) k) i j ∈ k₀ := by
      intro i j
      have := congrArg (fun A : SpecialLinearGroup (Fin p) k => (A : Matrix (Fin p) (Fin p) k) i j)
        hZσ
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at this
      exact RingHom.mem_eqLocusField.mpr this
    obtain ⟨Z₀, hZ₀⟩ := exists_sl_subfield_eq hZmem
    have hZ₀J : Z₀ ∈ coordBlockSL k₀ J := by
      rw [mem_coordBlockSL_iff]
      intro i j hij
      have h := mem_coordBlockSL_iff.1 hZJ i j hij
      rw [← hZ₀, hιapp] at h
      apply Subtype.val_injective
      rw [h]
      split_ifs <;> rfl
    refine ⟨⟨Z₀, hZ₀J⟩, ?_⟩
    rw [hψ]
    show proj p k (SpecialLinearGroup.map k₀.subtype Z₀) = _
    rw [hZ₀, hZ, map_mul, map_mul, map_inv, hB, hψ]
  have hLq : CFSG.Open.IsQuasisimple ↥ψ.range :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MonoidHom.ofInjective hψinj).symm (isQuasisimple_coordBlockSL hJ2 hk₀4)
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd (F := k₀) hp hpk₀
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set f : Fin p → k₀ := fun l => if l = a then ζ else if l = a' then ζ⁻¹ else 1 with hf
  have hfa : f a = ζ := if_pos rfl
  have hfa' : f a' = ζ⁻¹ := by
    show (if a' = a then ζ else if a' = a' then ζ⁻¹ else 1) = ζ⁻¹
    rw [if_neg haa'.symm, if_pos rfl]
  have hfo : ∀ l, l ≠ a → l ≠ a' → f l = 1 := fun l h1 h2 => by
    show (if l = a then ζ else if l = a' then ζ⁻¹ else 1) = 1
    rw [if_neg h1, if_neg h2]
  have hfdet : ∏ l, f l = 1 := by
    have hsub : ∀ l ∈ (Finset.univ : Finset (Fin p)), l ∉ ({a, a'} : Finset (Fin p)) → f l = 1 := by
      intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hfo l hl.1 hl.2
    rw [← Finset.prod_subset (Finset.subset_univ _) hsub, Finset.prod_pair haa', hfa, hfa',
      mul_inv_cancel₀ hζ0]
  have hfp : ∀ l, f l ^ p = 1 := by
    intro l
    by_cases h1 : l = a
    · rw [h1, hfa, hζ.pow_eq_one]
    · by_cases h2 : l = a'
      · rw [h2, hfa', inv_pow, hζ.pow_eq_one, inv_one]
      · rw [hfo l h1 h2, one_pow]
  let g₁ : SpecialLinearGroup (Fin p) k₀ := ⟨diagonal f, by rw [Matrix.det_diagonal, hfdet]⟩
  have hg₁m : (g₁ : Matrix (Fin p) (Fin p) k₀) = diagonal f := rfl
  have hg₁J : g₁ ∈ coordBlockSL k₀ J := by
    rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [hg₁m]
    by_cases h : i = j
    · subst h
      rw [diagonal_apply_eq, if_pos rfl]
      have hi : i ∉ J := by tauto
      exact hfo i (fun h' => hi (h' ▸ haJ)) (fun h' => hi (h' ▸ ha'J))
    · rw [diagonal_apply_ne _ h, if_neg h]
  have hg₁p : g₁ ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hg₁m, diagonal_pow,
      ← diagonal_one]
    congr 1
    funext l
    exact hfp l
  have htJ := transvection_mem_coordBlockSL haJ ha'J haa' (1 : k₀)
  have hnc : g₁ * Matrix.SpecialLinearGroup.transvection haa' (1 : k₀) ≠
      Matrix.SpecialLinearGroup.transvection haa' (1 : k₀) * g₁ := by
    intro h
    have h' := congrArg (fun A : SpecialLinearGroup (Fin p) k₀ =>
      (A : Matrix (Fin p) (Fin p) k₀) a a') h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hg₁m,
      CFSG.ClassicalInvolution.RouteD.Gaps.coe_transvection_eq, diagonal_mul, mul_diagonal] at h'
    simp [Matrix.add_apply, Matrix.one_apply, haa', Matrix.single_apply] at h'
    rw [hfa, hfa'] at h'
    have hζ2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h']
      exact mul_inv_cancel₀ hζ0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((hζ.pow_eq_one_iff_dvd 2).1 hζ2))
  set eJ := MonoidHom.ofInjective hψinj with heJ
  set x : ↥ψ.range := eJ ⟨g₁, hg₁J⟩ with hx
  set y : ↥ψ.range := eJ ⟨_, htJ⟩ with hy
  have hxy : x * y ≠ y * x := by
    intro h
    rw [hx, hy, ← map_mul, ← map_mul] at h
    exact hnc (congrArg (fun z : ↥(coordBlockSL k₀ J) => (z : SpecialLinearGroup (Fin p) k₀))
      (eJ.injective h))
  have hxp : x ^ p = 1 := by
    rw [hx, ← map_pow]
    have h1 : (⟨g₁, hg₁J⟩ : ↥(coordBlockSL k₀ J)) ^ p = 1 := Subtype.ext hg₁p
    rw [h1, map_one]
  have hxc : x ∉ Subgroup.center ↥ψ.range := fun hxc =>
    hxy (Subgroup.mem_center_iff.1 hxc y).symm
  have hdvd : p ∣ Nat.card (↥ψ.range ⧸ Subgroup.center ↥ψ.range) := by
    have hord : orderOf (x : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = p := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
      · intro h
        exact hxc ((QuotientGroup.eq_one_iff x).1 h)
    have h := orderOf_dvd_natCard (x : ↥ψ.range ⧸ Subgroup.center ↥ψ.range)
    rwa [hord] at h
  exact Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp hLH hN hLq hdvd

end Block

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
