module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOOddNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSpin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Lift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL slRingEquiv
  conj_injective_of_mulEquiv)
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

theorem eq_one_or_negOne_of_mem_center_spinOdd {K : Type} [Field K] [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hn : 3 ≤ n) {x : spinGroup (quadOdd n K)} (hx : x ∈ center (spinGroup (quadOdd n K))) :
    x = 1 ∨ x = spinGroup.negOne (quadOdd n K)
      (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n K h2)).ne_zero := by
  obtain ⟨-, hker1, hker2⟩ := spinToStatedProj_quadOdd h2 hn
  rw [← hker2, hker1, mem_comap] at hx
  obtain ⟨c, hc⟩ := hx
  set z : Fin n ⊕ Fin n ⊕ Unit → K := Pi.single (.inr (.inr ())) 1 with hz
  have hQz : quadOdd n K z = 1 := by
    rw [quadOdd_apply]
    simp [hz]
  have hcz := spinMatrix_mulVec (quadOdd n K) x z
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hcz
  have hcz2 : (diagonal fun _ => (c : K)) *ᵥ z = (c : K) • z := by
    funext i
    rw [mulVec_diagonal]
    simp
  have hQc := map_spinAction (quadOdd n K) x z
  rw [← hcz, hcz2, QuadraticMap.map_smul, hQz, smul_eq_mul, mul_one] at hQc
  have hdet : ((spinMatrix (quadOdd n K) x : GL (Fin n ⊕ Fin n ⊕ Unit) K) :
      Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K).det = 1 := by
    have hmem : spinMatrix (quadOdd n K) x ∈ StatedOmega (StatedQuadOdd n K) :=
      spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadOdd h2 hn) x
    have hle : StatedOmega (StatedQuadOdd n K) ≤
        (Matrix.GeneralLinearGroup.det : GL (Fin n ⊕ Fin n ⊕ Unit) K →* Kˣ).ker := by
      refine (Subgroup.commutator_mono le_top le_top).trans ?_
      exact Abelianization.commutator_subset_ker _
    have h1 := hle hmem
    rw [MonoidHom.mem_ker] at h1
    have h2' := congrArg Units.val h1
    simpa using h2'
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
    Finset.prod_const, Finset.card_univ] at hdet
  have hcard : Fintype.card (Fin n ⊕ Fin n ⊕ Unit) = 2 * n + 1 := by simp; ring
  rw [hcard, pow_succ, pow_mul, pow_two, hQc, one_pow, one_mul] at hdet
  have hc1 : c = 1 := Units.ext hdet
  have hx1 : spinAction (quadOdd n K) x = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [← spinMatrix_mulVec, ← hc, hc1, map_one]
    simp
  exact (mem_ker_spinAction_iff (quadOdd n K)
    (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n K h2)) x).1 hx1

theorem commutator_range_of_perfect {G H : Type*} [Group G] [Group H] (hG : Group.IsPerfect G)
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    hG.commutator_eq_top]

theorem odd_twin_comap {L₀ : Type} [Field L₀] [Finite L₀] (hK : ringChar L₀ ≠ 2)
    (hK5 : 5 ≤ Nat.card L₀) {d : ℕ} (hd5 : 5 ≤ d) {w : Fin d → L₀} (hw : ∀ i, w i ≠ 0)
    {α a : L₀} (hW : OSliceW (by omega : 4 ≤ d) w α a) (hker : OKer (oQ (diagGL hw)))
    {X : Type} [Group X] [Finite X] (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ (diagGL hw)))) {t : X}
    (ht : socleAction θ t = oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet))
    (hcore : ∀ y ∈ oddCoreIn (socleAction θ).range (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)),
      ∃ (R : GL (Fin d) L₀) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
        R ∈ oIsoBlock L₀ hw jSet ∧ y = oκ _ (linPair R hR))
    {Y : Subgroup X} (hY1 : Y ≠ ⊥) (hY2 : Y ≤ oddCentralizerCore t) {p f : ℕ} [Fact p.Prime]
    (hKc : Nat.card L₀ = p ^ f) :
    ∃ ū : X, orderOf ū = 2 ∧
      Nonempty ((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) ≃*
        SL(2, GaloisField p f)) ∧
      Nonempty ((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) ≃*
        SL(2, GaloisField p f)) ∧
      (∀ x ∈ (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ),
        ∀ y ∈ (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ), x * y = y * x) ∧
      ū ∈ (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) ∧
      ū ∈ (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) ∧
      (∀ x, x ∈ (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) →
        x ∈ (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) → x = 1 ∨ x = ū) ∧
      (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) ≤ centralizer ({ū} : Set X) ∧
      (((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)).subgroupOf
        (centralizer ({ū} : Set X))).IsSubnormal ∧
      (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) ≤ centralizer ({ū} : Set X) ∧
      (((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)).subgroupOf
        (centralizer ({ū} : Set X))).IsSubnormal ∧
      ActsProperly t Y ((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)) ⊥ ∧
      ActsProperly t Y ((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)) ⊥ := by
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ (socleAction θ).range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hYne : Y.map (socleAction θ) ≠ ⊥ := fun hmap =>
    hY1 ((map_eq_bot_iff_of_injective _ hψ).1 hmap)
  have hYO : Y.map (socleAction θ) ≤
      oddCoreIn (socleAction θ).range (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) := by
    rw [← ht, ← map_oddCentralizerCore_of_injective hψ]
    exact map_mono hY2
  obtain ⟨hu, ⟨e₁⟩, ⟨e₂⟩, hcommS, hu₁, hu₂, hint, hS₁u, hc₁, hS₂u, hc₂⟩ :=
    slice_twin_props hK hK5 hd5 hw hW hinj hInn
  have hprop₁ := slice_two_actsProperly_L hK hK5 hd5 hw hW hker hinj hcore hYne hYO
  have hprop₂ := slice_two_actsProperly_R hK hK5 hd5 hw hW hker hinj hcore hYne hYO
  rw [← ht] at hprop₁ hprop₂
  have : Fintype L₀ := Fintype.ofFinite L₀
  have : CharP L₀ p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let : Algebra (ZMod p) L₀ := ZMod.algebra L₀ p
  have eK : SL(2, L₀) ≃* SL(2, GaloisField p f) :=
    slRingEquiv (m := Fin 2) (GaloisField.algEquivGaloisField p f hKc).toRingEquiv
  obtain ⟨ū, -, h⟩ := twin_comap hψ (slice_le_range.trans hInn) (slice_le_range.trans hInn)
    (hInn ⟨_, rfl⟩) hu (e₁.trans eK) (e₂.trans eK) hcommS hu₁ hu₂ hint hS₁u hc₁ hS₂u hc₂ hprop₁
    hprop₂
  exact ⟨ū, h⟩

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem mem_twin_sup_of_spinOdd {L₀ : Type} [Field L₀] [Finite L₀] (hK : ringChar L₀ ≠ 2)
    (hK5 : 5 ≤ Nat.card L₀) {n : ℕ} (hn : 3 ≤ n) (hd5 : 5 ≤ 2 * n + 1)
    {w : Fin (2 * n + 1) → L₀} (hw : ∀ i, w i ≠ 0) {α a : L₀}
    (hW : OSliceW (by omega : 4 ≤ 2 * n + 1) w α a) {Q₁ : QuadraticForm L₀ (Fin (2 * n + 1) → L₀)}
    (S₁ : GL (Fin (2 * n + 1)) L₀) (ν₁ : L₀ˣ)
    (hS₁ : ∀ v, Q₁ (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm (oddIndexEquiv n) (quadOdd n L₀) v)
    (S₂ : GL (Fin (2 * n + 1)) L₀) (ν₂ : L₀ˣ) (hS₂ : ∀ v, oQ (diagGL hw) (S₂.val *ᵥ v) = ν₂ * Q₁ v)
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
    (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ (diagGL hw))))
    {c : K ⧸ pPrimeCore 2 K} (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hc1 : c ≠ 1) :
    c ∈ ⁅((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K),
        ((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K)⁆ ⊔
      ⁅((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K),
        ((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K)⁆ := by
  have h2 : (2 : L₀) ≠ 0 := Ring.two_ne_zero hK
  have : Invertible (2 : L₀) := invertibleOfNonzero h2
  have hψ := socleAction_injective hsimple hnab θ
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hsocle := mem_socle_iff hsimple hnab θ
  have hRs := range_spinMatrix_quadOdd h2 hn
  let Θ := (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n L₀)
    (coe_quadOdd n L₀)).trans ((oTransport S₁ ν₁ hS₁).trans (oTransport S₂ ν₂ hS₂))
  let fS : spinGroup (quadOdd n L₀) →* MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
    (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).comp
        (Θ.toMonoidHom.comp (spinToStatedProj (quadOdd n L₀) hRs))
  have hfS : ∀ x, fS x = MulAut.conj (Θ (spinToStatedProj (quadOdd n L₀) hRs x)) :=
    fun _ => rfl
  have hfSr : ∀ x, fS x ∈ (socleAction θ).range := fun x => conj_mem_range_socleAction θ _
  let β : spinGroup (quadOdd n L₀) →* (rhoZ K).range := factorHom hψ fS hfSr
  have hβ : ∀ g, socleAction θ (β g) = fS g := factorHom_spec hψ fS hfSr
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [hβ, hfS]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := Θ.surjective y
      obtain ⟨g, rfl⟩ := (spinToStatedProj_quadOdd h2 hn).1 z
      refine ⟨g, hψ ?_⟩
      rw [hβ, hfS]
      exact hy
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup (quadOdd n L₀)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : spinGroup (quadOdd n L₀) →* E, ∀ x, π (s x) = x := by
    intro E _ _ π hπ hker2 h2'
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.spinOdd_central_two_extension_splitting hn hK hπ hker2 h2'
    exact ⟨s, hs⟩
  have : Finite (spinGroup (quadOdd n L₀)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  obtain ⟨α', hαβ, -, hZ⟩ := exists_cover K hsplit hq hβr
  have hcα : c = α' (spinGroup.negOne (quadOdd n L₀)
      (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n L₀ h2)).ne_zero) := by
    have hcZ' := hcZ
    rw [hZ] at hcZ'
    obtain ⟨z, hz, hzc⟩ := hcZ'
    have hzc' : z ∈ center (spinGroup (quadOdd n L₀)) := by
      rw [← (spinToStatedProj_quadOdd h2 hn).2.2, MonoidHom.mem_ker]
      have h1 : fS z = 1 := by
        rw [SetLike.mem_coe, MonoidHom.mem_ker] at hz
        rw [← hβ, hz, map_one]
      have h3 : Θ (spinToStatedProj (quadOdd n L₀) hRs z) = 1 :=
        hinj (by rw [map_one, ← hfS]; exact h1)
      exact Θ.injective (by rw [h3, map_one])
    rcases eq_one_or_negOne_of_mem_center_spinOdd h2 hn hzc' with rfl | rfl
    · exact absurd (by rw [← hzc, map_one]) hc1
    · exact hzc.symm
  obtain ⟨R₁, R₂, hneg, hR₁, hR₂⟩ := spin_slices_bridge h2 (by omega) hd5 hw hW (oddIndexEquiv n)
    (quadOdd n L₀) (coe_quadOdd n L₀) hRs S₁ ν₁ hS₁ S₂ ν₂ hS₂
  have hnegmem : spinGroup.negOne (quadOdd n L₀)
      (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n L₀ h2)).ne_zero ∈
        R₁.range ⊔ R₂.range := by
    have : spinGroup.negOne (quadOdd n L₀)
        (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n L₀ h2)).ne_zero =
          R₁ (-1) * R₂ (-1) := Subtype.ext (by rw [hneg, spinGroup.coe_negOne])
    rw [this]
    exact mul_mem (mem_sup_left ⟨-1, rfl⟩) (mem_sup_right ⟨-1, rfl⟩)
  have hperf : Group.IsPerfect SL(2, L₀) := CatalogueBGeneralLinear.specialLinear_perfect 2 L₀
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hβ₁ : ∀ g ∈ R₁.range, β g ∈ (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, hβ, hfS]
    obtain ⟨x', hx'⟩ := hR₁ x
    rw [hx']
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hβ₂ : ∀ g ∈ R₂.range, β g ∈ (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, hβ, hfS]
    obtain ⟨x', hx'⟩ := hR₂ x
    rw [hx']
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hcT := map_mem_sup_of_cover (liftHom K) α' hαβ (commutator_range_of_perfect hperf R₁)
    (commutator_range_of_perfect hperf R₂) hβ₁ hβ₂ hnegmem
  rwa [← hcα] at hcT

theorem burgoynePropB_POmegaOdd {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .POmegaOdd n p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hq, hM4, ht, hY1, hY2, -, -, -, -, -, -, -, -, hcZ, -, hc2, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp, hf, hn, -⟩, L₀, _, _, hKc, ⟨e⟩⟩ := hcl
  have : Fintype L₀ := Fintype.ofFinite L₀
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP L₀ p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar L₀ ≠ 2 := by rw [ringChar.eq L₀ p']; exact hp2'
  have h2 : (2 : L₀) ≠ 0 := Ring.two_ne_zero hK
  have hker₀ := oKer_coordinateOdd hmod L₀ hKc e
  have hsurj₀ := oSurj_coordinateOdd hmod L₀ hKc e
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n L₀)
    (regular_coordinateQuadOdd n L₀ h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) L₀) : Matrix _ _ L₀) *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * coordinateQuadOdd n L₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hS₁' : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) L₀) : Matrix _ _ L₀) *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * reindexQuadraticForm (oddIndexEquiv n) (quadOdd n L₀) v := hS₁
  have hker := hker₀.transport 1 1 hS₁
  have hsurj := hsurj₀.transport 1 1 hS₁
  set θ := (coordinateOddWitnessEquiv L₀ e).trans (oTransport 1 1 hS₁) with hθ
  set tX := (rhoZ K).rangeRestrict t with htX
  have htX2 := orderOf_rangeRestrict_of_phiO K hq ht
  have hcore_ne : oddCentralizerCore tX ≠ ⊥ := fun h => hY1 (le_bot_iff.1 (h ▸ hY2))
  obtain ⟨g, hg⟩ := hsurj (socleAction θ tX)
  by_cases hσ : g.val.right = 1
  swap
  · exact (hcore_ne (field_odd_core_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
      (hsurj.surjX θ tX) htX2 hσ hg)).elim
  rcases inner_odd_twin hK (by omega) ⟨n, rfl⟩ hR hker hsimple hnab θ (hsurj.surjX θ tX) htX2 hσ
    hg with h | ⟨hK5, hd5, w, hw, α, a, hW, S, ν, hS, hker', hψ't, hcore'⟩
  · exact (hcore_ne h).elim
  clear hg hσ hsurj hker hsurj₀ hker₀ hcore_ne hR hRQ hmod
  obtain ⟨ū, hū, ⟨f₁⟩, ⟨f₂⟩, hcomm, hū₁, hū₂, hint', hs₁, hs₁s, hs₂, hs₂s, hprop₁', hprop₂'⟩ :=
    odd_twin_comap hK hK5 hd5 hw hW hker' hsimple hnab (θ.trans (oTransport S ν hS)) hψ't hcore'
      hY1 hY2 hKc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hcT := mem_twin_sup_of_spinOdd K hK hK5 hn hd5 hw hW 1 1 hS₁' S ν hS hq hsimple hnab
    (θ.trans (oTransport S ν hS)) hcZ hc1
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hSr : ∀ {L : Subgroup (matrixDerived (oQ (diagGL hw)))},
      (slice L).comap (socleAction (θ.trans (oTransport S ν hS))) ≤ (liftHom K).range := by
    intro L g hg
    rw [hrange, mem_socle_iff hsimple hnab (θ.trans (oTransport S ν hS))]
    exact slice_le_range hg
  have h5 : 5 ≤ p' ^ f' := by rw [← hKc]; exact hK5
  exact propB_of_twin K hq hSr hSr hp2' h5 f₁ f₂ hcomm hū hū₁ hū₂ hint' hs₁ hs₁s hs₂ hs₂s
    hprop₁' hprop₂' hcZ hc1 hcT

end CFSG.ComponentClassification.Burgoyne.B
