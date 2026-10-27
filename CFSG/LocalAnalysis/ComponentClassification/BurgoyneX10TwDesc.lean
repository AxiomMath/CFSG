module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwIso
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Desc

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem excCompModel_of_projectiveSL_root_fixed {m : ℕ} (hm68 : m + 1 = 6 ∨ m + 1 = 8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (α : MulAut (LinearFlag.projectiveSL (m + 1) K)) (hα2 : α ^ 2 = 1)
    {N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (r : K → SL(m + 1, K))
    (hr : ∀ c, ((r c : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 + c • N)
    (w : K → LinearFlag.projectiveSL (m + 1) K) (φ₀ : K → K)
    (hinto : ∀ c, ∃ c', w c = LinearFlag.proj (m + 1) K (r c'))
    (honto : ∀ c', ∃ c, w c = LinearFlag.proj (m + 1) K (r c'))
    (hact : ∀ c, α (w c) = w (φ₀ c)) (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1)
    (hKc : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K) (L : Subgroup (fixedSubgroup α))
    (hL : IsComponent L) : ExcCompModel p L := by
  have hα1 : α ≠ 1 := by
    intro h1'
    have hdec : α = LinearFlag.conjAut (m + 1) K 1 * LinearFlag.fieldAut (m + 1) K 1 *
        LinearFlag.dualAut (m + 1) K ^ 0 := by
      rw [h1', map_one, map_one, pow_zero, mul_one, mul_one]
    exact ringEquiv_ne_one_of_root_action (by omega) hN2 hN r hr 1 1 0 (by omega) w φ₀ hinto
      honto (fun c => by rw [← hdec]; exact hact c) h1 hKc rfl
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨A, σ, ε, hε, hαe⟩ := (LinearFlag.automorphism_generation (K := K) h3).2 α
  have hσ : σ ≠ 1 := ringEquiv_ne_one_of_root_action (by omega) hN2 hN r hr A σ ε hε w φ₀ hinto
    honto (fun c => by rw [← hαe]; exact hact c) h1 hKc
  exact excCompModel_of_projectiveSL_involution hm68 hp hp2 hf hK hα2 hα1 A σ hσ ε hε hαe L hL

theorem excCompModel_orbitGroup_of_slFrame
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {S : Set (Fin τ.rank → ℤ)}
    (hJS : D.simpleRootsJ = S) (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) (hq : IsQuasisimple D.orbitGroup)
    {m : ℕ} (hm68 : m + 1 = 6 ∨ m + 1 = 8) {β₀ : Fin τ.rank → ℤ} (hβ₀ : IsRoot τ β₀)
    (hβS : β₀ ∈ S) (hθβ₀ : D.θ (toReal β₀) = toReal β₀) (k₀ : Fin m)
    (hframe : ∃ Ψ : SL(m + 1, frobeniusFixedField k p (D.e * 2)) →*
        adjointGroup τ (frobeniusFixedField k p (D.e * 2)),
      Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range.map (adjointGroup τ _).subtype = pairSpan τ (frobeniusFixedField k p (D.e * 2)) S ∧
      (CurtisTits.rankOne (SpecialLinear.rootDatum m (frobeniusFixedField k p (D.e * 2))).rootGroup
        k₀).map Ψ =
        (adjDatum (rootOperatorFamily τ) (frobeniusFixedField k p (D.e * 2))).rootGroup β₀ ⊔
          (adjDatum (rootOperatorFamily τ) (frobeniusFixedField k p (D.e * 2))).rootGroup
            (-β₀)) :
    ExcCompModel p D.orbitGroup := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ D.e := D.one_le_e
  refine CompPred.model.orbitGroup_of_quadGroup_at D hθ2 hcard hq fun L hL => ?_
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨eY, heY⟩ := exists_quadGroup_equiv_pairSpan D hJS
  obtain ⟨Ψ, hker, hrange, hrk⟩ := hframe
  obtain ⟨θ, hθs, hθk, N, r, hN2, hN0, hr, hR1, hR2⟩ :=
    exists_pairSpan_projectiveSL_of_frame hp D.odd hK₂ (by omega) hβ₀ hβS k₀ Ψ hker hrange hrk
  let Φ : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D) ≃*
      LinearFlag.projectiveSL (m + 1) (frobeniusFixedField k p (D.e * 2)) :=
    (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY)).trans
      ((QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs))
  have hΦ : ∀ y : quadGroup D,
      Φ (y : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) = θ (eY y) := fun y => rfl
  have hβJ : β₀ ∈ D.simpleRootsJ := hJS ▸ hβS
  let y : frobeniusFixedField k p (D.e * 2) → quadGroup D := fun c =>
    ⟨⟨rootSL2 τ k β₀ (uSL (c : k)), rootSL2_mem_adjointGroup hβ₀ _⟩,
      Subgroup.subset_closure ⟨_, hβJ, (c : k), c.2, Or.inl rfl⟩⟩
  have heYy : ∀ c, eY (y c) = ⟨rootSL2 τ _ β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ := by
    intro c
    apply Subtype.ext
    apply baseChangeGL_injective (frobeniusFixedField k p (D.e * 2)).subtype
    rw [heY, baseChangeGL_rootSL2_of_field, CFSG.LieType.Chevalley.map_uSL]
    rfl
  have hσy : ∀ c, quadAut D hθ2 (y c) = y (c ^ p ^ D.e) := by
    intro c
    apply Subtype.ext
    apply Subtype.ext
    have h := D.map_rootSL2 _ hβJ.1 _ hθβ₀ (uSL (c : k)) (y c).1 rfl
    change (D.F (y c).1 : ModGL τ k) = _
    rw [h, CFSG.LieType.Chevalley.map_uSL]
    change rootSL2 τ k _ (uSL (iterateFrobenius k p D.e (c : k))) =
      rootSL2 τ k _ (uSL ((c ^ p ^ D.e : frobeniusFixedField k p (D.e * 2)) : k))
    rw [iterateFrobenius_def, SubmonoidClass.coe_pow]
  set α := MulAut.congr Φ (quadAutBar D hθ2) with hα
  set w : frobeniusFixedField k p (D.e * 2) →
      LinearFlag.projectiveSL (m + 1) (frobeniusFixedField k p (D.e * 2)) :=
    fun c => θ ⟨rootSL2 τ _ β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ with hw
  have hwy : ∀ c, w c = Φ (y c : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) := fun c => by
    rw [hΦ, heYy]
  have hact : ∀ c, α (w c) = w (c ^ p ^ D.e) := by
    intro c
    rw [hwy, hwy, hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, quadAutBar_mk, hσy]
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, quadAutBar_sq, map_one]
  have hfix := card_pow_fixed_frobeniusFixedField (k := k) (p := p) he
  have h1 : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠ 1 := by
    rw [hfix]
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hKc : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠
      Nat.card (frobeniusFixedField k p (D.e * 2)) := by
    rw [hfix, hK₂]
    intro h
    have := Nat.pow_right_injective hp.two_le h
    omega
  refine CompPred.model.of_component_equiv (fixedSubgroupCongrEquiv Φ _) (fun M hM => ?_) hL
  exact excCompModel_of_projectiveSL_root_fixed hm68 hp D.odd (by omega) hK₂ α hα2 hN2 hN0 r hr w
    (fun c => c ^ p ^ D.e) hR1 hR2 hact h1 hKc M hM

end CFSG.ComponentClassification.Burgoyne.X10
