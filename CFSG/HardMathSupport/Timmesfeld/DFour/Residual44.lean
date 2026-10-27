module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Defs
public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Chain
public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Fam
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataPlusImage
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.ComponentClassification.HarrisLit.T1.S8
open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.DefChar.Orth
open CFSG.LocalAnalysis.ComponentInitial (orthogonal_model_isometry_abelianization_order_bound)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration (exists_nonzero_value)
open scoped Pointwise

section Abstract

variable {P : Type*} [Group P]

theorem exists_mem_smul_family {C : Set P} {𝓕 : Set (Subgroup P)} {β : MulAut P}
    (hβ : ∀ s ∈ C, β s = s) (h : ∃ U ∈ 𝓕, ∀ s ∈ C, s ∈ U) :
    ∃ U ∈ β • 𝓕, ∀ s ∈ C, s ∈ U := by
  obtain ⟨U, hU, hCU⟩ := h
  refine ⟨β • U, Set.smul_mem_smul_set hU, fun s hs => ?_⟩
  rw [← hβ s hs]
  exact Subgroup.smul_mem_pointwise_smul s β U (hCU s hs)

theorem inv_apply_eq_of_fix {C : Set P} {β : MulAut P} (hβ : ∀ s ∈ C, β s = s) :
    ∀ s ∈ C, β⁻¹ s = s := by
  intro s hs
  calc β⁻¹ s = β⁻¹ (β s) := by rw [hβ s hs]
    _ = s := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem conj_smul_eq_of_family_swap {C : Set P} {F W Z : Set (Subgroup P)}
    (hO : ∀ β : MulAut P, β • F = F ∨ β • F = W ∨ β • F = Z)
    {γ : MulAut P} (hγW : γ • W = Z) (hγZ : γ • Z = W)
    (hW : ∃ U ∈ W, ∀ s ∈ C, s ∈ U) (hF : ¬ ∃ U ∈ F, ∀ s ∈ C, s ∈ U)
    {α : MulAut P} (hα : ∀ s ∈ C, α s = s) (hαF : α • F ≠ F) :
    (α * γ * α * (α * γ)⁻¹) • F = F := by
  have hbad : ∀ β : MulAut P, (∀ s ∈ C, β s = s) → ¬ ∃ U ∈ β • F, ∀ s ∈ C, s ∈ U := by
    intro β hβ h
    apply hF
    have := exists_mem_smul_family (inv_apply_eq_of_fix hβ) h
    rwa [inv_smul_smul] at this
  have h1 : α • F = Z := by
    rcases hO α with h | h | h
    · exact absurd h hαF
    · exact absurd (h ▸ hW) (hbad α hα)
    · exact h
  have h2 : α⁻¹ • F = Z := by
    rcases hO α⁻¹ with h | h | h
    · refine absurd ?_ hαF
      calc α • F = α • (α⁻¹ • F) := by rw [h]
        _ = F := smul_inv_smul α F
    · exact absurd (h ▸ hW) (hbad α⁻¹ (inv_apply_eq_of_fix hα))
    · exact h
  have h3 : α • W = W := by
    have hW' : α • W = (α * γ * α) • F := by rw [mul_smul, mul_smul, h1, hγZ]
    have hgood := exists_mem_smul_family hα hW
    rcases hO (α * γ * α) with h | h | h
    · rw [hW', h] at hgood
      exact absurd hgood hF
    · rw [hW', h]
    · rw [hW', h, ← h1] at hgood
      exact absurd hgood (hbad α hα)
  have hγinv : γ⁻¹ • Z = W := by rw [← hγW, inv_smul_smul]
  simp only [mul_inv_rev, mul_smul]
  rw [h2, hγinv, h3, hγW, ← h2, smul_inv_smul]

end Abstract

section Unipotent

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p]

theorem exists_one_add_mem (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {M : Module.End K (Fin d → K)} (hM : ∀ x y, polar Q (M x) y = -polar Q x (M y))
    (hMM : ∀ x, M (M x) = 0) : ∃ f : matrixDerived Q, toE f.val = 1 + M := by
  have h1 : (1 + M) * (1 - M) = 1 := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hMM]
    abel
  have h1' : (1 - M) * (1 + M) = 1 := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, hMM]
    abel
  set A : GL (Fin d) K := glOfEnd (1 + M) (1 - M) h1 h1' with hA
  have hAE : toE A = 1 + M := toE_glOfEnd _ _ h1 h1'
  have hiso : A ∈ matrixIsometries Q := (mem_matrixIsometries_iff' Q A).2 fun v => by
    rw [hAE, LinearMap.add_apply, Module.End.one_apply, QuadraticMap.map_add Q]
    have hq : Q (M v) = 0 := by
      have e1 := polar_self Q (M v)
      rw [hM, hMM, polar_zero_right, neg_zero, two_smul] at e1
      have : (2 : K) * Q (M v) = 0 := by linear_combination -e1
      exact (mul_eq_zero.1 this).resolve_left h2
    have hp : polar Q v (M v) = 0 := by
      have e2 := hM v v
      rw [polar_comm] at e2
      have : (2 : K) * polar Q v (M v) = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [hq, hp, add_zero, add_zero]
  have hpow : A ^ p ^ 1 = 1 := by
    apply toE_injective
    rw [toE_pow, hAE, toE_one]
    refine pow_prime_pow_eq_one (n := 2) ?_ ?_
    · refine LinearMap.ext fun x => ?_
      simp [pow_two, Module.End.mul_apply, hMM]
    · rw [pow_one]
      exact (Fact.out : p.Prime).two_le
  exact ⟨⟨A, mem_matrixDerived_of_pow_eq_one hp2 hab hiso hpow⟩, hAE⟩

end Unipotent

theorem pow_apply_of_eq_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} {x : V} {μ : K} (hx : f x = μ • x) (n : ℕ) :
    (f ^ n) x = μ ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

section Residual

variable {K : Type} [Field K] [Finite K]

local notation "Q₈" => coordinateQuadPlus 4 K

theorem coordinatePlusFour_facts (p : ℕ) [Fact p.Prime] [CharP K p] :
    (polarBilin Q₈).Nondegenerate ∧ (∃ v, Q₈ v ≠ 0) ∧
      (∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q₈)) = 2 ^ m) ∧
      projectivePointFamilyAut Q₈ = matrixProjectiveImage Q₈ := by
  have hp : p.Prime := Fact.out
  have := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K p
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 p
      f := ⟨⟨hp, f.pos, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hab₀ := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 p f hm K hK (quadPlus 4 K) (coe_quadPlus 4 K) (MulEquiv.refl _)
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus hm K hK (MulEquiv.refl _)
  exact ⟨hnd,
    exists_nonzero_value _ (coordinate_model_intrinsic_plus hm K hK (MulEquiv.refl _)).1,
    exists_two_pow_card_abelianization (plusIndexEquiv 4) (quadPlus 4 K) hab₀,
    coordinate_plus_family_eq_matrixImage hm K hK (MulEquiv.refl _)⟩

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem residual44_core (hp2 : p ≠ 2) {g : matrixProjectiveDerived Q₈} {gh : matrixDerived Q₈}
    (hgh : matrixProjectiveProjection Q₈ gh = g) (hghp : gh ^ p = 1) (hg : orderOf g = p)
    (hres : Residual44 gh) {α : MulAut (matrixProjectiveDerived Q₈)}
    (hcop : (orderOf α).Coprime p) (hfix : ∀ s, s * g = g * s → α s = s) :
    α ∈ matrixProjectiveImage Q₈ := by
  have : NeZero (2 * 4) := ⟨by norm_num⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hnd, hQ, hab, himage⟩ := coordinatePlusFour_facts (K := K) p
  have hcc : (1 : K) * 1 = 1 := mul_one 1
  have hG' : gEnd gh 1 = toE gh.val := by rw [gEnd, one_smul]
  have hG : gEnd gh 1 ^ p = 1 := by
    rw [hG', ← toE_pow, ← Subgroup.coe_pow, hghp, Subgroup.coe_one, toE_one]
  set z := zEnd p gh 1 with hzdef
  have hz : ∀ x y, polar Q₈ (z x) y = -polar Q₈ x (z y) := zEnd_skew gh h2 hodd hG hcc
  have hzp : z ^ p = 0 := zEnd_pow gh hG
  have hcomm : ∀ t : matrixDerived Q₈, matrixProjectiveProjection Q₈ t * g =
      g * matrixProjectiveProjection Q₈ t ↔ toE t.val * z = z * toE t.val := by
    intro t
    rw [← hgh, commute_proj_iff hcc hG t]
    exact ⟨comm_z_of_comm_g gh, comm_g_of_comm_z gh h2 hodd hG⟩
  have hY : ∀ w, z (z w) = 0 → Q₈ w = 0 := by
    intro w hw
    have hres' : ∀ w, ((toE gh.val - 1) ^ 2 : Module.End K (Fin (2 * 4) → K)) w = 0 →
        Q₈ w = 0 := hres
    apply hres'
    have h1 : z * (gEnd gh 1 + 1) = gEnd gh 1 - 1 := zOf_mul_add_one h2 hodd hG
    have hc : Commute z (gEnd gh 1 + 1) :=
      (show Commute (gEnd gh 1) z from commute_zOf (p := p) rfl).symm.add_right
        (Commute.one_right _)
    have h3 : (gEnd gh 1 - 1) ^ 2 = (gEnd gh 1 + 1) ^ 2 * z ^ 2 := by
      rw [← h1, hc.mul_pow, (hc.pow_pow 2 2).eq]
    rw [← hG', h3, Module.End.mul_apply, pow_two z, Module.End.mul_apply, hw, map_zero]
  have hV : finrank K (Fin (2 * 4) → K) = 8 := by simp
  obtain ⟨hz4, hd1, hd2, hker3⟩ := jordan_four_four h2 hnd hV hz ⟨p, hzp⟩ hY
  have h4 : ∀ x, z (z (z (z x))) = 0 := fun x => by
    have := congrArg (fun f => f x) hz4
    simpa [pow_succ, Module.End.mul_apply] using this
  set C : Set (matrixProjectiveDerived Q₈) := {s | s * g = g * s} with hC
  have hYsing : ∀ v ∈ LinearMap.ker (z ^ 2), Q₈ v = 0 := fun v hv => hY v (by
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hv
    exact hv)
  obtain ⟨U₀, hU₀, hU₀stab⟩ := exists_maximal_family_mem hd2 hYsing
  have hCU₀ : ∀ s ∈ C, s ∈ U₀ := by
    intro s hs
    obtain ⟨t, rfl⟩ := matrixProjectiveProjection_surjective Q₈ s
    apply hU₀stab t
    have htz : Commute (toE t.val) (z ^ 2) :=
      Commute.pow_right (show Commute (toE t.val) z from (hcomm t).1 hs) 2
    have hle : (LinearMap.ker (z ^ 2)).map (matrixLinearEquiv t.val).toLinearMap ≤
        LinearMap.ker (z ^ 2) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hw
      rw [LinearMap.mem_ker]
      have := congrArg (fun f => f w) htz.eq
      simp only [Module.End.mul_apply, hw, map_zero] at this
      exact this.symm
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)
  have hFbad : ¬ ∃ U ∈ projectivePointFamily Q₈, ∀ s ∈ C, s ∈ U := by
    rintro ⟨_, ⟨L, rfl⟩, hCU⟩
    obtain ⟨⟨x, hxL⟩, hx0, hxspan⟩ := finrank_eq_one_iff'.1 L.2.1
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have heig : ∀ t : matrixDerived Q₈, toE t.val * z = z * toE t.val →
        ∃ μ : K, toE t.val x = μ • x := by
      intro t ht
      have hmem := hCU _ ((hcomm t).2 ht)
      rw [mem_pointStabilizer_iff] at hmem
      have hL : L.val.map (matrixLinearEquiv t.val).toLinearMap = L.val := by
        rw [← projectivePointAction_mk_submodule, hmem]
      have hxm : toE t.val x ∈ L.val := by
        rw [← hL]
        exact ⟨x, hxL, rfl⟩
      obtain ⟨μ, hμ⟩ := hxspan ⟨_, hxm⟩
      exact ⟨μ, (congrArg Subtype.val hμ).symm⟩
    have hzx : z x = 0 := by
      obtain ⟨μ, hμ⟩ := heig gh (comm_z_of_comm_g gh (by rw [hG']))
      rw [← hG'] at hμ
      have hμp : μ ^ p = 1 := by
        have e1 := pow_apply_of_eq_smul hμ p
        rw [hG, Module.End.one_apply] at e1
        have e2 : (μ ^ p - 1) • x = 0 := by rw [sub_smul, ← e1, one_smul, sub_self]
        exact sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_right hx0')
      have hμ1 : μ = 1 := by
        have e3 : (μ - 1) ^ p = 0 := by rw [sub_pow_char, hμp, one_pow, sub_self]
        exact sub_eq_zero.1 (pow_eq_zero_iff hp.ne_zero |>.1 e3)
      have e4 := congrArg (fun f => f x) (zOf_mul_add_one h2 hodd hG)
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.one_apply, hμ, hμ1, one_smul, sub_self] at e4
      have e5 : (2 : K) • z x = 0 := by rw [two_smul, ← map_add]; exact e4
      exact (smul_eq_zero.1 e5).resolve_left h2
    let bas := Module.finBasisOfFinrankEq K (LinearMap.ker z) hd1
    have hb0 : ∀ i, (bas i : Fin (2 * 4) → K) ≠ 0 := fun i h =>
      bas.ne_zero i (Subtype.ext h)
    have hchain : ∀ i, ∃ e, z (z (z e)) = (bas i : Fin (2 * 4) → K) ∧ Q₈ e = 0 ∧
        polar Q₈ e (z (z e)) = 0 := by
      intro i
      obtain ⟨u, hu⟩ := hker3 (bas i).2
      have hu' : z (z (z u)) = (bas i : Fin (2 * 4) → K) := by
        rw [← hu]
        simp [pow_succ, Module.End.mul_apply]
      obtain ⟨e, he, hQe, hBe⟩ := exists_isotropic_chain h2 hnd hz h4 (hu' ▸ hb0 i)
      exact ⟨e, he.trans hu', hQe, hBe⟩
    obtain ⟨e₁, he₁, hQe₁, hBe₁⟩ := hchain 0
    obtain ⟨e₂, he₂, hQe₂, hBe₂⟩ := hchain 1
    have hli : LinearIndependent K ![z (z (z e₁)), z (z (z e₂))] := by
      have := bas.linearIndependent.map' (LinearMap.ker z).subtype (Submodule.ker_subtype _)
      convert this using 1
      ext i : 1
      fin_cases i
      · exact he₁
      · exact he₂
    have hspan : ∀ y, z y = 0 → y ∈ Submodule.span K {z (z (z e₁)), z (z (z e₂))} := by
      intro y hy
      have hsum := bas.sum_repr ⟨y, hy⟩
      rw [Fin.sum_univ_two] at hsum
      refine Submodule.mem_span_pair.2 ⟨bas.repr ⟨y, hy⟩ 0, bas.repr ⟨y, hy⟩ 1, ?_⟩
      rw [he₁, he₂]
      exact congrArg Subtype.val hsum
    have hunip : ∀ e : Fin (2 * 4) → K, Q₈ e = 0 → polar Q₈ e (z (z e)) = 0 →
        ∃ μ : K, x + polar Q₈ x e • z (z (z e)) = μ • x := by
      intro e hQe hBe
      have hiso := polar_isotropic_chain h2 hz h4 hQe hBe
      obtain ⟨t, ht⟩ := exists_one_add_mem hp2 h2 hab (chainMap_skew (Q := Q₈) _ _ _ _)
        (chainMap_chainMap hiso)
      have hMz : chainMap Q₈ e (z e) (z (z e)) (z (z (z e))) * z =
          z * chainMap Q₈ e (z e) (z (z e)) (z (z (z e))) :=
        LinearMap.ext fun y => chainMap_comm hz rfl rfl rfl (h4 e) y
      have htz : toE t.val * z = z * toE t.val := by
        rw [ht, add_mul, mul_add, one_mul, mul_one, hMz]
      obtain ⟨μ, hμ⟩ := heig t htz
      refine ⟨μ, ?_⟩
      rw [ht, LinearMap.add_apply, Module.End.one_apply, chainMap_of_ker hz hzx] at hμ
      exact hμ
    obtain ⟨μ₁, h₁⟩ := hunip e₁ hQe₁ hBe₁
    obtain ⟨μ₂, h₂⟩ := hunip e₂ hQe₂ hBe₂
    have hc₁ := polar_isotropic_chain h2 hz h4 hQe₁ hBe₁ (z (z (z e₁))) (by simp) e₁ (by simp)
    have hc₂ := polar_isotropic_chain h2 hz h4 hQe₂ hBe₂ (z (z (z e₂))) (by simp) e₂ (by simp)
    exact not_eigen_both hnd hz h4 (e₁ := e₁) (e₂ := e₂) hc₁ hc₂ hli hspan hzx hx0' h₁ h₂
  have hO : ∀ β : MulAut (matrixProjectiveDerived Q₈), β • projectivePointFamily Q₈ =
      projectivePointFamily Q₈ ∨ β • projectivePointFamily Q₈ = plusCX 4 K ∨
        β • projectivePointFamily Q₈ = plusCXstar 4 K (by norm_num) := by
    intro β
    have := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
      (MulAction.mem_orbit (projectivePointFamily Q₈) β)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hγ1 := kappa_swapIso_smul_plusCX K
  have hγ2 := kappa_swapIso_smul_plusCXstar K
  set γ := matrixProjectiveConjugationHom (coordinateQuadPlus 4 K)
    (matrixIsometryInclusion _ (CFSG.ComponentClassification.HarrisLit.T1.S8.swapIso K))
    with hγ
  have hstab : ∀ β : MulAut (matrixProjectiveDerived Q₈),
      β • projectivePointFamily Q₈ = projectivePointFamily Q₈ → β ∈ matrixProjectiveImage Q₈ :=
    fun β hβ => by
      rw [← himage]
      exact MulAction.mem_stabilizer_iff.2 hβ
  by_cases hαF : α • projectivePointFamily Q₈ = projectivePointFamily Q₈
  · exact hstab α hαF
  exfalso
  have hfixC : ∀ s ∈ C, α s = s := fun s hs => hfix s hs
  have hα' : (α * γ * α * (α * γ)⁻¹) • projectivePointFamily Q₈ = projectivePointFamily Q₈ := by
    rcases hU₀ with hX | hX
    · exact conj_smul_eq_of_family_swap hO hγ1 hγ2 ⟨U₀, hX, hCU₀⟩ hFbad hfixC hαF
    · refine conj_smul_eq_of_family_swap (fun β => ?_) hγ2 hγ1 ⟨U₀, hX, hCU₀⟩ hFbad hfixC hαF
      rcases hO β with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  set τ := α * γ with hτ
  have hcongr : MulAut.congr (MulEquiv.refl _) (τ * α * τ⁻¹) = τ * α * τ⁻¹ :=
    MulEquiv.ext fun x => rfl
  have hone : τ * α * τ⁻¹ = 1 := by
    refine orthModel_rigid_of_image hp2 (d := 2 * 4) (by norm_num) Q₈ hnd hQ hab (MulEquiv.refl _)
      (τ g) (by rw [MulEquiv.orderOf_eq]; exact hg) _ (by rw [hcongr]; exact hstab _ hα') ?_ ?_
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hcop
    · intro s hs
      have h1 : τ⁻¹ s * g = g * τ⁻¹ s := by
        apply τ.injective
        rw [map_mul, map_mul, MulAut.apply_inv_self]
        exact hs
      rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ h1, MulAut.apply_inv_self]
  have hα1 : α = 1 := by
    have := congrArg (fun β => τ⁻¹ * β * τ) hone
    simpa [mul_assoc] using this
  exact hαF (by rw [hα1, one_smul])

end Residual

theorem dFourResidual44_holds :
    ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], p ≠ 2 →
      ∀ (g : matrixProjectiveDerived (coordinateQuadPlus 4 K))
        (gh : matrixDerived (coordinateQuadPlus 4 K)),
        matrixProjectiveProjection (coordinateQuadPlus 4 K) gh = g → gh ^ p = 1 →
        orderOf g = p → Residual44 gh →
        ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
          (orderOf α).Coprime p → (∀ s, s * g = g * s → α s = s) →
            α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  intro K _ _ p _ _ hp2 g gh hgh hghp hg hres α hcop hfix
  exact residual44_core hp2 hgh hghp hg hres hcop hfix

end CFSG.HardMathSupport.Timmesfeld.DFour
