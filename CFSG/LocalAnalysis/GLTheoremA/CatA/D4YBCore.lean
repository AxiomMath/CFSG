module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBFlag
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthModel
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YB

open scoped Matrix
open CFSG.StandardType CFSG.StandardType.D4Rank CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem not_conjAct_of_not_inner [Subsingleton (K ≃+* K)] {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (Om8 K)) (g : similarityPairs (coordinateQuadPlus 4 K)) :
    conjAct _ g ≠ α := by
  intro hg
  obtain ⟨ι', hι', k, c, hc, hαeq⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨g₁, hg₁⟩ := exists_pair_of_mem_inner hι'
  obtain ⟨g₂, hg₂⟩ := exists_pair_of_mem_plusCompl hc
  have hθk : (theta : MulAut (Om8 K)) ^ k = conjAct _ (g₁⁻¹ * g * g₂⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, hg₁, hg, hg₂, hαeq]
    group
  have hθ1 := theta_pow_eq_one_of_eq_conjAct hθk
  rw [hθ1, one_mul] at hαeq
  obtain ⟨σ, rfl | rfl⟩ := hc
  · have hσ : σ = 1 := Subsingleton.elim _ _
    rw [hσ, map_one, mul_one] at hαeq
    exact hα (hαeq ▸ hι')
  · have hσ : σ = 1 := Subsingleton.elim _ _
    rw [hσ, map_one, mul_one] at hαeq
    obtain ⟨γ, rfl⟩ := hι'
    obtain ⟨γ', hγ'⟩ := conj_mul_cube (AutOm.plusRefl (K := K) one_le_four) γ
    rw [← hαeq, hα3] at hγ'
    have hρρ : AutOm.plusRefl (K := K) one_le_four * AutOm.plusRefl one_le_four = 1 :=
      AutOm.plusRefl_mul_self one_le_four
    have hρ3 : (AutOm.plusRefl (K := K) one_le_four) ^ 3 = AutOm.plusRefl one_le_four := by
      rw [pow_succ, sq, hρρ, one_mul]
    rw [hρ3] at hγ'
    have hmem : AutOm.plusRefl (K := K) one_le_four ∈ inner (Om8 K) := by
      have : AutOm.plusRefl (K := K) one_le_four = MulAut.conj γ'⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_right hγ'.symm
      rw [this]
      exact ⟨_, rfl⟩
    have hbot : AutOm.plusRefl (K := K) one_le_four ∈
        inner (Om8 K) ⊓ AutOm.plusCompl (K := K) one_le_four :=
      ⟨hmem, ⟨1, Or.inr (by rw [map_one, mul_one])⟩⟩
    rw [AutOm.inner_inf_plusCompl (K := K) (n := 4) (by norm_num)] at hbot
    have hρ1 : AutOm.plusRefl (K := K) one_le_four = 1 := hbot
    rw [hρ1] at hαeq
    apply hα
    rw [hαeq]
    exact ⟨γ, by rw [mul_one]⟩

theorem fixDim_two_or_four (hcls : GGD4TrialityClassInput) (α : MulAut (Om8 K))
    (hα3 : α ^ 3 = 1) (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α)
    (E : Subgroup (Om8 K)) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hfix : ∀ e ∈ E, α e = e) :
    ∀ e ∈ E, e ≠ 1 → omFixDim e = 2 ∨ omFixDim e = 4 := by
  obtain ⟨γ, k, σ, hk, rfl⟩ := exists_conj_theta_pow_fieldAutP α hα3 hns
  set φ := AutOm.fieldAutP 4 σ with hφ
  have hθφ : ∀ j : ℕ, ∀ y : Om8 K, (theta ^ j) (φ y) = φ ((theta ^ j) y) := by
    intro j y
    rw [← MulAut.mul_apply, ← MulAut.mul_apply,
      (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) j).eq]
  have hpair : ((theta : MulAut (Om8 K)) ^ k = theta ∧ (theta : MulAut (Om8 K)) ^ (k + k) =
      theta⁻¹) ∨ ((theta : MulAut (Om8 K)) ^ k = theta⁻¹ ∧
        (theta : MulAut (Om8 K)) ^ (k + k) = theta) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨pow_one _, theta_sq⟩
    · refine Or.inr ⟨theta_sq, ?_⟩
      rw [show 2 + 2 = 3 + 1 from rfl, pow_succ, theta_cube, one_mul]
  have hd1 : ∀ e ∈ E, omFixDim ((theta ^ k) (φ e)) = omFixDim e := by
    intro e he
    have h := hfix e he
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    rw [← omFixDim_conj γ, h]
  have hd2 : ∀ e ∈ E, omFixDim ((theta ^ (k + k)) (φ (φ e))) = omFixDim e := by
    intro e he
    have h2 : (MulAut.conj γ * (theta ^ k * φ)) ^ 2 =
        MulAut.conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ) * (theta ^ (k + k) * (φ * φ)) := by
      rw [conj_mul_sq, sq (theta ^ k * φ), mul_assoc, ← mul_assoc φ,
        ← (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) k).eq, mul_assoc,
        ← mul_assoc (theta ^ k), ← pow_add]
    have hα2 : ((MulAut.conj γ * (theta ^ k * φ) : MulAut (Om8 K)) ^ 2) e = e := by
      rw [sq, MulAut.mul_apply, hfix e he, hfix e he]
    rw [h2, MulAut.mul_apply] at hα2
    have h := omFixDim_conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ)
      ((theta ^ (k + k) * (φ * φ) : MulAut (Om8 K)) e)
    rw [hα2] at h
    exact h.symm
  intro e he he1
  have he3 : e ^ 3 = 1 := hE.2 e he
  have hy3 : φ e ^ 3 = 1 := by rw [← map_pow, he3, map_one]
  have hdy : omFixDim (φ e) = omFixDim e := omFixDim_fieldAutP σ e
  have hle : omFixDim e ≤ 8 := by
    have := Submodule.finrank_le (LinearMap.ker (omRep e - 1))
    rwa [Module.finrank_fin_fun] at this
  have h8 : omFixDim e ≠ 8 := fun h => he1 (eq_one_of_omFixDim h)
  obtain ⟨j, hj⟩ := omFixDim_even e he3
  have h6 : omFixDim e ≠ 6 := by
    intro h6
    obtain ⟨ha, hb⟩ := (hcls K (φ e) hy3).1 (hdy.trans h6)
    have h1 := hd1 e he
    rcases hpair with ⟨hk1, -⟩ | ⟨hk1, -⟩ <;> rw [hk1] at h1 <;> omega
  have h0 : omFixDim e ≠ 0 := by
    intro h0
    have h := (hcls K (φ e) hy3).2 (hdy.trans h0)
    have h1 := hd1 e he
    have h2 := hd2 e he
    rw [hθφ, omFixDim_fieldAutP] at h2
    rcases hpair with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;> rw [hk1] at h1 <;> rw [hk2] at h2 <;>
      rcases h with h | h <;> omega
  omega

theorem subsingleton_ringEquiv_of_card_two' (hK : Nat.card K = 2) : Subsingleton (K ≃+* K) := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have hx : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ((hy x hx0).trans (hy 1 one_ne_zero).symm)
  refine ⟨fun f g => RingEquiv.ext fun x => ?_⟩
  rcases hx x with rfl | rfl <;> simp

theorem card_singular_coordinate (hK : Nat.card K = 2) :
    Nat.card {v : Fin (2 * 4) → K // coordinateQuadPlus 4 K v = 0} = 136 := by
  rw [← CFSG.HardMathSupport.Curtis.Coordinator.card_singular_quadPlus_four hK]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.arrowCongr (plusIndexEquiv 4).symm (Equiv.refl K)) fun v => ?_)
  rw [coordinateQuadPlus_apply, CFSG.LieType.Universal.Spin.quadPlus_apply]
  simp [Equiv.arrowCongr_apply]

@[expose] noncomputable def omLin : Om8 K →* ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :=
  matrixLinearIso.toMonoidHom.comp (matrixDerived (coordinateQuadPlus 4 K)).subtype

theorem core (hK : Nat.card K = 2) {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (Om8 K)) {E : Subgroup (Om8 K)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hfix : ∀ e ∈ E, α e = e) (hcard : 9 ≤ Nat.card E) {R : Subgroup (Om8 K)}
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) (hER : E ≤ Subgroup.normalizer (R : Set (Om8 K))) :
    False := by
  haveI := subsingleton_ringEquiv_of_card_two' hK
  have hns := not_conjAct_of_not_inner hα3 hα
  have hd := fixDim_two_or_four ggD4TrialityClassInput_holds α hα3 hns E hE hfix
  obtain ⟨Z, hZne, hZs, hZE⟩ := exists_totallySingular R hR2 hR
  haveI : IsMulCommutative E := hE.1
  have hnd : ∀ v : Fin (2 * 4) → K, (∀ w, QuadraticMap.polar (coordinateQuadPlus 4 K) v w = 0) →
      v = 0 := fun v hv =>
    (regular_coordinateQuadPlus 4 K (by norm_num)).1.1 v fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w
  refine hZne (key_lemma (coordinateQuadPlus 4 K) (by rw [hK]) (by simp) hnd
    (by rw [card_singular_coordinate hK])
    (E := E) ((omLin (K := K)).comp E.subtype) (fun x v => ?_) (fun x => Subtype.ext (hE.2 x x.2))
    hcard (fun x hx => hd x x.2 fun h => hx (Subtype.ext h)) Z (fun x v hv => hZE x (hER x.2) v hv)
    hZs)
  exact omRep_Q (K := K) x v

omit [Finite K] in
theorem conj_injective_om8 : Function.Injective (MulAut.conj : Om8 K →* MulAut (Om8 K)) :=
  CFSG.StandardType.NbrGraphD4.conj_injective

theorem main_om8 (hK : Nat.card K = 2)
    (hOut : Nat.card (MulAut (Om8 K) ⧸ inner (Om8 K)) ≤ 6)
    {P S : Subgroup (MulAut (Om8 K))} (hP : CFSG.Open.IsElemAbelian 3 P)
    (hPn : ¬ P ≤ inner (Om8 K)) (hcard : Nat.card P = 3 ^ 3) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hPS : P ≤ Subgroup.normalizer (S : Set (MulAut (Om8 K)))) (hSi : S ≤ inner (Om8 K)) :
    False := by
  classical
  obtain ⟨α, hαP, hα⟩ := Set.not_subset.1 hPn
  have hα3 : α ^ 3 = 1 := hP.2 α hαP
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E : Subgroup (Om8 K) := P.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hEdef
  have hE : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun u v => Subtype.ext (conj_injective_om8 ?_)⟩⟩, fun γ hγ => conj_injective_om8 ?_⟩
    · change MulAut.conj ((u : Om8 K) * v) = MulAut.conj ((v : Om8 K) * u)
      rw [map_mul, map_mul]
      exact hcomm _ u.2 _ v.2
    · rw [map_pow, map_one]
      exact hP.2 _ hγ
  have hfix : ∀ γ ∈ E, α γ = γ := by
    intro γ hγ
    apply conj_injective_om8
    have h2 := hcomm α hαP _ hγ
    rw [D4Rank.mulAut_mul_conj α γ] at h2
    exact mul_right_cancel h2
  have hmap : E.map MulAut.conj = P ⊓ inner (Om8 K) := by
    ext a
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hγ, γ, rfl⟩
    · rintro ⟨haP, γ, rfl⟩
      exact ⟨γ, haP, rfl⟩
  have hEcard : Nat.card E = Nat.card ↥(P ⊓ inner (Om8 K)) := by
    rw [← hmap, Subgroup.card_map_of_injective conj_injective_om8]
  have hrel := Subgroup.relIndex_mul_card (H := inner (Om8 K)) (K := P)
  have hrel_le : (inner (Om8 K)).relIndex P ≤ 6 := by
    have h1 : (inner (Om8 K)).relIndex P = Nat.card (P.map (QuotientGroup.mk' (inner (Om8 K)))) := by
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact (Subgroup.card_le_card_group _).trans hOut
  have hrel_dvd : (inner (Om8 K)).relIndex P ∣ 27 := by
    rw [hcard] at hrel
    exact ⟨_, hrel.symm⟩
  have hrel1 : (inner (Om8 K)).relIndex P ≠ 1 := fun h => hPn (Subgroup.relIndex_eq_one.1 h)
  have hrel3 : (inner (Om8 K)).relIndex P = 3 := by
    have hpos : 0 < (inner (Om8 K)).relIndex P := Nat.pos_of_dvd_of_pos hrel_dvd (by norm_num)
    interval_cases h : (inner (Om8 K)).relIndex P <;> simp_all <;> omega
  have hE9 : 9 ≤ Nat.card E := by
    rw [hEcard, inf_comm]
    rw [hrel3, hcard] at hrel
    omega
  set R : Subgroup (Om8 K) := S.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hRdef
  have hR2 : IsPGroup 2 R := hS2.comap_of_injective _ conj_injective_om8
  have hR : R ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨γ, rfl⟩ := hSi hs
    have hγ : γ ∈ R := hs
    rw [hbot, Subgroup.mem_bot] at hγ
    rw [hγ, map_one]
    exact Subgroup.one_mem _
  have hER : E ≤ Subgroup.normalizer (R : Set (Om8 K)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have h := Subgroup.mem_normalizer_iff.1 (hPS he) (MulAut.conj r)
    simp only [hRdef, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  exact core hK hα3 hα hE hfix hE9 hR2 hR hER

end Outer

end CFSG.LocalAnalysis.GLTheoremA.D4YB
