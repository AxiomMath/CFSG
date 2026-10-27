module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame
public import CFSG.ClassicalInvolution.Phan.PhanDn.HermitianVanishing
public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] noncomputable def stdLag (n : ℕ) (K : Type) [Field K] :
    Submodule K (Fin n ⊕ Fin n → K) :=
  LinearMap.ker (LinearMap.funLeft K K (Sum.inr : Fin n → Fin n ⊕ Fin n))

theorem isLagrangian_stdLag (n : ℕ) (K : Type) [Field K] :
    (quadPlusForm n K).IsLagrangian (stdLag n K) :=
  isLagrangian_quadPlusForm n K

theorem finrank_stdLag (n : ℕ) (K : Type) [Field K] :
    Module.finrank K (stdLag n K) = n := by
  have h := (isLagrangian_stdLag n K).2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h
  simp only [Fintype.card_fin] at h
  omega

theorem finrank_flipSpace (n : ℕ) (K : Type) [Field K] :
    Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  simp only [Fintype.card_fin]
  ring

noncomputable def qPerp (n : ℕ) (K : Type) [Field K]
    (W : Submodule K (Fin n ⊕ Fin n → K)) : Submodule K (Fin n ⊕ Fin n → K) :=
  (quadPlusForm n K).polar.perp W

theorem mem_qPerp {W : Submodule K (Fin n ⊕ Fin n → K)} {v : Fin n ⊕ Fin n → K} :
    v ∈ qPerp n K W ↔ ∀ w ∈ W, polar (quadPlus n K) w v = 0 := by
  rw [qPerp, ReflForm.mem_perp]
  simp only [quadPlusForm_polar]

theorem qPerp_bot : qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) = ⊤ := by
  rw [qPerp, ReflForm.perp_bot]

theorem finrank_qPerp (W : Submodule K (Fin n ⊕ Fin n → K)) :
    Module.finrank K ↥(qPerp n K W) + Module.finrank K W = 2 * n := by
  rw [qPerp, ReflForm.finrank_perp, finrank_flipSpace]

theorem qPerp_qPerp (W : Submodule K (Fin n ⊕ Fin n → K)) :
    qPerp n K (qPerp n K W) = W := by
  rw [qPerp, qPerp, ReflForm.perp_perp]

theorem qPerp_antitone {W W' : Submodule K (Fin n ⊕ Fin n → K)} (h : W ≤ W') :
    qPerp n K W' ≤ qPerp n K W := by
  rw [qPerp, qPerp]
  exact (quadPlusForm n K).polar.perp_antitone h

theorem qPerp_sup (W W' : Submodule K (Fin n ⊕ Fin n → K)) :
    qPerp n K (W ⊔ W') = qPerp n K W ⊓ qPerp n K W' := by
  rw [qPerp, qPerp, qPerp, ReflForm.perp_sup]

theorem qPerp_eq_of_isLagrangian {M : Submodule K (Fin n ⊕ Fin n → K)}
    (hM : (quadPlusForm n K).IsLagrangian M) : qPerp n K M = M := by
  rw [qPerp]
  exact hM.perp_eq

theorem polar_self_of_singular {v : Fin n ⊕ Fin n → K} (hv : quadPlus n K v = 0) :
    polar (quadPlus n K) v v = 0 := by
  rw [← quadPlusForm_polar, QuadForm.polar_self, quadPlusForm_Q, hv, mul_zero]

def QSing (W : Submodule K (Fin n ⊕ Fin n → K)) : Prop := ∀ w ∈ W, quadPlus n K w = 0

theorem qSing_iff_isTotallySingular (W : Submodule K (Fin n ⊕ Fin n → K)) :
    QSing W ↔ (quadPlusForm n K).IsTotallySingular W := by
  constructor
  · intro h w hw
    rw [quadPlusForm_Q]
    exact h w hw
  · intro h w hw
    rw [← quadPlusForm_Q]
    exact h w hw

def QNondeg (W : Submodule K (Fin n ⊕ Fin n → K)) : Prop := W ⊓ qPerp n K W = ⊥

def QPlus (W : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  ∃ T ≤ W, QSing T ∧ 2 * Module.finrank K T = Module.finrank K W

theorem QSing.le_qPerp {T : Submodule K (Fin n ⊕ Fin n → K)} (hT : QSing T) :
    T ≤ qPerp n K T := by
  intro t ht
  rw [mem_qPerp]
  intro w hw
  have h := QuadraticMap.map_add (quadPlus n K) w t
  rw [hT _ (T.add_mem hw ht), hT w hw, hT t ht] at h
  simpa using h.symm

theorem finrank_inf_qPerp {M W : Submodule K (Fin n ⊕ Fin n → K)} (hM : QNondeg M)
    (hW : W ≤ M) :
    Module.finrank K ↥(M ⊓ qPerp n K W) + Module.finrank K W = Module.finrank K M := by
  have htop : M ⊔ qPerp n K W = ⊤ := by
    have h1 : qPerp n K (M ⊔ qPerp n K W) = ⊥ := by
      rw [qPerp_sup, qPerp_qPerp]
      exact le_bot_iff.mp (calc
        qPerp n K M ⊓ W ≤ qPerp n K M ⊓ M := inf_le_inf_left _ hW
        _ = M ⊓ qPerp n K M := inf_comm _ _
        _ = ⊥ := hM)
    have h2 := qPerp_qPerp (n := n) (K := K) (M ⊔ qPerp n K W)
    rw [h1, qPerp_bot] at h2
    exact h2.symm
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq M (qPerp n K W)
  rw [htop, finrank_top, finrank_flipSpace] at hsup
  have hperp := finrank_qPerp (n := n) (K := K) W
  omega

theorem QSing.two_mul_finrank_le {M T : Submodule K (Fin n ⊕ Fin n → K)} (hM : QNondeg M)
    (hT : T ≤ M) (hTs : QSing T) : 2 * Module.finrank K T ≤ Module.finrank K M := by
  have hTM : T ≤ M ⊓ qPerp n K T := le_inf hT hTs.le_qPerp
  have hfin := finrank_inf_qPerp (n := n) (K := K) hM hT
  have hmono := Submodule.finrank_mono hTM
  omega

theorem exists_polar_eq_one {M W : Submodule K (Fin n ⊕ Fin n → K)} (hM : QNondeg M)
    (hW : W ≤ M) {w : Fin n ⊕ Fin n → K} (hw : w ∈ M) (hwW : w ∉ W) :
    ∃ y ∈ M ⊓ qPerp n K W, polar (quadPlus n K) w y = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hW' : W ⊔ K ∙ w ≤ M :=
    sup_le hW ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
  have hdisj : W ⊓ K ∙ w = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxW, hxw⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxw
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      exact hwW (by
        have hmem : c⁻¹ • (c • w) ∈ W := W.smul_mem _ hxW
        rwa [inv_smul_smul₀ hc] at hmem)
  have hdimW' : Module.finrank K ↥(W ⊔ K ∙ w) = Module.finrank K W + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (K ∙ w)
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton (by
      rintro rfl
      exact hwW (W.zero_mem))] at h
    exact h
  have hzero : ∀ y ∈ M ⊓ qPerp n K W, polar (quadPlus n K) w y = 0 := by
    intro y hy
    by_contra hne
    exact hcon ((polar (quadPlus n K) w y)⁻¹ • y)
      ⟨M.smul_mem _ hy.1, (qPerp n K W).smul_mem _ hy.2⟩ (by
        rw [polar_smul_right, smul_eq_mul]
        exact inv_mul_cancel₀ hne)
  have hle : M ⊓ qPerp n K W ≤ M ⊓ qPerp n K (W ⊔ K ∙ w) := by
    refine le_inf inf_le_left ?_
    rw [qPerp_sup]
    refine le_inf inf_le_right ?_
    intro z hz
    rw [mem_qPerp]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [polar_smul_left, hzero z hz, smul_zero]
  have heq : M ⊓ qPerp n K W = M ⊓ qPerp n K (W ⊔ K ∙ w) :=
    le_antisymm hle (inf_le_inf_left _ (qPerp_antitone le_sup_left))
  have h1 := finrank_inf_qPerp (n := n) (K := K) hM hW
  have h2 := finrank_inf_qPerp (n := n) (K := K) hM hW'
  rw [← heq, hdimW'] at h2
  omega

theorem exists_singular_polar_eq_one {M W : Submodule K (Fin n ⊕ Fin n → K)} (hM : QNondeg M)
    (hW : W ≤ M) {v : Fin n ⊕ Fin n → K} (hv : v ∈ M ⊓ qPerp n K W) (hvW : v ∉ W)
    (hvs : quadPlus n K v = 0) :
    ∃ y ∈ M ⊓ qPerp n K W, quadPlus n K y = 0 ∧ polar (quadPlus n K) v y = 1 := by
  obtain ⟨y₀, hy₀, hy₀v⟩ := exists_polar_eq_one hM hW hv.1 hvW
  refine ⟨y₀ - quadPlus n K y₀ • v, ⟨M.sub_mem hy₀.1 (M.smul_mem _ hv.1), ?_⟩, ?_, ?_⟩
  · change y₀ - quadPlus n K y₀ • v ∈ qPerp n K W
    rw [mem_qPerp]
    intro z hz
    have hzv : polar (quadPlus n K) z v = 0 := (mem_qPerp.mp hv.2) z hz
    rw [polar_sub_right, polar_smul_right, hzv, smul_zero, sub_zero]
    exact (mem_qPerp.mp hy₀.2) z hz
  · have hQv : quadPlus n K (quadPlus n K y₀ • v) = 0 := by
      rw [QuadraticMap.map_smul (quadPlus n K), hvs, smul_zero]
    have hpolar : polar (quadPlus n K) y₀ (-(quadPlus n K y₀ • v)) = -quadPlus n K y₀ := by
      rw [polar_neg_right, polar_smul_right, polar_comm (quadPlus n K) y₀ v, hy₀v,
        smul_eq_mul, mul_one]
    rw [sub_eq_add_neg, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_neg (quadPlus n K), hQv, hpolar]
    ring
  · have hvv : polar (quadPlus n K) v v = 0 := polar_self_of_singular hvs
    rw [polar_sub_right, polar_smul_right, hvv, smul_zero, sub_zero]
    exact hy₀v

theorem QNondeg.sup_pair {A : Submodule K (Fin n ⊕ Fin n → K)} (hA : QNondeg A)
    {v w : Fin n ⊕ Fin n → K} (hv : v ∈ qPerp n K A) (hvs : quadPlus n K v = 0)
    (hvw : polar (quadPlus n K) v w ≠ 0) :
    QNondeg (A ⊔ K ∙ v ⊔ K ∙ w) ∧
      Module.finrank K ↥(A ⊔ K ∙ v ⊔ K ∙ w) = Module.finrank K A + 2 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvw (polar_zero_left (quadPlus n K) w)
  have hvv : polar (quadPlus n K) v v = 0 := polar_self_of_singular hvs
  have hvA : v ∉ A := by
    intro hvA
    have hmem : v ∈ A ⊓ qPerp n K A := ⟨hvA, hv⟩
    rw [hA] at hmem
    exact hv0 (by simpa using hmem)
  have hwAv : w ∉ A ⊔ K ∙ v := by
    intro hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h1 : polar (quadPlus n K) v a = 0 := by
      rw [polar_comm (quadPlus n K) v a]
      exact (mem_qPerp.mp hv) a ha
    have h2 : polar (quadPlus n K) v (c • v) = 0 := by
      rw [polar_smul_right, hvv, smul_zero]
    have := hvw
    rw [polar_add_right, h1, h2, add_zero] at this
    exact this rfl
  have hdisj1 : A ⊓ K ∙ v = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxA, hxV⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxV
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      exact hvA (by
        have hmem : c⁻¹ • (c • v) ∈ A := A.smul_mem _ hxA
        rwa [inv_smul_smul₀ hc] at hmem)
  have hdisj2 : (A ⊔ K ∙ v) ⊓ K ∙ w = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxA, hxW⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxW
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      exact hwAv (by
        have hmem : c⁻¹ • (c • w) ∈ A ⊔ K ∙ v := (A ⊔ K ∙ v).smul_mem _ hxA
        rwa [inv_smul_smul₀ hc] at hmem)
  have hdim1 : Module.finrank K ↥(A ⊔ K ∙ v) = Module.finrank K A + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A (K ∙ v)
    rw [hdisj1, finrank_bot, add_zero, finrank_span_singleton hv0] at h
    exact h
  have hdim2 : Module.finrank K ↥(A ⊔ K ∙ v ⊔ K ∙ w) =
      Module.finrank K A + 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ K ∙ v) (K ∙ w)
    rw [hdisj2, finrank_bot, add_zero, finrank_span_singleton (by
      rintro rfl
      exact hwAv (Submodule.zero_mem _)), hdim1] at h
    omega
  refine ⟨?_, hdim2⟩
  rw [QNondeg, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨hzW, hzperp⟩ := Submodule.mem_inf.mp hz
  obtain ⟨y, hy, w', hw', hzw⟩ := Submodule.mem_sup.mp hzW
  obtain ⟨a, ha, v', hv', hyv⟩ := Submodule.mem_sup.mp hy
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw'
  obtain ⟨lam, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  have hz_eq : z = a + lam • v + μ • w := by
    rw [← hzw, ← hyv]
  have hvW : v ∈ A ⊔ K ∙ v ⊔ K ∙ w :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  have hμ0 : μ = 0 := by
    have h := (mem_qPerp.mp hzperp) v hvW
    rw [hz_eq, polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
      polar_comm (quadPlus n K) v a, (mem_qPerp.mp hv) a ha, hvv,
      smul_zero, smul_eq_mul] at h
    have h' : μ * polar (quadPlus n K) v w = 0 := by simpa using h
    exact (mul_eq_zero.mp h').resolve_right hvw
  have hz_eq' : z = a + lam • v := by
    rw [hz_eq, hμ0]
    simp
  have hAW : A ≤ A ⊔ K ∙ v ⊔ K ∙ w := fun x hx =>
    Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have hzA : z ∈ qPerp n K A := qPerp_antitone hAW hzperp
  have haPerp : a ∈ qPerp n K A := by
    have hsub : z - lam • v ∈ qPerp n K A :=
      (qPerp n K A).sub_mem hzA ((qPerp n K A).smul_mem _ hv)
    simpa [hz_eq'] using hsub
  have ha0 : a = 0 := by
    have hmem : a ∈ A ⊓ qPerp n K A := ⟨ha, haPerp⟩
    rw [hA] at hmem
    simpa using hmem
  have hwW : w ∈ A ⊔ K ∙ v ⊔ K ∙ w :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
  have hlam0 : lam = 0 := by
    have h := (mem_qPerp.mp hzperp) w hwW
    have hz_eq'' : z = lam • v := by rw [hz_eq', ha0, zero_add]
    rw [hz_eq'', polar_smul_right, polar_comm (quadPlus n K) w v, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hvw
  rw [hz_eq', ha0, zero_add, hlam0, zero_smul]

theorem QPlus.sup_pair {A : Submodule K (Fin n ⊕ Fin n → K)} (hA : QNondeg A) (hP : QPlus A)
    {v w : Fin n ⊕ Fin n → K} (hv : v ∈ qPerp n K A) (hvs : quadPlus n K v = 0)
    (hvw : polar (quadPlus n K) v w ≠ 0) :
    QPlus (A ⊔ K ∙ v ⊔ K ∙ w) := by
  obtain ⟨T, hTA, hTs, hTdim⟩ := hP
  obtain ⟨-, hdimA⟩ := hA.sup_pair hv hvs hvw
  refine ⟨T ⊔ K ∙ v, ?_, ?_, ?_⟩
  · refine sup_le (le_trans hTA (le_trans le_sup_left le_sup_left)) ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self v))
  · intro x hx
    obtain ⟨t, ht, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_add (quadPlus n K), hTs t ht,
      QuadraticMap.map_smul (quadPlus n K), hvs, smul_zero,
      polar_smul_right, (mem_qPerp.mp hv) t (hTA ht), smul_zero, add_zero, add_zero]
  · have hvT : v ∉ T := fun hvT => by
      have hmem : v ∈ A ⊓ qPerp n K A := ⟨hTA hvT, hv⟩
      rw [hA] at hmem
      exact hvw (by rw [show v = 0 by simpa using hmem, polar_zero_left])
    have hdisj : T ⊓ K ∙ v = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro x ⟨hxT, hxV⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxV
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        exact hvT (by
          have hmem : c⁻¹ • (c • v) ∈ T := T.smul_mem _ hxT
          rwa [inv_smul_smul₀ hc] at hmem)
    have hdimT : Module.finrank K ↥(T ⊔ K ∙ v) = Module.finrank K T + 1 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq T (K ∙ v)
      rw [hdisj, finrank_bot, add_zero, finrank_span_singleton (by
        rintro rfl
        exact hvT (T.zero_mem))] at h
      exact h
    omega

local notation "qOrth" => CFSG.ClassicalInvolution.PhanDn.qPerp

theorem QNondeg.qPerp {N : Submodule K (Fin n ⊕ Fin n → K)}
    (hN : CFSG.ClassicalInvolution.PhanDn.QNondeg N) :
    CFSG.ClassicalInvolution.PhanDn.QNondeg (qOrth n K N) := by
  change qOrth n K N ⊓ qOrth n K (qOrth n K N) = ⊥
  rw [qPerp_qPerp, inf_comm]
  exact hN

theorem QPlus.qPerp {N : Submodule K (Fin n ⊕ Fin n → K)}
    (hN : CFSG.ClassicalInvolution.PhanDn.QNondeg N)
    (hP : CFSG.ClassicalInvolution.PhanDn.QPlus N) :
    CFSG.ClassicalInvolution.PhanDn.QPlus (qOrth n K N) := by
  obtain ⟨T, hTN, hTs, hTdim⟩ := hP
  obtain ⟨E, hElag, hTE⟩ := QuadForm.exists_isLagrangian_le (Φ := quadPlusForm n K)
    (isLagrangian_stdLag n K) ((qSing_iff_isTotallySingular T).mp hTs)
  have hEN : E ⊓ N = T := by
    have hsing : QSing (E ⊓ N) :=
      (qSing_iff_isTotallySingular (E ⊓ N)).mpr (hElag.1.mono inf_le_left)
    have hle := QSing.two_mul_finrank_le (n := n) (K := K) hN inf_le_right hsing
    have hmono := Submodule.finrank_mono (le_inf hTE hTN : T ≤ E ⊓ N)
    have hdim_eq : Module.finrank K ↥(E ⊓ N) = Module.finrank K T := by omega
    exact (Submodule.eq_of_le_of_finrank_eq (le_inf hTE hTN) hdim_eq.symm).symm
  have hEperp : qOrth n K E = E := qPerp_eq_of_isLagrangian hElag
  have hinf : E ⊓ qOrth n K N = qOrth n K (E ⊔ N) := by
    rw [qPerp_sup, hEperp]
  have hdimE : Module.finrank K E = n := by
    have h := hElag.2
    rw [finrank_flipSpace] at h
    omega
  have hdimEN : Module.finrank K ↥(E ⊔ N) + Module.finrank K T =
      n + Module.finrank K N := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq E N
    rw [hEN, hdimE] at h
    exact h
  have hdimN : Module.finrank K N = 2 * Module.finrank K T := hTdim.symm
  have hq := finrank_qPerp (n := n) (K := K) N
  have hqEN := finrank_qPerp (n := n) (K := K) (E ⊔ N)
  refine ⟨E ⊓ qOrth n K N, inf_le_right, ?_, ?_⟩
  · exact (qSing_iff_isTotallySingular (E ⊓ qOrth n K N)).mpr
      (hElag.1.mono inf_le_left)
  · rw [hinf]
    omega

private theorem dFlip_zero : dFlip σ (0 : Fin n ⊕ Fin n → K) = 0 := by
  funext x
  cases x <;> simp [dFlip]

theorem mem_dFlipSub (hσ : ∀ x, σ (σ x) = x) {W : Submodule K (Fin n ⊕ Fin n → K)}
    {v : Fin n ⊕ Fin n → K} : v ∈ dFlipSub σ W ↔ dFlip σ v ∈ W := by
  let W' : Submodule K (Fin n ⊕ Fin n → K) :=
    { carrier := {v | dFlip σ v ∈ W},
      zero_mem' := by
        show dFlip σ 0 ∈ W
        rw [dFlip_zero]
        exact W.zero_mem,
      add_mem' := by
        intro a b ha hb
        show dFlip σ (a + b) ∈ W
        rw [dFlip_add]
        exact W.add_mem ha hb,
      smul_mem' := by
        intro c a ha
        show dFlip σ (c • a) ∈ W
        rw [dFlip_smul]
        exact W.smul_mem (σ c) ha }
  have hle : dFlipSub σ W ≤ W' := by
    rw [dFlipSub]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu, rfl⟩
    show dFlip σ (dFlip σ u) ∈ W
    rw [dFlip_dFlip hσ]
    exact hu
  refine ⟨fun hv => hle hv, fun hv => ?_⟩
  exact Submodule.subset_span ⟨dFlip σ v, hv, dFlip_dFlip hσ v⟩

private theorem mem_dFlipSub_image {W : Submodule K (Fin n ⊕ Fin n → K)}
    {v : Fin n ⊕ Fin n → K} : v ∈ dFlipSub σ W ↔ ∃ u ∈ W, dFlip σ u = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        exact ⟨u, hu, rfl⟩
    | zero => exact ⟨0, W.zero_mem, dFlip_zero⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨u, hu, rfl⟩ := ihx
        obtain ⟨v, hv, rfl⟩ := ihy
        exact ⟨u + v, W.add_mem hu hv, dFlip_add u v⟩
    | smul a x _ ih =>
        obtain ⟨u, hu, rfl⟩ := ih
        refine ⟨σ.symm a • u, W.smul_mem _ hu, ?_⟩
        rw [dFlip_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨u, hu, rfl⟩

theorem dFlipSub_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    (W : Submodule K (Fin n ⊕ Fin n → K)) : dFlipSub σ (dFlipSub σ W) = W := by
  ext v
  rw [mem_dFlipSub hσ, mem_dFlipSub hσ, dFlip_dFlip hσ]

theorem dFlipSub_mono {W W' : Submodule K (Fin n ⊕ Fin n → K)} (h : W ≤ W') :
    dFlipSub σ W ≤ dFlipSub σ W' := by
  rw [dFlipSub, dFlipSub]
  exact Submodule.span_mono (Set.image_mono h)

theorem dFlipSub_inf (hσ : ∀ x, σ (σ x) = x)
    (W W' : Submodule K (Fin n ⊕ Fin n → K)) :
    dFlipSub σ (W ⊓ W') = dFlipSub σ W ⊓ dFlipSub σ W' := by
  ext v
  simp only [mem_dFlipSub hσ, Submodule.mem_inf]

theorem dFlipSub_sup (hσ : ∀ x, σ (σ x) = x)
    (W W' : Submodule K (Fin n ⊕ Fin n → K)) :
    dFlipSub σ (W ⊔ W') = dFlipSub σ W ⊔ dFlipSub σ W' := by
  ext v
  rw [mem_dFlipSub hσ, Submodule.mem_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨dFlip σ a, (mem_dFlipSub hσ).mpr (by rwa [dFlip_dFlip hσ]),
      dFlip σ b, (mem_dFlipSub hσ).mpr (by rwa [dFlip_dFlip hσ]), ?_⟩
    rw [← dFlip_add, hab, dFlip_dFlip hσ]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨dFlip σ x, (mem_dFlipSub hσ).mp hx, dFlip σ y, (mem_dFlipSub hσ).mp hy, ?_⟩
    rw [← dFlip_add, hxy]

theorem finrank_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    Module.finrank K ↥(dFlipSub σ W) = Module.finrank K W := by
  classical
  let f : W →+ ↥(dFlipSub σ W) :=
    { toFun := fun v => ⟨dFlip σ v.1, Submodule.subset_span ⟨v.1, v.2, rfl⟩⟩,
      map_zero' := Subtype.ext dFlip_zero,
      map_add' := fun v w => Subtype.ext (dFlip_add v.1 w.1) }
  have hf : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun x => ?_⟩
    · have h := congrArg Subtype.val hvw
      have h' := congrArg (dFlip σ) h
      simpa [f, dFlip_dFlip hσ] using h'
    · obtain ⟨u, hu, hux⟩ := mem_dFlipSub_image.mp x.2
      exact ⟨⟨u, hu⟩, Subtype.ext hux⟩
  let j : W ≃+ ↥(dFlipSub σ W) := AddEquiv.ofBijective f hf
  have hc : ∀ (r : K) (m : W), j (r • m) = σ r • j m := by
    intro r m
    exact Subtype.ext (dFlip_smul (σ := σ) r m.1)
  have h := lift_rank_eq_of_equiv_equiv (σ : K → K) j σ.bijective hc
  have h' := congrArg Cardinal.toNat h
  simpa only [Cardinal.toNat_lift, Module.finrank] using h'.symm

theorem qPerp_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    qPerp n K (dFlipSub σ W) = dFlipSub σ (qPerp n K W) := by
  ext v
  rw [mem_qPerp, mem_dFlipSub hσ]
  constructor
  · intro h
    rw [mem_qPerp]
    intro u hu
    have h' := h (dFlip σ u) (Submodule.subset_span ⟨u, hu, rfl⟩)
    have hb := polar_dFlip (σ := σ) u (dFlip σ v)
    rw [dFlip_dFlip hσ v] at hb
    rw [hb] at h'
    exact (map_eq_zero_iff σ σ.injective).mp h'
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ := mem_dFlipSub_image.mp hx
    have h1 : polar (quadPlus n K) u (dFlip σ v) = 0 := (mem_qPerp.mp h) u hu
    have hb := polar_dFlip (σ := σ) u (dFlip σ v)
    rw [dFlip_dFlip hσ v] at hb
    rw [hb, h1, map_zero]

theorem flipOrth_eq_qPerp_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    flipOrth σ W = qPerp n K (dFlipSub σ W) := by
  rw [qPerp_dFlipSub hσ]
  ext v
  rw [mem_flipOrth, mem_dFlipSub hσ, mem_qPerp]
  rfl

theorem QSing.dFlipSub {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : QSing W) :
    QSing (dFlipSub σ W) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_dFlipSub_image.mp hx
  rw [quadPlus_dFlip, hW u hu, map_zero]

theorem exists_isFlipflopPt_le_of_qPlus (hσ : IsUnitaryInvolution σ)
    {Y : Submodule K (Fin n ⊕ Fin n → K)} (hY : QNondeg Y) (hP : QPlus Y)
    (h4 : 4 ≤ Module.finrank K Y)
    (hne : ∃ u ∈ Y, ∃ v ∈ Y, flipHerm σ u v ≠ 0) :
    ∃ p ≤ Y, IsFlipflopPt σ p := by
  classical
  obtain ⟨T, hTY, hTs, hTdim⟩ := hP
  have hnd : (polarBilin ((quadPlus n K).comp Y.subtype)).Nondegenerate := by
    have hsep : ∀ x : Y,
        (∀ y : Y, polar ((quadPlus n K).comp Y.subtype) x y = 0) → x = 0 := by
      intro x hx
      have hxperp : (x : Fin n ⊕ Fin n → K) ∈ qPerp n K Y := by
        rw [mem_qPerp]
        intro z hz
        have h := hx ⟨z, hz⟩
        rw [polar_comm]
        simpa only [QuadraticMap.polar, QuadraticMap.comp_apply, Submodule.coe_subtype,
        Submodule.coe_add] using h
      have hmem : (x : Fin n ⊕ Fin n → K) ∈ Y ⊓ qPerp n K Y := ⟨x.2, hxperp⟩
      rw [hY] at hmem
      exact Subtype.ext (by simpa using hmem)
    exact ⟨hsep, fun y hy => hsep y fun x => by
      rw [polar_comm]
      exact hy x⟩
  have hplus : IsPlusType ((quadPlus n K).comp Y.subtype) := by
    refine ⟨T.comap Y.subtype, ?_, ?_⟩
    · have hfin : Module.finrank K ↥(T.comap Y.subtype) = Module.finrank K T :=
        (Submodule.comapSubtypeEquivOfLe hTY).finrank_eq
      rw [hfin]
      omega
    · intro x hx
      have hxT : (x : Fin n ⊕ Fin n → K) ∈ T := hx
      have := hTs (x : Fin n ⊕ Fin n → K) hxT
      simpa only [QuadraticMap.comp_apply, Submodule.coe_subtype] using this
  have hdim : Module.finrank K Y = 2 * Module.finrank K T := hTdim.symm
  have hk : 2 ≤ Module.finrank K T := by omega
  exact exists_isFlipflopPt_le_of_isPlusType (n := n) (σ := σ) hk hσ.exists_ne hσ.invol
    hdim hnd hplus hne

theorem exists_flipHerm_ne_zero_of_le (hσ : ∀ x, σ (σ x) = x)
    {Z : Submodule K (Fin n ⊕ Fin n → K)} (hZ : n ≤ Module.finrank K Z)
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ qPerp n K Z) (hww : flipHerm σ w w ≠ 0) :
    ∃ u ∈ Z, ∃ v ∈ Z, flipHerm σ u v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hZperp : dFlipSub σ Z ≤ qPerp n K Z := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_dFlipSub_image.mp hx
    rw [mem_qPerp]
    intro t ht
    exact hcon t ht z hz
  have hdimZ : Module.finrank K Z ≤ n := by
    have h1 := Submodule.finrank_mono hZperp
    have h2 := finrank_qPerp (n := n) (K := K) Z
    have h3 := finrank_dFlipSub (σ := σ) (n := n) hσ Z
    omega
  have hdim_eq : Module.finrank K Z = n := le_antisymm hdimZ hZ
  have heq : dFlipSub σ Z = qPerp n K Z := by
    refine Submodule.eq_of_le_of_finrank_eq hZperp ?_
    rw [finrank_dFlipSub (σ := σ) hσ, hdim_eq]
    have h2 := finrank_qPerp (n := n) (K := K) Z
    omega
  have hw' : w ∈ dFlipSub σ Z := by
    rw [heq]
    exact hw
  have hflip : dFlip σ w ∈ Z := (mem_dFlipSub hσ).mp hw'
  have hzero : flipHerm σ w w = 0 := by
    rw [flipHerm, polar_comm]
    exact (mem_qPerp.mp hw) (dFlip σ w) hflip
  exact hww hzero

theorem exists_flipHerm_ne_zero_of_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    {Z : Submodule K (Fin n ⊕ Fin n → K)} (hZ : QNondeg Z)
    (hinv : dFlipSub σ Z = Z) (hne : Z ≠ ⊥) :
    ∃ u ∈ Z, ∃ v ∈ Z, flipHerm σ u v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hZperp : Z ≤ qPerp n K Z := by
    intro z hz
    rw [mem_qPerp]
    intro t ht
    have hz' : z ∈ dFlipSub σ Z := by rw [hinv]; exact hz
    have hflip : dFlip σ z ∈ Z := (mem_dFlipSub hσ).mp hz'
    have h := hcon t ht (dFlip σ z) hflip
    rwa [flipHerm, dFlip_dFlip hσ z] at h
  have hrad : Z ⊓ qPerp n K Z = Z := inf_eq_left.mpr hZperp
  rw [hZ] at hrad
  exact hne hrad.symm

theorem exists_singular_apply_ne_zero {E Z : Submodule K (Fin n ⊕ Fin n → K)}
    (hE : E ≤ Z) (hEs : QSing E) (hZE : Z ⊓ qPerp n K E ≤ E)
    (φ : (Fin n ⊕ Fin n → K) →ₗ[K] K) {z : Fin n ⊕ Fin n → K} (hz : z ∈ Z)
    (hφ : φ z ≠ 0) :
    ∃ w ∈ Z, quadPlus n K w = 0 ∧ φ w ≠ 0 := by
  classical
  by_cases hEφ : ∃ e ∈ E, φ e ≠ 0
  · obtain ⟨e, he, hφe⟩ := hEφ
    exact ⟨e, hE he, hEs e he, hφe⟩
  push Not at hEφ
  have hzE : z ∉ E := by
    intro hzE
    exact hφ (hEφ z hzE)
  have hzPerp : z ∉ qPerp n K E := fun hzPerp => hzE (hZE ⟨hz, hzPerp⟩)
  have hex : ∃ e ∈ E, polar (quadPlus n K) e z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hzPerp ((mem_qPerp).mpr hcon)
  obtain ⟨e, he, hez⟩ := hex
  let t : Fin n ⊕ Fin n → K := (polar (quadPlus n K) z e)⁻¹ • e
  have ht : t ∈ E := E.smul_mem _ he
  have hze : polar (quadPlus n K) z e ≠ 0 := by
    rwa [polar_comm (quadPlus n K) z e]
  have hzt : polar (quadPlus n K) z t = 1 := by
    rw [polar_smul_right, smul_eq_mul]
    exact inv_mul_cancel₀ hze
  refine ⟨z - quadPlus n K z • t, Z.sub_mem hz (Z.smul_mem _ (hE ht)), ?_, ?_⟩
  · have hQt : quadPlus n K (quadPlus n K z • t) = 0 := by
      rw [QuadraticMap.map_smul (quadPlus n K), hEs t ht, smul_zero]
    have hpolar : polar (quadPlus n K) z (-(quadPlus n K z • t)) = -quadPlus n K z := by
      rw [polar_neg_right, polar_smul_right, hzt, smul_eq_mul, mul_one]
    rw [sub_eq_add_neg, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_neg (quadPlus n K), hQt, hpolar]
    ring
  · rw [map_sub, map_smul, hEφ t ht, smul_zero, sub_zero]
    exact hφ

theorem stdLag_inf_dFlipSub (hσ : ∀ x, σ (σ x) = x) :
    stdLag n K ⊓ dFlipSub σ (stdLag n K) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  rw [mem_dFlipSub hσ] at hv2
  have h1 : ∀ i, v (Sum.inr i) = 0 := fun i => by
    have h := congrFun (LinearMap.mem_ker.mp hv1) i
    simpa only [LinearMap.funLeft_apply, Pi.zero_apply] using h
  have h2 : ∀ i, v (Sum.inl i) = 0 := by
    intro i
    have h := congrFun (LinearMap.mem_ker.mp hv2) i
    have h' : σ (v (Sum.inl i)) = 0 := by
      simpa only [LinearMap.funLeft_apply, dFlip_apply_inr, Pi.zero_apply] using h
    exact (map_eq_zero_iff σ σ.injective).mp h' 
  funext x
  cases x with
  | inl i => exact h2 i
  | inr i => exact h1 i

end CFSG.ClassicalInvolution.PhanDn
