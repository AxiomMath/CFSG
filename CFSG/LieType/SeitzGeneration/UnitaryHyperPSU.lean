module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperToral
public import CFSG.LieType.SeitzGeneration.UnitaryHyperGen
public import CFSG.LieType.SeitzGeneration.UnitarySplit
public import CFSG.LieType.SeitzGeneration.SpAnisoFinal

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.CTP
  CFSG.LinearGroups

variable {ℓ f p : ℕ} {K : Type} [Field K]

section Model

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem suid_unitaryInvolution_eq (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    SUid (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) n = StatedSU n (ℓ ^ f) K :=
  SUid_eq_statedSU h.card_eq_sq n

@[expose] def projSUid (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    SUid (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) n →*
      StatedProj (StatedSU n (ℓ ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K))).comp
    (MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h n)).toMonoidHom

theorem projSUid_surjective (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    Function.Surjective (projSUid h n) :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.subgroupCongr _).surjective

theorem projSUid_ker_scalar (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    ∀ g ∈ (projSUid h n).ker, ∃ c : K, matU g = c • 1 := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h2 := (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h2
  refine ⟨(c : K), ?_⟩
  have : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) := congrArg Units.val hc.symm
  rw [matU, this, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem card_ker_projSUid (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSUid h n).ker = Nat.gcd n (ℓ ^ f + 1) := by
  have hker : (projSUid h n).ker = (unitaryScalars h n).comap
      (MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h n)).toMonoidHom := by
    rw [projSUid, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', unitaryScalars_eq h hn]
  rw [hker, ← card_unitaryScalars h hn]
  exact Nat.card_congr
    ((MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h n)).toEquiv.subtypeEquiv fun _ => Iff.rfl)

end Model

theorem not_dvd_gcd_of_dvd_sub_one {q n : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q - 1) : ¬ p ∣ Nat.gcd n (q + 1) := by
  intro hd
  have h1 : p ∣ q + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h1 hpq
  have h3 : (q + 1) - (q - 1) = 2 := by omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem hyperGen_statedProj_unitary_toral (h : UnitaryFieldData ℓ f K) {n : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (hgcd : ¬ p ∣ Nat.gcd (n + 1) (ℓ ^ f + 1))
    {E : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) :
    HyperGen p (⊤ : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K))) E := by
  classical
  have hfin := h.finite
  have hfp : Fact p.Prime := ⟨hp⟩
  let π : unitarySU ℓ f K (n + 1) →* StatedProj (StatedSU (n + 1) (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin (n + 1)) K).subgroupOf (unitarySU ℓ f K (n + 1)))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk', ← unitaryScalars_eq h (by omega), card_unitaryScalars h (by omega)]
    exact hgcd
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ := exists_lift_elemAbelian π hπ hker hcomm hE.2
  have htop := hyperClosure_eq_top_unitarySU_toral h hp hpq hq A hAcomm hAexp (hAcard.trans hcard)
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ hyperClosure p ⊤ A := by
    rw [htop]
    exact Subgroup.mem_top g
  exact map_hyperClosure_le_of_lift hAE hAdis ⟨g, hg, rfl⟩

theorem hyperGen_statedProj_unitary_split (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ h.bar s * s ≠ 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f - 1) {E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) :
    HyperGen p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) E := by
  classical
  have hfin := h.finite
  have hfp : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hσbar : ∀ c, σ c = h.bar c := fun c => by
    rw [hσdef, CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have hdvd : ℓ ∣ p := (CharP.cast_eq_zero_iff K ℓ p).1 h0
    have hpl : p = ℓ := ((Nat.prime_dvd_prime_iff_eq h.prime hp).1 hdvd).symm
    have hf : f ≠ 0 := by have := h.one_le; omega
    have : p ∣ ℓ ^ f := by rw [hpl]; exact dvd_pow_self ℓ hf
    have h2 : p ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub this hpq
    rw [show ℓ ^ f - (ℓ ^ f - 1) = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hker : ¬ p ∣ Nat.card (projSUid h n).ker := by
    rw [card_ker_projSUid h (by omega)]
    exact not_dvd_gcd_of_dvd_sub_one hq1 hp hp2 hpq
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian (projSUid h n) (projSUid_surjective h n) hker hcomm hE.2
  let S : A → Module.End K (Fin n → K) := fun a =>
    Matrix.toLinAlgEquiv' (matU (a : SUid σ n))
  have hSapp : ∀ (a : A) (v : Fin n → K), S a v = (a : SUid σ n) • v := fun a v => by
    simp [S, Matrix.toLinAlgEquiv'_apply, smul_def, matU]
  have hScomm : ∀ a b : A, Commute (S a) (S b) := by
    intro a b
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hSapp, hSapp, hSapp, hSapp, ← mul_smul,
      ← mul_smul, hAcomm a a.2 b b.2]
  have hSpow : ∀ a : A, S a ^ p = 1 := by
    intro a
    have hmat : matU (a : SUid σ n) ^ p = 1 := by
      have := congrArg (fun g : SUid σ n => matU g) (hAexp a a.2)
      simpa [matU] using this
    simp only [S]
    rw [← map_pow, hmat, map_one]
  have hSiso : ∀ (a : A) (v w : Fin n → K),
      stdHermForm h n (S a v) (S a w) = stdHermForm h n v w := by
    intro a v w
    have hh := herm_smul_smul σ (a : SUid σ n) v w
    simp only [herm_def, hσbar] at hh
    rw [hSapp, hSapp, stdHermForm_apply, stdHermForm_apply]
    exact hh
  obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card A ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr ⟨fun x y => by
      rw [hcon x, hcon y]⟩
    rw [hAcard, hcard] at this
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  have hS1 : S a₀ ≠ 1 := by
    intro hS
    apply ha₀
    apply Subtype.ext
    refine ext_smul σ fun v => ?_
    have := congrArg (fun T : Module.End K (Fin n → K) => T v) hS
    simp only [Module.End.one_apply, hSapp] at this
    rw [this]
    simp
  obtain ⟨v, w₀, hv0, hvv, -, -, hvS⟩ := exists_hyperbolic_pair_of_ne_one h
    (stdHermForm_separatingLeft h n) hp hp2 hpq S hScomm hSpow hSiso a₀ hS1
  have hvv' : herm σ v v = 0 := by
    rw [herm_def]
    simp only [hσbar]
    rw [← stdHermForm_apply]
    exact hvv
  refine hyperGen_top_of_isotropic_unitary hσ hn (fun h3' => ?_) (projSUid h n)
    (projSUid_surjective h n) (projSUid_ker_scalar h n) hp hp2 hpK hE hcard
    (W := K ∙ v) ?_ ?_ ?_
  · obtain ⟨s, hs0, hs⟩ := h3 h3'
    exact ⟨s, hs0, by rw [hσbar]; exact hs⟩
  · exact fun hW => hv0 (Submodule.span_singleton_eq_bot.mp hW)
  · intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [herm_smul_left, herm_smul_right, hvv', mul_zero, mul_zero]
  · intro g hg w hw
    rw [← hAE] at hg
    obtain ⟨a, ha, hag⟩ := hg
    have hz : a⁻¹ * g ∈ (projSUid h n).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
    obtain ⟨c, hc⟩ := projSUid_ker_scalar h n _ hz
    have hc' : (((a⁻¹ * g : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1 := hc
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨μ, -, hμ, -⟩ := hvS ⟨a, ha⟩
    have hgz : g = a * (a⁻¹ * g) := by group
    rw [hgz, mul_smul, smul_def σ (a⁻¹ * g), hc', Matrix.smul_mulVec, Matrix.one_mulVec, smul_comm,
      ← hSapp ⟨a, ha⟩, map_smul, hμ]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self v)))

end CFSG.LieType.SeitzGeneration
