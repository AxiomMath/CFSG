module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwoPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Inner

open LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem units_eq_one_of_card_two (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h1).1.elim u 1

omit [Finite K] in
theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · have hx1 : x = 1 := by
      simpa using congrArg Units.val (units_eq_one_of_card_two hK (Units.mk0 x hx))
    rw [hx1, map_one]
    rfl

theorem mem_innerAut_of_odd_card_two (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    {x : MulAut (projectiveSL n K)} (hx : Odd (orderOf x)) :
    x ∈ innerAut (projectiveSL n K) := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinearAutGroup_of_odd hn hx)
  rw [ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one]
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h := congrArg Units.val (units_eq_one_of_card_two hK (GeneralLinearGroup.det A))
    rwa [GeneralLinearGroup.val_det_apply] at h
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin n) K, SpecialLinearGroup.toGL g = A :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  rw [← hg, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem mem_innerAut_of_mulEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G) {x : MulAut S}
    (h : MulAut.congr e x ∈ innerAut G) : x ∈ innerAut S := by
  obtain ⟨g, hg⟩ := h
  refine ⟨e.symm g, ?_⟩
  ext s
  have h1 := congrArg (fun f : MulAut G => f (e s)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  apply e.injective
  simp [MulAut.conj_apply, h1]

theorem mem_innerAut_psl_of_odd_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {n : ℕ} (hn : 3 ≤ n) {x : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)}
    (hx : Odd (orderOf x)) : x ∈ innerAut (ProjectiveSpecialLinearGroup (Fin n) F) := by
  refine mem_innerAut_of_mulEquiv (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F) ?_
  refine mem_innerAut_of_odd_card_two hF hn ?_
  rwa [MulEquiv.orderOf_eq]

end Inner

section Balance

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem isLocallyBalancedAbs_psl_three_two (hn : 3 ≤ n) (hF : Nat.card F = 2)
    (hinj : Function.Injective
      (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →*
        MulAut (ProjectiveSpecialLinearGroup (Fin n) F))) :
    IsLocallyBalancedAbs 3 3 (ProjectiveSpecialLinearGroup (Fin n) F) := by
  intro D hD hcard H hH _
  have hDin : D ≤ innerAut (ProjectiveSpecialLinearGroup (Fin n) F) := fun x hx =>
    mem_innerAut_psl_of_odd_card_two hF hn (by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one (hD.2 x hx)) with h | h
      · rw [h]; exact odd_one
      · rw [h]; decide)
  have hZ : Subgroup.center (SpecialLinearGroup (Fin n) F) = ⊥ := by
    have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega : 1 ≤ n) F
    rw [hF, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, Nat.dvd_one] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hπinj : Function.Injective (toPSL n F) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toPSL, hZ]
  set f := (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _).comp (toPSL n F) with hfdef
  have hf : Function.Injective f := hinj.comp hπinj
  have hDf : D ≤ f.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hDin hx
    obtain ⟨s, rfl⟩ := toPSL_surjective y
    exact ⟨s, rfl⟩
  set D₀ := D.comap f with hD₀
  have hD₀map : D₀.map f = D := Subgroup.map_comap_eq_self hDf
  have hD₀el : IsElemAbelian 3 D₀ := isElemAbelian_comap f hf hD
  have hD₀c : Nat.card D₀ = 27 := by
    rw [← Subgroup.card_map_of_injective hf, hD₀map, hcard]
    norm_num
  have h3 : ((3 : ℕ) : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card
    Nat.prime_three (by rw [hF]; norm_num)
  obtain ⟨E₀, hE₀D, hE₀, hE₀c, v, hv0, hv⟩ :=
    exists_plane_fixing_vector (by omega) (by exact_mod_cast h3) hD₀el hD₀c
  have hbot := localDeltaIn_eq_bot_psl_nonsplit_fix Nat.prime_three (by rw [hF]; norm_num)
    (by rw [hF]; norm_num) (by omega) hinj E₀ hE₀ (by rw [hE₀c]; norm_num)
    (Or.inr (Or.inr ⟨v, hv0, hv⟩)) hH
  have hle : (E₀.map (toPSL n F)).map
      (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) ≤ D := by
    rw [Subgroup.map_map, ← hfdef, ← hD₀map]
    exact Subgroup.map_mono hE₀D
  exact le_bot_iff.1 ((localDeltaIn_antitone H hle).trans hbot.le)

end Balance

theorem crossCharFamAt_A_three_two :
    CrossCharFamAt .A (fun idx p => ∃ m q, idx.1 = .A m q ∧ p = 3 ∧ q.card = 2) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨m, q, hd, rfl, hq⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm3 : 3 ≤ m + 1 := by
    by_contra h
    have := hrange.2 (by omega)
    omega
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) (Or.inl hm3)).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) (Or.inl hm3)).commutator_eq_top
  have hinjP := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_psl_three_two (n := m + 1) hm3 (by rw [hcardF, hq]) hinjP)

@[expose] def regimeANondiag (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1)

theorem crossCharFamAt_A_nondiag : CrossCharFamAt .A regimeANondiag := by
  rintro idx hk p hp hp2 hc ⟨m, q, hd, hnd⟩
  by_cases h32 : p = 3 ∧ q.card = 2
  · exact crossCharFamAt_A_three_two idx hk p hp hp2 hc ⟨m, q, hd, h32.1, h32.2⟩
  · exact crossCharFamAt_A idx hk p hp hp2 hc ⟨m, q, hd, hnd, h32⟩

theorem not_regimeANondiag_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (hk : DefChar.LieFamily.A.Matches idx.1) :
    ¬ regimeANondiag idx p ↔ ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧
      p ∣ q.card - 1 ∧ p ∣ m + 1 := by
  obtain ⟨m, q, hmq⟩ := hk
  constructor
  · intro h
    by_contra h'
    exact h ⟨m, q, hmq, fun hc => h' ⟨m, q, hmq, hc⟩⟩
  · rintro ⟨m', q', hmq', hc⟩ ⟨m'', q'', hmq'', h1⟩
    rw [hmq'] at hmq''
    obtain ⟨rfl, rfl⟩ : m' = m'' ∧ q' = q'' := by
      injection hmq'' with h3 h4
      exact ⟨h3, h4⟩
    exact h1 hc

theorem crossCharFamCat_A_of_diag
    (h : CrossCharFamAt .A fun idx p => ¬ regimeANondiag idx p) : CrossCharFamCat .A :=
  crossCharFamCat_of_at regimeANondiag crossCharFamAt_A_nondiag h

end CFSG.HardMathSupport.Timmesfeld.CrossChar
