module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutTowerLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDetCommute
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Cover

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_mul_fieldAut_zpow_mem (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ γ₀ : MulAut (projectiveSL n F), ∀ α : MulAut (projectiveSL n F), α ^ p = 1 →
      ∃ i : ℤ, α * γ₀ ^ i ∈ linearAutGroup n F := by
  have : (linearAutGroup n F).Normal :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.linearAutGroup_normal hn
  obtain ⟨-, hnf⟩ := automorphism_generation (K := F) hn
  have htrans := standard_automorphism_transport (K := F) (n := n)
  have hcyc : IsCyclic (F ≃+* F) := CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card hℓ hf hF
  obtain ⟨σ₀, hσ₀⟩ := hcyc.exists_generator
  refine ⟨fieldAut n F σ₀, fun α hα => ?_⟩
  set π := QuotientGroup.mk' (linearAutGroup n F) with hπ
  set u := π (fieldAut n F σ₀) with hu
  set w := π (dualAut n F) with hw
  have hc : ∀ A, π (conjAut n F A) = 1 := fun A =>
    (QuotientGroup.eq_one_iff _).2 (conjAut_mem_linearAutGroup A)
  have hww : w * w = 1 := by rw [hw, ← map_mul, htrans.2.2.2.1, map_one]
  have huw : Commute u w := by
    change u * w = w * u
    rw [hu, hw, ← map_mul, ← map_mul]
    congr 1
    have h1 := htrans.2.2.2.2.2.1 σ₀
    have h2 := htrans.2.2.2.1
    calc fieldAut n F σ₀ * dualAut n F
        = dualAut n F * fieldAut n F σ₀ * dualAut n F * dualAut n F := by rw [h1]
      _ = dualAut n F * fieldAut n F σ₀ * (dualAut n F * dualAut n F) := by group
      _ = dualAut n F * fieldAut n F σ₀ := by rw [h2, mul_one]
  obtain ⟨A, σ, ε, hε, rfl⟩ := hnf α
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ₀ σ)
  have hπα : π (conjAut n F A * fieldAut n F (σ₀ ^ a) * dualAut n F ^ ε) = u ^ a * w ^ ε := by
    rw [map_mul, map_mul, hc, one_mul, map_zpow, map_zpow, map_pow]
  have hgoal : ∀ i : ℤ, u ^ a * w ^ ε * u ^ i = 1 → ∃ i : ℤ,
      conjAut n F A * fieldAut n F (σ₀ ^ a) * dualAut n F ^ ε * fieldAut n F σ₀ ^ i ∈
        linearAutGroup n F := by
    intro i hi
    refine ⟨i, (QuotientGroup.eq_one_iff _).1 ?_⟩
    change π _ = 1
    rw [map_mul, hπα, map_zpow]
    exact hi
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · refine hgoal (-a) ?_
    rw [pow_zero, mul_one, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  · have hp1 : (u ^ a * w) ^ p = 1 := by
      rw [← pow_one w, ← hπα, ← map_pow, hα, map_one]
    have hwp : w ^ p = w := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      rw [hk, pow_succ, pow_mul, sq, hww, one_pow, one_mul]
    rw [(huw.zpow_left a).mul_pow, hwp, ← zpow_natCast, ← _root_.zpow_mul] at hp1
    have hw' : w = u ^ (-(a * p)) := by
      rw [_root_.zpow_neg]
      exact eq_inv_of_mul_eq_one_right hp1
    refine hgoal (a * p - a) ?_
    rw [pow_one, hw', ← _root_.zpow_add, ← _root_.zpow_add]
    convert zpow_zero u using 2
    ring

theorem mem_inner_of_pow_eq_one (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hq : ¬ p ∣ Nat.card F - 1) {δ : MulAut (projectiveSL n F)} (hδ : δ ∈ linearAutGroup n F)
    (hδp : δ ^ p = 1) :
    δ ∈ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
  set D := linearAutGroup n F with hD
  set I := (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range with hI
  have : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have : Finite (MulAut (projectiveSL n F)) :=
    CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' _
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hδp]
    exact I.one_mem
  have hcard : Nat.card (D ⧸ I.subgroupOf D) ∣ Nat.gcd n (Nat.card F - 1) := by
    have : Nat.card (D ⧸ I.subgroupOf D) = (inner (projectiveSL n F)).relIndex D := rfl
    rw [this]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.relIndex_inner_linearAutGroup_dvd hn
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have h2 : orderOf x ∣ Nat.gcd n (Nat.card F - 1) := (orderOf_dvd_natCard x).trans hcard
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact hq (h2.trans (Nat.gcd_dvd_right _ _))
  rw [orderOf_eq_one_iff, hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem exists_conj_agree_of_isPGroup {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    (hqn : ¬ Nat.card F ^ n ≡ 1 [MOD p]) (P : Subgroup (projectiveSL n F)) (hP : IsPGroup p P)
    (A : GL (Fin n) F) : ∃ k : projectiveSL n F, ∀ x ∈ P, conjAut n F A x = k * x * k⁻¹ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set π₀ := proj n F with hπ₀
  set Q := P.comap π₀ with hQ
  have : Finite (SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (Subtype.val : SpecialLinearGroup (Fin n) F → Matrix (Fin n) (Fin n) F)
      Subtype.val_injective
  let φ : Q →* P := π₀.subgroupComap P
  have hφ : Function.Surjective φ := π₀.subgroupComap_surjective P (proj_surjective n F)
  obtain ⟨S⟩ : Nonempty (Sylow p Q) := inferInstance
  have hT : ((S.mapSurjective hφ : Sylow p P) : Subgroup P) = ⊤ :=
    ((S.mapSurjective hφ).is_maximal' (hP.of_equiv Subgroup.topEquiv.symm) le_top).symm
  rw [Sylow.coe_mapSurjective] at hT
  have hlift : ∀ x ∈ P, ∃ s ∈ (S : Subgroup Q), π₀ (s : SpecialLinearGroup (Fin n) F) = x := by
    intro x hx
    have hmem : (⟨x, hx⟩ : P) ∈ (S : Subgroup Q).map φ := by
      rw [hT]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsx⟩ := hmem
    exact ⟨s, hs, congrArg Subtype.val hsx⟩
  let P' : Subgroup (GL (Fin n) F) :=
    (S : Subgroup Q).map ((SpecialLinearGroup.toGL).comp Q.subtype)
  have hP' : IsPGroup p P' := S.isPGroup'.map _
  obtain ⟨c, hc, hdet⟩ := exists_commute_det_eq hpF P' hP'
    (by rwa [← Nat.card_eq_fintype_card]) (GeneralLinearGroup.det A)
  let b : SpecialLinearGroup (Fin n) F := ⟨((A * c⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
    by rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hdet, mul_inv_cancel,
      Units.val_one]⟩
  have hAbc : A = SpecialLinearGroup.toGL b * c := by
    apply Units.ext
    change (A : Matrix (Fin n) (Fin n) F) = ((A * c⁻¹ * c : GL (Fin n) F) : Matrix _ _ F)
    rw [inv_mul_cancel_right]
  refine ⟨π₀ b, fun x hx => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hlift x hx
  have hcs : conjAut n F c (π₀ s) = π₀ s := by
    rw [hπ₀, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation]
    have h1 := hc (SpecialLinearGroup.toGL (s : SpecialLinearGroup (Fin n) F))
      (Subgroup.mem_map_of_mem _ hs)
    have h2 : c * SpecialLinearGroup.toGL (s : SpecialLinearGroup (Fin n) F) * c⁻¹ =
        SpecialLinearGroup.toGL (s : SpecialLinearGroup (Fin n) F) := by
      rw [h1, mul_inv_cancel_right]
    have h3 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h2
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using h3
  rw [hAbc, map_mul, MulAut.mul_apply, hcs, conjAut_toGL, MulAut.conj_apply]

theorem detCoverAt_projectiveSL (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    (hq1 : ¬ p ∣ Nat.card F - 1) (hqn : ¬ Nat.card F ^ n ≡ 1 [MOD p]) :
    DetCoverAt (projectiveSL n F) p := by
  have hp : p.Prime := Fact.out
  refine ⟨linearAutGroup n F, commutator_mem_linearAutGroup hn hℓ hf hF,
    exists_mul_fieldAut_zpow_mem hn hℓ hf hF hp hp2,
    fun δ hδ hδp => mem_inner_of_pow_eq_one (by omega) hp hq1 hδ hδp, fun P hP δ hδ => ?_⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hδ
  exact exists_conj_agree_of_isPGroup hpF hqn P hP A

end Cover

end CFSG.AGLEmbedding
