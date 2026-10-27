module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHMinimal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator
import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHPower
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement

section HallHigman

variable {K : Type*} [Group K] {B Q : Subgroup K}

theorem hhMinimal_ne_bot (h : HHMinimal B Q) : Q ≠ ⊥ := fun hbot =>
  h.nontrivial (by rw [hbot, Subgroup.commutator_bot_left])

variable [Finite K]

theorem hhMinimal_commutator_eq_self {p d : ℕ} [Fact p.Prime] [Fact d.Prime] (hpd : p ≠ d)
    (h : HHMinimal B Q) (hQ : IsPGroup p Q) (hB : IsPGroup d B) : ⁅Q, B⁆ = Q :=
  GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime B Q B h.normalizes
    le_normalizer h.normalizes (IsPGroup.coprime_card_of_ne d p hpd.symm B Q hB hQ)
    h.nontrivial h.minimal

theorem hhMinimal_commutator_le_centralizer {p : ℕ} [Fact p.Prime] (h : HHMinimal B Q)
    (hQ : IsPGroup p Q) : ⁅Q, Q⁆ ≤ centralizer (B : Set K) := by
  have hRQ : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le_self Q
  have hBR : B ≤ normalizer ((⁅Q, Q⁆ : Subgroup K) : Set K) :=
    GorensteinWalter.le_normalizer_commutator_of_le_normalizer B Q Q h.normalizes h.normalizes
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  haveI : Group.IsSolvable ↥Q := inferInstance
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr (hhMinimal_ne_bot h)
  have hlt : ⁅Q, Q⁆ < Q := by
    have hcom : _root_.commutator ↥Q < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Q
    have hmap := (Subgroup.map_subtype_lt_map_subtype (G' := Q)
      (H := _root_.commutator ↥Q) (K := ⊤)).mpr hcom
    rwa [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hbot : ⁅⁅Q, Q⁆, B⁆ = ⊥ := by
    by_contra hne
    exact (lt_iff_le_not_ge.mp hlt).2 (h.minimal ⁅Q, Q⁆ hRQ hBR hne)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem hhMinimal_commutator_le_centralizer_self {p d : ℕ} [Fact p.Prime] [Fact d.Prime]
    (hpd : p ≠ d) (h : HHMinimal B Q) (hQ : IsPGroup p Q) (hB : IsPGroup d B) :
    ⁅Q, Q⁆ ≤ centralizer (Q : Set K) := by
  have hcomm : ⁅Q, B⁆ = Q := hhMinimal_commutator_eq_self hpd h hQ hB
  have hB' : ⁅Q, Q⁆ ≤ centralizer (B : Set K) := hhMinimal_commutator_le_centralizer h hQ
  have h1le : ⁅Q, ⁅Q, Q⁆⁆ ≤ ⁅Q, Q⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp (Subgroup.normalizer_commutator_ge_left Q Q)
  have h1 : ⁅⁅Q, ⁅Q, Q⁆⁆, B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h1le.trans hB')
  have hP'A : ⁅⁅Q, Q⁆, B⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hB'
  have h2 : ⁅⁅⁅Q, Q⁆, B⁆, Q⁆ = ⊥ := by rw [hP'A, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := B) (H₂ := Q)
    (H₃ := ⁅Q, Q⁆) h1 h2
  rw [Subgroup.commutator_comm B Q, hcomm, Subgroup.commutator_comm Q ⁅Q, Q⁆] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem hhMinimal_pow_mem_centralizer {p : ℕ} [Fact p.Prime] (h : HHMinimal B Q)
    (hQ : IsPGroup p Q) : ∀ x ∈ Q, x ^ p ∈ centralizer (B : Set K) := by
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr (hhMinimal_ne_bot h)
  let S : Set K := {y | ∃ x ∈ Q, y = x ^ p}
  let R : Subgroup K := Subgroup.closure S
  have hRQ : R ≤ Q := by
    show Subgroup.closure S ≤ Q
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact Q.pow_mem hx p
  have hBR : B ≤ normalizer (R : Set K) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.closure S).map (MulAut.conj b) = Subgroup.closure S
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.mp (h.normalizes hb) x).1 hx, ?_⟩
      rw [map_pow]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(MulAut.conj b)⁻¹ (x ^ p), ⟨(MulAut.conj b)⁻¹ x, ?_, map_pow _ x p⟩, ?_⟩
      · rw [MulAut.conj_inv_apply]
        simpa using (Subgroup.mem_normalizer_iff.mp (h.normalizes (inv_mem hb)) x).1 hx
      · show b * (b⁻¹ * x ^ p * b) * b⁻¹ = x ^ p
        group
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Subgroup ↥Q)
  haveI : N.Normal := NormalizerCondition.normal_of_coatom N
    (Group.normalizerCondition_of_isNilpotent (G := ↥Q)) hN
  have hNindex : N.index = p := (IsPGroup.isCoatom_iff_index_eq_prime (p := p) hQ).mp hN
  have hsub : R ≤ N.map (Subgroup.subtype Q) := by
    show Subgroup.closure S ≤ N.map (Subgroup.subtype Q)
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(⟨x, hx⟩ : ↥Q) ^ p, ?_, by simp⟩
    have hxN := N.pow_index_mem (⟨x, hx⟩ : ↥Q)
    rwa [hNindex] at hxN
  have hNlt : N.map (Subgroup.subtype Q) < Q := by
    have hmap := (Subgroup.map_subtype_lt_map_subtype (G' := Q) (H := N) (K := ⊤)).mpr hN.lt_top
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hne : ⁅R, B⁆ = ⊥ := by
    by_contra hne'
    exact (lt_iff_le_not_ge.mp (lt_of_le_of_lt hsub hNlt)).2 (h.minimal R hRQ hBR hne')
  intro x hx
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hne (Subgroup.subset_closure ⟨x, hx, rfl⟩)

theorem sixteen_le_relIndex_centralizer_of_fiveGroup (hQ : IsPGroup 2 Q) (hB : IsPGroup 5 B)
    (hBQ : B ≤ normalizer (Q : Set K)) (hne : ¬ Q ≤ centralizer (B : Set K)) :
    16 ≤ (centralizer (B : Set K)).relIndex Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup K, F = Q ⊓ centralizer (B : Set K) := ⟨_, rfl⟩
  have hFQ : F ≤ Q := by rw [hF]; exact inf_le_left
  have hFC : F ≤ centralizer (B : Set K) := by rw [hF]; exact inf_le_right
  have hrelF : F.relIndex Q = (centralizer (B : Set K)).relIndex Q := by
    rw [hF, inf_comm]
    exact Subgroup.inf_relIndex_right (centralizer (B : Set K)) Q
  rw [← hrelF]
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hdvd : F.relIndex Q ∣ 2 ^ m := by
    rw [← hm]
    exact F.relIndex_dvd_card Q
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hn1 : F.relIndex Q ≠ 1 := by
    intro h
    exact hne ((Subgroup.relIndex_eq_one.mp h).trans hFC)
  have hsne : s ≠ 0 := by
    rintro rfl
    exact hn1 (by rw [hs, pow_zero])
  obtain ⟨X, hX⟩ : ∃ X : Set K, X = (Q : Set K) \ (F : Set K) := ⟨_, rfl⟩
  have hXstable : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    rw [hX, Set.mem_sdiff] at hx ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hx.1, fun hcon => hx.2 ?_⟩
    rw [hF] at hcon ⊢
    refine Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hcomm : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b :=
      (Subgroup.mem_centralizer_iff.mp hcon.2) b hb
    have hxeq : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
        _ = b * x * b⁻¹ := by group
    rw [hxeq]
    exact (Subgroup.mem_centralizer_iff.mp hcon.2) c hc
  let _ : MulAction B X :=
    { smul := fun b x => ⟨(b : K) * (x : K) * (b : K)⁻¹, hXstable (b : K) b.2 (x : K) x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : B) : K) * (x : K) * ((1 : B) : K)⁻¹ = (x : K)
        simp)
      mul_smul := fun b b' x => Subtype.ext (by
        show ((b * b' : B) : K) * (x : K) * ((b * b' : B) : K)⁻¹ =
          (b : K) * ((b' : K) * (x : K) * (b' : K)⁻¹) * (b : K)⁻¹
        simp [mul_assoc]) }
  have hfix_empty : MulAction.fixedPoints B X = (∅ : Set X) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, hx⟩ hfix
    rw [MulAction.mem_fixedPoints] at hfix
    rw [hX, Set.mem_sdiff] at hx
    refine hx.2 ?_
    rw [hF]
    refine Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hval : c * x * c⁻¹ = x := congrArg Subtype.val (hfix ⟨c, hc⟩)
    exact mul_inv_eq_iff_eq_mul.mp hval
  have hdvdX : 5 ∣ Nat.card X := by
    have hcong := hB.card_modEq_card_fixedPoints X
    rw [hfix_empty] at hcong
    simp only [Nat.card_of_isEmpty] at hcong
    exact Nat.modEq_zero_iff_dvd.mp hcong
  have hcardQ : F.relIndex Q * Nat.card F = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := Q)
    rwa [inf_eq_left.mpr hFQ] at h
  have hcardX : Nat.card X = Nat.card F * (F.relIndex Q - 1) := by
    have hFsub : (F : Set K) ⊆ (Q : Set K) := fun x hx => hFQ hx
    have h1 : Nat.card X = Nat.card Q - Nat.card F := by
      rw [hX]
      exact Set.ncard_sdiff hFsub
    rw [h1, ← hcardQ, Nat.mul_comm (F.relIndex Q) (Nat.card F), Nat.mul_sub_left_distrib,
      Nat.mul_one]
  have hcop : Nat.Coprime 5 (Nat.card F) := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro hdivF
    have hFdvd : Nat.card F ∣ 2 ^ m := by
      rw [← hm, ← hcardQ]
      exact dvd_mul_left (Nat.card F) (F.relIndex Q)
    have h52 : 5 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by norm_num) (hdivF.trans hFdvd))
    omega
  have hdiv : 5 ∣ F.relIndex Q - 1 := by
    have h := hdvdX
    rw [hcardX] at h
    exact hcop.dvd_of_dvd_mul_left h
  rw [hs] at hdiv ⊢
  have hs4 : 4 ≤ s := by
    by_contra hlt
    interval_cases s
    · exact hsne rfl
    all_goals norm_num at hdiv
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs4

end HallHigman

section Linear

variable {F : Type*} [Field F]

theorem linearIndependent_of_jointEigenvector {V G ι : Type*} [AddCommGroup V] [Module F V]
    (φ : G → Module.End F V) (v : ι → V) (t : ι → G → F) (hv : ∀ i, v i ≠ 0)
    (ht : ∀ i g, φ g (v i) = t i g • v i) (hinj : Function.Injective t) :
    LinearIndependent F v :=
  iSupIndep.linearIndependent _ ((TauCeti.iSupIndep_iInf_eigenspace φ).comp hinj)
    (fun i => (Submodule.mem_iInf _).mpr fun g => Module.End.mem_eigenspace_iff.mpr (ht i g)) hv

theorem iterate_fixed_of_finrank_lt {r : ℕ} (hr : r.Prime) {V G : Type*} [AddCommGroup V]
    [Module F V] [Module.Finite F V] (hV : Module.finrank F V < r) (φ : G → Module.End F V)
    (T : (G → F) → G → F) (s₀ : G → F) {k : ℕ} (hT : T^[r ^ k] s₀ = s₀) (v : ℕ → V)
    (hv : ∀ j, v j ≠ 0) (hφ : ∀ j g, φ g (v j) = (T^[j] s₀) g • v j) : T s₀ = s₀ := by
  have hdvd : Function.minimalPeriod T s₀ ∣ r ^ k :=
    Function.IsPeriodicPt.minimalPeriod_dvd hT
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  rcases i with _ | i
  · have h1 := Function.iterate_minimalPeriod (f := T) (x := s₀)
    rwa [hi, pow_zero, Function.iterate_one] at h1
  · exfalso
    have hr' : r ≤ Function.minimalPeriod T s₀ := by
      rw [hi]
      exact le_self_pow hr.one_lt.le (Nat.succ_ne_zero i)
    have hinj : Function.Injective (fun j : Fin r => T^[(j : ℕ)] s₀) := fun a b hab =>
      Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (lt_of_lt_of_le a.isLt hr') (lt_of_lt_of_le b.isLt hr')).mp hab)
    have hli := linearIndependent_of_jointEigenvector φ (fun j : Fin r => v j)
      (fun j : Fin r => T^[(j : ℕ)] s₀) (fun j => hv j) (fun j g => hφ j g) hinj
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    omega

theorem iterate_comp_conj {K X : Type*} [Group K] (b : K) (s : K → X) (n : ℕ) :
    (fun s : K → X => fun g => s (b⁻¹ * g * b))^[n] s = fun g => s ((b ^ n)⁻¹ * g * b ^ n) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    funext g
    simp only [pow_succ, mul_inv_rev, mul_assoc]

theorem exists_jointEigenProj {A : Type*} [Ring A] [Algebra F A] (hF : (2 : F) ≠ 0)
    (S : Finset A) (hS2 : ∀ s ∈ S, s * s = 1) (hSc : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    {z : A} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzS : ∀ s ∈ S, Commute z s) :
    ∃ π : A, π ≠ 0 ∧ z * π = -π ∧ (∀ s ∈ S, s * π = π ∨ s * π = -π) ∧
      ∀ a : A, Commute a z → (∀ s ∈ S, Commute a s) → Commute a π := by
  classical
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : A, π₀ = (2⁻¹ : F) • (1 - z) := ⟨_, rfl⟩
  have h2 : (2⁻¹ : F) * 2 = 1 := inv_mul_cancel₀ hF
  have hπ₀ne : π₀ ≠ 0 := by
    intro h0
    apply hz1
    have h1 : (2 : F) • π₀ = 1 - z := by rw [hπ₀, smul_smul, mul_inv_cancel₀ hF, one_smul]
    rw [h0, smul_zero] at h1
    exact (sub_eq_zero.mp h1.symm).symm
  have hzπ₀ : z * π₀ = -π₀ := by
    rw [hπ₀, mul_smul_comm, mul_sub, mul_one, hz2, ← neg_sub 1 z, smul_neg]
  have hcπ₀ : ∀ a : A, Commute a z → Commute a π₀ := fun a ha => by
    rw [hπ₀]
    exact ((Commute.one_right a).sub_right ha).smul_right _
  have key : ∀ S' : Finset A, S' ⊆ S → ∃ c : A, π₀ * c ≠ 0 ∧
      (∀ s ∈ S', s * (π₀ * c) = π₀ * c ∨ s * (π₀ * c) = -(π₀ * c)) ∧
      ∀ a : A, (∀ s ∈ S', Commute a s) → Commute a c := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, by rwa [mul_one], fun s hs => absurd hs (Finset.notMem_empty s),
        fun a _ => Commute.one_right a⟩
    | insert s S' hs ih =>
      intro hsub
      obtain ⟨c, hc0, hcS, hca⟩ := ih ((Finset.subset_insert s S').trans hsub)
      have hsS : s ∈ S := hsub (Finset.mem_insert_self s S')
      have hsc : Commute s c :=
        hca s fun t ht => hSc s hsS t (hsub (Finset.mem_insert_of_mem ht))
      have hsπ₀ : Commute s π₀ := hcπ₀ s (hzS s hsS).symm
      have step : ∀ e : A, (s * e = e ∨ s * e = -e) → (∀ a : A, Commute a s → Commute a e) →
          π₀ * (c * e) ≠ 0 → ∃ c' : A, π₀ * c' ≠ 0 ∧
            (∀ t ∈ insert s S', t * (π₀ * c') = π₀ * c' ∨ t * (π₀ * c') = -(π₀ * c')) ∧
            ∀ a : A, (∀ t ∈ insert s S', Commute a t) → Commute a c' := by
        intro e hse hae hne
        refine ⟨c * e, hne, fun t ht => ?_, fun a ha => ?_⟩
        · rcases Finset.mem_insert.mp ht with heq | ht
          · rw [heq]
            have hcomm : s * (π₀ * (c * e)) = π₀ * (c * (s * e)) := by
              rw [← mul_assoc, hsπ₀.eq, mul_assoc, ← mul_assoc s c, hsc.eq, mul_assoc]
            rcases hse with h | h
            · left
              rw [hcomm, h]
            · right
              rw [hcomm, h, mul_neg, mul_neg]
          · rcases hcS t ht with h | h
            · left
              rw [← mul_assoc π₀, ← mul_assoc, h]
            · right
              rw [← mul_assoc π₀, ← mul_assoc, h, neg_mul]
        · exact (hca a fun t ht => ha t (Finset.mem_insert_of_mem ht)).mul_right
            (hae a (ha s (Finset.mem_insert_self s S')))
      obtain ⟨eP, heP⟩ : ∃ e : A, e = (2⁻¹ : F) • (1 + s) := ⟨_, rfl⟩
      obtain ⟨eM, heM⟩ : ∃ e : A, e = (2⁻¹ : F) • (1 - s) := ⟨_, rfl⟩
      have hsum : eP + eM = 1 := by
        rw [heP, heM, ← smul_add, add_add_sub_cancel, ← two_smul F (1 : A), smul_smul, h2,
          one_smul]
      have hseP : s * eP = eP := by
        rw [heP, mul_smul_comm, mul_add, mul_one, hS2 s hsS, add_comm]
      have hseM : s * eM = -eM := by
        rw [heM, mul_smul_comm, mul_sub, mul_one, hS2 s hsS, ← neg_sub 1 s, smul_neg]
      have haeP : ∀ a : A, Commute a s → Commute a eP := fun a ha => by
        rw [heP]
        exact ((Commute.one_right a).add_right ha).smul_right _
      have haeM : ∀ a : A, Commute a s → Commute a eM := fun a ha => by
        rw [heM]
        exact ((Commute.one_right a).sub_right ha).smul_right _
      by_cases hP : π₀ * (c * eP) = 0
      · refine step eM (Or.inr hseM) haeM fun hM => hc0 ?_
        calc π₀ * c = π₀ * (c * (eP + eM)) := by rw [hsum, mul_one]
          _ = π₀ * (c * eP) + π₀ * (c * eM) := by rw [mul_add, mul_add]
          _ = 0 := by rw [hP, hM, add_zero]
      · exact step eP (Or.inl hseP) haeP hP
  obtain ⟨c, hc0, hcS, hca⟩ := key S (Finset.Subset.refl S)
  refine ⟨π₀ * c, hc0, by rw [← mul_assoc, hzπ₀, neg_mul], hcS, fun a haz has => ?_⟩
  exact (hcπ₀ a haz).mul_right (hca a has)

theorem eq_zero_of_mul_eq_self_of_mul_eq_neg {A : Type*} [Ring A] [Algebra F A]
    (hF : (2 : F) ≠ 0) {z π : A} (h1 : z * π = π) (h2 : z * π = -π) : π = 0 := by
  have hππ : π = -π := h1.symm.trans h2
  have h2π : (2 : F) • π = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hππ]
    exact neg_add_cancel π
  exact (smul_eq_zero.mp h2π).resolve_left hF

variable {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]

theorem commute_of_sq_eq_one_of_normalizes {r : ℕ} (hr : r.Prime) (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W < r) {E : Subgroup (Module.End F W)ˣ} [Finite E]
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {b : (Module.End F W)ˣ} {k : ℕ} (hb : b ^ (r ^ k) = 1)
    (hbE : b ∈ normalizer (E : Set (Module.End F W)ˣ)) : ∀ e ∈ E, b * e = e * b := by
  classical
  intro h hh
  by_contra hne
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hbh : b * h * b⁻¹ ∈ E := (mem_normalizer_iff.mp hbE h).mp hh
  obtain ⟨h', hh'def⟩ : ∃ h' : (Module.End F W)ˣ, h' = h⁻¹ * (b * h * b⁻¹) := ⟨_, rfl⟩
  have hh' : h' ∈ E := hh'def ▸ E.mul_mem (E.inv_mem hh) hbh
  have hh'1 : ((h' : (Module.End F W)ˣ) : Module.End F W) ≠ 1 := by
    intro h1
    apply hne
    have h2 : h⁻¹ * (b * h * b⁻¹) = 1 := hh'def ▸ Units.ext h1
    have h3 : b * h * b⁻¹ = h := (inv_mul_eq_one.mp h2).symm
    calc b * h = b * h * b⁻¹ * b := by group
      _ = h * b := by rw [h3]
  haveI : Fintype E := Fintype.ofFinite E
  let S : Finset (Module.End F W) :=
    Finset.univ.image fun e : E => ((e : (Module.End F W)ˣ) : Module.End F W)
  have hS : ∀ a ∈ S, ∃ e ∈ E, a = ((e : (Module.End F W)ˣ) : Module.End F W) := by
    intro a ha
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨e, e.2, rfl⟩
  have hmemS : ∀ e ∈ E, ((e : (Module.End F W)ˣ) : Module.End F W) ∈ S := fun e he =>
    Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩
  have hcoe2 : ∀ e ∈ E, ((e : (Module.End F W)ˣ) : Module.End F W) * e = 1 := fun e he => by
    rw [← Units.val_mul, hE2 e he, Units.val_one]
  have hcoec : ∀ e ∈ E, ∀ f ∈ E,
      Commute ((e : (Module.End F W)ˣ) : Module.End F W) (f : Module.End F W) :=
    fun e he f hf => Commute.units_val (hEc e he f hf)
  obtain ⟨π, hπ0, hzπ, hSπ, -⟩ := exists_jointEigenProj hF2 S
    (fun s hs => by obtain ⟨e, he, rfl⟩ := hS s hs; exact hcoe2 e he)
    (fun s hs t ht => by
      obtain ⟨e, he, rfl⟩ := hS s hs
      obtain ⟨f, hf, rfl⟩ := hS t ht
      exact hcoec e he f hf)
    (hcoe2 h' hh') hh'1
    (fun s hs => by obtain ⟨e, he, rfl⟩ := hS s hs; exact hcoec h' hh' e he)
  let χ : (Module.End F W)ˣ → F := fun u => if (u : Module.End F W) * π = π then 1 else -1
  have hχ : ∀ e ∈ E, ((e : (Module.End F W)ˣ) : Module.End F W) * π = χ e • π := by
    intro e he
    by_cases h1 : ((e : (Module.End F W)ˣ) : Module.End F W) * π = π
    · simp only [χ, if_pos h1, one_smul, h1]
    · rcases hSπ _ (hmemS e he) with h2 | h2
      · exact absurd h2 h1
      · simp only [χ, if_neg h1, neg_one_smul, h2]
  have hχsq : ∀ u, χ u * χ u = 1 := fun u => by
    by_cases h1 : (u : Module.End F W) * π = π <;> simp [χ, h1]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, π w₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hπ0 (LinearMap.ext hall)
  have hχw : ∀ e ∈ E, ((e : (Module.End F W)ˣ) : Module.End F W) (π w₀) = χ e • π w₀ :=
    fun e he => by rw [← Module.End.mul_apply, hχ e he, LinearMap.smul_apply]
  have hbn : ∀ (n : ℕ) (g : (Module.End F W)ˣ), (b ^ n)⁻¹ * g * b ^ n ∈ E ↔ g ∈ E := by
    intro n g
    have hbnE : (b ^ n)⁻¹ ∈ normalizer (E : Set (Module.End F W)ˣ) := inv_mem (pow_mem hbE n)
    rw [mem_normalizer_iff.mp hbnE g, inv_inv]
  let s₀ : (Module.End F W)ˣ → F := fun g => if g ∈ E then χ g else 0
  let φ : (Module.End F W)ˣ → Module.End F W := fun g =>
    if g ∈ E then ((g : (Module.End F W)ˣ) : Module.End F W) else 0
  let v : ℕ → W := fun j => (((b ^ j : (Module.End F W)ˣ)) : Module.End F W) (π w₀)
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j h0
    apply hw₀
    have h1 := congrArg (((((b ^ j)⁻¹ : (Module.End F W)ˣ)) : Module.End F W)) h0
    rwa [map_zero, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply] at h1
  have hφv : ∀ j g, φ g (v j) = ((fun s : (Module.End F W)ˣ → F => fun g => s (b⁻¹ * g * b))^[j]
      s₀) g • v j := by
    intro j g
    rw [iterate_comp_conj]
    by_cases hg : g ∈ E
    · have hg' : (b ^ j)⁻¹ * g * b ^ j ∈ E := (hbn j g).mpr hg
      have hconj : ((g : (Module.End F W)ˣ) : Module.End F W) *
          (((b ^ j : (Module.End F W)ˣ)) : Module.End F W) =
          (((b ^ j : (Module.End F W)ˣ)) : Module.End F W) *
            ((((b ^ j)⁻¹ * g * b ^ j : (Module.End F W)ˣ)) : Module.End F W) := by
        rw [← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      simp only [φ, s₀, v, if_pos hg, if_pos hg']
      rw [← Module.End.mul_apply, hconj, Module.End.mul_apply, hχw _ hg', map_smul]
    · have hg' : (b ^ j)⁻¹ * g * b ^ j ∉ E := fun h1 => hg ((hbn j g).mp h1)
      simp only [φ, s₀, if_neg hg, if_neg hg', LinearMap.zero_apply, zero_smul]
  have hT : (fun s : (Module.End F W)ˣ → F => fun g => s (b⁻¹ * g * b))^[r ^ k] s₀ = s₀ := by
    rw [iterate_comp_conj, hb]
    funext g
    simp
  have hfix := iterate_fixed_of_finrank_lt hr hW φ _ s₀ hT v hv0 hφv
  have hχh : χ (b * h * b⁻¹) = χ h := by
    have h1 := congrFun hfix (b * h * b⁻¹)
    have hconj : b⁻¹ * (b * h * b⁻¹) * b = h := by group
    simp only [s₀] at h1
    rw [hconj, if_pos hh, if_pos hbh] at h1
    exact h1.symm
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hE2 h hh)
  have hh'π : ((h' : (Module.End F W)ˣ) : Module.End F W) * π = π := by
    rw [hh'def, Units.val_mul, mul_assoc, hχ _ hbh, mul_smul_comm, hhinv, hχ _ hh, smul_smul,
      hχh, hχsq, one_smul]
  exact hπ0 (eq_zero_of_mul_eq_self_of_mul_eq_neg hF2 hh'π hzπ)

theorem commute_of_five_normalizes_two [Finite F] (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W ≤ 3) {R : Subgroup (Module.End F W)ˣ} (hR : IsPGroup 2 R)
    {y : (Module.End F W)ˣ} (hy : ∃ k : ℕ, y ^ (5 ^ k) = 1)
    (hyR : y ∈ Subgroup.normalizer (R : Set (Module.End F W)ˣ)) :
    ∀ x ∈ R, y * x = x * y := by
  classical
  obtain ⟨k, hk⟩ := hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F W)ˣ :=
    Finite.of_injective (fun u : (Module.End F W)ˣ => (u : Module.End F W)) Units.val_injective
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  let B : Subgroup (Module.End F W)ˣ := Subgroup.zpowers y
  have hBk : ∀ b ∈ B, b ^ (5 ^ k) = 1 := fun b hb =>
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hb).trans (orderOf_dvd_of_pow_eq_one hk))
  have hB : IsPGroup 5 B := fun b => ⟨k, Subtype.ext (by simpa using hBk b b.2)⟩
  have hBR : B ≤ normalizer (R : Set (Module.End F W)ˣ) := Subgroup.zpowers_le.mpr hyR
  by_contra hcon
  have hne : ⁅R, B⁆ ≠ ⊥ := by
    intro hbot
    apply hcon
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hx)) y (Subgroup.mem_zpowers y)
  obtain ⟨Q, hQR, hmin⟩ := exists_hhMinimal hBR hne
  have hQ : IsPGroup 2 Q := hR.to_le hQR
  have h1 : ⁅Q, B⁆ = Q := hhMinimal_commutator_eq_self (by norm_num) hmin hQ hB
  have h2 : ⁅Q, Q⁆ ≤ centralizer (B : Set (Module.End F W)ˣ) :=
    hhMinimal_commutator_le_centralizer hmin hQ
  have h3 : ⁅Q, Q⁆ ≤ centralizer (Q : Set (Module.End F W)ˣ) :=
    hhMinimal_commutator_le_centralizer_self (by norm_num) hmin hQ hB
  have h4 : ∀ x ∈ Q, x ^ 2 ∈ centralizer (B : Set (Module.End F W)ˣ) :=
    hhMinimal_pow_mem_centralizer hmin hQ
  have h5 : Q ⊓ centralizer (B : Set (Module.End F W)ˣ) ≤ centralizer (Q : Set _) :=
    inf_centralizer_le_centralizer_self hmin.normalizes h1 h3 h2
  have hnot : ¬ Q ≤ centralizer (B : Set (Module.End F W)ˣ) := fun hle =>
    hmin.nontrivial (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  by_cases hab : ∀ g ∈ Q, ∀ x ∈ Q, g * x = x * g
  ·
    let Ω : Subgroup (Module.End F W)ˣ :=
      { carrier := {x | x ∈ Q ∧ x * x = 1}
        mul_mem' := by
          rintro a c ⟨ha, ha2⟩ ⟨hc, hc2⟩
          refine ⟨Q.mul_mem ha hc, ?_⟩
          calc a * c * (a * c) = a * (c * a) * c := by group
            _ = a * (a * c) * c := by rw [hab c hc a ha]
            _ = a * a * (c * c) := by group
            _ = 1 := by rw [ha2, hc2, one_mul]
        one_mem' := ⟨Q.one_mem, one_mul 1⟩
        inv_mem' := by
          rintro a ⟨ha, ha2⟩
          exact ⟨Q.inv_mem ha, by rw [← mul_inv_rev, ha2, inv_one]⟩ }
    have hΩ : ∀ x, x ∈ Ω ↔ x ∈ Q ∧ x * x = 1 := fun _ => Iff.rfl
    have hle : ⁅Q, B⁆ ≤ Ω := by
      rw [Subgroup.commutator_le]
      intro q hq b hb
      have hq' : b * q⁻¹ * b⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp (hmin.normalizes hb) q⁻¹).mp (Q.inv_mem hq)
      have hdecomp : ⁅q, b⁆ = q * (b * q⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
      have hcomm : q * (b * q⁻¹ * b⁻¹) = (b * q⁻¹ * b⁻¹) * q := hab q hq _ hq'
      have hcb : Commute b (q * q)⁻¹ := by
        have hb2 : b * q ^ 2 = q ^ 2 * b := (Subgroup.mem_centralizer_iff.mp (h4 q hq)) b hb
        rw [sq] at hb2
        exact Commute.inv_right hb2
      have hq'sq : (b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹) = (q * q)⁻¹ := by
        calc (b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹) = b * (q * q)⁻¹ * b⁻¹ := by group
          _ = (q * q)⁻¹ := by rw [hcb.eq]; group
      refine (hΩ _).mpr ⟨by rw [hdecomp]; exact Q.mul_mem hq hq', ?_⟩
      rw [hdecomp]
      calc q * (b * q⁻¹ * b⁻¹) * (q * (b * q⁻¹ * b⁻¹))
          = q * ((b * q⁻¹ * b⁻¹) * q) * (b * q⁻¹ * b⁻¹) := by group
        _ = q * (q * (b * q⁻¹ * b⁻¹)) * (b * q⁻¹ * b⁻¹) := by rw [← hcomm]
        _ = (q * q) * ((b * q⁻¹ * b⁻¹) * (b * q⁻¹ * b⁻¹)) := by group
        _ = 1 := by rw [hq'sq, mul_inv_cancel]
    have hsq : ∀ x ∈ Q, x * x = 1 := fun x hx => ((hΩ x).mp (hle (h1.ge hx))).2
    exact hnot fun q hq => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      commute_of_sq_eq_one_of_normalizes (by norm_num : Nat.Prime 5) hF (by omega) hsq hab
        (hBk b hb) (hmin.normalizes hb) q hq
  ·
    push Not at hab
    obtain ⟨g₀, hg₀, x₀, hx₀, hne₀⟩ := hab
    have hcent : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q, ⁅g, x⁆ * h = h * ⁅g, x⁆ := fun g hg x hx h hh =>
      ((Subgroup.mem_centralizer_iff.mp (h3 (Subgroup.commutator_mem_commutator hg hx))) h hh).symm
    have hcB : ∀ g ∈ Q, ∀ x ∈ Q, ∀ b ∈ B, b * ⁅g, x⁆ = ⁅g, x⁆ * b := fun g hg x hx b hb =>
      (Subgroup.mem_centralizer_iff.mp (h2 (Subgroup.commutator_mem_commutator hg hx))) b hb
    have hcQ : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q := fun g hg x hx =>
      Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator hg hx)
    have hinv : ∀ g ∈ Q, ∀ x ∈ Q, ⁅g, x⁆ * ⁅g, x⁆ = 1 := by
      intro g hg x hx
      have hsqZ : x * g ^ 2 = g ^ 2 * x :=
        (Subgroup.mem_centralizer_iff.mp
          (h5 (Subgroup.mem_inf.mpr ⟨Q.pow_mem hg 2, h4 g hg⟩))) x hx
      have hc : ⁅g, x⁆ * g = g * ⁅g, x⁆ := hcent g hg x hx g hg
      have hgx : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
      have hg2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by rw [← hsqZ]; group
      have h6 : g ^ 2 * x * (g ^ 2)⁻¹ = ⁅g, x⁆ * ⁅g, x⁆ * x := by
        calc g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [sq]; group
          _ = g * (⁅g, x⁆ * x) * g⁻¹ := by rw [hgx]
          _ = (g * ⁅g, x⁆) * x * g⁻¹ := by group
          _ = (⁅g, x⁆ * g) * x * g⁻¹ := by rw [hc]
          _ = ⁅g, x⁆ * (g * x * g⁻¹) := by group
          _ = ⁅g, x⁆ * ⁅g, x⁆ * x := by rw [hgx, mul_assoc]
      rw [hg2] at h6
      exact mul_right_cancel (h6.symm.trans (one_mul x).symm)
    have hbil : ∀ g a c : (Module.End F W)ˣ, ⁅g, c⁆ * a = a * ⁅g, c⁆ →
        ⁅g, a * c⁆ = ⁅g, a⁆ * ⁅g, c⁆ := by
      intro g a c hc
      have hc' : ⁅g, c⁆ * a⁻¹ = a⁻¹ * ⁅g, c⁆ := (Commute.inv_right hc).eq
      calc ⁅g, a * c⁆ = g * a * g⁻¹ * (⁅g, c⁆ * a⁻¹) := by group
        _ = g * a * g⁻¹ * (a⁻¹ * ⁅g, c⁆) := by rw [hc']
        _ = ⁅g, a⁆ * ⁅g, c⁆ := by group
    have hcinv : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁻¹⁆ = ⁅g, q⁆ := by
      intro g hg q hq
      have h6 : ⁅g, q * q⁻¹⁆ = ⁅g, q⁆ * ⁅g, q⁻¹⁆ :=
        hbil g q q⁻¹ (hcent g hg q⁻¹ (Q.inv_mem hq) q hq)
      rw [mul_inv_cancel, commutatorElement_one_right] at h6
      rw [eq_inv_of_mul_eq_one_right h6.symm, inv_eq_of_mul_eq_one_right (hinv g hg q hq)]
    let C : Set (Module.End F W) :=
      {a | ∃ g ∈ Q, ∃ x ∈ Q, a = ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W)}
    let S : Finset (Module.End F W) := C.toFinite.toFinset
    have hS : ∀ a ∈ S, ∃ g ∈ Q, ∃ x ∈ Q,
        a = ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) := fun a ha =>
      (Set.Finite.mem_toFinset (Set.toFinite C)).mp ha
    have hmemS : ∀ g ∈ Q, ∀ x ∈ Q, ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) ∈ S :=
      fun g hg x hx => (Set.Finite.mem_toFinset (Set.toFinite C)).mpr ⟨g, hg, x, hx, rfl⟩
    have hcoe2 : ∀ g ∈ Q, ∀ x ∈ Q, ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) *
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) = 1 := fun g hg x hx => by
      rw [← Units.val_mul, hinv g hg x hx, Units.val_one]
    have hcoeQ : ∀ g ∈ Q, ∀ x ∈ Q, ∀ h ∈ Q,
        Commute ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) (h : Module.End F W) :=
      fun g hg x hx h hh => Commute.units_val (hcent g hg x hx h hh)
    have hz1 : ((⁅g₀, x₀⁆ : (Module.End F W)ˣ) : Module.End F W) ≠ 1 := fun h6 =>
      hne₀ (commutatorElement_eq_one_iff_mul_comm.mp (Units.ext h6))
    obtain ⟨π, hπ0, hzπ, hSπ, hπc⟩ := exists_jointEigenProj hF2 S
      (fun s hs => by obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs; exact hcoe2 g hg x hx)
      (fun s hs t ht => by
        obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs
        obtain ⟨g', hg', x', hx', rfl⟩ := hS t ht
        exact hcoeQ g hg x hx _ (hcQ g' hg' x' hx'))
      (hcoe2 g₀ hg₀ x₀ hx₀) hz1
      (fun s hs => by
        obtain ⟨g, hg, x, hx, rfl⟩ := hS s hs
        exact hcoeQ g₀ hg₀ x₀ hx₀ _ (hcQ g hg x hx))
    let χ : (Module.End F W)ˣ → F := fun u => if (u : Module.End F W) * π = π then 1 else -1
    have hχ : ∀ g ∈ Q, ∀ x ∈ Q,
        ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = χ ⁅g, x⁆ • π := by
      intro g hg x hx
      by_cases h6 : ((⁅g, x⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π
      · simp only [χ, if_pos h6, one_smul, h6]
      · rcases hSπ _ (hmemS g hg x hx) with h7 | h7
        · exact absurd h7 h6
        · simp only [χ, if_neg h6, neg_one_smul, h7]
    have hχsq : ∀ u, χ u * χ u = 1 := fun u => by
      by_cases h6 : (u : Module.End F W) * π = π <;> simp [χ, h6]
    have hπQ : ∀ g ∈ Q, Commute ((g : (Module.End F W)ˣ) : Module.End F W) π := fun g hg =>
      hπc _ (hcoeQ g₀ hg₀ x₀ hx₀ g hg).symm fun s hs => by
        obtain ⟨g', hg', x', hx', rfl⟩ := hS s hs
        exact (hcoeQ g' hg' x' hx' g hg).symm
    let N : Subgroup (Module.End F W)ˣ :=
      { carrier := {w | w ∈ Q ∧ ∀ g ∈ Q,
          ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π}
        mul_mem' := by
          rintro w₁ w₂ ⟨hw₁, hw₁'⟩ ⟨hw₂, hw₂'⟩
          refine ⟨Q.mul_mem hw₁ hw₂, fun g hg => ?_⟩
          rw [hbil g w₁ w₂ (hcent g hg w₂ hw₂ w₁ hw₁), Units.val_mul, mul_assoc, hw₂' g hg,
            hw₁' g hg]
        one_mem' := ⟨Q.one_mem, fun g _ => by
          rw [commutatorElement_one_right, Units.val_one, one_mul]⟩
        inv_mem' := by
          rintro w ⟨hw, hw'⟩
          exact ⟨Q.inv_mem hw, fun g hg => by rw [hcinv g hg w hw]; exact hw' g hg⟩ }
    have hN : ∀ w, w ∈ N ↔ w ∈ Q ∧ ∀ g ∈ Q,
        ((⁅g, w⁆ : (Module.End F W)ˣ) : Module.End F W) * π = π := fun _ => Iff.rfl
    have hNB : ∀ b ∈ B, ∀ w ∈ N, b * w * b⁻¹ ∈ N := by
      intro b hb w hw
      obtain ⟨hwQ, hw'⟩ := (hN w).mp hw
      refine (hN _).mpr ⟨(mem_normalizer_iff.mp (hmin.normalizes hb) w).mp hwQ, fun g hg => ?_⟩
      have hg' : b⁻¹ * g * b ∈ Q := by
        have h6 := (mem_normalizer_iff.mp (hmin.normalizes (inv_mem hb)) g).mp hg
        rwa [inv_inv] at h6
      have hconj : ⁅g, b * w * b⁻¹⁆ = ⁅b⁻¹ * g * b, w⁆ := by
        calc ⁅g, b * w * b⁻¹⁆ = b * ⁅b⁻¹ * g * b, w⁆ * b⁻¹ := by
              rw [conjugate_commutatorElement]
              group
          _ = ⁅b⁻¹ * g * b, w⁆ := by rw [hcB _ hg' w hwQ b hb]; group
      rw [hconj]
      exact hw' _ hg'
    have hBN : B ≤ normalizer (N : Set (Module.End F W)ˣ) := by
      intro b hb
      rw [mem_normalizer_iff]
      intro w
      refine ⟨hNB b hb w, fun hw => ?_⟩
      have h6 := hNB b⁻¹ (inv_mem hb) _ hw
      have h7 : b⁻¹ * (b * w * b⁻¹) * b⁻¹⁻¹ = w := by group
      rwa [h7] at h6
    have hNQ : N ≤ Q := fun w hw => ((hN w).mp hw).1
    have hx₀N : x₀ ∉ N := fun hx =>
      hπ0 (eq_zero_of_mul_eq_self_of_mul_eq_neg hF2 (((hN x₀).mp hx).2 g₀ hg₀) hzπ)
    have hNC : N ≤ centralizer (B : Set (Module.End F W)ˣ) := by
      have hbot : ⁅N, B⁆ = ⊥ := by
        by_contra hne'
        exact hx₀N (hmin.minimal N hNQ hBN hne' hx₀)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hrel : N.relIndex Q ≤ 9 := by
      haveI : Fintype (↥Q ⧸ N.subgroupOf Q) := Fintype.ofFinite _
      let rep : ↥Q ⧸ N.subgroupOf Q → (Module.End F W)ˣ := fun c => ((Quotient.out c : ↥Q) : _)
      have hrepQ : ∀ c, rep c ∈ Q := fun c => (Quotient.out c).2
      let φ : (Module.End F W)ˣ → Module.End F (Module.End F W) := fun g =>
        if g ∈ Q then LinearMap.mulLeft F ((g : (Module.End F W)ˣ) : Module.End F W) ∘ₗ
          LinearMap.mulRight F (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W) else 0
      let t : ↥Q ⧸ N.subgroupOf Q → (Module.End F W)ˣ → F := fun c g =>
        if g ∈ Q then χ ⁅g, rep c⁆ else 0
      let v : ↥Q ⧸ N.subgroupOf Q → Module.End F W := fun c =>
        ((rep c : (Module.End F W)ˣ) : Module.End F W) * π
      have hv0 : ∀ c, v c ≠ 0 := by
        intro c h0
        apply hπ0
        have h6 := congrArg (fun a => ((((rep c)⁻¹ : (Module.End F W)ˣ)) : Module.End F W) * a) h0
        simpa [v, ← mul_assoc, ← Units.val_mul] using h6
      have hφv : ∀ c g, φ g (v c) = t c g • v c := by
        intro c g
        by_cases hg : g ∈ Q
        · have hginv : Commute (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W) π :=
            hπQ g⁻¹ (inv_mem hg)
          have h6 : g * rep c * g⁻¹ = rep c * ⁅g, rep c⁆ := by
            rw [← hcent g hg (rep c) (hrepQ c) (rep c) (hrepQ c), commutatorElement_def]
            group
          simp only [φ, t, v, if_pos hg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
            LinearMap.mulRight_apply]
          calc ((g : (Module.End F W)ˣ) : Module.End F W) *
                (((rep c : (Module.End F W)ˣ) : Module.End F W) * π *
                  (((g⁻¹ : (Module.End F W)ˣ)) : Module.End F W))
              = ((g * rep c * g⁻¹ : (Module.End F W)ˣ) : Module.End F W) * π := by
                rw [mul_assoc ((rep c : (Module.End F W)ˣ) : Module.End F W) π, ← hginv.eq]
                simp only [Units.val_mul, mul_assoc]
            _ = χ ⁅g, rep c⁆ • (((rep c : (Module.End F W)ˣ) : Module.End F W) * π) := by
                rw [h6, Units.val_mul, mul_assoc, hχ g hg (rep c) (hrepQ c), mul_smul_comm]
        · simp only [φ, t, if_neg hg, LinearMap.zero_apply, zero_smul]
      have htinj : Function.Injective t := by
        intro c c' hcc
        have hchar : ∀ g ∈ Q, χ ⁅g, rep c⁆ = χ ⁅g, rep c'⁆ := fun g hg => by
          have h6 := congrFun hcc g
          simpa only [t, if_pos hg] using h6
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        show (rep c)⁻¹ * rep c' ∈ N
        refine (hN _).mpr ⟨Q.mul_mem (Q.inv_mem (hrepQ c)) (hrepQ c'), fun g hg => ?_⟩
        rw [hbil g _ _ (hcent g hg _ (hrepQ c') _ (Q.inv_mem (hrepQ c))),
          hcinv g hg _ (hrepQ c), Units.val_mul, mul_assoc, hχ g hg _ (hrepQ c'),
          mul_smul_comm, hχ g hg _ (hrepQ c), smul_smul, ← hchar g hg, hχsq, one_smul]
      have hli := linearIndependent_of_jointEigenvector φ v t hv0 hφv htinj
      have hcard := hli.fintype_card_le_finrank
      have h9 : Module.finrank F (Module.End F W) ≤ 9 :=
        calc Module.finrank F (Module.End F W) = Module.finrank F W * Module.finrank F W :=
              Module.finrank_linearMap F F W W
          _ ≤ 3 * 3 := Nat.mul_le_mul hW hW
          _ = 9 := by norm_num
      calc N.relIndex Q = Fintype.card (↥Q ⧸ N.subgroupOf Q) := by
            rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
        _ ≤ 9 := hcard.trans h9
    have hpos : 0 < N.relIndex Q := by
      rw [Subgroup.relIndex, Subgroup.index]
      exact Nat.card_pos
    have h16 := sixteen_le_relIndex_centralizer_of_fiveGroup hQ hB hmin.normalizes hnot
    have hdvd := Subgroup.relIndex_dvd_of_le_left Q hNC
    have := Nat.le_of_dvd hpos hdvd
    omega

end Linear

theorem fiveCentralizesTwo {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : FiveCentralizesTwo q := by
  intro W _ _ _ hW R hR y hy hyR
  exact commute_of_five_normalizes_two (by rw [ZMod.ringChar_zmod_n]; exact hq2) hW hR hy hyR

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
