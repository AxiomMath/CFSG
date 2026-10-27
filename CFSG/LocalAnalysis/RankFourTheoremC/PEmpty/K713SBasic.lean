module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SLift
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms Subgroup

@[expose] def OutLift (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ R : Subgroup (MulAut K), IsPGroup p R ∧ R ⊓ inner K = ⊥ ∧ ¬ p ∣ (inner K ⊔ R).index

@[expose] def LiftClause (K : Type*) [Group K] [Finite K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup K) ≤ 1 → OutLift p K

theorem OutLift.split {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (h : OutLift p K)
    (S : Sylow p (MulAut K)) :
    ∃ R : Subgroup (MulAut K), R ≤ (S : Subgroup (MulAut K)) ∧ R ⊓ inner K = ⊥ ∧
      ((S : Subgroup (MulAut K)) ⊓ inner K) ⊔ R = (S : Subgroup (MulAut K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hRp, hRI, hidx⟩ := h
  exact exists_complement_in_sylow (inner K) R hRp hRI hidx S

theorem outLift_of_split {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (S : Sylow p (MulAut K))
    (h : ∃ R : Subgroup (MulAut K), R ≤ (S : Subgroup (MulAut K)) ∧ R ⊓ inner K = ⊥ ∧
      ((S : Subgroup (MulAut K)) ⊓ inner K) ⊔ R = (S : Subgroup (MulAut K))) : OutLift p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hRS, hRI, hsup⟩ := h
  refine ⟨R, S.isPGroup'.to_le hRS, hRI, fun hd => ?_⟩
  have hle : (S : Subgroup (MulAut K)) ≤ inner K ⊔ R := by
    rw [← hsup]
    exact sup_le_sup inf_le_right le_rfl
  exact S.not_dvd_index (hd.trans (index_dvd_of_le hle))

theorem OutLift.of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : OutLift p Y) : OutLift p X := by
  obtain ⟨R, hRp, hRI, hidx⟩ := h
  let φ : MulAut Y ≃* MulAut X := MulAut.congr e.symm
  have hI : (inner Y).map φ.toMonoidHom = inner X := inner_map_congr e.symm
  refine ⟨R.map φ.toMonoidHom, hRp.map _, ?_, ?_⟩
  · rw [← hI, ← Subgroup.map_inf R (inner Y) φ.toMonoidHom φ.injective, hRI, Subgroup.map_bot]
  · rw [← hI, ← Subgroup.map_sup, Subgroup.index_map_of_bijective φ.bijective]
    exact hidx

theorem LiftClause.of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : LiftClause Y) : LiftClause X := by
  intro p hp hp2 hX
  refine OutLift.of_mulEquiv e (h p hp hp2 ?_)
  rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]

theorem outLift_of_not_dvd {p : ℕ} {K : Type*} [Group K] (h : ¬ p ∣ Nat.card (Outer K)) :
    OutLift p K :=
  ⟨⊥, IsPGroup.of_bot, bot_inf_eq _, by rw [sup_bot_eq]; exact h⟩

theorem outLift_of_chain {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K]
    {D F : Subgroup (MulAut K)} [D.Normal] (hID : inner K ≤ D) (hF : F ⊓ D = ⊥)
    (hD : ¬ p ∣ (inner K).relIndex D) (hFD : ¬ p ∣ (D ⊔ F).index) : OutLift p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_lift_of_chain hID hF hD hFD

theorem index_sup_inner_mul_card {K : Type*} [Group K] [Finite K] {R : Subgroup (MulAut K)}
    (hR : R ⊓ inner K = ⊥) : (inner K ⊔ R).index * Nat.card R = Nat.card (Outer K) := by
  have h1 := relIndex_mul_index (le_sup_left : inner K ≤ inner K ⊔ R)
  have h2 : (inner K).relIndex (inner K ⊔ R) = Nat.card R := by
    rw [relIndex_sup_left]
    have := relIndex_mul_card (inner K) R
    rw [inf_comm, hR] at this
    simpa using this
  rw [h2] at h1
  rw [mul_comm] at h1
  exact h1

theorem outLift_of_hom {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] {Q : Type*}
    [Group Q] [Finite Q] (φ : Q →* MulAut K) (hφ : ∀ q : Q, φ q ∈ inner K → q = 1)
    (hcard : (Nat.card (Outer K)).factorization p ≤ (Nat.card Q).factorization p) :
    OutLift p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    exact hφ q (by rw [hq]; exact one_mem _)
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  set R : Subgroup (MulAut K) := (P : Subgroup Q).map φ with hR
  have hRI : R ⊓ inner K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hrI⟩
    rw [hφ r hrI]
    simp
  have hRcard : Nat.card R = p ^ (Nat.card Q).factorization p := by
    rw [hR, Subgroup.card_map_of_injective hinj]
    exact P.card_eq_multiplicity
  refine ⟨R, P.isPGroup'.map φ, hRI, fun hd => ?_⟩
  have h1 := index_sup_inner_mul_card hRI
  have hne : Nat.card (Outer K) ≠ 0 := Nat.card_pos.ne'
  have h2 : p ^ ((Nat.card Q).factorization p + 1) ∣ Nat.card (Outer K) := by
    have e : p ^ ((Nat.card Q).factorization p + 1) = p * p ^ (Nat.card Q).factorization p := by
      ring
    rw [← h1, hRcard, e]
    exact mul_dvd_mul_right hd _
  have h3 := (hp.pow_dvd_iff_le_factorization hne).1 h2
  omega

theorem outLift_of_complement {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K]
    {F : Subgroup (MulAut K)} (hF : F ⊓ inner K = ⊥) (htop : inner K ⊔ F = ⊤) : OutLift p K := by
  refine outLift_of_chain hp (D := inner K) le_rfl hF ?_ ?_
  · rw [relIndex_self]
    exact hp.not_dvd_one
  · rw [htop, index_top]
    exact hp.not_dvd_one

theorem card_outer_dvd_of_surj {K : Type*} [Group K] {Q : Type*} [Group Q] [Finite Q]
    (φ : Q →* MulAut K) (h : ∀ α : MulAut K, ∃ (g : K) (q : Q), α = MulAut.conj g * φ q) :
    Nat.card (Outer K) ∣ Nat.card Q := by
  refine Subgroup.card_dvd_of_surjective (f := (QuotientGroup.mk' (inner K)).comp φ) ?_
  intro x
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner K) x
  obtain ⟨g, q, rfl⟩ := h α
  refine ⟨q, ?_⟩
  simp only [MonoidHom.comp_apply, map_mul]
  rw [show QuotientGroup.mk' (inner K) (MulAut.conj g) = 1 from
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩, one_mul]

theorem outLift_of_hom_surj {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] {Q : Type*}
    [Group Q] [Finite Q] (φ : Q →* MulAut K) (hφ : ∀ q : Q, φ q ∈ inner K → q = 1)
    (h : ∀ α : MulAut K, ∃ (g : K) (q : Q), α = MulAut.conj g * φ q) : OutLift p K :=
  outLift_of_hom hp φ hφ (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne' |>.2
    (card_outer_dvd_of_surj φ h) p)

theorem outLift_of_section {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] {Q : Type*}
    [Group Q] (Θ : MulAut K →* Q) (φ : Q →* MulAut K) (hΘφ : ∀ q, Θ (φ q) = q)
    (hI : inner K ≤ Θ.ker) (hD : ¬ p ∣ (inner K).relIndex Θ.ker) : OutLift p K := by
  refine outLift_of_chain hp (D := Θ.ker) (F := φ.range) hI ?_ hD ?_
  · rw [eq_bot_iff]
    rintro _ ⟨⟨q, rfl⟩, hq⟩
    have : q = 1 := by simpa [hΘφ] using hq
    simp [this]
  · have htop : Θ.ker ⊔ φ.range = ⊤ := by
      refine eq_top_iff.2 fun g _ => ?_
      have h1 : g * (φ (Θ g))⁻¹ ∈ Θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hΘφ, mul_inv_cancel]
      have h2 : φ (Θ g) ∈ φ.range := ⟨Θ g, rfl⟩
      simpa using mul_mem_sup h1 h2
    rw [htop, index_top]
    exact hp.not_dvd_one

theorem outLift_of_cyclic {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] {n : ℕ}
    [NeZero n] (Θ : MulAut K →* Multiplicative (ZMod n)) (φ : MulAut K) (hφn : φ ^ n = 1)
    (hΘφ : Θ φ = Multiplicative.ofAdd 1) (hker : Θ.ker = inner K) : OutLift p K := by
  have hΘpow : ∀ i : ℤ, Θ (φ ^ i) = Multiplicative.ofAdd (i : ZMod n) := by
    intro i
    rw [map_zpow, hΘφ, ← ofAdd_zsmul]
    simp
  refine outLift_of_complement hp (F := Subgroup.zpowers φ) ?_ ?_
  · rw [eq_bot_iff]
    rintro _ ⟨hx, hxI⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    have h1 : Θ (φ ^ i) = 1 := by rw [← hker] at hxI; exact hxI
    rw [hΘpow] at h1
    have h2 : (i : ZMod n) = 0 := by simpa using h1
    obtain ⟨m, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd i n).1 h2
    rw [zpow_mul, zpow_natCast, hφn, one_zpow]
    exact one_mem _
  · refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨c, hc⟩ := ZMod.intCast_surjective (n := n) (Multiplicative.toAdd (Θ α))
    have h1 : α * (φ ^ c)⁻¹ ∈ inner K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΘpow, hc]
      simp
    have h2 : φ ^ c ∈ Subgroup.zpowers φ := zpow_mem (mem_zpowers φ) c
    simpa using mul_mem_sup h1 h2

theorem outLift_of_section_ker {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] [Finite K] {Q : Type*}
    [Group Q] (Θ : MulAut K →* Q) (φ : Q →* MulAut K) (hΘφ : ∀ q, Θ (φ q) = q)
    (hker : Θ.ker = inner K) : OutLift p K :=
  outLift_of_section hp Θ φ hΘφ hker.ge (by rw [hker, relIndex_self]; exact hp.not_dvd_one)

theorem finite_ringAut (K : Type*) [Field K] [Finite K] : Finite (RingAut K) :=
  Finite.of_injective (fun σ : RingAut K => (σ : K → K)) DFunLike.coe_injective

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
