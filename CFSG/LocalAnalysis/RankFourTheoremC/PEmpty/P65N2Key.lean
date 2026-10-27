module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Form

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem card_le_of_range {E N Fs : Subgroup K} {G : Type*} [Group G] (ψ : ↥N →* G)
    (hEN : E ≤ N) {m : ℕ}
    (hker : ∀ a : ↥E, ψ (Subgroup.inclusion hEN a) = 1 → (a : K) ∈ centralizer (Fs : Set K))
    (hrange : Nat.card (ψ.comp (Subgroup.inclusion hEN)).range ≤ m) :
    Nat.card E ≤ m * Nat.card (E ⊓ centralizer (Fs : Set K) : Subgroup K) := by
  have h1 := Subgroup.card_ker_mul_card_range (ψ.comp (Subgroup.inclusion hEN))
  have h2 : Nat.card (ψ.comp (Subgroup.inclusion hEN)).ker ≤
      Nat.card (E ⊓ centralizer (Fs : Set K) : Subgroup K) := by
    refine Nat.card_le_card_of_injective
      (fun a => (⟨(a.1 : K), a.1.2, hker a.1 a.2⟩ : (E ⊓ centralizer (Fs : Set K) : Subgroup K)))
      ?_
    intro a b hab
    have := congrArg (fun x : (E ⊓ centralizer (Fs : Set K) : Subgroup K) => (x : K)) hab
    exact Subtype.ext (Subtype.ext this)
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul hrange h2

@[expose] noncomputable def actEquiv {f : ℕ} {N : Subgroup K} {W : Type} [AddCommGroup W]
    [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥N W) : ↥N →* (W ≃ₗ[ZMod f] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod f) W).toMonoidHom.comp ρ.toHomUnits

theorem exists_rank_bound {f p : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hp : p.Prime) (hpf : p ≠ f)
    {Fs N : Subgroup K} (hFs : IsPGroup f Fs) (hN : N ≤ normalizer (Fs : Set K))
    (hrank : ∀ E : Subgroup K, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 3) :
    ∃ χ : ↥N →* (ZMod f)ˣ, ∀ (E : Subgroup K) (hEN : E ≤ N),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ p = 1) →
      (∀ (a : K) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1) →
      Nat.card E ≤ p ^ 2 * Nat.card (E ⊓ centralizer (Fs : Set K) : Subgroup K) := by
  have hf : f.Prime := Fact.out
  obtain ⟨Ω, hΩ⟩ := exists_omega hf2 hp hpf hFs hN
  have hΩ5 : Nat.card Ω ≤ f ^ 5 := card_le_pow_five hf hΩ.exp hΩ.central
    (fun E hEΩ hEc => hrank E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha)))
  have hle : (⁅Ω, Ω⁆ : Subgroup K) ≤ Ω := commutator_le_self Ω
  obtain ⟨W, _, _, _, π, ρ, hs⟩ := exists_elemSec (f := f) (Y := Ω) (M := ⁅Ω, Ω⁆) (G := N) hle
    (fun x hx m hm => (mem_normalizer_iff.mp
      (normalizer_le_normalizer_commutator Ω (le_normalizer hx)) m).mp hm)
    (fun x hx y hy => Subgroup.commutator_mem_commutator hx hy)
    (fun x hx => by rw [hΩ.exp x hx]; exact one_mem _)
    hΩ.norm (fun g hg => normalizer_le_normalizer_commutator Ω (hΩ.norm hg))
  haveI : Finite W := Module.finite_of_finite (ZMod f)
  set d := Module.finrank (ZMod f) W with hd
  have hrK : ((p : ℕ) : ZMod f) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff p f).mp h
    exact hpf ((Nat.prime_dvd_prime_iff_eq hf hp).mp this).symm
  have hfaith : ∀ (a : K) (haN : a ∈ N), a ^ p = 1 → actEquiv ρ ⟨a, haN⟩ = 1 →
      a ∈ centralizer (Fs : Set K) := by
    intro a haN hap h1
    rw [mem_centralizer_iff]
    intro x hx
    refine (hΩ.faithful a haN 1 (by simpa using hap) (fun y hy => ?_) x hx).symm
    have hay : a * y * a⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hΩ.norm haN) y).mp hy
    refine (hs.eq_iff hy hay).mp ?_
    have h2 := hs.act ⟨a, haN⟩ y hy
    have h3 : ρ ⟨a, haN⟩ (π y) = π y := by
      have := LinearEquiv.congr_fun h1 (π y)
      exact this
    rw [h3] at h2
    exact h2
  have hcardW : Nat.card Ω = Nat.card (⁅Ω, Ω⁆ : Subgroup K) * f ^ d := by
    rw [hs.card_eq hle, Module.natCard_eq_pow_finrank (K := ZMod f) (V := W), Nat.card_zmod]
  obtain ⟨k, hk⟩ := (hFs.to_le (hle.trans hΩ.le)).exists_card_eq
  have hdcase : d ≤ 3 ∨ (d = 4 ∧ Nat.card (⁅Ω, Ω⁆ : Subgroup K) = f) := by
    by_cases hk0 : k = 0
    · left
      have hbot : (⁅Ω, Ω⁆ : Subgroup K) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
      have hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := by
        intro a ha b hb
        have : ⁅a, b⁆ ∈ (⁅Ω, Ω⁆ : Subgroup K) := Subgroup.commutator_mem_commutator ha hb
        rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have h1 := hrank Ω hΩ.le hcomm hΩ.exp
      rw [hcardW, hk, hk0, pow_zero, one_mul] at h1
      exact (Nat.pow_le_pow_iff_right hf.one_lt).mp h1
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have h5 : f ^ (k + d) ≤ f ^ 5 := by rw [pow_add, ← hk, ← hcardW]; exact hΩ5
      have h6 : k + d ≤ 5 := (Nat.pow_le_pow_iff_right hf.one_lt).mp h5
      by_cases hd4 : d ≤ 3
      · exact Or.inl hd4
      · right
        have hd : d = 4 := by omega
        refine ⟨hd, ?_⟩
        have hk' : k = 1 := by omega
        rw [hk, hk', pow_one]
  have himg : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ p = 1) →
      Finite (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range,
        ∀ h ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g * h = h * g) ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g ^ p = 1) := by
    intro E hEN hEc hEp
    refine ⟨Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hEp a a.2)
      rw [this, map_one]
  have hker : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, a ^ p = 1) → ∀ a : ↥E,
      actEquiv ρ (Subgroup.inclusion hEN a) = 1 → (a : K) ∈ centralizer (Fs : Set K) :=
    fun E hEN hEp a h => hfaith (a : K) (hEN a.2) (hEp a a.2) h
  rcases hdcase with hd3 | ⟨hd4, hcard⟩
  · by_cases hd2 : d ≤ 2
    · refine ⟨1, fun E hEN hEc hEp _ => ?_⟩
      obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
      haveI := hfin
      refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
      have h1 := CFSG.RankThree.PartOne.LIT.card_le_pow_finrank_sub hp hrK
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp
      exact h1.trans (Nat.pow_le_pow_right hp.pos hd2)
    · have hd3' : d = 3 := by omega
      refine ⟨LinearEquiv.det.comp (actEquiv ρ), fun E hEN hEc hEp hχ => ?_⟩
      obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
      haveI := hfin
      refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
      refine CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_eq_one hp hrK hd3'
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp ?_
      rintro _ ⟨a, rfl⟩
      have h2 : LinearMap.det (((actEquiv ρ) ⟨(a : K), hEN a.2⟩ : W ≃ₗ[ZMod f] W) :
          W →ₗ[ZMod f] W) = 1 := by
        have h3 := congrArg (fun z : (ZMod f)ˣ => (z : ZMod f)) (hχ (a : K) a.2)
        simpa [LinearEquiv.coe_det] using h3
      exact h2
  · obtain ⟨B, lam, hnd, halt, hpres⟩ := exists_form hΩ.exp hΩ.central hΩ.norm hcard
      (fun E hEΩ hEc => hrank E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha))) hs hd4
    refine ⟨lam, fun E hEN hEc hEp hχ => ?_⟩
    obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
    haveI := hfin
    refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
    have h1 := CFSG.RankThree.PartOne.LIT.card_le_pow_half_of_alt hp hrK 4 W hd4 B hnd halt
      (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp (by
        rintro _ ⟨a, rfl⟩ u w
        exact hpres _ (hχ (a : K) a.2) u w)
    simpa using h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
