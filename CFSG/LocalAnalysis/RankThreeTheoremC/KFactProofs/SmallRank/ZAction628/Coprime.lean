module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem exists_fixed_in_coset {q : ℕ} [Fact q.Prime] {T M : Subgroup K} (hT : IsPGroup q T)
    (hTM : T ≤ normalizer (M : Set K)) (hq : ¬ q ∣ Nat.card M) {x : K}
    (hx : ∀ t ∈ T, x⁻¹ * (t * x * t⁻¹) ∈ M) :
    ∃ m ∈ M, ∀ t ∈ T, t * (x * m) * t⁻¹ = x * m := by
  have hmem : ∀ t ∈ T, ∀ y : K, x⁻¹ * y ∈ M → x⁻¹ * (t * y * t⁻¹) ∈ M := by
    intro t ht y hy
    have h1 : x⁻¹ * (t * y * t⁻¹) = (x⁻¹ * (t * x * t⁻¹)) * (t * (x⁻¹ * y) * t⁻¹) := by
      group
    rw [h1]
    exact M.mul_mem (hx t ht) ((Subgroup.mem_normalizer_iff.mp (hTM ht) _).mp hy)
  letI hact : MulAction ↥T {y : K // x⁻¹ * y ∈ M} :=
    { smul := fun g v => ⟨(g : K) * v.1 * (g : K)⁻¹, hmem (g : K) g.2 v.1 v.2⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : ↥T) : K) * v.1 * ((1 : ↥T) : K)⁻¹ = v.1
        simp)
      mul_smul := fun g h v => Subtype.ext (by
        show ((g * h : ↥T) : K) * v.1 * ((g * h : ↥T) : K)⁻¹
          = (g : K) * ((h : K) * v.1 * (h : K)⁻¹) * (g : K)⁻¹
        simp [mul_assoc]) }
  have hY : Nat.card {y : K // x⁻¹ * y ∈ M} = Nat.card M :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun m => ⟨x * m.1, by simpa using m.2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun m => Subtype.ext (by simp) }
  have hY' : ¬ q ∣ Nat.card {y : K // x⁻¹ * y ∈ M} := by
    rw [hY]
    exact hq
  have hG : IsPGroup q ↥T := hT
  have h1 := IsPGroup.card_modEq_card_fixedPoints hG {y : K // x⁻¹ * y ∈ M}
  have hne : Nat.card ↥(MulAction.fixedPoints ↥T {y : K // x⁻¹ * y ∈ M}) ≠ 0 := by
    intro h0
    rw [h0] at h1
    exact hY' (Nat.modEq_zero_iff_dvd.mp h1)
  obtain ⟨⟨⟨y, hy⟩, hyfix⟩⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne) |>.1
  refine ⟨x⁻¹ * y, hy, fun t ht => ?_⟩
  have h2 : t * y * t⁻¹ = y := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hyfix ⟨t, ht⟩)
  rw [mul_inv_cancel_left]
  exact h2
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem trace_zpow_invariant {G A : Type*} [Group G] [Group A] (N : G →* A) (φ : MulAut G)
    (h : ∀ g, N (φ g) = N g) (j : ℤ) (g : G) : N ((φ ^ j) g) = N g := by
  induction j using Int.induction_on generalizing g with
  | zero => simp
  | succ i ih => rw [zpow_add_one, MulAut.mul_apply, ih, h]
  | pred i ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, ← h (φ⁻¹ g), MulAut.apply_inv_self]

theorem trace_exists_norm {G A : Type*} [Group G] [CommGroup A] (ψ : G →* A) (φ : MulAut G)
    (p : ℕ) (hφ : φ ^ p = 1) :
    ∃ N : G →* A, (∀ g, N g = ∏ i ∈ Finset.range p, ψ ((φ ^ i) g)) ∧ ∀ g, N (φ g) = N g := by
  refine ⟨∏ i ∈ Finset.range p, ψ.comp (φ ^ i : MulAut G).toMonoidHom, ?_, ?_⟩
  · intro g
    rw [MonoidHom.finset_prod_apply]
    rfl
  · intro g
    have h1 : ∀ g, (∏ i ∈ Finset.range p, ψ.comp (φ ^ i : MulAut G).toMonoidHom) g =
        ∏ i ∈ Finset.range p, ψ ((φ ^ i) g) := by
      intro g
      rw [MonoidHom.finset_prod_apply]
      rfl
    rw [h1, h1]
    set f : ℕ → A := fun i => ψ ((φ ^ i) g) with hf
    have h2 : ∀ i, ψ ((φ ^ i) (φ g)) = f (i + 1) := by
      intro i
      simp [hf, pow_succ]
    have h3 : f p = f 0 := by
      simp [hf, hφ]
    have h4 := Finset.prod_range_succ f p
    have h5 := Finset.prod_range_succ' f p
    simp only [h2]
    apply mul_right_cancel (b := f 0)
    rw [← h5, ← h3, ← h4]

theorem pow_mem_commutator_of_fixed {P : Subgroup K} {z x : K} {p : ℕ} (hz : z ^ p = 1)
    (hzP : z ∈ normalizer (P : Set K)) (hxP : x ∈ ⁅zpowers z, P⁆) (hxfix : z * x = x * z) :
    x ^ p ∈ ⁅P, P⁆ := by
  set n : ↥(normalizer (P : Set K)) := ⟨z, hzP⟩ with hn
  set φ : MulAut ↥P := P.normalizerMonoidHom n with hφdef
  have hφp : φ ^ p = 1 := by
    rw [hφdef, ← map_pow]
    have : n ^ p = 1 := Subtype.ext (by simpa [hn] using hz)
    rw [this, map_one]
  have hφj : ∀ (j : ℤ) (a : ↥P), (((φ ^ j) a : ↥P) : K) = z ^ j * a * (z ^ j)⁻¹ := by
    intro j a
    rw [hφdef, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [hn]
  obtain ⟨N, hN, hNφ⟩ := trace_exists_norm (Abelianization.of : ↥P →* Abelianization ↥P) φ p hφp
  have hQ : ⁅zpowers z, P⁆ ≤ (N.ker).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₁
    refine ⟨(φ ^ j) ⟨g₂, hg₂⟩ * ⟨g₂, hg₂⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, trace_zpow_invariant N φ hNφ j,
        mul_inv_cancel]
    · simp [hφj, commutatorElement_def]
  obtain ⟨g, hgker, rfl⟩ := hQ hxP
  have hgfix : φ g = g := by
    apply Subtype.ext
    have h1 : ((φ g : ↥P) : K) = z * g * z⁻¹ := by
      have := hφj 1 g
      simpa using this
    rw [h1]
    have : z * (g : K) = g * z := hxfix
    rw [this, mul_inv_cancel_right]
  have hgfixn : ∀ i : ℕ, (φ ^ i) g = g := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, MulAut.mul_apply, hgfix, ih]
  have hNg : N g = (Abelianization.of g) ^ p := by
    rw [hN]
    simp [hgfixn]
  have hker : Abelianization.of (g ^ p) = 1 := by
    rw [map_pow, ← hNg]
    exact hgker
  have hcomm : g ^ p ∈ commutator ↥P := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hker
  have himg : (commutator ↥P).map P.subtype = ⁅P, P⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [← himg]
  exact ⟨g ^ p, hcomm, by simp⟩
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem rrBasic_conj_centralizer {X : Subgroup K} {z : K} (hz : z ∈ normalizer (X : Set K))
    {g : K} (hg : g ∈ centralizer (X : Set K)) : z * g * z⁻¹ ∈ centralizer (X : Set K) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro x hx
  have hzx : z⁻¹ * x * z ∈ (X : Set K) := by
    refine (Subgroup.mem_normalizer_iff.1 hz (z⁻¹ * x * z)).2 ?_
    rw [show z * (z⁻¹ * x * z) * z⁻¹ = x by group]
    exact hx
  have hc := hg (z⁻¹ * x * z) hzx
  calc x * (z * g * z⁻¹) = z * ((z⁻¹ * x * z) * g) * z⁻¹ := by group
    _ = z * (g * (z⁻¹ * x * z)) * z⁻¹ := by rw [hc]
    _ = z * g * z⁻¹ * x := by group

theorem rrBasic_normalizes_centralizer {X : Subgroup K} {z : K}
    (hz : z ∈ normalizer (X : Set K)) :
    z ∈ normalizer ((centralizer (X : Set K) : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact rrBasic_conj_centralizer hz hg
  · intro hg
    have hg' : z * g * z⁻¹ ∈ centralizer (X : Set K) := hg
    have h' := rrBasic_conj_centralizer ((normalizer (X : Set K)).inv_mem hz) hg'
    have e : z⁻¹ * (z * g * z⁻¹) * z⁻¹⁻¹ = g := by group
    rw [e] at h'
    exact h'

theorem rrBasic_normalizer_inf {S C : Subgroup K} {z : K} (h1 : z ∈ normalizer (S : Set K))
    (h2 : z ∈ normalizer (C : Set K)) : z ∈ normalizer ((S ⊓ C : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro g
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (h1 g) (h2 g)

theorem RR_le_S {S : Subgroup K} {z : K} (hzS : zpowers z ≤ normalizer (S : Set K)) :
    RR S z ≤ S := by
  refine Subgroup.commutator_le.2 ?_
  intro g hg s hs
  have hgN : g ∈ normalizer (S : Set K) := hzS hg
  have hconj : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hgN s).1 hs
  rw [commutatorElement_def]
  exact S.mul_mem hconj (S.inv_mem hs)

theorem commutator_RR_eq {p : ℕ} {S : Subgroup K} {z : K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsPGroup 2 S) (hzp : z ^ p = 1) (hz1 : z ≠ 1)
    (hzS : zpowers z ≤ normalizer (S : Set K)) : ⁅RR S z, zpowers z⁆ = RR S z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hS
  have hz : Nat.card (zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card S) := by
    rw [hz, hn]
    exact Nat.Coprime.pow_right n hcop2
  have key := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.commutator_commutator_eq_of_coprime
    hzS hcop
  show ⁅⁅zpowers z, S⁆, zpowers z⁆ = ⁅zpowers z, S⁆
  rw [Subgroup.commutator_comm (zpowers z) S]
  exact key

theorem centralizer_S_X {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z) :
    ∀ s ∈ S, (∀ x ∈ X, s * x = x * s) → s = 1 := by
  intro s hsS hsX
  have hzS : z ∈ normalizer (S : Set K) := h.hzS (mem_zpowers z)
  have hzX : z ∈ normalizer (X : Set K) := h.hSX (mem_sup_right (mem_zpowers z))
  have hzC : z ∈ normalizer ((centralizer (X : Set K) : Subgroup K) : Set K) :=
    rrBasic_normalizes_centralizer hzX
  have hzS₀ : z ∈ normalizer ((S ⊓ centralizer (X : Set K) : Subgroup K) : Set K) :=
    rrBasic_normalizer_inf hzS hzC
  have hsS₀ : s ∈ S ⊓ centralizer (X : Set K) :=
    ⟨hsS, Subgroup.mem_centralizer_iff.2 (fun x hx => (hsX x hx).symm)⟩
  have hbot : S ⊓ centralizer (X : Set K) = ⊥ := by
    by_contra hne
    have hCN := h.hC (S ⊓ centralizer (X : Set K)) inf_le_left hne
      (Subgroup.zpowers_le.2 hzS₀)
    have hXc : X ≤ centralizer ((S ⊓ centralizer (X : Set K) : Subgroup K) : Set K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ S ⊓ centralizer (X : Set K) := hy
      exact (Subgroup.mem_centralizer_iff.1 hy'.2 x hx).symm
    apply h.hXN
    intro x hx
    have hxC : x ∈ X ⊓ centralizer ((S ⊓ centralizer (X : Set K) : Subgroup K) : Set K) :=
      ⟨hx, hXc hx⟩
    exact hCN hxC
  have hsbot : s ∈ (⊥ : Subgroup K) := by
    rw [← hbot]
    exact hsS₀
  exact Subgroup.mem_bot.1 hsbot

theorem k_pos {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z) {t : K}
    (hR : IsExt2 (RR S z) t) (hzt : z * t = t * z) {k : ℕ}
    (hk : Nat.card (RR S z) = 2 ^ (1 + 2 * k)) : 1 ≤ k := by
  by_contra hlt
  have hk0 : k = 0 := by omega
  subst hk0
  have hcard : Nat.card (RR S z) = 2 := hk.trans (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht_ord : orderOf t = 2 := orderOf_eq_prime hR.t_sq hR.t_ne
  have hle : zpowers t ≤ RR S z := Subgroup.zpowers_le.2 hR.t_mem
  have heq : zpowers t = RR S z :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard, Nat.card_zpowers, ht_ord]))
  have hcomm : ∀ r ∈ RR S z, Commute r z := by
    intro r hr
    rw [← heq] at hr
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hct : Commute t z := hzt.symm
    exact hct.zpow_left m
  have hbot : ⁅RR S z, zpowers z⁆ = ⊥ := by
    refine eq_bot_iff.2 (Subgroup.commutator_le.2 ?_)
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_commute.2 ((hcomm g₁ hg₁).zpow_right m)
  have hRbot : RR S z = ⊥ :=
    (commutator_RR_eq h.hp h.hp2 h.hS h.hzp h.hz1 h.hzS).symm.trans hbot
  have htbot : t ∈ (⊥ : Subgroup K) := by
    rw [← hRbot]
    exact hR.t_mem
  exact hR.t_ne (Subgroup.mem_bot.1 htbot)
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
