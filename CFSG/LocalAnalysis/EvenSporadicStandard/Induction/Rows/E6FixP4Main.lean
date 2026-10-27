module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6FixP3Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixCount
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.GH74.Generic.GKFCover
public import CFSG.GH74.Generic.Certificates

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.GH74.Generic CFSG.EvenSmallLie.TwoE6


theorem e6fix_pow_std {g : ↥stdGroup} {j : ℕ} (hg : g ^ (2 ^ j) = 1) : g ^ (2 ^ 7) = 1 := by
  have h1 : (g : ModGL Tag.E6 K) ^ (2 ^ j) = 1 := by
    have := congrArg (fun z : ↥stdGroup => (z : ModGL Tag.E6 K)) hg
    simpa using this
  have hfr : Module.finrank K (RootModule Tag.E6 K) ≤ 2 ^ 7 := by
    rw [Module.finrank_finsupp_self, CFSG.Monster.B.E6.StdF4.card_label_E6']
    norm_num
  have h2 := pow_two_pow_eq_one_of_finrank_le (F := K) (V := RootModule Tag.E6 K) hfr
    (g : ModGL Tag.E6 K) h1
  exact Subtype.ext (by simpa using h2)

theorem e6fix_pow_cover {K₂ : Type} [Group K₂] [Finite K₂] (hperf : Group.IsPerfect K₂)
    (ε : K₂ ⧸ center K₂ ≃* ↥stdGroup) {x : K₂} {j : ℕ} (hx : x ^ (2 ^ j) = 1) :
    x ^ (2 ^ 9) = 1 := by
  have hker := centralQuotientMap_ker ε
  have hZ12 : Nat.card (center K₂) ∣ 12 := by
    have h1 := card_ker_dvd_hopfMultiplier hperf (centralQuotientMap ε)
      (centralQuotientMap_surjective ε) hker.le
    rw [hker, CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.card_hopfMultiplier] at h1
    exact h1
  have h7 : (centralQuotientMap ε x) ^ (2 ^ 7) = 1 :=
    e6fix_pow_std (j := j) (by rw [← map_pow, hx, map_one])
  have hz : x ^ (2 ^ 7) ∈ center K₂ := by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact h7
  have hz2 : (x ^ (2 ^ 7)) ^ (2 ^ j) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have hord1 : orderOf (x ^ (2 ^ 7)) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hz2
  have hord2 : orderOf (x ^ (2 ^ 7)) ∣ 12 := by
    have h3 : orderOf (⟨x ^ (2 ^ 7), hz⟩ : ↥(center K₂)) ∣ Nat.card (center K₂) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    exact h3.trans hZ12
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord1
  have hi2 : i ≤ 2 := by
    by_contra hne
    have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega : 3 ≤ i)).trans (hi ▸ hord2)
    omega
  have hord4 : orderOf (x ^ (2 ^ 7)) ∣ 4 := by
    rw [hi]
    exact (pow_dvd_pow 2 hi2 : 2 ^ i ∣ 2 ^ 2)
  rw [show 2 ^ 9 = 2 ^ 7 * 4 by norm_num, pow_mul]
  exact orderOf_dvd_iff_pow_eq_one.1 hord4

theorem e6fix_main {K₂ : Type} [Group K₂] [Finite K₂] (hperf : Group.IsPerfect K₂)
    (ε : K₂ ⧸ center K₂ ≃* ↥stdGroup) (α : MulAut K₂) (hα1 : α ≠ 1) (hα2 : α * α = 1)
    (F : Subgroup K₂) (hF : ∀ x, x ∈ F ↔ α x = x) :
    ¬ ElemBound 4 ↥F ∨ ¬ TwoSubgroupsAbelian ↥F := by
  by_contra hcon
  obtain ⟨hel', hab'⟩ := not_or.1 hcon
  have hel : ElemBound 4 ↥F := not_not.1 hel'
  have hab : TwoSubgroupsAbelian ↥F := not_not.1 hab'
  have hπ := centralQuotientMap_surjective ε
  have hker := centralQuotientMap_ker ε
  obtain ⟨β, hβ⟩ := CoverFix.exists_induced (centralQuotientMap ε) hπ hker α
  have hβ1 := CoverFix.induced_ne_one hperf (centralQuotientMap ε) hker.le hβ hα1
  have hβ2 := CoverFix.induced_sq (centralQuotientMap ε) hπ hβ hα2
  obtain ⟨a, y, hyy, hay, hy⟩ := e6fix_exists_conj_rho' β hβ2
  obtain ⟨B, hBcard, hBfix⟩ := e6fix_exists_fixed_subgroup hyy hy
  obtain ⟨B', hB'def⟩ : ∃ B' : Subgroup ↥stdGroup,
      B' = B.map (a⁻¹ : MulAut ↥stdGroup).toMonoidHom := ⟨_, rfl⟩
  have hB'card : Nat.card B' = 2 ^ 19 := by
    rw [hB'def, Subgroup.card_map_of_injective (a⁻¹ : MulAut ↥stdGroup).injective]
    exact hBcard
  have hB'fix : ∀ b ∈ B', β b = b := by
    rw [hB'def]
    rintro _ ⟨c, hc, rfl⟩
    have h3 : a (β (a⁻¹ c)) = c := by
      have h2 : (a * β * a⁻¹) c = c := by
        rw [hay]
        exact hBfix c hc
      exact h2
    exact (MulAut.inv_apply_self _ a (β (a⁻¹ c))).symm.trans
      (congrArg (a⁻¹ : MulAut ↥stdGroup) h3)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPle, hPcard⟩ := CoverFix.exists_subgroup_card_two_pow (centralQuotientMap ε) hπ
    hker.le hβ B' hB'fix hB'card
  have hPF : P ≤ F := fun x hx => (hF x).2 (CoverFix.mem_fixed.1 (hPle hx).1)
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup ↥F, A = P.subgroupOf F := ⟨_, rfl⟩
  have hAcard : Nat.card A = 2 ^ 19 := by
    rw [hAdef]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv).trans hPcard
  have hAp : IsPGroup 2 A := IsPGroup.of_card hAcard
  have hAexp : ∀ x ∈ A, x ^ (2 ^ 9) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hAp ⟨x, hx⟩
    have hk' : ((x : ↥F) : K₂) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : ↥A => ((z : ↥F) : K₂)) hk
      simpa using this
    exact Subtype.ext (by simpa using e6fix_pow_cover hperf ε hk')
  have hle := e6fix_card_le_pow_of_exponent (F := ↥F) (b := 4) hel 9 A (hab A hAp) hAexp
  rw [hAcard] at hle
  norm_num at hle

theorem e6InvolutionFixed_proved : E6InvolutionFixed := by
  intro K₂ _ _ hperf hlm α hα1 hα2
  obtain ⟨ε⟩ := (lieModel_twistedE6_two_iff _).1 hlm
  refine Or.inr (e6fix_main hperf ε α hα1 hα2 _ ?_)
  intro x
  exact Iff.rfl

end CFSG.EvenSporadicStandard.Induction.Hyp
