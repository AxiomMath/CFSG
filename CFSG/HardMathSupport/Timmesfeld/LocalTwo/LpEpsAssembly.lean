module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsUpper
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLower
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLift
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

theorem UpperP.of_injective {p : ℕ} {K K' : Type*} [Group K] [Group K']
    (ψ : MulAut K →* MulAut K') (hψ : Function.Injective ψ)
    (hinn : innerAut K' ≤ (innerAut K).map ψ) (h : UpperP p K') : UpperP p K := by
  intro D hD hcard H hH hDH hΔ A hDA hA hAfin
  have hel : ∀ E : Subgroup (MulAut K), IsElemAbelian p E → IsElemAbelian p (E.map ψ) := by
    intro E hE
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  have hH' : innerAut K' ≤ H.map ψ := hinn.trans (Subgroup.map_mono hH)
  have hDH' : D.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup (MulAut K')) : Set (MulAut K')) :=
    (Subgroup.map_mono hDH).trans (Subgroup.le_normalizer_map ψ)
  have hΔ' : localDeltaIn p (H.map ψ) (D.map ψ) ≠ ⊥ := by
    intro h0
    have hle := map_localDeltaIn_le p ψ hψ H D
    rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
    exact hΔ hle
  have hfin : Finite (A.map ψ) := Finite.of_equiv _ (Subgroup.equivMapOfInjective A ψ hψ).toEquiv
  have := h (D.map ψ) (hel D hD) (by rw [Subgroup.card_map_of_injective hψ, hcard]) (H.map ψ) hH'
    hDH' hΔ' (A.map ψ) (Subgroup.map_mono hDA) (hel A hA) hfin
  rwa [Subgroup.card_map_of_injective hψ] at this

variable {G : Type} [Group G] [Finite G]

theorem isCompLocallyBalanced_of_data {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {X B : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B)
    (hrank : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) {L : Subgroup G}
    (hL : GLAPComponent p X L)
    (hU : UpperP p (barOf p L ⧸ Subgroup.center (barOf p L)))
    (hD : Nonempty (LowerData p (barOf p L ⧸ Subgroup.center (barOf p L)))) :
    IsCompLocallyBalanced p 2 B L := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D0⟩ := hD
  have hperf : commutator (barOf p L) = ⊤ := (isQuasisimple_barOf hp hL).1
  have hUb : UpperP p (barOf p L) :=
    UpperP.of_injective (autCenterQuot (barOf p L)) (autCenterQuot_injective_of_perfect hperf)
      innerAut_le_map_autCenterQuot hU
  intro D hD H hH hDH
  by_contra hΔ
  obtain ⟨hDA, hDe, hD2⟩ := hD
  have hAe := isElemAbelian_autBar hB L
  have hAfin : Finite (autBar p B L) := inferInstance
  have hAcard : Nat.card (autBar p B L) ≤ p ^ 3 := hUb D hDe hD2 H hH hDH hΔ _ hDA hAe hAfin
  set Γ : barOf p L →* barOf p L ⧸ Subgroup.center (barOf p L) :=
    QuotientGroup.mk' (Subgroup.center (barOf p L)) with hΓ
  have hΓsurj : Function.Surjective Γ := QuotientGroup.mk'_surjective _
  have hker : Γ.ker = Subgroup.center (barOf p L) := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card Γ.ker) := by
    rw [hker]; exact odd_card_center_barOf hp hp2 L
  obtain ⟨E, T, hEe, ⟨r, hr4, hEcard⟩, hEker, hT, hT2, hET⟩ :=
    exists_cover_lower hp D0 Γ hΓsurj hker.le hodd
  have hZ : ∀ x ∈ E, (∀ y, x * y = y * x) → x = 1 := by
    intro x hx hc
    have hxz : x ∈ Γ.ker := by
      rw [hker]; exact Subgroup.mem_center_iff.2 fun g => (hc g).symm
    have : x ∈ E ⊓ Γ.ker := ⟨hx, hxz⟩
    rw [hEker, Subgroup.mem_bot] at this
    exact this
  obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ := exists_twoLocal_lower_central hp hp2 hBX hB hL
    E T r hZ ⟨hEe.1, hEe.2, hEcard⟩ ⟨hT, hT2⟩ hET
  have hpgB : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card B = p ^ m := IsPGroup.iff_card.1 hpgB
  have hpgA : IsPGroup p (autBar p B L) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hAe.2 _ g.2)⟩
  obtain ⟨β, hβ⟩ : ∃ β, Nat.card (autBar p B L) = p ^ β := IsPGroup.iff_card.1 hpgA
  have hpgC : IsPGroup p (centB p B L) := hpgB.to_le (centB_le p B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB p B L) = p ^ γ := IsPGroup.iff_card.1 hpgC
  have hcardB := card_B_eq p B L
  rw [hm, hβ, hγ] at hcardB
  have hdvd : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B ∣ p ^ m :=
    ⟨p ^ β * p ^ γ, hcardB.trans rfl⟩
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvd |>.imp fun a h => h.2
  have hmaβγ : m = a + (β + γ) := by
    rw [ha, ← pow_add, ← pow_add] at hcardB
    exact Nat.pow_right_injective hp.two_le hcardB
  have hPcard' : Nat.card P = p ^ (γ + r * p ^ a) := by
    rw [hPcard, hγ, ha, ← pow_add]
  have hrkP : CFSG.Open.pRank p P = γ + r * p ^ a :=
    pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
  have hrkB : CFSG.Open.pRank p B = m := pRank_eq_of_card hp hB hm
  have h1 : CFSG.Open.pRank p P ≤ GLATwoLocalRank p ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
  have h2 : γ + r * p ^ a ≤ a + (β + γ) := by
    rw [← hrkP, ← hmaβγ, ← hrkB]
    exact h1.trans hrank
  have hβ3 : β ≤ 3 := by
    rw [hβ] at hAcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hAcard
  have hpa := two_mul_add_one_le_pow hp3 a
  have h4 : 4 * p ^ a ≤ r * p ^ a := Nat.mul_le_mul_right _ hr4
  nlinarith [h2, h4, hpa, hβ3]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
