module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathP1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathE2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OddComplement
public import CFSG.GroupTheory.OddInfOfComplementaryActions
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL6Wreath

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

private theorem phiQ_commute_w (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (c : G) (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c * w = w * phiQ hD Q c := by
  rcases hΦ c hc with h | h | h | h
  · rw [h, zero_mul, mul_zero]
  · rw [h, one_mul, mul_one]
  · rw [h]
  · rw [h, add_mul, one_mul, mul_add, mul_one]

private theorem phiQ_commute_add_one (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (c : G) (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q c * (w + 1) = (w + 1) * phiQ hD Q c :=
  commute_add_one_of_commute hD (phiQ_commute_w hD hΦ c hc)

private theorem commute_vConj_add_one (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n) :
    ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * (w + 1) = (w + 1) * vConj hD n :=
  fun n hn => commute_add_one_of_commute hD (hwH n hn)

theorem ThCyc.wreathE₂_inf_wreathE₂_add_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    wreathE₂ hD Q (w + 1) ⊓ wreathE₂ hD Q w = ⊥ := by
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  have hτw' : vConj hD t * (w + 1) * vConj hD t = (w + 1) + 1 :=
    vConj_t_mul_add_one_mul H W W2 hD hτw
  have hgw' : g ∈ wComm hD (w + 1) := by rwa [wComm_add_one hD w]
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hsurj₂⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb
    (commute_vConj_add_one hD hwH) hww' hτw' hQ hgQ hgw' hgM
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hsurj₁⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ
    hgQ hgw hgM
  refine le_antisymm ?_ bot_le
  rintro e ⟨he₁, he₂⟩
  have he₁2 : e ^ 2 ∈ wFix hD w := by
    have h := sq_mem_wKer_of_mem_wreathE₂ hD hww' hQ hq4 hc₂ ρ₂ hρ₂ hsurj₂ he₁
    rwa [wKer_add_one hD w] at h
  have he₂2 : e ^ 2 ∈ wKer hD w :=
    sq_mem_wKer_of_mem_wreathE₂ hD hww hQ hq4 hc₁ ρ₁ hρ₁ hsurj₁ he₂
  have he2one : e ^ 2 = 1 := by
    have hmem : e ^ 2 ∈ wFix hD w ⊓ wKer hD w := ⟨he₁2, he₂2⟩
    rw [wFix_inf_wKer_eq_bot hD w] at hmem
    exact Subgroup.mem_bot.1 hmem
  have heV : e ∈ omega1 D hD.comm :=
    (QHyp.mem_omega1_iff hD hQ (wreathE₂_le hD Q (w + 1) he₁)).2 he2one
  have heV₁ : e ∈ wFix hD w := by
    have hmem : e ∈ wreathE₂ hD Q (w + 1) ⊓ omega1 D hD.comm := ⟨he₁, heV⟩
    rwa [wreathE₂_inf_omega1 hD hww' hQ hc₂ ρ₂ hρ₂ hsurj₂, wKer_add_one hD w] at hmem
  have heV₂ : e ∈ wKer hD w := by
    have hmem : e ∈ wreathE₂ hD Q w ⊓ omega1 D hD.comm := ⟨he₂, heV⟩
    rwa [wreathE₂_inf_omega1 hD hww hQ hc₁ ρ₁ hρ₁ hsurj₁] at hmem
  have hbot : e ∈ wFix hD w ⊓ wKer hD w := ⟨heV₁, heV₂⟩
  rw [wFix_inf_wKer_eq_bot hD w] at hbot
  exact Subgroup.mem_bot.1 hbot

theorem ThCyc.exists_mul_of_mem_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {q : G} (hq : q ∈ Q) :
    ∃ e₁ ∈ wreathE₂ hD Q (w + 1), ∃ e₂ ∈ wreathE₂ hD Q w, q = e₁ * e₂ := by
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  have hτw' : vConj hD t * (w + 1) * vConj hD t = (w + 1) + 1 :=
    vConj_t_mul_add_one_mul H W W2 hD hτw
  have hgw' : g ∈ wComm hD (w + 1) := by rwa [wComm_add_one hD w]
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hsurj₂⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb
    (commute_vConj_add_one hD hwH) hww' hτw' hQ hgQ hgw' hgM
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hsurj₁⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ
    hgQ hgw hgM
  have hq2Q : q ^ 2 ∈ Q := Q.pow_mem hq 2
  have hq2V : q ^ 2 ∈ omega1 D hD.comm :=
    (QHyp.mem_omega1_iff hD hQ hq2Q).2 (by
      rw [show (q ^ 2) ^ 2 = q ^ 4 by rw [← pow_mul]]
      exact hq4 q hq)
  obtain ⟨v₁, hv₁, v₂, hv₂, hq2eq⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hq2V
  have hv₁' : v₁ ∈ wKer hD (w + 1) := by rwa [wKer_add_one hD w]
  obtain ⟨e₁, he₁, he₁sq⟩ := exists_mem_wreathE₂_sq_eq hD hww' hQ hq4 hsq hc₂ ρ₂ hρ₂ hsurj₂
    (phiQ_commute_add_one hD hΦ) hv₁'
  obtain ⟨e₂, he₂, he₂sq⟩ := exists_mem_wreathE₂_sq_eq hD hww hQ hq4 hsq hc₁ ρ₁ hρ₁ hsurj₁
    (phiQ_commute_w hD hΦ) hv₂
  have he₁Q : e₁ ∈ Q := wreathE₂_le hD Q (w + 1) he₁
  have he₂Q : e₂ ∈ Q := wreathE₂_le hD Q w he₂
  have hprodQ : e₁ * e₂ ∈ Q := Q.mul_mem he₁Q he₂Q
  have hprod2 : (e₁ * e₂) ^ 2 = q ^ 2 := by
    have hc : Commute e₁ e₂ := by
      rw [commute_iff_eq]
      exact hQ.comm e₁ he₁Q e₂ he₂Q
    rw [hc.mul_pow 2, he₁sq, he₂sq, hq2eq]
  have hr2 : ((e₁ * e₂)⁻¹ * q) ^ 2 = 1 := by
    have hc : Commute (e₁ * e₂) q := by
      rw [commute_iff_eq]
      exact hQ.comm (e₁ * e₂) hprodQ q hq
    rw [hc.inv_left.mul_pow 2, inv_pow, hprod2, inv_mul_cancel]
  have hrV : (e₁ * e₂)⁻¹ * q ∈ omega1 D hD.comm :=
    (QHyp.mem_omega1_iff hD hQ (Q.mul_mem (Q.inv_mem hprodQ) hq)).2 hr2
  obtain ⟨u₁, hu₁, u₂, hu₂, hreq⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hrV
  have hu₁Q : u₁ ∈ Q := hQ.D_le (mem_omega1_iff.1 (wFix_le_omega1 hD w hu₁)).1
  have he₁u₁ : e₁ * u₁ ∈ wreathE₂ hD Q (w + 1) := by
    have hu₁' : u₁ ∈ wKer hD (w + 1) := by rwa [wKer_add_one hD w]
    exact (wreathE₂ hD Q (w + 1)).mul_mem he₁ (wKer_le_wreathE₂ hD hQ hu₁')
  have he₂u₂ : e₂ * u₂ ∈ wreathE₂ hD Q w :=
    (wreathE₂ hD Q w).mul_mem he₂ (wKer_le_wreathE₂ hD hQ hu₂)
  have hqeq : q = (e₁ * u₁) * (e₂ * u₂) := by
    calc q = (e₁ * e₂) * (u₁ * u₂) := by rw [← hreq]; group
      _ = e₁ * (e₂ * u₁) * u₂ := by group
      _ = e₁ * (u₁ * e₂) * u₂ := by rw [hQ.comm e₂ he₂Q u₁ hu₁Q]
      _ = (e₁ * u₁) * (e₂ * u₂) := by group
  exact ⟨e₁ * u₁, he₁u₁, e₂ * u₂, he₂u₂, hqeq⟩

private theorem eq_one_of_mem_wreathE₂_add_one_of_fixed (hD : DHyp A Aa t D)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj₁ : Function.Surjective ρ₁)
    {c₂ : G → (Fin 4 → ZMod 2)} (hc₂ : IsCoord (wFix hD (w + 1)) c₂)
    (ρ₂ : ↥(wreathN₁ hD Q (w + 1)) →* GL (Fin 4) (ZMod 2))
    (hρ₂ : ∀ σ : ↥(wreathN₁ hD Q (w + 1)),
      IsRep (wFix hD (w + 1)) c₂ σ (ρ₂ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj₂ : Function.Surjective ρ₂)
    {e : G} (he : e ∈ wreathE₂ hD Q (w + 1))
    (hfix : ∀ x ∈ wreathP₁ hD Q w, x * e * x⁻¹ = e) : e = 1 := by
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  obtain ⟨σ, hσP, -, hσfree⟩ := exists_fixedPointFree_mem_wreathP₁ hD hc₁ ρ₁ hρ₁ hsurj₁
  have heQ : e ∈ Q := wreathE₂_le hD Q (w + 1) he
  have he2 : e ^ 2 ∈ wFix hD w := by
    have h := sq_mem_wKer_of_mem_wreathE₂ hD hww' hQ hq4 hc₂ ρ₂ hρ₂ hsurj₂ he
    rwa [wKer_add_one hD w] at h
  have hfix2 : σ * e ^ 2 * σ⁻¹ = e ^ 2 := by
    calc σ * e ^ 2 * σ⁻¹ = (σ * e * σ⁻¹) ^ 2 := by
          rw [pow_two, pow_two]
          group
      _ = e ^ 2 := by rw [hfix σ hσP]
  have he2one : e ^ 2 = 1 := hσfree _ he2 hfix2
  have heV : e ∈ omega1 D hD.comm := (QHyp.mem_omega1_iff hD hQ heQ).2 he2one
  have heV₁ : e ∈ wFix hD w := by
    have hmem : e ∈ wreathE₂ hD Q (w + 1) ⊓ omega1 D hD.comm := ⟨he, heV⟩
    rwa [wreathE₂_inf_omega1 hD hww' hQ hc₂ ρ₂ hρ₂ hsurj₂, wKer_add_one hD w] at hmem
  exact hσfree e heV₁ (hfix σ hσP)

private theorem eq_one_of_mem_wreathE₂_of_fixed (hD : DHyp A Aa t D)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2))
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj₁ : Function.Surjective ρ₁)
    {c₂ : G → (Fin 4 → ZMod 2)} (hc₂ : IsCoord (wFix hD (w + 1)) c₂)
    (ρ₂ : ↥(wreathN₁ hD Q (w + 1)) →* GL (Fin 4) (ZMod 2))
    (hρ₂ : ∀ σ : ↥(wreathN₁ hD Q (w + 1)),
      IsRep (wFix hD (w + 1)) c₂ σ (ρ₂ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj₂ : Function.Surjective ρ₂)
    {e : G} (he : e ∈ wreathE₂ hD Q w)
    (hfix : ∀ y ∈ wreathP₁ hD Q (w + 1), y * e * y⁻¹ = e) : e = 1 := by
  obtain ⟨σ, hσP, -, hσfree⟩ := exists_fixedPointFree_mem_wreathP₁ hD hc₂ ρ₂ hρ₂ hsurj₂
  have heQ : e ∈ Q := wreathE₂_le hD Q w he
  have he2 : e ^ 2 ∈ wFix hD (w + 1) := by
    have h := sq_mem_wKer_of_mem_wreathE₂ hD hww hQ hq4 hc₁ ρ₁ hρ₁ hsurj₁ he
    rwa [wFix_add_one hD w]
  have hfix2 : σ * e ^ 2 * σ⁻¹ = e ^ 2 := by
    calc σ * e ^ 2 * σ⁻¹ = (σ * e * σ⁻¹) ^ 2 := by
          rw [pow_two, pow_two]
          group
      _ = e ^ 2 := by rw [hfix σ hσP]
  have he2one : e ^ 2 = 1 := hσfree _ he2 hfix2
  have heV : e ∈ omega1 D hD.comm := (QHyp.mem_omega1_iff hD hQ heQ).2 he2one
  have heV₂ : e ∈ wFix hD (w + 1) := by
    rw [wFix_add_one hD w]
    have hmem : e ∈ wreathE₂ hD Q w ⊓ omega1 D hD.comm := ⟨he, heV⟩
    rwa [wreathE₂_inf_omega1 hD hww hQ hc₁ ρ₁ hρ₁ hsurj₁] at hmem
  exact hσfree e heV₂ (hfix σ hσP)

theorem ThCyc.odd_card_wreathP₁_inf (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    Odd (Nat.card ↥(wreathP₁ hD Q w ⊓ wreathP₁ hD Q (w + 1))) := by
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  have hτw' : vConj hD t * (w + 1) * vConj hD t = (w + 1) + 1 :=
    vConj_t_mul_add_one_mul H W W2 hD hτw
  have hgw' : g ∈ wComm hD (w + 1) := by rwa [wComm_add_one hD w]
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hsurj₂⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb
    (commute_vConj_add_one hD hwH) hww' hτw' hQ hgQ hgw' hgM
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hsurj₁⟩ := H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ
    hgQ hgw hgM
  obtain ⟨O, hO, hCQ⟩ := QHyp.exists_odd_complement hQ
  have hE : ∀ q ∈ Q, ∃ e₁ ∈ wreathE₂ hD Q (w + 1), ∃ e₂ ∈ wreathE₂ hD Q w,
      q = e₁ * e₂ :=
    fun q hq => H.exists_mul_of_mem_Q W W2 hD h4 hb hwH hww hτw hQ hq4 hsq hΦ hgQ hgw hgM hq
  have hE12 : wreathE₂ hD Q (w + 1) ⊓ wreathE₂ hD Q w = ⊥ :=
    H.wreathE₂_inf_wreathE₂_add_one W W2 hD h4 hb hwH hww hτw hQ hq4 hgQ hgw hgM
  have h₁₂ : ∀ x ∈ wreathP₁ hD Q w, ∀ e ∈ wreathE₂ hD Q w, x * e = e * x :=
    fun x hx e he => ((mem_wreathE₂_iff hD).1 he).2 x hx
  have h₁₁ : ∀ x ∈ wreathP₁ hD Q w, ∀ e ∈ wreathE₂ hD Q (w + 1),
      x * e * x⁻¹ ∈ wreathE₂ hD Q (w + 1) := by
    intro x hx e he
    have hxN : x ∈ normalizer (Q : Set G) ⊓ wComm hD (w + 1) := by
      rw [wComm_add_one hD w]
      exact wreathP₁_le hD Q w hx
    exact conj_mem_wreathE₂ hD hxN he
  have h₂₁ : ∀ y ∈ wreathP₁ hD Q (w + 1), ∀ e ∈ wreathE₂ hD Q (w + 1), y * e = e * y :=
    fun y hy e he => ((mem_wreathE₂_iff hD).1 he).2 y hy
  have h₂₂ : ∀ y ∈ wreathP₁ hD Q (w + 1), ∀ e ∈ wreathE₂ hD Q w,
      y * e * y⁻¹ ∈ wreathE₂ hD Q w := by
    intro y hy e he
    have hyN : y ∈ normalizer (Q : Set G) ⊓ wComm hD w := by
      rw [← wComm_add_one hD w]
      exact wreathP₁_le hD Q (w + 1) hy
    exact conj_mem_wreathE₂ hD hyN he
  have hP : ∀ x ∈ wreathP₁ hD Q w, ∀ y ∈ wreathP₁ hD Q (w + 1),
      x * y * x⁻¹ * y⁻¹ ∈ wreathP₁ hD Q w ⊓ wreathP₁ hD Q (w + 1) :=
    fun x hx y hy => commutator_mem_wreathP₁_inf hD hx hy
  have hP₁ : wreathP₁ hD Q w ≤
      Subgroup.closure {x : G | x ∈ wreathP₁ hD Q w ∧ Odd (orderOf x)} :=
    wreathP₁_le_closure_odd hD Q w
  have hP₂ : wreathP₁ hD Q (w + 1) ≤
      Subgroup.closure {x : G | x ∈ wreathP₁ hD Q (w + 1) ∧ Odd (orderOf x)} :=
    wreathP₁_le_closure_odd hD Q (w + 1)
  have hC₁ : ∀ e ∈ wreathE₂ hD Q (w + 1),
      (∀ x ∈ wreathP₁ hD Q w, x * e * x⁻¹ = e) → e = 1 :=
    fun e he hfix => eq_one_of_mem_wreathE₂_add_one_of_fixed hD hQ hww hq4 hc₁ ρ₁ hρ₁ hsurj₁
      hc₂ ρ₂ hρ₂ hsurj₂ he hfix
  have hC₂ : ∀ e ∈ wreathE₂ hD Q w, (∀ y ∈ wreathP₁ hD Q (w + 1), y * e * y⁻¹ = e) →
      e = 1 :=
    fun e he hfix => eq_one_of_mem_wreathE₂_of_fixed hD hQ hww hq4 hc₁ ρ₁ hρ₁ hsurj₁
      hc₂ ρ₂ hρ₂ hsurj₂ he hfix
  exact odd_card_inf_of_complementary_actions (Q := Q) (E₁ := wreathE₂ hD Q (w + 1))
    (E₂ := wreathE₂ hD Q w) (P₁ := wreathP₁ hD Q w) (P₂ := wreathP₁ hD Q (w + 1)) (O := O)
    hQ.pgroup hQ.comm (wreathE₂_le hD Q (w + 1)) (wreathE₂_le hD Q w) hE hE12 h₁₂ h₁₁ h₂₁ h₂₂
    hP hP₁ hP₂ hO hCQ hC₁ hC₂

theorem ThCyc.false_of_wreath_case (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    (hX₀ : ∃ X₀ : Subgroup G, X₀ ≤ wreathP₁ hD Q w ∧ IsPGroup 2 X₀ ∧ Nat.card X₀ = 2 ^ 15) :
    False := by
  obtain ⟨X₀, hX₀P, hX₀p, hX₀card⟩ := hX₀
  have hmap : (wreathP₁ hD Q w).map (MulAut.conj t).toMonoidHom = wreathP₁ hD Q (w + 1) :=
    map_conj_t_wreathP₁ H W W2 hD hτw hQ
  have hodd : Odd (Nat.card ↥(wreathP₁ hD Q w ⊓
      (wreathP₁ hD Q w).map (MulAut.conj t).toMonoidHom)) := by
    rw [hmap]
    exact H.odd_card_wreathP₁_inf W W2 hD h4 hb hwH hww hτw hQ hq4 hsq hΦ hgQ hgw hgM
  have hcomm : ∀ x ∈ wreathP₁ hD Q w,
      ∀ y ∈ (wreathP₁ hD Q w).map (MulAut.conj t).toMonoidHom,
      x * y * x⁻¹ * y⁻¹ ∈ wreathP₁ hD Q w ⊓
        (wreathP₁ hD Q w).map (MulAut.conj t).toMonoidHom := by
    intro x hx y hy
    rw [hmap] at hy ⊢
    exact commutator_mem_wreathP₁_inf hD hx hy
  obtain ⟨X, -, hXcard, hXcomm, hXinter⟩ :=
    exists_le_card_eq_commute_conj_of_odd_inf H.sq_t hX₀P hX₀p hodd hcomm
  refine ThCyc.false_of_wreath H W.isThSylow ?_ hXcomm hXinter
  rw [hXcard, hX₀card, ThLocalIn.card_S W]

end CFSG.EvenSporadicStandard.ThStd
