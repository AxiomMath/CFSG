module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {W : Type} [CommGroup W] [Finite W]

theorem four_le_index_of_outer_inverts (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : 3 ≤ orderOf (2 : ZMod p)) {x : S} (hx : orderOf x = p)
    (hinv : psiAut L e hb x = x⁻¹) :
    4 ≤ (fixV (Subgroup.zpowers b)).index := by
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨y, rfl⟩ := hπ x
  have hπy : π y = e (QuotientGroup.mk y) := rfl
  have hby : (conjAut L hb y : MulAut W) = b * y * b⁻¹ := coe_conjAut L hb y
  set u : ↥L := conjAut L hb y * y⁻¹ with hu
  have hπu : π u = (π y)⁻¹ * (π y)⁻¹ := by
    have h1 : π (conjAut L hb y) = psiAut L e hb (π y) := by
      rw [hπy, psiAut_mk]
      rfl
    rw [hu, map_mul, h1, hinv, map_inv]
  have hpu : p ∣ orderOf u := by
    have h1 := orderOf_map_dvd π u
    have h2 : orderOf (π u) = p := by
      rw [hπu, ← mul_inv_rev, orderOf_inv, ← sq, orderOf_pow' _ (by norm_num), hx,
        Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Fact.out Nat.prime_two).2 hp2), Nat.div_one]
    rwa [h2] at h1
  obtain ⟨j, hj⟩ := hpu
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, mul_zero] at hj
      exact absurd hj (orderOf_pos u).ne'
    · exact h0
  have hord : orderOf (u ^ j) = p := by
    rw [orderOf_pow_of_dvd hjpos.ne' ⟨p, by rw [hj, mul_comm]⟩, hj, Nat.mul_div_cancel _ hjpos]
  have hordW : orderOf (((u ^ j : ↥L)) : MulAut W) = p := by
    rw [Subgroup.orderOf_coe, hord]
  have h1 := two_pow_orderOf_le_index_fixV hW hp2 hordW
  have h2 : (fixV (Subgroup.zpowers (((u ^ j : ↥L)) : MulAut W))).index ≤
      (fixV (Subgroup.zpowers (u : MulAut W))).index := by
    have := index_fixV_pow_le (u : MulAut W) j
    simpa using this
  have hbinv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one]
    exact hb2
  have h3 : (fixV (Subgroup.zpowers (u : MulAut W))).index ≤
      (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index := by
    have hu' : (u : MulAut W) = b * ((y : MulAut W) * b⁻¹ * (y : MulAut W)⁻¹) := by
      rw [hu, Subgroup.coe_mul, hby, Subgroup.coe_inv]
      group
    have := index_fixV_mul_le b ((y : MulAut W) * b⁻¹ * (y : MulAut W)⁻¹)
    rw [index_fixV_conj, hbinv] at this
    rw [hu', hbinv]
    exact this
  have h4 : 2 ^ orderOf (2 : ZMod p) ≤ (fixV (Subgroup.zpowers b)).index ^ 2 := by
    rw [sq]
    exact h1.trans (h2.trans h3)
  have h5 := two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h4 (ρ := 2) (by omega)
  simpa using h5

theorem weight_lt_of_route_A (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L) {S : Type} [Group S] [Finite S]
    (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {r ρ : ℕ} (hrρ : r + 1 < ρ)
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hinner : ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index)
    (houter : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ (p : ℕ) (_ : Fact p.Prime) (x : S), p ≠ 2 ∧ 3 ≤ orderOf (2 : ZMod p) ∧
        orderOf x = p ∧ ψ x = x⁻¹) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  apply weight_lt_of_lt_index
  have hmono : ∀ b ∈ E, (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := fun b hb =>
    Subgroup.index_antitone (QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 hb))
  have hEcard := card_le_two_mul_inf hW hq.1 hirr hE hEel e hcent hcard2
  by_cases hEL : E ⊓ L = ⊥
  ·
    rw [hEL, Subgroup.card_bot, mul_one] at hEcard
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hb2 : b * b = 1 := by
      have := hEel.2 b hbE
      rwa [sq] at this
    have hbL : b ∉ L := fun h => by
      have : b ∈ E ⊓ L := ⟨hbE, h⟩
      rw [hEL, Subgroup.mem_bot] at this
      exact hb1' this
    have hψo : psiAut L e (hE hbE) ∉ (MulAut.conj : S →* MulAut S).range := by
      rintro ⟨s, hs⟩
      refine hbL (mem_of_psiAut_inner hW hq.1 hirr hE hEel e hbE s fun x => ?_)
      rw [← hs, MulAut.conj_apply]
    have hψ2 : psiAut L e (hE hbE) * psiAut L e (hE hbE) = 1 := by
      have hbb : b * b ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).mul_mem (hE hbE) (hE hbE)
      have key : ∀ (c : MulAut W) (hc : c ∈ Subgroup.normalizer (L : Set (MulAut W))), c = 1 →
          psiAut L e hc = 1 := by
        rintro c hc rfl
        exact psiAut_one e hc
      rw [← psiAut_mul e (hE hbE) (hE hbE) hbb]
      exact key _ hbb hb2
    obtain ⟨p, hp, x, hp2, hd, hx, hinv⟩ := houter _ hψo hψ2
    have h4 := four_le_index_of_outer_inverts hW e (hE hbE) hb2 hp2 hd hx hinv
    calc Nat.card E ≤ 2 := hEcard
      _ < 4 := by norm_num
      _ ≤ (fixV E).index := h4.trans (hmono b hbE)
  ·
    obtain ⟨⟨a, haEL⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEL
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha2 : a * a = 1 := by
      have := hEel.2 a haEL.1
      rwa [sq] at this
    have hEel' : IsElemAbelian2 (E ⊓ L) :=
      ⟨fun x hx y hy => hEel.1 x hx.1 y hy.1, fun x hx => hEel.2 x hx.1⟩
    have hE0 : Nat.card ↥(E ⊓ L) ≤ 2 ^ r :=
      card_le_two_pow_of_le hW hirr inf_le_right hEel' e hr
    have hρ := hinner a haEL.2 ha1' ha2
    calc Nat.card E ≤ 2 * 2 ^ r := hEcard.trans (Nat.mul_le_mul_left _ hE0)
      _ = 2 ^ (r + 1) := by ring
      _ < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hrρ
      _ ≤ (fixV E).index := hρ.trans (hmono a haEL.1)

theorem noIrrFFOffender_of_route_A {Y : Type} [Group Y] [Finite Y]
    (hcent : Subgroup.center Y = ⊥) (hcard2 : Nat.card (MulAut Y) ≤ 2 * Nat.card Y)
    {r ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hrρ : r + 1 < ρ)
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hr : ∀ B : Subgroup Y, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hZ : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* Y) → Odd (Nat.card (Subgroup.center L)) →
        ¬ p ∣ Nat.card (Subgroup.center L))
    (hgen : ∀ t : Y, t * t = 1 → t ≠ 1 → ∃ (x y : Fin (n + 1) → Y) (z : Y),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹)
    (houter : ∀ ψ : MulAut Y, ψ ∉ (MulAut.conj : Y →* MulAut Y).range → ψ * ψ = 1 →
      ∃ (p' : ℕ) (_ : Fact p'.Prime) (x : Y), p' ≠ 2 ∧ 3 ≤ orderOf (2 : ZMod p') ∧
        orderOf x = p' ∧ ψ x = x⁻¹) :
    NoIrrFFOffender Y := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hZp := hZ ↥L hq ⟨e⟩ (odd_card_center_of_isIrrOn hW hirr)
  exact weight_lt_of_route_A hW hq hirr e hcent hcard2 hEN hE hel hrρ hr
    (rank_of_heisCfg hW hirr e hp2 hZp hρ hgen) houter

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
