module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.PrimeTorsionExponentRankTwo
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.PGroupTripleCommutatorCentral
import CFSG.FeitThompson.Local.PrimePowerMapHomClassThree
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p d : ℕ} {G : Type*} [Group G]

theorem map_omega1_mulEquiv {H : Type*} [Group H] (p : ℕ) (f : G ≃* H) :
    (omega1 p G).map (f : G →* H) = omega1 p H := by
  rw [omega1_eq_closure, omega1_eq_closure, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  refine ⟨?_, fun hy => ⟨f.symm y, ?_, f.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← map_pow, hx, map_one]
  · have h : f.symm y ^ p = f.symm (y ^ p) := by rw [map_pow]
    rw [h, hy, map_one]

theorem natCard_omega1_congr {H : Type*} [Group H] (p : ℕ) (f : G ≃* H) :
    Nat.card (omega1 p G) = Nat.card (omega1 p H) := by
  rw [Nat.card_congr ((omega1 p G).equivMapOfInjective (f : G →* H) f.injective).toEquiv,
    map_omega1_mulEquiv p f]

theorem omega1_eq_top_of_forall_pow_eq_one (h : ∀ x : G, x ^ p = 1) : omega1 p G = ⊤ :=
  eq_top_iff.2 fun x _ => mem_omega1_of_pow_eq_one (h x)

theorem natCard_omega1_of_forall_pow_eq_one (h : ∀ x : G, x ^ p = 1) :
    Nat.card (omega1 p G) = Nat.card G := by
  rw [omega1_eq_top_of_forall_pow_eq_one h, Subgroup.card_top]

theorem omega1_omega1_eq_top (p : ℕ) (G : Type*) [Group G] : omega1 p ↥(omega1 p G) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  have h : (y : G) ∈ (omega1 p ↥(omega1 p G)).map (omega1 p G).subtype := by
    rw [map_omega1_subtype_eq_omega1Subgroup]
    exact omega1_le (H := omega1Subgroup p (omega1 p G))
      (fun x hx => mem_omega1Subgroup (mem_omega1_of_pow_eq_one hx) hx) y.2
  obtain ⟨z, hz, hzy⟩ := h
  exact Subtype.ext hzy ▸ hz

theorem natCard_omega1_omega1 (p : ℕ) (G : Type*) [Group G] :
    Nat.card (omega1 p ↥(omega1 p G)) = Nat.card (omega1 p G) := by
  rw [omega1_omega1_eq_top, Subgroup.card_top]

theorem natCard_omega1_subgroup_le [Finite G] (p : ℕ) (K : Subgroup G) :
    Nat.card (omega1 p ↥K) ≤ Nat.card (omega1 p G) := by
  have h1 : (omega1 p ↥K).map K.subtype ≤ omega1 p G := by
    rw [map_omega1_subtype_eq_omega1Subgroup]
    exact omega1Subgroup_le fun _ _ hxp => mem_omega1_of_pow_eq_one hxp
  calc Nat.card (omega1 p ↥K)
      = Nat.card ((omega1 p ↥K).map K.subtype) :=
        Nat.card_congr ((omega1 p ↥K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv
    _ ≤ Nat.card (omega1 p G) := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h1)

theorem pow_le_natCard_omega1_of_mem_elementaryAbelianRanks [Finite G]
    (hd : d ∈ elementaryAbelianRanks p G) : p ^ d ≤ Nat.card (omega1 p G) := by
  obtain ⟨E, ⟨f⟩⟩ := mem_elementaryAbelianRanks.1 hd
  have hle : E ≤ omega1 p G := fun x hx => mem_omega1_of_pow_eq_one (by
    have h : (⟨x, hx⟩ : ↥E) ^ p = 1 :=
      f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
    simpa using congrArg (Subgroup.subtype E) h)
  calc p ^ d = Nat.card ↥E := by rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
    _ ≤ Nat.card (omega1 p G) := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)

theorem elementaryAbelianPRank_le_two_of_natCard_omega1_le [Finite G] (hp : p.Prime)
    (h : Nat.card (omega1 p G) ≤ p ^ 2) : elementaryAbelianPRank p G ≤ 2 := by
  by_contra hc
  have h3 : (3 : ℕ) ∈ elementaryAbelianRanks p G :=
    mem_elementaryAbelianRanks_of_le (by omega)
      (elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt)
  exact absurd ((pow_le_natCard_omega1_of_mem_elementaryAbelianRanks h3).trans h)
    (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

noncomputable def quotientSubgroupOfComapEquiv (N : Subgroup G) [N.Normal] (J : Subgroup (G ⧸ N)) :
    ↥(J.comap (QuotientGroup.mk' N)) ⧸ N.subgroupOf (J.comap (QuotientGroup.mk' N)) ≃* ↥J := by
  set H := J.comap (QuotientGroup.mk' N) with hH
  have hmem : ∀ x : ↥H, (QuotientGroup.mk' N) (x : G) ∈ J := fun x => x.2
  set f : ↥H →* ↥J := ((QuotientGroup.mk' N).comp H.subtype).codRestrict J hmem with hf
  have hfval : ∀ x : ↥H, (f x : G ⧸ N) = QuotientGroup.mk (x : G) := fun _ => rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : f.ker = N.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (x : G),
      ← Subtype.coe_inj (p := fun z => z ∈ J), hfval x]
    simp
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

theorem comap_mk'_ne_top (N : Subgroup G) [N.Normal] {J : Subgroup (G ⧸ N)} (hJ : J ≠ ⊤) :
    J.comap (QuotientGroup.mk' N) ≠ ⊤ := fun h => hJ (by
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) J, h,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)])

private theorem normal_of_le_center' {R : Type*} [Group R] {Z : Subgroup R}
    (h : Z ≤ Subgroup.center R) : Z.Normal where
  conj_mem z hz g := by
    rw [(Subgroup.mem_center_iff.1 (h hz)) g, mul_assoc, mul_inv_cancel, mul_one]
    exact hz

private theorem natCard_quotient_lt {R : Type*} [Group R] [Finite R] {Z : Subgroup R}
    [Z.Normal] (hZ : Z ≠ ⊥) : Nat.card (R ⧸ Z) < Nat.card R := by
  have h := Z.card_eq_card_quotient_mul_card_subgroup
  have h1 : 1 < Nat.card ↥Z := (Subgroup.one_lt_card_iff_ne_bot Z).2 hZ
  have h2 : 0 < Nat.card (R ⧸ Z) := Nat.card_pos
  rw [h]
  nlinarith

private theorem self_lt_pow (hp : 1 < p) {k : ℕ} (hk : 1 < k) : p < p ^ k := by
  simpa using Nat.pow_lt_pow_right hp hk

private theorem card_eq_and_exponent_of_lt_card_omega1 {Q : Type*} [Group Q] [Finite Q]
    (hp : p.Prime) (hp3 : 3 < p) (hQ : IsPGroup p Q)
    (hJ : ∀ J : Subgroup Q, J ≠ ⊤ → Nat.card (omega1 p ↥J) ≤ p ^ 2)
    (hlt : p ^ 2 < Nat.card (omega1 p Q)) :
    Nat.card Q = p ^ 3 ∧ ∀ x : Q, x ^ p = 1 := by
  have := Fact.mk hp
  have htop : omega1 p Q = ⊤ := by
    by_contra hne
    exact absurd hlt (not_lt.2 (by rw [← natCard_omega1_omega1]; exact hJ _ hne))
  have hcardQ : p ^ 2 < Nat.card Q := by rwa [htop, Subgroup.card_top] at hlt
  rcases Nat.lt_or_ge (elementaryAbelianPRank p Q) 3 with hrank | hrank
  · have hrank2 : elementaryAbelianPRank p Q ≤ 2 := by omega
    have hexp : ∀ x : Q, x ^ p = 1 := fun x =>
      pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hQ hrank2 (htop ▸ mem_top x)
    refine ⟨?_, hexp⟩
    have hle := card_le_pow_three_of_elementaryAbelianPRank_le_two hp hrank2 hexp
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    rw [ha] at hle hcardQ ⊢
    have h1 : 2 < a := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcardQ
    have h2 : a ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
    exact congrArg (p ^ ·) (by omega)
  · obtain ⟨H, ⟨f⟩⟩ := mem_elementaryAbelianRanks.1 (mem_elementaryAbelianRanks_of_le
      (M := Q) (p := p) hrank (elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt))
    have hexpH : ∀ x : ↥H, x ^ p = 1 := fun x =>
      f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
    have hcardH : Nat.card ↥H = p ^ 3 := by
      rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
    have hHtop : H = ⊤ := by
      by_contra hne
      have h := hJ H hne
      rw [natCard_omega1_of_forall_pow_eq_one hexpH, hcardH] at h
      exact absurd h (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
    refine ⟨by rw [← Subgroup.card_top (G := Q), ← hHtop, hcardH], fun x => ?_⟩
    simpa using hexpH ⟨x, hHtop ▸ mem_top x⟩

private theorem not_exists_pow_four_config {R : Type*} [Group R] [Finite R] (hp : p.Prime)
    (hp3 : 3 < p) (hR : IsPGroup p R) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) (N : Subgroup R)
    [N.Normal] (hNp : Nat.card ↥N = p) (hQcard : Nat.card (R ⧸ N) = p ^ 3)
    (hQexp : ∀ x : R ⧸ N, x ^ p = 1) : False := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hRcard : Nat.card R = p ^ 4 := by
    rw [N.card_eq_card_quotient_mul_card_subgroup, hQcard, hNp]; ring
  have hxpN : ∀ x : R, x ^ p ∈ N := fun x => by
    refine (QuotientGroup.eq_one_iff (x ^ p)).1 ?_
    have h : ((x : R ⧸ N)) ^ p = 1 := hQexp _
    rwa [← QuotientGroup.mk_pow] at h
  have hnc : ¬ IsCyclic R := by
    intro hcyc
    have : IsCyclic (R ⧸ N) := isCyclic_of_surjective _ (QuotientGroup.mk'_surjective N)
    have hd : Monoid.exponent (R ⧸ N) ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hQexp
    rw [IsCyclic.exponent_eq_card, hQcard] at hd
    exact absurd (Nat.le_of_dvd hp.pos hd) (not_le.2 (self_lt_pow hp.one_lt (by norm_num)))
  have hrank2 := two_le_elementaryAbelianPRank_of_not_isCyclic hp hodd hR hnc
  have hΩge : p ^ 2 ≤ Nat.card (omega1 p R) :=
    pow_le_natCard_omega1_of_mem_elementaryAbelianRanks
      (mem_elementaryAbelianRanks_of_le hrank2
        (elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt))
  have hΩeq : Nat.card (omega1 p R) = p ^ 2 := le_antisymm hΩ hΩge
  have hrank := elementaryAbelianPRank_le_two_of_natCard_omega1_le hp hΩ
  have hΩcoe : (omega1 p R : Set R) = {x : R | x ^ p = 1} :=
    coe_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank
  have hquotcard : Nat.card (R ⧸ omega1 p R) = p ^ 2 := by
    have h := (omega1 p R).card_eq_card_quotient_mul_card_subgroup
    rw [hRcard, hΩeq, show p ^ 4 = p ^ 2 * p ^ 2 by ring] at h
    exact Nat.mul_right_cancel (pow_pos hp.pos 2) h.symm
  have hcomm : _root_.commutator R ≤ omega1 p R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.1
      (isMulCommutative_of_natCard_le_sq hp (hR.to_quotient _) hquotcard.le)
  have hexp : ∀ c ∈ _root_.commutator R, c ^ p = 1 := fun c hc =>
    (Set.ext_iff.1 hΩcoe c).1 (hcomm hc)
  have hZ : ⁅_root_.commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R :=
    commutator_commutator_le_center hp hR hRcard.le
  set f := powHomOfTripleCommutatorLeCenter hp hp3 hZ hexp with hf
  have hker : f.ker = omega1 p R := SetLike.coe_injective (by
    rw [hf, coe_ker_powHomOfTripleCommutatorLeCenter, hΩcoe])
  have hrange : f.range ≤ N := by
    rintro y ⟨x, rfl⟩
    rw [hf, powHomOfTripleCommutatorLeCenter_apply]
    exact hxpN x
  have hcard : Nat.card R = Nat.card f.range * Nat.card f.ker := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup]
    exact congrArg (· * Nat.card f.ker)
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv)
  rw [hRcard, hker, hΩeq, show p ^ 4 = p ^ 2 * p ^ 2 by ring] at hcard
  have hrangecard : Nat.card f.range = p ^ 2 :=
    Nat.mul_right_cancel (pow_pos hp.pos 2) hcard.symm
  have hle : Nat.card f.range ≤ p := hNp ▸ Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hrange)
  rw [hrangecard] at hle
  exact absurd hle (not_le.2 (self_lt_pow hp.one_lt (by norm_num)))

private theorem quotient_aux (hp : p.Prime) (hp3 : 3 < p) (n : ℕ) :
    ∀ {R : Type u} [Group R] [Finite R], Nat.card R < n → IsPGroup p R →
      Nat.card (omega1 p R) ≤ p ^ 2 →
      ∀ (m : ℕ) (N : Subgroup R) [N.Normal], Nat.card ↥N < m →
        Nat.card (omega1 p (R ⧸ N)) ≤ p ^ 2 := by
  induction n with
  | zero => intro R _ _ hcard; exact absurd hcard (Nat.not_lt_zero _)
  | succ n ih =>
    intro R _ _ hcard hR hΩ m
    induction m with
    | zero => intro N _ hNcard; exact absurd hNcard (Nat.not_lt_zero _)
    | succ m ihm =>
      intro N hN hNcard
      have := Fact.mk hp
      obtain ⟨a, ha⟩ := hR.exists_card_eq
      rcases eq_or_ne N ⊥ with rfl | hNbot
      · rw [natCard_omega1_congr p (QuotientGroup.quotientBot (G := R))]
        exact hΩ
      obtain ⟨k, hk⟩ := (hR.to_subgroup N).exists_card_eq
      rcases Nat.lt_or_ge 1 k with hk1 | hk1
      ·
        obtain ⟨Z, hZle, hZcard⟩ := exists_le_inf_center_natCard_eq N hp ha hNbot
        have hZN : Z ≤ N := hZle.trans inf_le_left
        have hZcen : Z.Normal := normal_of_le_center' (hZle.trans inf_le_right)
        have := hZcen
        have hZbot : Z ≠ ⊥ := by
          intro h; rw [h, Subgroup.card_bot] at hZcard; exact hp.one_lt.ne hZcard
        have hZlt : Nat.card ↥Z < m := by
          have hpk : p < p ^ k := by simpa using Nat.pow_lt_pow_right hp.one_lt hk1
          rw [hk] at hNcard
          omega
        have hΩZ : Nat.card (omega1 p (R ⧸ Z)) ≤ p ^ 2 := ihm Z hZlt
        have hlt : Nat.card (R ⧸ Z) < n := by
          have := natCard_quotient_lt (R := R) (Z := Z) hZbot
          omega
        have hNmap := hN.map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
        have hkey := ih hlt (hR.to_quotient Z) hΩZ (Nat.card ↥(N.map (QuotientGroup.mk' Z)) + 1)
          (N.map (QuotientGroup.mk' Z)) (Nat.lt_succ_self _)
        rwa [natCard_omega1_congr p (QuotientGroup.quotientQuotientEquivQuotient Z N hZN)] at hkey
      ·
        have hNp : Nat.card ↥N = p := by
          interval_cases k
          · rw [pow_zero] at hk
            exact absurd (Subgroup.card_eq_one.1 hk) hNbot
          · rwa [pow_one] at hk
        by_contra hcon
        rw [not_le] at hcon
        have hJ : ∀ J : Subgroup (R ⧸ N), J ≠ ⊤ → Nat.card (omega1 p ↥J) ≤ p ^ 2 := by
          intro J hJtop
          have hHtop : J.comap (QuotientGroup.mk' N) ≠ ⊤ := comap_mk'_ne_top N hJtop
          have hHlt : Nat.card ↥(J.comap (QuotientGroup.mk' N)) < n := by
            have := natCard_lt_natCard_of_ne_top (G := R) hHtop
            omega
          have hΩH : Nat.card (omega1 p ↥(J.comap (QuotientGroup.mk' N))) ≤ p ^ 2 :=
            (natCard_omega1_subgroup_le p _).trans hΩ
          have hkey := ih hHlt (hR.to_subgroup _) hΩH
            (Nat.card ↥(N.subgroupOf (J.comap (QuotientGroup.mk' N))) + 1)
            (N.subgroupOf (J.comap (QuotientGroup.mk' N))) (Nat.lt_succ_self _)
          rwa [natCard_omega1_congr p (quotientSubgroupOfComapEquiv N J)] at hkey
        obtain ⟨hQcard, hQexp⟩ :=
          card_eq_and_exponent_of_lt_card_omega1 hp hp3 (hR.to_quotient N) hJ hcon
        exact not_exists_pow_four_config hp hp3 hR hΩ N hNp hQcard hQexp

variable {R : Type*} [Group R]

theorem natCard_omega1_quotient_le_sq [Finite R] (hp : p.Prime) (hp3 : 3 < p) (hR : IsPGroup p R)
    (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) (N : Subgroup R) [N.Normal] :
    Nat.card (omega1 p (R ⧸ N)) ≤ p ^ 2 :=
  quotient_aux hp hp3 (Nat.card R + 1) (Nat.lt_succ_self _) hR hΩ (Nat.card ↥N + 1) N
    (Nat.lt_succ_self _)

theorem natCard_omega1_quotient_le_sq_of_card_eq_pow {a : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hR : Nat.card R = p ^ a) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) (N : Subgroup R) [N.Normal] :
    Nat.card (omega1 p (R ⧸ N)) ≤ p ^ 2 :=
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; exact pow_ne_zero _ hp.pos.ne')
  natCard_omega1_quotient_le_sq hp hp3 (IsPGroup.of_card hR) hΩ N

theorem elementaryAbelianPRank_quotient_le_two [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) (N : Subgroup R) [N.Normal] :
    elementaryAbelianPRank p (R ⧸ N) ≤ 2 :=
  elementaryAbelianPRank_le_two_of_natCard_omega1_le hp
    (natCard_omega1_quotient_le_sq hp hp3 hR hΩ N)

end

end CFSG.FeitThompson
