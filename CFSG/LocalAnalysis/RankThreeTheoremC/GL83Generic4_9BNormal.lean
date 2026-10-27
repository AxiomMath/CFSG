module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

section

variable {Y : Type} [Group Y]

private theorem gen49bn_comm {S : Subgroup Y} (hS : IsMulCommutative S) {a b : Y} (ha : a ∈ S)
    (hb : b ∈ S) : Commute a b :=
  congrArg Subtype.val ((IsMulCommutative.is_comm (M := S)).comm ⟨a, ha⟩ ⟨b, hb⟩)

private def gen49bnOmega (p : ℕ) (S : Subgroup Y) (hS : IsMulCommutative S) : Subgroup Y where
  carrier := {s | s ∈ S ∧ s ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haS, hap⟩ ⟨hbS, hbp⟩
    exact ⟨S.mul_mem haS hbS, by rw [(gen49bn_comm hS haS hbS).mul_pow, hap, hbp, one_mul]⟩
  one_mem' := ⟨S.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haS, hap⟩
    exact ⟨S.inv_mem haS, by rw [inv_pow, hap, inv_one]⟩

end

section

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]

private theorem gen49bn_exists_sylow [Finite Y] {S : Subgroup Y} (hS : IsSylowOf p S ⊤) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) = S := by
  obtain ⟨-, hp, hdvd⟩ := isSylowOf_iff.1 hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hp.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

private theorem gen49bn_mem_of_pow_eq_one [Finite Y] {S R Γ : Subgroup Y} {x : Y}
    (h : Gen49BHyp p S R Γ x) {s : Y} (hs : s ∈ S) (hsp : s ^ p = 1) : s ∈ R := by
  have hprime : p.Prime := Fact.out
  have hRΩ : R ≤ gen49bnOmega p S h.abelian := fun r hr => ⟨h.le_sylow hr, h.elemAbelian.2 r hr⟩
  have hΩS : gen49bnOmega p S h.abelian ≤ S := fun s hs => hs.1
  obtain ⟨k, hk⟩ := (h.sylow.isPGroup.to_le hΩS).exists_card_eq
  have hΩe : IsElemAbelian p (gen49bnOmega p S h.abelian) :=
    ⟨⟨⟨fun a b => Subtype.ext (gen49bn_comm h.abelian (hΩS a.2) (hΩS b.2))⟩⟩, fun a ha => ha.2⟩
  have hk2 : k ≤ 2 := by
    refine le_trans (le_csSup (pRank_set_bddAbove p hprime.one_lt (⊤ : Subgroup Y))
      ⟨gen49bnOmega p S h.abelian, le_top, hΩe, hk⟩) h.pRank_le
  have hcard : Nat.card (gen49bnOmega p S h.abelian) ≤ Nat.card R := by
    rw [hk, h.card_eq]
    exact Nat.pow_le_pow_right hprime.pos hk2
  have heq := Subgroup.eq_of_le_of_card_ge hRΩ hcard
  rw [heq]
  exact ⟨hs, hsp⟩

private theorem gen49bn_conj_eq {x t : Y} (hx : orderOf x = p) (hN : t * x * t⁻¹ ∈ zpowers x)
    {m : ℕ} (ht : t ^ p ^ m = 1) : t * x * t⁻¹ = x := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hN
  have key : ∀ n : ℕ, t ^ n * x * (t ^ n)⁻¹ = x ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc t ^ (n + 1) * x * (t ^ (n + 1))⁻¹ = t * (t ^ n * x * (t ^ n)⁻¹) * t⁻¹ := by group
        _ = t * x ^ (k ^ n) * t⁻¹ := by rw [ih]
        _ = (t * x * t⁻¹) ^ (k ^ n) := by rw [conj_zpow]
        _ = (x ^ k) ^ (k ^ n) := by rw [← hk]
        _ = x ^ (k ^ (n + 1)) := by rw [← zpow_mul, pow_succ']
  have h1 : x ^ (k ^ p ^ m) = x := by simpa [ht] using (key (p ^ m)).symm
  have h2 : (k : ZMod p) ^ p ^ m = 1 := by
    have h3 : k ^ p ^ m ≡ 1 [ZMOD (orderOf x : ℤ)] := by
      rw [← zpow_eq_zpow_iff_modEq, h1, zpow_one]
    rw [hx] at h3
    simpa using (ZMod.intCast_eq_intCast_iff _ _ p).2 h3
  have h4 : (k : ZMod p) = 1 := by rw [← ZMod.pow_card_pow (n := m) (k : ZMod p)]; exact h2
  have h5 : k ≡ 1 [ZMOD (orderOf x : ℤ)] := by
    rw [hx]
    exact (ZMod.intCast_eq_intCast_iff _ _ p).1 (by simpa using h4)
  rw [← hk]
  simpa using zpow_eq_zpow_iff_modEq.2 h5

private theorem gen49bn_normalClosure_le {x : Y} {S : Subgroup Y} (hx : orderOf x = p)
    (hxn : (zpowers x).Normal) (hSp : IsPGroup p S) :
    normalClosure (S : Set Y) ≤ centralizer ({x} : Set Y) := by
  refine (Subgroup.closure_le _).2 ?_
  intro u hu
  obtain ⟨s, hs, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hu
  obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
  obtain ⟨m, hm⟩ := hSp ⟨s, hs⟩
  have hsm : s ^ p ^ m = 1 := congrArg Subtype.val hm
  have hu1 : g * s * g⁻¹ * x * (g * s * g⁻¹)⁻¹ = x :=
    gen49bn_conj_eq hx (hxn.conj_mem x (mem_zpowers x) _) (m := m)
      (by rw [conj_pow, hsm, mul_one, mul_inv_cancel])
  exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hu1)

end

theorem gl83Generic4_9BNormal_holds : GL83Generic4_9BNormal := by
  intro p _ Y _ _ S R Γ x h hP
  have hprime : p.Prime := Fact.out
  obtain ⟨Q, hQ⟩ := gen49bn_exists_sylow h.sylow
  have hP0n : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hP0S : CFSG.pCore p Y ≤ S := by
    rw [← hQ]
    exact CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have hΩn : (CFSG.pCore p Y ⊓ R).Normal := by
    refine ⟨fun y hy g => ⟨hP0n.conj_mem y hy.1 g, ?_⟩⟩
    refine gen49bn_mem_of_pow_eq_one h (hP0S (hP0n.conj_mem y hy.1 g)) ?_
    rw [conj_pow, h.elemAbelian.2 y hy.2, mul_one, mul_inv_cancel]
  obtain ⟨a, haΩ, haord⟩ : ∃ a ∈ CFSG.pCore p Y ⊓ R, orderOf a = p := by
    have hnt : Nontrivial (CFSG.pCore p Y) := (nontrivial_iff_ne_bot _).2 hP
    obtain ⟨n, hn, hcard⟩ :=
      (CFSG.pCore_isPGroup (p := p) (G := Y)).nontrivial_iff_card.1 hnt
    have hdvd : p ∣ Nat.card (CFSG.pCore p Y) := hcard ▸ dvd_pow_self p hn.ne'
    obtain ⟨⟨a, haP0⟩, ha⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.pCore p Y) p hdvd
    have ha' : orderOf a = p := by rw [← Subgroup.orderOf_mk a haP0, ha]
    exact ⟨a, ⟨haP0, gen49bn_mem_of_pow_eq_one h (hP0S haP0) (ha' ▸ pow_orderOf_eq_one a)⟩, ha'⟩
  have haR : a ∈ R := haΩ.2
  by_cases hΩR : CFSG.pCore p Y ⊓ R = R
  ·
    left
    have hRn : R.Normal := hΩR ▸ hΩn
    refine eq_top_iff.2 fun g _ => h.normalizer_R ?_
    rw [normalizer_eq_top_iff.2 hRn]
    exact mem_top g
  ·
    have hΩa : CFSG.pCore p Y ⊓ R = zpowers a := by
      have hdvd : Nat.card (CFSG.pCore p Y ⊓ R : Subgroup Y) ∣ p ^ 2 :=
        h.card_eq ▸ Subgroup.card_dvd_of_le inf_le_right
      have hle : Nat.card (zpowers a) ≤ Nat.card (CFSG.pCore p Y ⊓ R : Subgroup Y) :=
        Subgroup.card_le_of_le (zpowers_le.2 haΩ)
      rw [Nat.card_zpowers, haord] at hle
      obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hprime).1 hdvd
      interval_cases i
      · rw [pow_zero] at hci
        have := hprime.one_lt
        omega
      · refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 haΩ) ?_).symm
        rw [hci, Nat.card_zpowers, haord, pow_one]
      · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_right
          (by rw [h.card_eq, hci])) hΩR
    have ha1 : a ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at haord
      exact hprime.one_lt.ne haord
    have hzn : (zpowers a).Normal := hΩa ▸ hΩn
    by_cases hax : zpowers a = zpowers x
    ·
      have hxn : (zpowers x).Normal := hax ▸ hzn
      have hxord : orderOf x = p := by
        rw [← Nat.card_zpowers x, ← hax, Nat.card_zpowers, haord]
      have hKC := gen49bn_normalClosure_le hxord hxn h.sylow.isPGroup
      by_cases hKΓ : normalClosure (S : Set Y) ≤ Γ
      · left
        have hQK : (Q : Subgroup Y) ≤ normalClosure (S : Set Y) := hQ.le.trans le_normalClosure
        have hfr := Sylow.normalizer_sup_eq_top' (N := normalClosure (S : Set Y)) Q hQK
        rw [show (Q : Set Y) = (S : Set Y) by rw [← Sylow.coe_coe, hQ]] at hfr
        rw [eq_top_iff, ← hfr]
        exact sup_le h.normalizer_S hKΓ
      · exact Or.inr ⟨_, Subgroup.normalClosure_normal, hKC, hKΓ⟩
    ·
      left
      refine eq_top_iff.2 fun g _ => (h.others a haR ha1 hax).2 ?_
      rw [normalizer_eq_top_iff.2 hzn]
      exact mem_top g

end CFSG.LocalAnalysis.RankThreeTheoremC
