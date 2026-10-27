module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC

private lemma conj_zpow_eq {X : Type} [Group X] {g d : X} {u : ℤ} (hu : d * g * d⁻¹ = g ^ u)
    (e : ℤ) : d * g ^ e * d⁻¹ = g ^ (u * e) := by
  rw [← conj_zpow, hu, ← zpow_mul]

private lemma conj_pow_eq {X : Type} [Group X] {g d : X} {u : ℤ} (hu : d * g * d⁻¹ = g ^ u)
    (k : ℕ) : d * g ^ k * d⁻¹ = g ^ (u * k) := by
  rw [← conj_pow, hu, ← zpow_natCast, ← zpow_mul]

private lemma dvd_sub_one_of_conj_eq {X : Type} [Group X] {p : ℕ} (hp : p.Prime) {g d : X}
    {u : ℤ} (hu : d * g * d⁻¹ = g ^ u) {j : ℕ} (hj : d ^ (p ^ j) = 1)
    (hpn : p ∣ orderOf g) : (p : ℤ) ∣ u - 1 := by
  have key : ∀ N : ℕ, d ^ N * g * (d ^ N)⁻¹ = g ^ (u ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc d ^ (N + 1) * g * (d ^ (N + 1))⁻¹
          = d * (d ^ N * g * (d ^ N)⁻¹) * d⁻¹ := by group
        _ = d * g ^ (u ^ N) * d⁻¹ := by rw [ih]
        _ = (d * g * d⁻¹) ^ (u ^ N) := conj_zpow.symm
        _ = g ^ (u ^ (N + 1)) := by rw [hu, ← zpow_mul, pow_succ']
  have h1 : g ^ (u ^ p ^ j) = g := by
    have h := key (p ^ j)
    rw [hj, inv_one, mul_one, one_mul] at h
    exact h.symm
  have h2 : g ^ (u ^ p ^ j - 1) = 1 := by
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  have h3 : (orderOf g : ℤ) ∣ u ^ p ^ j - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  have h4 : (p : ℤ) ∣ u ^ p ^ j - 1 := (Int.natCast_dvd_natCast.mpr hpn).trans h3
  haveI := Fact.mk hp
  have h5 : (u : ZMod p) ^ p ^ j = 1 := by
    have h6 : ((u ^ p ^ j - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h4
    push_cast at h6
    exact sub_eq_zero.mp h6
  have ha0 : (u : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero j hp.ne_zero)] at h5
    exact zero_ne_one h5
  have hferm : (u : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hord1 : orderOf (u : ZMod p) ∣ p ^ j := orderOf_dvd_of_pow_eq_one h5
  have hord2 : orderOf (u : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hferm
  have hnd : ¬ p ∣ p - 1 := by
    intro h
    have := Nat.le_of_dvd (by have := hp.two_le; omega) h
    have := hp.two_le
    omega
  have hcop : Nat.Coprime (p ^ j) (p - 1) :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have hone : orderOf (u : ZMod p) = 1 := by
    have h7 : orderOf (u : ZMod p) ∣ Nat.gcd (p ^ j) (p - 1) := Nat.dvd_gcd hord1 hord2
    rw [Nat.Coprime.gcd_eq_one hcop] at h7
    exact Nat.dvd_one.mp h7
  have h8 : (u : ZMod p) = 1 := orderOf_eq_one_iff.mp hone
  have h9 : ((u - 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [h8, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h9

private lemma le_normalizer_inf_normal {X : Type} [Group X] {S L : Subgroup X} [L.Normal] :
    S ≤ normalizer ((S ⊓ L : Subgroup X) : Set X) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hh, hhL⟩
    exact ⟨S.mul_mem (S.mul_mem hd hh) (S.inv_mem hd),
      Subgroup.Normal.conj_mem ‹L.Normal› h hhL d⟩
  · rintro ⟨hh, hhL⟩
    have hS1 : d⁻¹ * (d * h * d⁻¹) * d ∈ S :=
      S.mul_mem (S.mul_mem (S.inv_mem hd) hh) hd
    have hL1 : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ ∈ L :=
      Subgroup.Normal.conj_mem ‹L.Normal› _ hhL d⁻¹
    have e1 : d⁻¹ * (d * h * d⁻¹) * d = h := by group
    have e2 : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
    rw [e1] at hS1
    rw [e2] at hL1
    exact ⟨hS1, hL1⟩

private lemma exists_pGroup_sylow_inf {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {L D : Subgroup X} [L.Normal] (hD : IsPGroup p D) :
    ∃ S : Subgroup X, IsPGroup p S ∧ D ≤ S ∧ CFSG.ABGLocalTools.IsSylowOf p (S ⊓ L) L := by
  have hLM : L ≤ L ⊔ D := le_sup_left
  have hMN : L ⊔ D ≤ normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨Q₀, hQ₀⟩ := (hD.comap_subtype (K := L ⊔ D)).exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf p ((Q₀ : Subgroup ↥(L ⊔ D)).map (L ⊔ D).subtype)
      (L ⊔ D) :=
    ⟨Q₀, rfl⟩
  refine ⟨(Q₀ : Subgroup ↥(L ⊔ D)).map (L ⊔ D).subtype, Q₀.isPGroup'.map _, ?_, ?_⟩
  · intro d hd
    have hdLD : d ∈ L ⊔ D := (le_sup_right : D ≤ L ⊔ D) hd
    have hmem : (⟨d, hdLD⟩ : ↥(L ⊔ D)) ∈ D.comap (L ⊔ D).subtype := hd
    exact Subgroup.mem_map.mpr ⟨_, hQ₀ hmem, rfl⟩
  · exact hS.inf_of_le_normalizer hLM hMN

theorem false_of_cyclic_sylow_ge_sq {X : Type} [Group X] [Finite X] {p : ℕ} {L D : Subgroup X}
    [L.Normal] (hF : ThompsonFrame p D) (hE : NormalizerExponent p D) (P₀ : Sylow p L)
    (hc : IsCyclic (P₀ : Subgroup L)) (hP : p ^ 2 ∣ Nat.card (P₀ : Subgroup L)) : False := by
  haveI : Fact p.Prime := ⟨hF.prime⟩
  have hp : p.Prime := hF.prime
  haveI : Finite (Sylow p L) :=
    Finite.of_injective (fun Q : Sylow p L => ((Q : Subgroup L) : Set L))
      (fun P Q h => Sylow.ext (SetLike.coe_injective h))
  have hDp : IsPGroup p D := IsPGroup.of_card hF.card
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elem.1.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩)
  obtain ⟨S, hSp, hDS, hSL⟩ := exists_pGroup_sylow_inf (L := L) hDp
  have hDN : D ≤ normalizer ((S ⊓ L : Subgroup X) : Set X) := hDS.trans le_normalizer_inf_normal
  obtain ⟨Q₁, hQ₁⟩ := hSL
  have hcycQ : IsCyclic (Q₁ : Subgroup L) := (Sylow.equiv P₀ Q₁).isCyclic.mp hc
  have hcardQ : Nat.card (Q₁ : Subgroup L) = Nat.card (P₀ : Subgroup L) :=
    (Nat.card_congr (Sylow.equiv P₀ Q₁).toEquiv).symm
  have hcardP : Nat.card (S ⊓ L : Subgroup X) = Nat.card (P₀ : Subgroup L) := by
    rw [← hQ₁, ← hcardQ]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (Q₁ : Subgroup L) L.subtype L.subtype_injective).toEquiv).symm
  have hcycP : IsCyclic (S ⊓ L : Subgroup X) := by
    rw [← hQ₁]
    exact (Subgroup.equivMapOfInjective (Q₁ : Subgroup L) L.subtype L.subtype_injective).isCyclic.mp
      hcycQ
  obtain ⟨g, hgP, hgen, hord⟩ : ∃ g : X, g ∈ (S ⊓ L : Subgroup X) ∧
      (∀ x ∈ (S ⊓ L : Subgroup X), ∃ k : ℤ, g ^ k = x) ∧
      orderOf g = Nat.card (S ⊓ L : Subgroup X) := by
    haveI := hcycP
    obtain ⟨g₁, hg₁⟩ := IsCyclic.exists_generator (α := (S ⊓ L : Subgroup X))
    refine ⟨(g₁ : X), g₁.2, fun x hx => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ ⟨x, hx⟩)
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.orderOf_coe]
      exact orderOf_eq_card_of_forall_mem_zpowers hg₁
  have hpn2 : p ^ 2 ∣ orderOf g := by
    rw [hord, hcardP]
    exact hP
  obtain ⟨m, hm⟩ := hpn2
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have := orderOf_pos g
      rw [hm, h, mul_zero] at this
      exact absurd this (lt_irrefl 0)
    · exact h
  have hpn : p ∣ orderOf g := (dvd_pow_self p two_ne_zero).trans ⟨m, hm⟩
  have hgn : ∀ k : ℤ, g ^ (k * (orderOf g : ℤ)) = 1 := fun k =>
    orderOf_dvd_iff_zpow_eq_one.mp (dvd_mul_left _ _)
  have hN : (orderOf g : ℤ) = (p : ℤ) ^ 2 * m := by
    rw [hm]
    push_cast
    ring
  have hact : ∀ d ∈ D, ∃ t : ℤ, d * g * d⁻¹ = g ^ (1 + (p : ℤ) * t) := by
    intro d hd
    have hmem : d * g * d⁻¹ ∈ (S ⊓ L : Subgroup X) :=
      (Subgroup.mem_normalizer_iff.mp (hDN hd) g).mp hgP
    obtain ⟨u, hu⟩ := hgen _ hmem
    obtain ⟨j, hj⟩ := hDp ⟨d, hd⟩
    have hj' : d ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
    obtain ⟨c, hc'⟩ := dvd_sub_one_of_conj_eq hp hu.symm hj' hpn
    refine ⟨c, ?_⟩
    rw [← hu]
    congr 1
    linarith
  have hzconj : ∀ d ∈ D, d * g ^ (p * m) * d⁻¹ = g ^ (p * m) := by
    intro d hd
    obtain ⟨t, ht⟩ := hact d hd
    rw [conj_pow_eq ht]
    have e : (1 + (p : ℤ) * t) * ((p * m : ℕ) : ℤ) =
        ((p * m : ℕ) : ℤ) + t * (orderOf g : ℤ) := by
      rw [hN]
      push_cast
      ring
    rw [e, zpow_add, hgn t, mul_one, zpow_natCast]
  have hzS : g ^ (p * m) ∈ S := (Subgroup.mem_inf.mp (Subgroup.pow_mem _ hgP (p * m))).1
  have hzD : g ^ (p * m) ∈ D := by
    have hzc : g ^ (p * m) ∈ centralizer (D : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact mul_inv_eq_iff_eq_mul.mp (hzconj h hh)
    have hDc : D ≤ centralizer (D : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm h hh x hx
    have hQ : D ⊔ Subgroup.zpowers (g ^ (p * m)) ≤ centralizer (D : Set X) :=
      sup_le hDc (Subgroup.zpowers_le.mpr hzc)
    have hQS : D ⊔ Subgroup.zpowers (g ^ (p * m)) ≤ S :=
      sup_le hDS (Subgroup.zpowers_le.mpr hzS)
    have hDQ := hF.sylow.eq_of_le le_sup_left hQ (hSp.to_le hQS)
    have hmem : g ^ (p * m) ∈ D ⊔ Subgroup.zpowers (g ^ (p * m)) :=
      (le_sup_right : Subgroup.zpowers (g ^ (p * m)) ≤ D ⊔ Subgroup.zpowers (g ^ (p * m)))
        (Subgroup.mem_zpowers _)
    rw [hDQ] at hmem
    exact hmem
  have hzpowD : ∀ k : ℤ, g ^ (((p * m : ℕ) : ℤ) * k) ∈ D := fun k => by
    rw [zpow_mul, zpow_natCast]
    exact D.zpow_mem hzD k
  have hcommE : ∀ d ∈ D, ∃ t : ℤ, ∀ e : ℤ,
      d * g ^ ((m : ℤ) * e) * d⁻¹ = g ^ ((m : ℤ) * e) * g ^ (((p * m : ℕ) : ℤ) * (t * e)) := by
    intro d hd
    obtain ⟨t, ht⟩ := hact d hd
    refine ⟨t, fun e => ?_⟩
    rw [conj_zpow_eq ht, ← zpow_add]
    congr 1
    push_cast
    ring
  have hA : ∀ d ∈ D, ∀ e : ℤ, (g ^ ((m : ℤ) * e))⁻¹ * d * g ^ ((m : ℤ) * e) ∈ D := by
    intro d hd e
    obtain ⟨t, ht⟩ := hcommE d hd
    have h1 : (g ^ ((m : ℤ) * e))⁻¹ * d * g ^ ((m : ℤ) * e) =
        g ^ (((p * m : ℕ) : ℤ) * (t * e)) * d := by
      calc (g ^ ((m : ℤ) * e))⁻¹ * d * g ^ ((m : ℤ) * e)
          = (g ^ ((m : ℤ) * e))⁻¹ * (d * g ^ ((m : ℤ) * e) * d⁻¹) * d := by group
        _ = (g ^ ((m : ℤ) * e))⁻¹ *
              (g ^ ((m : ℤ) * e) * g ^ (((p * m : ℕ) : ℤ) * (t * e))) * d := by
          rw [ht e]
        _ = g ^ (((p * m : ℕ) : ℤ) * (t * e)) * d := by group
    rw [h1]
    exact D.mul_mem (hzpowD _) hd
  have hyN : g ^ m ∈ normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 : g ^ ((m : ℤ) * -1) = (g ^ m)⁻¹ := by
      rw [mul_neg_one, zpow_neg, zpow_natCast]
    have e2 : g ^ ((m : ℤ) * 1) = g ^ m := by
      rw [mul_one, zpow_natCast]
    constructor
    · intro hh
      have := hA h hh (-1)
      rw [e1, inv_inv] at this
      exact this
    · intro hh
      have := hA (g ^ m * h * (g ^ m)⁻¹) hh 1
      rw [e2] at this
      have e3 : (g ^ m)⁻¹ * (g ^ m * h * (g ^ m)⁻¹) * g ^ m = h := by group
      rw [e3] at this
      exact this
  have hy2 : (g ^ m) ^ (p ^ 2) = 1 := by
    rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have hEy : (g ^ m) ^ p = 1 := hE (g ^ m) hyN ⟨2, hy2⟩
  have hne : (g ^ m) ^ p ≠ 1 := by
    rw [← pow_mul]
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.mul_pos hm0 hp.pos).ne'
    · rw [hm]
      nlinarith [hp.two_le, Nat.mul_pos hm0 hp.pos]
  exact hne hEy

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
