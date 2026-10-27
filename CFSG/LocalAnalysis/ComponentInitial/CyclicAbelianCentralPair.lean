module

public import CFSG.LocalAnalysis.ComponentInitial.LowRankFacts

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {P : Type*} [Group P]

theorem eq_of_le_cyclic_of_card_eq [Finite P] (C : Subgroup P) [IsCyclic C] {H K : Subgroup P}
    (hH : H ≤ C) (hK : K ≤ C) (hcard : Nat.card H = Nat.card K) : H = K := by
  have hH' : Nat.card (H.subgroupOf C) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv
  have hK' : Nat.card (K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv
  have h := (IsCyclic.subgroup_eq_iff_card_eq (H := H.subgroupOf C) (K := K.subgroupOf C)).2
    (by rw [hH', hK', hcard])
  rw [subgroupOf_inj, inf_of_le_left hH, inf_of_le_left hK] at h
  exact h

theorem pow_le_pow_pred_of_lt {p k m : ℕ} (hp : p.Prime) (h : p ^ k < p ^ m) :
    k + 1 ≤ m := by
  by_contra hkm
  push Not at hkm
  have : p ^ m ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
  omega

theorem cyclic_abelian_central_quotient_pair {p : ℕ} (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) (hnab : ∃ x y : P, x * y ≠ y * x)
    (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B) :
    ∃ a b : P, (QuotientGroup.mk a : P ⧸ center P) ∈ center (P ⧸ center P) ∧
      orderOf (QuotientGroup.mk a : P ⧸ center P) = p ∧
      a ^ p = b ^ p ∧ zpowers (a ^ p) = center P ∧
      zpowers a ⊓ zpowers b = center P ∧ a * b ≠ b * a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcomp, -⟩ := cyclic_abelian_center_comparison hp hP hnab hcyc
  set Z := center P with hZ
  have : Nontrivial P := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨⟨x * y, y * x, hxy⟩⟩
  have hZnt : Nontrivial Z := hP.center_nontrivial
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hP.to_subgroup Z)
  have hk1 : 1 ≤ k := by
    by_contra h0
    push Not at h0
    have : k = 0 := by omega
    rw [this, pow_zero] at hk
    exact (Finite.one_lt_card (α := Z)).ne' hk
  have hQnt : Nontrivial (P ⧸ Z) := by
    rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
    intro htop
    obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ Z := htop ▸ mem_top x
    exact hxy (mem_center_iff.1 hx y).symm
  have hQZnt : Nontrivial (center (P ⧸ Z)) := (hP.to_quotient Z).center_nontrivial
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 ((hP.to_quotient Z).to_subgroup (center (P ⧸ Z)))
  have hpdvd : p ∣ Nat.card (center (P ⧸ Z)) := by
    rw [hj]
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact absurd hj (Finite.one_lt_card (α := center (P ⧸ Z))).ne'
    · exact dvd_pow_self p (Nat.succ_ne_zero j)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center (P ⧸ Z)) p hpdvd
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (c : P ⧸ Z)
  have hmkc : (QuotientGroup.mk a : P ⧸ Z) ∈ center (P ⧸ Z) := ha ▸ c.2
  have hmko : orderOf (QuotientGroup.mk a : P ⧸ Z) = p := by
    rw [ha, Subgroup.orderOf_coe, hc]
  have haZ : a ∉ Z := by
    intro h
    have : (QuotientGroup.mk a : P ⧸ Z) = 1 := (QuotientGroup.eq_one_iff a).2 h
    rw [this, orderOf_one] at hmko
    exact hp.one_lt.ne hmko
  have hapZ : a ^ p ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmko, pow_orderOf_eq_one]
  obtain ⟨hZa, hZalt⟩ := hcomp a haZ
  obtain ⟨m, hm⟩ := hP.exists_orderOf_eq_pow a
  have hkm : k + 1 ≤ m := by
    rw [hk, hm] at hZalt
    exact pow_le_pow_pred_of_lt hp hZalt
  have hpa : p ∣ orderOf a := by
    rw [hm]
    exact dvd_pow_self p (by omega)
  have hordap : orderOf (a ^ p) = p ^ (m - 1) := by
    rw [orderOf_pow_of_dvd hp.ne_zero hpa, hm]
    have h : p ^ m = p ^ (m - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h, Nat.mul_div_cancel _ hp.pos]
  have hZdvd : Nat.card Z ∣ orderOf a := by
    rw [← Nat.card_zpowers]
    exact card_dvd_of_le hZa.le
  have hm1 : m = k + 1 := by
    have h1 : p ^ k ∣ p ^ m := by rw [← hk, ← hm]; exact hZdvd
    have h2 : Nat.card (zpowers (a ^ p)) ≤ Nat.card Z :=
      card_le_of_le ((zpowers_le).2 hapZ)
    rw [Nat.card_zpowers, hordap, hk] at h2
    have h3 : m - 1 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
    omega
  have hZap : zpowers (a ^ p) = Z := by
    refine eq_of_le_of_card_ge ((zpowers_le).2 hapZ) ?_
    rw [Nat.card_zpowers, hordap, hk, hm1, Nat.add_sub_cancel]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : P, a * b₀ ≠ b₀ * a := by
    by_contra hall
    push Not at hall
    exact haZ (mem_center_iff.2 fun g => (hall g).symm)
  have hb₀Z : b₀ ∉ Z := fun h => hb₀ (mem_center_iff.1 h a)
  obtain ⟨hZb₀, hZb₀lt⟩ := hcomp b₀ hb₀Z
  have hinf₀ : zpowers a ⊓ zpowers b₀ = Z := by
    symm
    refine eq_of_le_of_card_ge (le_inf hZa.le hZb₀.le) ?_
    have hdvd : Nat.card (zpowers a ⊓ zpowers b₀ : Subgroup P) ∣ p ^ m := by
      rw [← hm, ← Nat.card_zpowers]
      exact card_dvd_of_le inf_le_left
    obtain ⟨t, ht, ht'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hne : t ≠ m := by
      rintro rfl
      have heq : zpowers a ⊓ zpowers b₀ = zpowers a := by
        refine eq_of_le_of_card_ge inf_le_left ?_
        rw [Nat.card_zpowers, hm, ht']
      have ha' : a ∈ zpowers b₀ := (inf_le_right : zpowers a ⊓ zpowers b₀ ≤ _)
        (heq.symm ▸ mem_zpowers a)
      obtain ⟨n, rfl⟩ := ha'
      exact hb₀ (by simp only; exact (Commute.self_zpow b₀ n).symm.eq)
    rw [ht', hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨m₀, hm₀⟩ := hP.exists_orderOf_eq_pow b₀
  have hkm₀ : k + 1 ≤ m₀ := by
    rw [hk, hm₀] at hZb₀lt
    exact pow_le_pow_pred_of_lt hp hZb₀lt
  set r := m₀ - k with hr
  have hr1 : 1 ≤ r := by omega
  set c₀ := b₀ ^ (p ^ r) with hc₀
  have hdvdr : p ^ r ∣ orderOf b₀ := by
    rw [hm₀]
    exact Nat.pow_dvd_pow p (by omega)
  have hordc₀ : orderOf c₀ = p ^ k := by
    rw [hc₀, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvdr, hm₀,
      Nat.pow_div (by omega) hp.pos]
    congr 1
    omega
  have hZc₀ : zpowers c₀ = Z := by
    have : IsCyclic (zpowers b₀) := inferInstance
    refine eq_of_le_cyclic_of_card_eq (zpowers b₀) ((zpowers_le).2 (pow_mem (mem_zpowers b₀) _))
      hZb₀.le ?_
    rw [Nat.card_zpowers, hordc₀, hk]
  have hc₀Z : c₀ ∈ zpowers (a ^ p) := by
    rw [hZap, ← hZc₀]
    exact mem_zpowers c₀
  obtain ⟨u, hu⟩ := (isOfFinOrder_of_finite (a ^ p)).mem_powers_iff_mem_zpowers.2 hc₀Z
  replace hu : (a ^ p) ^ u = c₀ := hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hu
    rw [← hu, orderOf_one] at hordc₀
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hucop : Nat.Coprime u p := by
    have h1 := orderOf_pow' (a ^ p) hu0
    rw [hu, hordc₀, hordap, hm1, Nat.add_sub_cancel] at h1
    have hgcd : Nat.gcd (p ^ k) u = 1 := by
      have hpos : 0 < p ^ k := pow_pos hp.pos k
      have hdvd : Nat.gcd (p ^ k) u ∣ p ^ k := Nat.gcd_dvd_left _ _
      have := Nat.div_eq_self.1 h1.symm
      rcases this with h | h
      · omega
      · exact h
    have : Nat.Coprime p u := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpu
      have : p ∣ Nat.gcd (p ^ k) u := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpu
      rw [hgcd] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    exact this.symm
  set a' := a ^ u with ha'
  set b := b₀ ^ (p ^ (r - 1)) with hb
  have hordu : orderOf a' = orderOf a := by
    rw [ha', orderOf_pow' a hu0, hm]
    have : Nat.gcd (p ^ m) u = 1 := Nat.Coprime.pow_left m hucop.symm
    rw [this, Nat.div_one]
  have hza' : zpowers a' = zpowers a := by
    refine eq_of_le_of_card_ge ((zpowers_le).2 (pow_mem (mem_zpowers a) u)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hordu]
  have hpow : a' ^ p = b ^ p := by
    rw [ha', hb, ← pow_mul, ← pow_mul, mul_comm u p, pow_mul, hu, hc₀, ← pow_succ]
    congr 2
    omega
  have hZa'p : zpowers (a' ^ p) = Z := by
    rw [hpow, hb, ← pow_mul, ← pow_succ, show r - 1 + 1 = r by omega, ← hc₀, hZc₀]
  have hinf : zpowers a' ⊓ zpowers b = Z := by
    have hZb : Z ≤ zpowers b := by
      rw [← hZa'p, hpow]
      exact (zpowers_le).2 (pow_mem (mem_zpowers b) p)
    refine le_antisymm ?_ (le_inf (hza' ▸ hZa.le) hZb)
    rw [hza', ← hinf₀]
    exact inf_le_inf_left _ ((zpowers_le).2 (pow_mem (mem_zpowers b₀) _))
  refine ⟨a', b, ?_, ?_, hpow, hZa'p, hinf, ?_⟩
  · rw [ha', QuotientGroup.mk_pow]
    exact pow_mem hmkc u
  · rw [ha', QuotientGroup.mk_pow, orderOf_pow' _ hu0, hmko]
    have : Nat.gcd p u = 1 := hucop.symm
    rw [this, Nat.div_one]
  ·
    intro hcomm
    have hcl : IsMulCommutative (closure ({a', b} : Set P)) := by
      apply isMulCommutative_closure
      intro x hx y hy _
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hcomm
      · exact hcomm.symm
      · exact Commute.refl _
    have : IsCyclic (closure ({a', b} : Set P)) := hcyc _ hcl
    obtain ⟨t, ht⟩ := hP.exists_orderOf_eq_pow b
    have hbp : orderOf (b ^ p) = p ^ k := by
      rw [← hpow, ← Nat.card_zpowers, hZa'p, hk]
    have ht1 : 1 ≤ t := by
      by_contra h0
      push Not at h0
      have : t = 0 := by omega
      rw [this, pow_zero, orderOf_eq_one_iff] at ht
      rw [ht, one_pow, orderOf_one] at hbp
      have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    have htp : p ^ t = p ^ (t - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [orderOf_pow_of_dvd hp.ne_zero (by rw [ht]; exact dvd_pow_self p (by omega)), ht, htp,
      Nat.mul_div_cancel _ hp.pos] at hbp
    have htk : t - 1 = k := Nat.pow_right_injective hp.two_le hbp
    have hab : zpowers a' = zpowers b := by
      refine eq_of_le_cyclic_of_card_eq (closure ({a', b} : Set P))
        ((zpowers_le).2 (subset_closure (Set.mem_insert _ _)))
        ((zpowers_le).2 (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hordu, hm, hm1, ht]
      congr 1
      omega
    have hZeq : Z = zpowers a' := by
      rw [← hinf, hab, inf_idem]
    have hcard : Nat.card Z = Nat.card (zpowers a') := by rw [hZeq]
    rw [hk, Nat.card_zpowers, hordu, hm, hm1] at hcard
    have := Nat.pow_right_injective hp.two_le hcard
    omega

end CFSG.LocalAnalysis.ComponentInitial
