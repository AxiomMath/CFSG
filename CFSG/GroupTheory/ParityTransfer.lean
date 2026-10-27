module

public import CFSG.GroupTheory.ThompsonTransferCount

public section

namespace CFSG.ParityTransfer

open MulAction Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.ThompsonTransferCount
  CFSG.ThompsonIndexTwo

variable {G : Type*} [Group G] [Finite G]

section Helpers

private theorem conj_mem_iff_of_mem_normal {T U : Subgroup G}
    (hUN : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U) {t : G} (ht : t ∈ T) (w : G) :
    t⁻¹ * w * t ∈ U ↔ w ∈ U := by
  constructor
  · intro h
    have h2 := hUN t ht (t⁻¹ * w * t) h
    simpa [mul_assoc] using h2
  · intro h
    have h2 := hUN t⁻¹ (T.inv_mem ht) w h
    simpa using h2

private theorem mem_normalizer_of_commutes {Y : Subgroup G} {d : G}
    (hd : ∀ y ∈ Y, d * y = y * d) : d ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [show d * y * d⁻¹ = y by rw [hd y hy]; group]
    exact hy
  · intro hdy
    have hdz : d⁻¹ * (d * y * d⁻¹) = (d * y * d⁻¹) * d⁻¹ := by
      have h := hd (d * y * d⁻¹) hdy
      have hdyz : d * y = d * (d * y * d⁻¹) := by
        calc d * y = (d * y * d⁻¹) * d := by group
          _ = d * (d * y * d⁻¹) := h.symm
      calc d⁻¹ * (d * y * d⁻¹) = d⁻¹ * (d * y) * d⁻¹ := by group
        _ = d⁻¹ * (d * (d * y * d⁻¹)) * d⁻¹ := by rw [← hdyz]
        _ = (d * y * d⁻¹) * d⁻¹ := by group
    have hy : y = d * y * d⁻¹ := by
      calc y = d⁻¹ * (d * y * d⁻¹) * d := by group
        _ = ((d * y * d⁻¹) * d⁻¹) * d := by rw [hdz]
        _ = d * y * d⁻¹ := by group
    rwa [hy]

private theorem mem_conj_mem_U_smul_iff {T U : Subgroup G}
    (hUN : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U) {x d : G} (hd : d * x = x * d)
    (y : G ⧸ T) :
    ((d • y).out⁻¹ * x * (d • y).out ∈ U) ↔ (y.out⁻¹ * x * y.out ∈ U) := by
  have hdt : (d * y.out)⁻¹ * (d • y).out ∈ T := by
    refine QuotientGroup.eq.mp ?_
    have h1 : ((d * y.out : G) : G ⧸ T) = d • y := by
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rfl
    exact h1.trans (QuotientGroup.out_eq' (d • y)).symm
  set t : G := (d * y.out)⁻¹ * (d • y).out with ht
  have hout : (d • y).out = d * y.out * t := by
    rw [ht]
    group
  have hmain : (d • y).out⁻¹ * x * (d • y).out =
      t⁻¹ * (y.out⁻¹ * x * y.out) * t := by
    rw [hout]
    have hdx : d⁻¹ * x * d = x := by
      calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
        _ = d⁻¹ * (d * x) := by rw [← hd]
        _ = x := by group
    calc (d * y.out * t)⁻¹ * x * (d * y.out * t)
        = t⁻¹ * ((d * y.out)⁻¹ * x * (d * y.out)) * t := by group
      _ = t⁻¹ * (y.out⁻¹ * x * y.out) * t := by
        rw [show (d * y.out)⁻¹ * x * (d * y.out) =
          y.out⁻¹ * (d⁻¹ * x * d) * y.out by group, hdx]
  rw [hmain]
  exact conj_mem_iff_of_mem_normal hUN hdt _

private theorem mem_fixedPoints_zpowers_iff_period_eq_one {T : Subgroup G} (x : G) (y : G ⧸ T) :
    y ∈ fixedPoints (zpowers x) (G ⧸ T) ↔ Function.minimalPeriod (x • ·) y = 1 := by
  constructor
  · intro h
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
    exact h ⟨x, Subgroup.mem_zpowers x⟩
  · intro h
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at h
    intro g
    exact smul_eq_self_of_mem_zpowers g.2 h

end Helpers

theorem exists_normal_index_two_not_mem_of_parity {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2)
    {z x : G} (hzT : z ∈ T) (hzc : ∀ t ∈ T, t * z = z * t)
    (hxT : x ∈ T) (hxU : x ∉ U) (hx4 : x ^ 4 = 1)
    (hsq : ∀ g : G, g⁻¹ * x ^ 2 * g ∈ T → g⁻¹ * x ^ 2 * g ∈ U)
    (hout : ∀ g : G, g * z = z * g → g⁻¹ * x * g ∉ U)
    {Y : Subgroup G} (hYx : Y ≤ Subgroup.centralizer {x}) (hY : IsPGroup 2 Y)
    (hYmax : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {x} → IsPGroup 2 P → Y ≤ P → P = Y)
    (hR : ∀ a ∈ Y, (∀ y ∈ Y, a * y = y * a) → ∀ g : G, g⁻¹ * z * g = a → a = z) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ x ∉ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hUN : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hUNconj : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U := by
    intro t ht u hu
    exact Subgroup.mem_subgroupOf.mp
      (hUN.conj_mem ⟨u, hUT hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨t, ht⟩)
  have hQcard : Nat.card (Qbar T U) = 2 := hUidx
  haveI : IsCyclic (Qbar T U) := isCyclic_of_prime_card hQcard
  letI : CommGroup (Qbar T U) := IsCyclic.commGroup
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  set g₀ : Qbar T U := phiQ T U ⟨x, hxT⟩ with hg₀
  have hg₀1 : g₀ ≠ 1 := fun h => hxU ((phiQ_eq_one_iff T U _).mp h)
  have hg₀2 : g₀ ^ 2 = 1 := by
    rw [← hQcard]
    exact pow_card_eq_one'
  have hval : ∀ w : ↥T, phiQ T U w = if (w : G) ∈ U then 1 else g₀ := by
    intro w
    split_ifs with hw
    · exact (phiQ_eq_one_iff T U w).mpr hw
    · have h1 : (((⟨x, hxT⟩ : ↥T)⁻¹ * w : ↥T) : G) ∈ U := by
        simpa using inv_mul_mem_of_not_mem hUidx hxT w.2 hxU hw
      have h2 := (phiQ_eq_one_iff T U _).mpr h1
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
  set mp : G ⧸ T → ℕ := fun y => Function.minimalPeriod (x • ·) y with hmp
  set outer : orbitRel.Quotient (zpowers x) (G ⧸ T) → Prop :=
    fun q => mp q.out = 1 ∧ q.out.out⁻¹ * x * q.out.out ∉ U with houter
  set inner : orbitRel.Quotient (zpowers x) (G ⧸ T) → Prop :=
    fun q => mp q.out = 1 ∧ q.out.out⁻¹ * x * q.out.out ∈ U with hinner
  have hfac : ∀ q : orbitRel.Quotient (zpowers x) (G ⧸ T),
      phiQ T U ⟨q.out.out⁻¹ * x ^ mp q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem T x q.out⟩ =
      (if outer q then g₀ else 1) := by
    intro q
    have hmpdvd : mp q.out ∣ 4 := by
      have h1 : Function.minimalPeriod (x • ·) q.out ∣ 4 :=
        (pow_smul_eq_iff_dvd x q.out 4).mp (by rw [hx4, one_smul])
      simpa [hmp] using h1
    have hmpdvd' : mp q.out ∣ 2 ^ 2 := by
      have h22 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rwa [h22]
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hmpdvd'
    have hj012 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj012 with rfl | rfl | rfl
    · have hmp1 : mp q.out = 1 := by simpa using hj
      rw [hval]
      by_cases hU : q.out.out⁻¹ * x * q.out.out ∈ U
      · have hwU : q.out.out⁻¹ * x ^ mp q.out * q.out.out ∈ U := by
          rwa [hmp1, pow_one]
        rw [if_pos hwU]
        simp [houter, hmp1, hU]
      · have hwU : q.out.out⁻¹ * x ^ mp q.out * q.out.out ∉ U := by
          rwa [hmp1, pow_one]
        rw [if_neg hwU]
        simp [houter, hmp1, hU]
    · have hmp2 : mp q.out = 2 := by simpa using hj
      have hwT : q.out.out⁻¹ * x ^ mp q.out * q.out.out ∈ T :=
        QuotientGroup.out_conj_pow_minimalPeriod_mem T x q.out
      have hw2T : q.out.out⁻¹ * x ^ 2 * q.out.out ∈ T := by
        rwa [hmp2] at hwT
      have hw2U : q.out.out⁻¹ * x ^ 2 * q.out.out ∈ U := hsq _ hw2T
      have hwU : q.out.out⁻¹ * x ^ mp q.out * q.out.out ∈ U := by
        rwa [hmp2]
      rw [hval, if_pos hwU]
      simp [houter, hmp2]
    · have hmp4 : mp q.out = 4 := by simpa using hj
      have hwU : q.out.out⁻¹ * x ^ mp q.out * q.out.out ∈ U := by
        have hw1 : q.out.out⁻¹ * x ^ mp q.out * q.out.out = 1 := by
          rw [hmp4, hx4]
          group
        rw [hw1]
        exact U.one_mem
      rw [hval, if_pos hwU]
      simp [houter, hmp4]
  have hτ : MonoidHom.transfer (phiQ T U) x = g₀ ^ (Finset.univ.filter outer).card := by
    rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    have hprod : (∏ q : orbitRel.Quotient (zpowers x) (G ⧸ T),
        phiQ T U ⟨q.out.out⁻¹ * x ^ Function.minimalPeriod (x • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem T x q.out⟩) =
        ∏ q, (if outer q then g₀ else 1) :=
      Finset.prod_congr rfl fun q _ => by simpa [hmp] using hfac q
    rw [hprod, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hfixed_of_memU : ∀ y : G ⧸ T, y.out⁻¹ * x * y.out ∈ U →
      Function.minimalPeriod (x • ·) y = 1 := by
    intro y hy
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
    exact (smul_eq_iff x y).mpr (hUT hy)
  have hiffFix : ∀ y : G ⧸ T,
      y ∈ fixedPoints (zpowers x) (G ⧸ T) ↔ Function.minimalPeriod (x • ·) y = 1 :=
    fun y => mem_fixedPoints_zpowers_iff_period_eq_one x y
  have hfixcard : Nat.card (fixedPoints (zpowers x) (G ⧸ T)) =
      (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
        mp q.out = 1)).card := by
    have hinvF : ∀ (h : zpowers x) (y : G ⧸ T),
        h • y ∈ fixedPoints (zpowers x) (G ⧸ T) ↔ y ∈ fixedPoints (zpowers x) (G ⧸ T) := by
      intro h y
      constructor
      · intro hy
        have h1 : h⁻¹ • (h • y) = h • y := mem_fixedPoints.mp hy h⁻¹
        rw [inv_smul_smul] at h1
        rw [h1]
        exact hy
      · intro hy
        rw [mem_fixedPoints.mp hy h]
        exact hy
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
        card_filter_eq_sum_orbit (H := zpowers x)
          (fun y => y ∈ fixedPoints (zpowers x) (G ⧸ T)) hinvF,
        Finset.card_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hiff := hiffFix q.out
    by_cases hq : q.out ∈ fixedPoints (zpowers x) (G ⧸ T)
    · rw [if_pos hq, if_pos (hiff.mp hq), Nat.card_eq_fintype_card,
        (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mp hq]
    · rw [if_neg hq, if_neg (fun h => hq (hiff.mpr h))]
  have hfixodd : Odd (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
      mp q.out = 1)).card := by
    rw [← hfixcard]
    have hzp : IsPGroup 2 (zpowers x) := hT.to_le (Subgroup.zpowers_le.mpr hxT)
    have hmod := hzp.card_modEq_card_fixedPoints (G ⧸ T)
    rw [Nat.odd_iff]
    rw [show Nat.card (fixedPoints (zpowers x) (G ⧸ T)) % 2 = Nat.card (G ⧸ T) % 2
      from hmod.symm]
    rw [← Subgroup.index_eq_card]
    exact Nat.two_dvd_ne_zero.mp hTidx
  have hx2p : IsPGroup 2 (Subgroup.zpowers x) := hT.to_le (Subgroup.zpowers_le.mpr hxT)
  have hxnormY : x ∈ Subgroup.normalizer (Y : Set G) :=
    mem_normalizer_of_commutes
      (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hYx hy)).symm)
  have hzpnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr hxnormY
  have hPle : Y ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {x} := by
    refine sup_le hYx (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hP2 : IsPGroup 2 ↥(Y ⊔ Subgroup.zpowers x) :=
    IsPGroup.to_sup_of_normal_left' (H := Y) (K := Subgroup.zpowers x) hY hx2p hzpnorm
  have hxY : x ∈ Y := by
    have heq := hYmax (Y ⊔ Subgroup.zpowers x) hPle hP2 le_sup_left
    have hxsup : x ∈ Y ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    simpa [heq] using hxsup
  have hnoAfix : ∀ y : G ⧸ T, y.out⁻¹ * x * y.out ∈ U →
      y ∉ fixedPoints Y (G ⧸ T) := by
    intro y hyA hyfix
    set a : G := y.out with ha
    have hconjYT : ∀ h : Y, a⁻¹ * (h : G) * a ∈ T := by
      intro h
      have hsm : (h : G) • y = y := mem_fixedPoints.mp hyfix h
      exact (smul_eq_iff (h : G) y).mp hsm
    set c : G := a * z * a⁻¹ with hc
    have hcCentral : ∀ h ∈ Y, c * h = h * c := by
      intro h hh
      have hconj : a⁻¹ * h * a ∈ T := hconjYT ⟨h, hh⟩
      have hzc : z * (a⁻¹ * h * a) = (a⁻¹ * h * a) * z := (hzc _ hconj).symm
      calc c * h = a * z * a⁻¹ * h := rfl
        _ = a * (z * (a⁻¹ * h * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * h * a) * z) * a⁻¹ := by rw [hzc]
        _ = h * (a * z * a⁻¹) := by group
        _ = h * c := rfl
    have hcCx : c ∈ Subgroup.centralizer {x} :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcCentral x hxY)
    have hc2p : IsPGroup 2 (Subgroup.zpowers c) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT ⟨z, hzT⟩
      refine IsPGroup.iff_card.mpr ⟨n, ?_⟩
      have hzord : orderOf z = 2 ^ n := (Subgroup.orderOf_coe (⟨z, hzT⟩ : T)).trans hn
      have hcorder : orderOf c = orderOf z := by
        rw [hc, ← MulAut.conj_apply]
        exact MulEquiv.orderOf_eq (MulAut.conj a) z
      rw [Nat.card_zpowers, hcorder, hzord]
    have hcnorm : c ∈ Subgroup.normalizer (Y : Set G) :=
      mem_normalizer_of_commutes hcCentral
    have hPle' : Y ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer {x} :=
      sup_le hYx (Subgroup.zpowers_le.mpr hcCx)
    have hP2' : IsPGroup 2 ↥(Y ⊔ Subgroup.zpowers c) :=
      IsPGroup.to_sup_of_normal_left' (H := Y) (K := Subgroup.zpowers c) hY hc2p
        (Subgroup.zpowers_le.mpr hcnorm)
    have hcY : c ∈ Y := by
      have heq := hYmax (Y ⊔ Subgroup.zpowers c) hPle' hP2' le_sup_left
      have hcsup : c ∈ Y ⊔ Subgroup.zpowers c :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      simpa [heq] using hcsup
    have hcE : c = z := by
      refine hR c hcY hcCentral (a⁻¹) ?_
      rw [inv_inv]
    have hcz : a * z * a⁻¹ = z := by
      rw [← hc, hcE]
    have haz : a * z = z * a := by
      calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [hcz]
    exact hout a haz (by simpa [ha] using hyA)
  have hYA : ∀ (h : Y) (y : G ⧸ T),
      (h • y).out⁻¹ * x * (h • y).out ∈ U ↔ y.out⁻¹ * x * y.out ∈ U := by
    intro h y
    exact mem_conj_mem_U_smul_iff hUNconj
      (Subgroup.mem_centralizer_singleton_iff.mp (hYx h.2)) y
  have hAeven : 2 ∣ (Finset.univ.filter (fun y : G ⧸ T =>
      y.out⁻¹ * x * y.out ∈ U)).card := by
    rw [card_filter_eq_sum_orbit (H := Y)
      (R := fun y : G ⧸ T => y.out⁻¹ * x * y.out ∈ U) hYA]
    refine Finset.dvd_sum fun q _ => ?_
    split_ifs with hq
    · obtain ⟨n, hn⟩ := IsPGroup.card_orbit hY q.out
      rw [hn]
      refine dvd_pow_self 2 ?_
      intro hn0
      exact hnoAfix q.out hq
        ((MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mpr
          (by rw [← Nat.card_eq_fintype_card, hn, hn0, pow_zero]))
    · exact dvd_zero 2
  have hAcardPoints : Nat.card ↥{y : G ⧸ T | y.out⁻¹ * x * y.out ∈ U} =
      (Finset.univ.filter (fun y : G ⧸ T => y.out⁻¹ * x * y.out ∈ U)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Set.mem_setOf_eq]
  have hAeven' : 2 ∣ Nat.card ↥{y : G ⧸ T | y.out⁻¹ * x * y.out ∈ U} := by
    rwa [hAcardPoints]
  have hAcard : Nat.card ↥{y : G ⧸ T | y.out⁻¹ * x * y.out ∈ U} =
      (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
        q.out.out⁻¹ * x * q.out.out ∈ U)).card := by
    have hinvA : ∀ (h : zpowers x) (y : G ⧸ T),
        (h • y).out⁻¹ * x * (h • y).out ∈ U ↔ y.out⁻¹ * x * y.out ∈ U := by
      intro h y
      exact mem_conj_mem_U_smul_iff hUNconj (by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
        rw [← hk]
        exact ((Commute.refl x).zpow_left k).eq) y
    have hsum : (Finset.univ.filter (fun y : G ⧸ T => y.out⁻¹ * x * y.out ∈ U)).card =
        ∑ q : orbitRel.Quotient (zpowers x) (G ⧸ T),
          if q.out.out⁻¹ * x * q.out.out ∈ U then
            Nat.card (orbit (zpowers x) q.out) else 0 :=
      card_filter_eq_sum_orbit (H := zpowers x)
        (R := fun y : G ⧸ T => y.out⁻¹ * x * y.out ∈ U) hinvA
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    change (Finset.univ.filter (fun y : G ⧸ T => y.out⁻¹ * x * y.out ∈ U)).card = _
    rw [hsum, Finset.card_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.out.out⁻¹ * x * q.out.out ∈ U
    · rw [if_pos hq]
      have hfix : q.out ∈ fixedPoints (zpowers x) (G ⧸ T) :=
        (hiffFix q.out).mpr (hfixed_of_memU q.out hq)
      rw [Nat.card_eq_fintype_card, (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mp hfix,
        if_pos hq]
    · rw [if_neg hq, if_neg hq]
  have hInnerEq : (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
        q.out.out⁻¹ * x * q.out.out ∈ U)) = Finset.univ.filter inner := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinner]
    constructor
    · intro hq
      exact ⟨hfixed_of_memU q.out hq, hq⟩
    · exact fun h => h.2
  have hOuterOdd : Odd (Finset.univ.filter outer).card := by
    have hInnerEven : Even (Finset.univ.filter inner).card := by
      rw [even_iff_two_dvd, ← hInnerEq, ← hAcard]
      exact hAeven'
    have hunion : (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
          mp q.out = 1)) = Finset.univ.filter inner ∪ Finset.univ.filter outer := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hinner, houter]
      constructor
      · intro hq
        by_cases hU : q.out.out⁻¹ * x * q.out.out ∈ U
        · exact Or.inl ⟨hq, hU⟩
        · exact Or.inr ⟨hq, hU⟩
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    have hdisj : Disjoint (Finset.univ.filter inner) (Finset.univ.filter outer) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinner, houter] at hq1 hq2
      exact hq2.2 hq1.2
    have hparts : (Finset.univ.filter (fun q : orbitRel.Quotient (zpowers x) (G ⧸ T) =>
          mp q.out = 1)).card =
        (Finset.univ.filter inner).card + (Finset.univ.filter outer).card := by
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hFixOddSum : Odd ((Finset.univ.filter inner).card +
        (Finset.univ.filter outer).card) := by
      rwa [← hparts]
    by_contra h
    have hOuterEven : Even (Finset.univ.filter outer).card := Nat.not_odd_iff_even.mp h
    exact (Nat.not_even_iff_odd.mpr hFixOddSum) (hInnerEven.add hOuterEven)
  have hτ1 : MonoidHom.transfer (phiQ T U) x ≠ 1 := by
    rw [hτ]
    obtain ⟨M, hM⟩ := hOuterOdd
    rw [hM, pow_succ, pow_mul, hg₀2, one_pow, one_mul]
    exact hg₀1
  set τ : G →* Qbar T U := MonoidHom.transfer (phiQ T U) with hτdef
  refine ⟨τ.ker, τ.normal_ker, ?_, ?_⟩
  · rw [Subgroup.index_ker]
    have hdvd : Nat.card τ.range ∣ 2 := hQcard ▸ Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card τ.range ≠ 1 := by
      rw [Ne, Subgroup.card_eq_one]
      intro h
      have hx : τ x ∈ τ.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at hx
      exact hτ1 hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  · intro hxN
    exact hτ1 (MonoidHom.mem_ker.mp hxN)

theorem eq_of_le_of_center_rigid {z x : G} {Y : Subgroup G}
    (hYzx : Y ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer {x}) (hY : IsPGroup 2 Y)
    (hYmax : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 P → Y ≤ P → P = Y)
    (hzY : z ∈ Y)
    (hR : ∀ a ∈ Y, (∀ y ∈ Y, a * y = y * a) → ∀ g : G, g⁻¹ * z * g = a → a = z) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer {x} → IsPGroup 2 P → Y ≤ P → P = Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hPleC hP2 hYP
  by_contra hPne
  have hYPne : Y.subgroupOf P ≠ ⊤ := by
    intro htop
    apply hPne
    refine le_antisymm ?_ hYP
    intro p hp
    have hp' : (⟨p, hp⟩ : P) ∈ Y.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hp'
  have hYPproper : Y.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr hYPne
  haveI : Group.IsNilpotent P := hP2.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hltN : Y.subgroupOf P < Subgroup.normalizer (Y.subgroupOf P : Set P) :=
    hnc _ hYPproper
  obtain ⟨n, hnN, hnYP⟩ := SetLike.exists_of_lt hltN
  have hnNormY : (n : G) ∈ Subgroup.normalizer (Y : Set G) := by
    have hnsub : n ∈ (Subgroup.normalizer (Y : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hYP]
      exact hnN
    exact Subgroup.mem_subgroupOf.mp hnsub
  have hnNY : (n : G) ∉ Y := fun h => hnYP (Subgroup.mem_subgroupOf.mpr h)
  have hnP : (n : G) ∈ P := n.2
  have hnCx : (n : G) ∈ Subgroup.centralizer {x} := hPleC n.2
  have hnconjY : ∀ y ∈ Y, (n : G) * y * (n : G)⁻¹ ∈ Y := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hnNormY y).mp hy
  have hnconjYinv : ∀ y ∈ Y, (n : G)⁻¹ * y * (n : G) ∈ Y := by
    intro y hy
    refine (Subgroup.mem_normalizer_iff.mp hnNormY ((n : G)⁻¹ * y * (n : G))).mpr ?_
    rw [show (n : G) * ((n : G)⁻¹ * y * (n : G)) * (n : G)⁻¹ = y by group]
    exact hy
  have hzYcenter : ∀ y ∈ Y, z * y = y * z := by
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hYzx hy).1).symm
  set a : G := (n : G) * z * (n : G)⁻¹ with ha
  have haY : a ∈ Y := hnconjY z hzY
  have haCent : ∀ y ∈ Y, a * y = y * a := by
    intro y hy
    have hzy : z * ((n : G)⁻¹ * y * (n : G)) = ((n : G)⁻¹ * y * (n : G)) * z :=
      hzYcenter _ (hnconjYinv y hy)
    calc a * y = (n : G) * z * (n : G)⁻¹ * y := rfl
      _ = (n : G) * (z * ((n : G)⁻¹ * y * (n : G))) * (n : G)⁻¹ := by group
      _ = (n : G) * (((n : G)⁻¹ * y * (n : G)) * z) * (n : G)⁻¹ := by rw [hzy]
      _ = y * ((n : G) * z * (n : G)⁻¹) := by group
      _ = y * a := rfl
  have haeq : a = z := by
    refine hR a haY haCent (n : G)⁻¹ ?_
    rw [inv_inv]
  have hnz : (n : G) * z = z * (n : G) := by
    have hc : (n : G) * z * (n : G)⁻¹ = z := by rw [← ha, haeq]
    calc (n : G) * z = ((n : G) * z * (n : G)⁻¹) * (n : G) := by group
      _ = z * (n : G) := by rw [hc]
  have hnCz : (n : G) ∈ Subgroup.centralizer {z} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hnz
  have hn2p : IsPGroup 2 (Subgroup.zpowers (n : G)) :=
    hP2.to_le (Subgroup.zpowers_le.mpr hnP)
  have hP2' : IsPGroup 2 ↥(Y ⊔ Subgroup.zpowers (n : G)) :=
    IsPGroup.to_sup_of_normal_left' (H := Y) (K := Subgroup.zpowers (n : G)) hY hn2p
      (Subgroup.zpowers_le.mpr hnNormY)
  have hPle' : Y ⊔ Subgroup.zpowers (n : G) ≤
      Subgroup.centralizer {z} ⊓ Subgroup.centralizer {x} := by
    refine sup_le hYzx ?_
    exact le_inf (Subgroup.zpowers_le.mpr hnCz) (Subgroup.zpowers_le.mpr hnCx)
  have heq := hYmax (Y ⊔ Subgroup.zpowers (n : G)) hPle' hP2' le_sup_left
  have hnY : (n : G) ∈ Y := by
    have hnsup : (n : G) ∈ Y ⊔ Subgroup.zpowers (n : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (n : G))
    simpa [heq] using hnsup
  exact hnNY hnY

theorem exists_normal_index_two_not_mem_of_parity' {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2)
    {z x : G} (hzT : z ∈ T) (hzc : ∀ t ∈ T, t * z = z * t)
    (hxT : x ∈ T) (hxU : x ∉ U) (hx4 : x ^ 4 = 1)
    (hsq : ∀ g : G, g⁻¹ * x ^ 2 * g ∈ T → g⁻¹ * x ^ 2 * g ∈ U)
    (hout : ∀ g : G, g * z = z * g → g⁻¹ * x * g ∉ U)
    {Y : Subgroup G} (hYzx : Y ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer {x})
    (hY : IsPGroup 2 Y)
    (hYmax : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 P → Y ≤ P → P = Y)
    (hzY : z ∈ Y)
    (hR : ∀ a ∈ Y, (∀ y ∈ Y, a * y = y * a) → ∀ g : G, g⁻¹ * z * g = a → a = z) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ x ∉ N := by
  exact exists_normal_index_two_not_mem_of_parity hT hTidx hUT hUidx hzT hzc hxT hxU hx4
    hsq hout (hYzx.trans inf_le_right) hY
    (eq_of_le_of_center_rigid hYzx hY hYmax hzY hR) hR

end CFSG.ParityTransfer
