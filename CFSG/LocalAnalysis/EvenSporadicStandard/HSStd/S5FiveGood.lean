module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {K : Type*} [Group K]

theorem normal_zpowers_of_mem_center {r : K} (hr : r ∈ center K) : (zpowers r).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  have : g * r ^ k * g⁻¹ = r ^ k := by
    rw [(Commute.zpow_right (show Commute g r from (mem_center_iff.1 hr g)) k).eq]
    simp
  rw [this]
  exact zpow_mem_zpowers _ _

theorem odd_card_oddCore' [Finite K] : Odd (Nat.card (CFSG.oddCore K)) := by
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem le_oddCore_of_normal' {N : Subgroup K} [N.Normal] (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.oddCore K :=
  le_sSup ⟨inferInstance, hodd⟩

section Quot

variable {x : K}

theorem quot_mem_centralizer (c : ↥(centralizer ({x} : Set K))) :
    QuotientGroup.mk' (CFSG.oddCore K) c.1 ∈
      centralizer ({QuotientGroup.mk' (CFSG.oddCore K) x} : Set (K ⧸ CFSG.oddCore K)) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact congrArg _ (mem_centralizer_singleton_iff.1 c.2)

@[expose] noncomputable def quotHom (x : K) :
    ↥(centralizer ({x} : Set K)) →*
      ↥(centralizer ({QuotientGroup.mk' (CFSG.oddCore K) x} : Set (K ⧸ CFSG.oddCore K))) :=
  ((QuotientGroup.mk' (CFSG.oddCore K)).comp (centralizer ({x} : Set K)).subtype).codRestrict _
    quot_mem_centralizer

theorem quotHom_surjective [Finite K] (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    Function.Surjective (quotHom x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNp : ¬ 2 ∣ Nat.card (CFSG.oddCore K) := fun h =>
    (Nat.not_even_iff_odd.2 odd_card_oddCore') (even_iff_two_dvd.2 h)
  have hQp : IsPGroup 2 (zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1]
    simp
  have hlift := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hNp hQp
  intro y
  have hy : (y : K ⧸ CFSG.oddCore K) ∈ centralizer
      (((zpowers x).map (QuotientGroup.mk' (CFSG.oddCore K)) :
        Subgroup (K ⧸ CFSG.oddCore K)) : Set (K ⧸ CFSG.oddCore K)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hyr : (y : K ⧸ CFSG.oddCore K) * QuotientGroup.mk' (CFSG.oddCore K) x =
        QuotientGroup.mk' (CFSG.oddCore K) x * y := mem_centralizer_singleton_iff.1 y.2
    have h2 := ((Commute.zpow_right (show Commute (y : K ⧸ CFSG.oddCore K)
      (QuotientGroup.mk' (CFSG.oddCore K) x) from hyr) k).eq)
    simpa [map_zpow] using h2.symm
  rw [hlift] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hcx : x * c = c * x := mem_centralizer_iff.1 hc x (mem_zpowers x)
  refine ⟨⟨c, mem_centralizer_singleton_iff.2 hcx.symm⟩, ?_⟩
  exact Subtype.ext hcy

end Quot

section GoodQuot

variable [Finite K] {r x : K}

@[expose] def centralRElem (hr : r ∈ center K) (x : K) : ↥(centralizer ({x} : Set K)) :=
  ⟨r, mem_centralizer_singleton_iff.2 (mem_center_iff.1 hr x).symm⟩

omit [Finite K] in
theorem central_five_mem_oddCore (hr : r ∈ center K) (hr5 : orderOf r = 5) :
    r ∈ CFSG.oddCore K := by
  have := normal_zpowers_of_mem_center hr
  have hodd : Odd (Nat.card (zpowers r)) := by
    rw [Nat.card_zpowers, hr5]
    decide
  exact le_oddCore_of_normal' hodd (mem_zpowers r)

theorem quotHom_ker_eq (hr : r ∈ center K) (hr5 : orderOf r = 5)
    (e : ↥(centralizer ({x} : Set K)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    (quotHom x).ker = zpowers (centralRElem hr x) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrN := central_five_mem_oddCore hr hr5
  have hrC5 : orderOf (centralRElem hr x) = 5 :=
    (Subgroup.orderOf_mk r _).trans hr5
  have hkerN : ∀ c ∈ (quotHom x).ker, (c : K) ∈ CFSG.oddCore K := by
    intro c hc
    have h1 : (QuotientGroup.mk' (CFSG.oddCore K)) c.1 = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
    exact (QuotientGroup.eq_one_iff _).1 h1
  apply le_antisymm
  · intro c hc
    set Nx : Subgroup ↥(centralizer ({x} : Set K)) := (quotHom x).ker with hNx
    have hNodd : Odd (Nat.card Nx) := by
      have hle : Nx.map (centralizer ({x} : Set K)).subtype ≤ CFSG.oddCore K := by
        rintro _ ⟨c', hc', rfl⟩
        exact hkerN c' hc'
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective Subtype.val_injective] at hdvd
      exact Odd.of_dvd_nat odd_card_oddCore' hdvd
    have hMn : (Nx.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
    have hModd : Odd (Nat.card (Nx.map e.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact hNodd
    obtain ⟨hc1, hc3⟩ := normal_odd_le_prod_five hModd (e c) ⟨c, hc, rfl⟩
    have hrcen : centralRElem hr x ∈ center ↥(centralizer ({x} : Set K)) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.1 hr g)
    have herc : e (centralRElem hr x) ∈ center
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (mem_center_iff.1 hrcen g').symm]
    have hr3 : (e (centralRElem hr x)).2.2 = 1 :=
      CFSG.perm_eq_one_of_forall_commute (by simp) fun σ =>
        (congr_arg (fun z => z.2.2) (mem_center_iff.1 herc (1, 1, σ))).symm
    have hr5' : orderOf (e (centralRElem hr x)) = 5 := by
      rw [MulEquiv.orderOf_eq]
      exact hrC5
    have hr1 : (e (centralRElem hr x)).1 = 1 := by
      have h5 : (e (centralRElem hr x)) ^ 5 = 1 := by
        have := pow_orderOf_eq_one (e (centralRElem hr x))
        rwa [hr5'] at this
      have h5' := congrArg Prod.fst h5
      have hsq := sq_eq_one_multiplicative_zmod_two (e (centralRElem hr x)).1
      exact eq_one_of_pow_odd_of_sq_eq_one (n := 5) (by decide) (by simpa using h5') hsq
    have hrb : (e (centralRElem hr x)).2.1 ≠ 1 := by
      intro hb
      have : e (centralRElem hr x) = 1 := Prod.ext hr1 (Prod.ext hb hr3)
      rw [this, orderOf_one] at hr5'
      omega
    obtain ⟨k, hk⟩ := exists_pow_eq_multiplicative_zmod_five hrb (e c).2.1
    refine ⟨(k : ℤ), ?_⟩
    show centralRElem hr x ^ (k : ℤ) = c
    rw [zpow_natCast]
    apply e.injective
    rw [map_pow]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [hr1, hc1]
    · simpa using hk
    · simp [hr3, hc3]
  · rw [zpowers_le, MonoidHom.mem_ker]
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 hrN)

theorem good_quot (hr : r ∈ center K) (hr5 : orderOf r = 5) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (e : ↥(centralizer ({x} : Set K)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    Nonempty (↥(centralizer ({(QuotientGroup.mk x : K ⧸ CFSG.oddCore K)} :
      Set (K ⧸ CFSG.oddCore K))) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) := by
  classical
  have hrC5 : orderOf (centralRElem hr x) = 5 := (Subgroup.orderOf_mk r _).trans hr5
  have hrcen : centralRElem hr x ∈ center ↥(centralizer ({x} : Set K)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hr g)
  have := normal_zpowers_of_mem_center hrcen
  obtain ⟨e₂⟩ := exists_mulEquiv_quotient_prod_five e hrcen hrC5
  have hfs := quotHom_surjective hx2 hx1
  have hker := quotHom_ker_eq hr hr5 e
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective (quotHom x) hfs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans e₂⟩

end GoodQuot

section ZStar

theorem oddCore_quot_eq_bot [Finite K] : CFSG.oddCore (K ⧸ CFSG.oddCore K) = ⊥ :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot (G := K)

theorem eq_one_of_sq_mem_oddCore [Finite K] {g : K} (hg : g ∈ CFSG.oddCore K) (h : g * g = 1) :
    g = 1 := by
  have h1 : orderOf g ∣ Nat.card (CFSG.oddCore K) :=
    Subgroup.orderOf_dvd_natCard (CFSG.oddCore K) hg
  have hodd : Odd (orderOf g) := Odd.of_dvd_nat odd_card_oddCore' h1
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 this

variable {X : Type*} [Group X]

theorem eq_of_central_involution {y z : X} (e : ↥(centralizer ({y} : Set X)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))
    (hz : z ∈ center X) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    z = y := by
  have hzy : z ∈ centralizer ({y} : Set X) :=
    mem_centralizer_singleton_iff.2 (mem_center_iff.1 hz y).symm
  have hyy : y ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.2 rfl
  have hcen : ∀ w : ↥(centralizer ({y} : Set X)),
      (∀ g : ↥(centralizer ({y} : Set X)), (g : X) * (w : X) = (w : X) * g) →
      w ∈ center ↥(centralizer ({y} : Set X)) := fun w hw => by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hw g)
  have hdec : ∀ w : ↥(centralizer ({y} : Set X)), w ∈ center ↥(centralizer ({y} : Set X)) →
      w * w = 1 → w ≠ 1 → e w = (Multiplicative.ofAdd 1, 1) := by
    intro w hw hw2 hw1
    have hec : e w ∈ center (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.1 hw g']
    have h2 : (e w).2 = 1 := center_prod_two_perm_five _ hec
    have h1 : (e w).1 ≠ 1 := by
      intro h
      apply hw1
      apply e.injective
      rw [map_one]
      exact Prod.ext h h2
    have hall : ∀ a : Multiplicative (ZMod 2), a ≠ 1 → a = Multiplicative.ofAdd 1 := by decide
    exact Prod.ext (hall _ h1) h2
  have hz' := hdec ⟨z, hzy⟩ (hcen _ fun g => mem_center_iff.1 hz g)
    (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h))
  have hy' := hdec ⟨y, hyy⟩ (hcen _ fun g => (mem_centralizer_singleton_iff.1 g.2))
    (Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
  have := e.injective (hz'.trans hy'.symm)
  exact congrArg Subtype.val this

theorem fusionZStar_le_center {H : Type*} [Group H] (hO : Open.fusionOddCore H = ⊥) :
    Open.fusionZStar H ≤ center H := by
  intro x hx
  rw [mem_center_iff]
  intro g
  have hx' : QuotientGroup.mk' (Open.fusionOddCore H) x ∈
      center (H ⧸ Open.fusionOddCore H) := hx
  have h1 := mem_center_iff.1 hx' (QuotientGroup.mk g)
  have h2 : (QuotientGroup.mk (g * x) : H ⧸ Open.fusionOddCore H) = QuotientGroup.mk (x * g) := h1
  rw [QuotientGroup.eq, hO, mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

variable [Finite K] {t v : K}

theorem mk_ne_of_involutions (ht2 : t * t = 1) (hv2 : v * v = 1) (htv : t * v = v * t)
    (hne : t ≠ v) :
    (QuotientGroup.mk t : K ⧸ CFSG.oddCore K) ≠ QuotientGroup.mk v := by
  intro h
  rw [QuotientGroup.eq] at h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [hti] at h
  have hsq : t * v * (t * v) = 1 := by
    calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [htv]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [ht2, hv2, one_mul]
  have h1 := eq_one_of_sq_mem_oddCore h hsq
  apply hne
  calc t = t * (t * v) := by rw [h1, mul_one]
    _ = v := by rw [← mul_assoc, ht2, one_mul]

theorem center_quot_eq_bot (ht2 : t * t = 1) (hv2 : v * v = 1) (ht1 : t ≠ 1) (hv1 : v ≠ 1)
    (htv : t * v = v * t) (hne : t ≠ v)
    (et : ↥(centralizer ({(QuotientGroup.mk t : K ⧸ CFSG.oddCore K)} :
      Set (K ⧸ CFSG.oddCore K))) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))
    (ev : ↥(centralizer ({(QuotientGroup.mk v : K ⧸ CFSG.oddCore K)} :
      Set (K ⧸ CFSG.oddCore K))) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    center (K ⧸ CFSG.oddCore K) = ⊥ := by
  classical
  by_contra hne'
  have hZ1 : Nat.card (center (K ⧸ CFSG.oddCore K)) ≠ 1 := fun h =>
    hne' (Subgroup.card_eq_one.1 h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hZ1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center (K ⧸ CFSG.oddCore K))) p hpd
  have hzc : (z : K ⧸ CFSG.oddCore K) ∈ center (K ⧸ CFSG.oddCore K) := z.2
  have hz1 : (z : K ⧸ CFSG.oddCore K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  by_cases hp2 : p = 2
  · subst hp2
    have hzz : (z : K ⧸ CFSG.oddCore K) * (z : K ⧸ CFSG.oddCore K) = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz, pow_two] at this
      exact congrArg Subtype.val this
    have htk : (QuotientGroup.mk t : K ⧸ CFSG.oddCore K) * QuotientGroup.mk t = 1 := by
      rw [← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
    have hvk : (QuotientGroup.mk v : K ⧸ CFSG.oddCore K) * QuotientGroup.mk v = 1 := by
      rw [← QuotientGroup.mk_mul, hv2, QuotientGroup.mk_one]
    have htk1 : (QuotientGroup.mk t : K ⧸ CFSG.oddCore K) ≠ 1 := fun h => ht1
      (eq_one_of_sq_mem_oddCore ((QuotientGroup.eq_one_iff t).1 h) ht2)
    have hvk1 : (QuotientGroup.mk v : K ⧸ CFSG.oddCore K) ≠ 1 := fun h => hv1
      (eq_one_of_sq_mem_oddCore ((QuotientGroup.eq_one_iff v).1 h) hv2)
    have e1 := eq_of_central_involution et hzc hzz hz1 htk htk1
    have e2 := eq_of_central_involution ev hzc hzz hz1 hvk hvk1
    exact mk_ne_of_involutions ht2 hv2 htv hne (e1.symm.trans e2)
  ·
    have hnorm : (zpowers (z : K ⧸ CFSG.oddCore K)).Normal :=
      normal_zpowers_of_mem_center hzc
    have hodd : Odd (Nat.card (zpowers (z : K ⧸ CFSG.oddCore K))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      exact hp.odd_of_ne_two hp2
    have hle := le_oddCore_of_normal' hodd
    rw [oddCore_quot_eq_bot] at hle
    exact hz1 (mem_bot.1 (hle (mem_zpowers _)))

theorem fusionZStar_quot_eq_bot (ht2 : t * t = 1) (hv2 : v * v = 1) (ht1 : t ≠ 1) (hv1 : v ≠ 1)
    (htv : t * v = v * t) (hne : t ≠ v)
    (et : ↥(centralizer ({(QuotientGroup.mk t : K ⧸ CFSG.oddCore K)} :
      Set (K ⧸ CFSG.oddCore K))) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))
    (ev : ↥(centralizer ({(QuotientGroup.mk v : K ⧸ CFSG.oddCore K)} :
      Set (K ⧸ CFSG.oddCore K))) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    Open.fusionZStar (K ⧸ CFSG.oddCore K) = ⊥ := by
  have hO : Open.fusionOddCore (K ⧸ CFSG.oddCore K) = ⊥ := oddCore_quot_eq_bot
  have h1 := fusionZStar_le_center hO
  rw [center_quot_eq_bot ht2 hv2 ht1 hv1 htv hne et ev] at h1
  exact le_bot_iff.1 h1

end ZStar

end CFSG.EvenSporadicStandard.HSStd



