module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelNoSig

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

theorem pfree_centralizer_plane_extra {M : Type*} [Group M] [Finite M] {R Q E : Subgroup M}
    {p : ℕ} (hp : p.Prime) (hQ3 : Nat.card Q = p ^ 3) (hQexp : ∀ x ∈ Q, x ^ p = 1) {z : M}
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hzc : ∀ q ∈ Q, z * q = q * z)
    (hZ : ∀ x ∈ Q, (∀ q ∈ Q, x * q = q * x) → x ∈ Subgroup.zpowers z)
    (hN : ∀ c ∈ R ⊓ Subgroup.centralizer ({z} : Set M), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hCC : PFree p (R ⊓ Subgroup.centralizer ({z} : Set M) ⊓ Subgroup.centralizer (Q : Set M) :
      Subgroup M))
    (hEQ : E ≤ Q) (hEel : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2) :
    PFree p (R ⊓ Subgroup.centralizer (E : Set M) : Subgroup M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzord : orderOf z = p := orderOf_eq_prime (hQexp z hzQ) hz1
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQnc : ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro hab
    have hle : Q ≤ Subgroup.zpowers z := fun x hx => hZ x hx fun q hq => hab x hx q hq
    have := Subgroup.card_le_of_le hle
    rw [hQ3, hzcard] at this
    have h3 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hzE : z ∈ E := by
    by_contra hzE
    apply hQnc
    set F : Subgroup M := Subgroup.closure ((E : Set M) ∪ {z}) with hF
    have hFQ : F ≤ Q := by
      rw [hF, Subgroup.closure_le]
      rintro x (hx | rfl)
      · exact hEQ hx
      · exact hzQ
    have hEF : E ≤ F := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hzF : z ∈ F := Subgroup.subset_closure (Or.inr rfl)
    have hFcard : Nat.card F = p ^ 3 := by
      have hlt : Nat.card E < Nat.card F := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hEF) fun heq => hzE ?_
        have := Subgroup.eq_of_le_of_card_ge hEF heq.ge
        rw [this]
        exact hzF
      have hdvd : Nat.card F ∣ p ^ 3 := hQ3 ▸ Subgroup.card_dvd_of_le hFQ
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      rw [hE2] at hlt
      by_contra hne
      have hj2 : j ≤ 2 := by
        by_contra h3
        have : j = 3 := by omega
        subst this
        exact hne hj'
      have : p ^ j ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hj2
      omega
    have hFQ' : F = Q := Subgroup.eq_of_le_of_card_ge hFQ (by rw [hFcard, hQ3])
    have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
      have hS : ∀ x ∈ (E : Set M) ∪ {z}, ∀ y ∈ (E : Set M) ∪ {z}, x * y = y * x := by
        intro x hx y hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact hEcomm x hx y hy
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (hzc x (hEQ hx)).symm
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact hzc y (hEQ hy)
        · rw [Set.mem_singleton_iff] at hx hy
          rw [hx, hy]
      have hF1 : F ≤ Subgroup.centralizer ((E : Set M) ∪ {z}) := by
        rw [hF, Subgroup.closure_le]
        intro x hx
        exact Subgroup.mem_centralizer_iff.2 fun y hy => hS y hy x hx
      intro a ha b hb
      have hb' : ∀ s ∈ (E : Set M) ∪ {z}, s * b = b * s := fun s hs =>
        Subgroup.mem_centralizer_iff.1 (hF1 hb) s hs
      have hF2 : F ≤ Subgroup.centralizer ({b} : Set M) := by
        rw [hF, Subgroup.closure_le]
        intro s hs
        exact Subgroup.mem_centralizer_singleton_iff.2 (hb' s hs)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hF2 ha)
    rw [← hFQ']
    exact hFcomm
  have hcommz : ∀ v ∈ Q, ∀ e ∈ Q, ∃ c ∈ Subgroup.zpowers z, v * e * v⁻¹ = e * c := by
    intro v hv e he
    set N : Subgroup ↥Q := (Subgroup.zpowers z).subgroupOf Q with hN'
    have hzle : Subgroup.zpowers z ≤ Q := (Subgroup.zpowers_le).2 hzQ
    have hNnormal : N.Normal := ⟨fun n hn g => by
      rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hcomm : (g : M) * (n : M) = (n : M) * (g : M) := by
        rw [← hk]
        have hcz : Commute z (g : M) := hzc g g.2
        exact (hcz.zpow_left k).eq.symm
      have : (g : M) * (g : M)⁻¹ = 1 := mul_inv_cancel _
      have e1 : (↑(g * n * g⁻¹) : M) = (n : M) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (g : M) * n * (g : M)⁻¹ = (n : M) * g * (g : M)⁻¹ := by rw [hcomm]
          _ = n := by group
      rw [e1]
      exact hn⟩
    have hNcard : Nat.card N = p := by
      rw [hN']
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, hzcard]
    have hquot : Nat.card (↥Q ⧸ N) = p ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hQ3, hNcard] at h
      have hp0 : 0 < p := hp.pos
      have : p ^ 3 = p ^ 2 * p := by ring
      rw [this] at h
      exact (Nat.eq_of_mul_eq_mul_right hp0 h).symm
    haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
    have hmk := mul_comm' (QuotientGroup.mk (⟨v, hv⟩ : ↥Q) : ↥Q ⧸ N) (QuotientGroup.mk ⟨e, he⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hmk
    have hmem := QuotientGroup.eq.1 hmk.symm
    rw [hN', Subgroup.mem_subgroupOf] at hmem
    set c : M := (e * v)⁻¹ * (v * e) with hcdef
    have hc_mem : c ∈ Subgroup.zpowers z := by
      have h1 : c = v⁻¹ * e⁻¹ * (v * e) := by rw [hcdef]; group
      rw [h1]
      simpa using hmem
    refine ⟨c, hc_mem, ?_⟩
    have hevc : v * e = e * v * c := by rw [hcdef]; group
    have hcv : v * c = c * v := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc_mem
      rw [← hk]
      have hcz : Commute z v := hzc v hv
      exact (hcz.zpow_left k).eq.symm
    calc v * e * v⁻¹ = (e * v * c) * v⁻¹ := by rw [hevc]
      _ = e * (v * c * v⁻¹) := by group
      _ = e * (c * v * v⁻¹) := by rw [hcv]
      _ = e * c := by group
  obtain ⟨e, heE, hez⟩ : ∃ e ∈ E, e ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have hle : E ≤ Subgroup.zpowers z := fun x hx => hall x hx
    have := Subgroup.card_le_of_le hle
    rw [hE2, hzcard] at this
    have h2 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hCQe : Q ⊓ Subgroup.centralizer ({e} : Set M) = E := by
    have hEle : E ≤ Q ⊓ Subgroup.centralizer ({e} : Set M) := fun x hx =>
      ⟨hEQ hx, Subgroup.mem_centralizer_singleton_iff.2 (hEcomm x hx e heE)⟩
    have hle : Q ⊓ Subgroup.centralizer ({e} : Set M) ≤ Q := inf_le_left
    have hdvd : Nat.card (Q ⊓ Subgroup.centralizer ({e} : Set M) : Subgroup M) ∣ p ^ 3 :=
      hQ3 ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hge : p ^ 2 ≤ Nat.card (Q ⊓ Subgroup.centralizer ({e} : Set M) : Subgroup M) := by
      rw [← hE2]
      exact Subgroup.card_le_of_le hEle
    have hne : Nat.card (Q ⊓ Subgroup.centralizer ({e} : Set M) : Subgroup M) ≠ p ^ 3 := by
      intro h3
      have hQeq : Q ⊓ Subgroup.centralizer ({e} : Set M) = Q :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hQ3])
      apply hez
      refine hZ e (hEQ heE) fun q hq => ?_
      have : q ∈ Q ⊓ Subgroup.centralizer ({e} : Set M) := by rw [hQeq]; exact hq
      exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
    have hj2 : j = 2 := by
      rw [hj'] at hge hne
      have : 2 ≤ j := by
        by_contra hlt
        push Not at hlt
        have : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        have h2' : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      have : j ≤ 3 := hj
      interval_cases j <;> simp_all
    have hcard' : Nat.card (Q ⊓ Subgroup.centralizer ({e} : Set M) : Subgroup M) = p ^ 2 := by
      rw [hj', hj2]
    exact (Subgroup.eq_of_le_of_card_ge hEle (by rw [hcard', hE2])).symm
  intro u hu hcop
  obtain ⟨huR, huE⟩ := hu
  have hcomm_u : ∀ h ∈ E, h * u = u * h := fun h hh => Subgroup.mem_centralizer_iff.1 huE h hh
  have huz : u ∈ R ⊓ Subgroup.centralizer ({z} : Set M) :=
    ⟨huR, Subgroup.mem_centralizer_singleton_iff.2 (hcomm_u z hzE).symm⟩
  have hfix : ∀ h ∈ E, u * h * u⁻¹ = h := fun h hh => by
    rw [← hcomm_u h hh]
    group
  have hcentQ : ∀ v ∈ Q, u * v = v * u := by
    intro v hv
    set w : M := u * v * u⁻¹ with hw
    have hwQ : w ∈ Q := hN u huz v hv
    obtain ⟨c, hc, hvc⟩ := hcommz v hv e (hEQ heE)
    have hcu : u * c * u⁻¹ = c := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
      rw [← hk]
      have hzu : u * z = z * u := (hcomm_u z hzE).symm
      have : u * z ^ k = z ^ k * u := (Commute.zpow_right (show Commute u z from hzu) k).eq
      rw [this]
      group
    have hweq : w * e * w⁻¹ = v * e * v⁻¹ := by
      have h1 : u⁻¹ * e * u = e := by
        have := hfix e heE
        calc u⁻¹ * e * u = u⁻¹ * (u * e * u⁻¹) * u := by rw [this]
          _ = e := by group
      calc w * e * w⁻¹ = u * v * (u⁻¹ * e * u) * v⁻¹ * u⁻¹ := by rw [hw]; group
        _ = u * v * e * v⁻¹ * u⁻¹ := by rw [h1]
        _ = u * (v * e * v⁻¹) * u⁻¹ := by group
        _ = u * (e * c) * u⁻¹ := by rw [hvc]
        _ = (u * e * u⁻¹) * (u * c * u⁻¹) := by group
        _ = e * c := by rw [hfix e heE, hcu]
        _ = v * e * v⁻¹ := hvc.symm
    set t : M := v⁻¹ * w with ht
    have htQ : t ∈ Q := Q.mul_mem (Q.inv_mem hv) hwQ
    have hte : t ∈ E := by
      rw [← hCQe]
      refine ⟨htQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc t * e = v⁻¹ * (w * e * w⁻¹) * w := by rw [ht]; group
        _ = v⁻¹ * (v * e * v⁻¹) * w := by rw [hweq]
        _ = e * (v⁻¹ * w) := by group
        _ = e * t := by rw [ht]
    have hiter : ∀ k : ℕ, u ^ k * v * (u ^ k)⁻¹ = v * t ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have htk : u * t ^ k * u⁻¹ = t ^ k := hfix _ (E.pow_mem hte k)
        calc u ^ (k + 1) * v * (u ^ (k + 1))⁻¹ = u * (u ^ k * v * (u ^ k)⁻¹) * u⁻¹ := by group
          _ = u * (v * t ^ k) * u⁻¹ := by rw [ih]
          _ = (u * v * u⁻¹) * (u * t ^ k * u⁻¹) := by group
          _ = (v * t) * t ^ k := by rw [htk, ← hw]; rw [ht]; group
          _ = v * t ^ (k + 1) := by group
    have hu1 : u ^ orderOf u = 1 := pow_orderOf_eq_one u
    have htm : t ^ orderOf u = 1 := by
      have := hiter (orderOf u)
      rw [hu1] at this
      simp only [inv_one, one_mul, mul_one] at this
      exact (mul_left_cancel (a := v) (by rw [mul_one]; exact this.symm))
    have htp : t ^ p = 1 := hQexp t htQ
    have ht1 : t = 1 := by
      have hg : Nat.gcd (orderOf u) p = 1 := hcop
      have := pow_gcd_eq_one.2 ⟨htm, htp⟩
      rwa [hg, pow_one] at this
    have hwv : w = v := by
      have : v⁻¹ * w = 1 := by rw [← ht]; exact ht1
      exact (inv_mul_eq_one.1 this).symm
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v * u := by rw [← hw, hwv]
  exact hCC u ⟨⟨huR, Subgroup.mem_centralizer_singleton_iff.2 (hcomm_u z hzE).symm⟩,
    Subgroup.mem_centralizer_iff.2 fun q hq => (hcentQ q hq).symm⟩ hcop

end CFSG.HardMathSupport.Dickson.I271
