module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Cent
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup CFSG.Open

theorem _root_.CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp.crel_one {X : Type} [Group X] {t u : X}
    (h : SecTwoHyp X t u) : CRel t u 1 where
  t_sq := h.t_sq
  u_four := h.u_pow_four
  x_five := one_pow 5
  tu := h.commute
  tx := by rw [mul_one, one_mul]
  ux := by rw [mul_one, mul_inv_cancel, one_pow]
  t_ne_one := h.t_ne_one
  z_ne_one := h.z_ne_one
  z_ne_t := h.sq_ne

end CFSG.LocalAnalysis.EvenBN.Tits.I21

namespace CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar

open I21

variable {G : Type} [Group G] {t u x : G}

theorem x_five (h : Sec622Bar G t u x) : x ^ 5 = 1 := by
  rcases h.x_cases with rfl | hx
  · exact one_pow 5
  · rw [← hx]; exact pow_orderOf_eq_one x

theorem crel (h : Sec622Bar G t u x) : CRel t u x where
  t_sq := h.secTwo.t_sq
  u_four := h.secTwo.u_pow_four
  x_five := h.x_five
  tu := h.secTwo.commute
  tx := h.comm_tx
  ux := h.conj_ux
  t_ne_one := h.secTwo.t_ne_one
  z_ne_one := h.secTwo.z_ne_one
  z_ne_t := h.secTwo.sq_ne

end CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup CFSG.Open

section Quotient

variable {Y : Type} [Group Y] [Finite Y]

theorem exp_quotient (hexp : ∀ g : Y, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1)
    (K : Subgroup Y) [K.Normal] (g : Y ⧸ K) (hg : ∃ k : ℕ, orderOf g = 2 ^ k) : g ^ 8 = 1 := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k, hk⟩ := hg
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g₀) (orderOf_pos g₀).ne'
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hord : orderOf (g₀ ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 (by rw [ho]; exact dvd_mul_left m _), ho,
      Nat.mul_div_cancel _ hm.pos]
  have h8 : (g₀ ^ m) ^ 8 = 1 := hexp _ ⟨a, hord⟩
  have h1 : (QuotientGroup.mk g₀ : Y ⧸ K) ^ (8 * m) = 1 := by
    rw [show 8 * m = m * 8 by ring, pow_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, h8,
      QuotientGroup.mk_one]
  have h2 : 2 ^ k ∣ 8 * m := hk ▸ orderOf_dvd_of_pow_eq_one h1
  have hc2 : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (fun h2 => by obtain ⟨c, hc⟩ := hm; omega)
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k hc2
  have h3 : 2 ^ k ∣ 8 := hc.dvd_of_dvd_mul_right h2
  rw [← hk] at h3
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem centralizer_mk_le {t : Y} (ht : t * t = 1) :
    centralizer ({(QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y)} : Set _) ≤
      (centralizer ({t} : Set Y)).map (QuotientGroup.mk' (standardComponentOddCore Y)) := by
  set K := standardComponentOddCore Y with hKdef
  have hK : Odd (Nat.card K) := secTwo_odd_card_oddCore
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [mem_centralizer_singleton_iff] at hy
  have hg : t⁻¹ * (g * t * g⁻¹) ∈ K := by
    rw [← QuotientGroup.eq_one_iff (N := K), QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    change (QuotientGroup.mk t : Y ⧸ K)⁻¹ * ((QuotientGroup.mk g) * QuotientGroup.mk t *
      (QuotientGroup.mk g)⁻¹) = 1
    rw [hy, mul_assoc (QuotientGroup.mk t : Y ⧸ K), mul_inv_cancel, mul_one, inv_mul_cancel]
  obtain ⟨m, hm, hmg⟩ := secTwo_exists_mem_centralizer hK ht hg
  refine ⟨m * g, hmg, ?_⟩
  change (QuotientGroup.mk (m * g) : Y ⧸ K) = QuotientGroup.mk g
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).mpr hm, one_mul]

theorem centralizer_mk_eq {t u x : Y} (hH : SecTwoHyp Y t u) (hx : t * x = x * t)
    (hC : centralizer ({t} : Set Y) = closure {t, u, x}) :
    centralizer ({(QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y)} : Set _) =
      closure {(QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y), QuotientGroup.mk u,
        QuotientGroup.mk x} := by
  set K := standardComponentOddCore Y with hKdef
  apply le_antisymm
  · refine (centralizer_mk_le hH.t_mul_t).trans ?_
    rw [hC, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    intro g hg
    obtain ⟨a, ha, rfl⟩ := hg
    rcases ha with rfl | rfl | rfl <;> simp
  · rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · rfl
    · change (QuotientGroup.mk u : Y ⧸ K) * QuotientGroup.mk t = QuotientGroup.mk t *
        QuotientGroup.mk u
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hH.commute.symm]
    · change (QuotientGroup.mk x : Y ⧸ K) * QuotientGroup.mk t = QuotientGroup.mk t *
        QuotientGroup.mk x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx]

end Quotient

end CFSG.LocalAnalysis.EvenBN.Tits.I21

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.I21

theorem sec622_quotient {Y : Type} [Group Y] [Finite Y] {t u x : Y} (hH : SecTwoHyp Y t u)
    (hx : orderOf x = 5) (htx : Commute t x) (hux : u * x * u⁻¹ = x ^ 2)
    (hC : centralizer ({t} : Set Y) = closure {t, u, x}) (hcard : Nat.card Y ∣ sec622N)
    (hexp : ∀ g : Y, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) :
    Sec622Bar (Y ⧸ standardComponentOddCore Y) (QuotientGroup.mk t) (QuotientGroup.mk u)
      (QuotientGroup.mk x) where
  secTwo := hH.quotient
  oddCore := secTwo_oddCore_quotient
  x_cases := by
    have h5 : (QuotientGroup.mk x : Y ⧸ standardComponentOddCore Y) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one h5) with
      h1 | h1
    · left; exact orderOf_eq_one_iff.mp h1
    · right; exact h1
  comm_tx := by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, htx.eq]
  conj_ux := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_pow, hux]
  cent := centralizer_mk_eq hH htx.eq hC
  card_dvd := by
    refine Dvd.dvd.trans ?_ hcard
    rw [← Subgroup.index_eq_card]
    exact (standardComponentOddCore Y).index_dvd_card
  exp_two := exp_quotient hexp _

end CFSG.LocalAnalysis.EvenBN.Tits
