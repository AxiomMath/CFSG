module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.F1Loc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Std
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem false_of_outer (hr : 4 ≤ r) {s : G} (hsS : s ∈ (S : Subgroup G)) (hs2 : s * s = 1)
    (hst : s * t * s⁻¹ = t * z)
    (hno : ¬ ∃ w ∈ (S : Subgroup G) ⊓ K, orderOf w = 4 ∧ w * s = s * w) : False := by
  have hd0 := hd.toTightSylowDataR
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd0.comm_of_mem
  have htW : t ∈ W := hd.mem_W
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hsS)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  set R : Subgroup G := (S : Subgroup G) ⊓ K with hRdef
  have hRR : R ∈ RSet (CoreAssembly.conjClass K) := hd0.inf_mem_rSet
  obtain ⟨e⟩ := hd.exists_quat_of_mem_RSet hRR
  have hzR : z ∈ R := hd0.mem_inf
  have hzs : ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥R) : G) = z := by
    rcases QSub.eq_of_mul_self_eq_one e hzR hI.sq with h | h
    · exact absurd h hI.ne_one
    · exact h.symm
  have hconjR : ∀ c ∈ (S : Subgroup G), ∀ y ∈ R, c * y * c⁻¹ ∈ R := by
    intro c hc y hy
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hc hy.1)
      ((S : Subgroup G).inv_mem hc), (Subgroup.mem_normalizer_iff.mp (hd0.hSN hc) y).mp hy.2⟩
  have hU := hd0.inf_mem_USet
  have hUR : K ⊓ W ≤ R := fun a ha => ⟨hd.hWS ha.2, ha.1⟩
  have hUc : IsCyclic ↥(K ⊓ W) := by
    obtain ⟨-, -, -, -, -, -, hUc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    exact hUc
  have hUi : (K ⊓ W).relIndex R = 2 := by
    obtain ⟨R', hR', hUR', -, hidx⟩ := hU
    have h1 := Subgroup.relIndex_mul_card (H := K ⊓ W) (K := R')
    have h2 := Subgroup.relIndex_mul_card (H := K ⊓ W) (K := R)
    rw [inf_eq_left.mpr hUR', hidx] at h1
    rw [inf_eq_left.mpr hUR] at h2
    have hpos : 0 < Nat.card ↥(K ⊓ W) := Nat.card_pos
    have h3 : (K ⊓ W).relIndex R * Nat.card ↥(K ⊓ W) = 2 * Nat.card ↥(K ⊓ W) := by
      rw [h2, hd.tight.natCard_rSet hRR, ← hd.tight.natCard_rSet hR', ← h1]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hUX : K ⊓ W = QSub.xc e := QSub.eq_xc_of_cyclic_index_two e hr hUR hUc hUi
  obtain ⟨r₀, hrR, hrt⟩ := hd.exists_conj_eq_mul
  have hrW : r₀ ∉ W := by
    intro hrW
    have h1 : r₀ * t * r₀⁻¹ = t := by rw [hcomm r₀ hrW t htW]; group
    rw [h1] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hrX : r₀ ∉ QSub.xc e := by
    rw [← hUX]
    exact fun h => hrW h.2
  have hsQ : ∀ q ∈ R, s * q * s⁻¹ ∈ R := hconjR s hsS
  have hord : orderOf ((s * r₀ * s⁻¹) * r₀) = 2 ^ (r - 1) :=
    QSub.orderOf_swap_mul e hr hsQ hno hrR fun i hi => hrX ((QSub.mem_xc_iff e).mpr ⟨i, hi⟩)
  set y : G := s * r₀ with hy
  have hyS : y ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hsS hrR.1
  have hyy : y * y = (s * r₀ * s⁻¹) * r₀ := by
    show (s * r₀) * (s * r₀) = (s * r₀ * s⁻¹) * r₀
    rw [hsinv]
    group
  have hy4 : y ^ 2 ^ (r - 1) = z := by
    obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hrk1 : r - 1 = k + 1 := by omega
    have hwR : (s * r₀ * s⁻¹) * r₀ ∈ R := R.mul_mem (hsQ r₀ hrR) hrR
    set x : G := ((s * r₀ * s⁻¹) * r₀) ^ 2 ^ k with hx
    have hpow : y ^ 2 ^ (r - 1) = x := by
      rw [hrk1, pow_succ', pow_mul, pow_two y, hyy]
    have hxR : x ∈ R := R.pow_mem hwR _
    have hord2 : orderOf x = 2 := by
      rw [hx, orderOf_pow' _ (pow_ne_zero k two_ne_zero), hord, hrk1,
        Nat.gcd_eq_right (pow_dvd_pow 2 (Nat.le_succ k)), pow_succ', Nat.mul_div_cancel _
        (by positivity)]
    have hsq : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hord2, pow_two] at h
    rcases QSub.eq_of_mul_self_eq_one e hxR hsq with h | h
    · exfalso
      rw [h, orderOf_one] at hord2
      omega
    · rw [hpow, h, hzs]
  have hyt : y * t * y⁻¹ = t := by
    calc y * t * y⁻¹ = s * (r₀ * t * r₀⁻¹) * s⁻¹ := by rw [hy]; group
      _ = (s * t * s⁻¹) * (s * z * s⁻¹) := by rw [hrt]; group
      _ = t := by rw [hst, hsz, mul_inv_cancel_right, mul_assoc, hI.sq, mul_one]
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [hyt]
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hyC
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
  obtain ⟨Q, hQ, hQY⟩ := exists_sylow_normalized hy2 (Subgroup.zpowers_le.mpr hyL)
  have hQR : Q ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_iff.mpr ⟨L, hd.memL, hQ.1, hQ.2.1, hQ.2.2⟩
  obtain ⟨eQ⟩ := hd.exists_quat_of_mem_RSet hQR
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro q hq
    have h := conj_mem_conjSub (n := y) hq
    rwa [hQY y (Subgroup.mem_zpowers y)] at h
  have hQz : Q ≤ Subgroup.centralizer ({z} : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := QSub.pow_exponent_comm eQ hr hyQ hq
    rw [hy4] at this
    exact this.symm
  exact hd.tight.not_le_centralizer_of_mem_rSet hd.memL (CoreAssembly.mem_conjClass_self K)
    hd.member_ne hI hQR hQ.1 hQz

theorem exists_conj_eq_of_comm_z (hr : 4 ≤ r) {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹)) (hsz : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hI := hd.tight.isUniqueInvolution
  have hss : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hI.sq]
    group
  have hs2 : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) :=
    (S19Q.isPGroup_zpowers_iff_exists_pow _).mpr ⟨1, by rw [pow_one, sq, hss]⟩
  obtain ⟨S', hd', hx', c, hc, hcs⟩ := hd.exists_sylow_conj hx
    (Subgroup.mem_centralizer_singleton_iff.mpr hsx)
    (Subgroup.mem_centralizer_singleton_iff.mpr hsz)
    hs2
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc.1
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have e₂ : c * (g * z * g⁻¹) * c⁻¹ = (c * g) * z * (c * g)⁻¹ := by group
  rw [e₂] at hcs
  have hsx₂ : (c * g) * z * (c * g)⁻¹ * x = x * ((c * g) * z * (c * g)⁻¹) := by
    rw [← e₂]
    calc c * (g * z * g⁻¹) * c⁻¹ * x = c * (g * z * g⁻¹) * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * (g * z * g⁻¹) * x * c⁻¹ := by
          rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx, inv_mul_cancel_left]]
      _ = c * (x * (g * z * g⁻¹)) * c⁻¹ := by rw [mul_assoc c, hsx, ← mul_assoc]
      _ = x * (c * (g * z * g⁻¹) * c⁻¹) := by
          rw [show c * (x * (g * z * g⁻¹)) * c⁻¹ = (c * x) * (g * z * g⁻¹) * c⁻¹ by group, hcx]
          group
  have hsz₂ : (c * g) * z * (c * g)⁻¹ * z = z * ((c * g) * z * (c * g)⁻¹) := by
    rw [← e₂]
    calc c * (g * z * g⁻¹) * c⁻¹ * z = c * (g * z * g⁻¹) * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * (g * z * g⁻¹) * z * c⁻¹ := by
          rw [show c⁻¹ * z * c = z by rw [mul_assoc, ← hcz, inv_mul_cancel_left]]
      _ = c * (z * (g * z * g⁻¹)) * c⁻¹ := by rw [mul_assoc c, hsz, ← mul_assoc]
      _ = z * (c * (g * z * g⁻¹) * c⁻¹) := by
          rw [show c * (z * (g * z * g⁻¹)) * c⁻¹ = (c * z) * (g * z * g⁻¹) * c⁻¹ by group, hcz]
          group
  have key : ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = (c * g) * z * (c * g)⁻¹ := by
    have hzt : z * t = t * z := hd.toTightSylowDataR.comm_of_mem z hd.mem_W_z t hd.mem_W
    rcases hd'.conj_t_eq_or_of_le_normalizer hd'.le_normalizer_W hcs with ht | ht
    · have hst : (c * g) * z * (c * g)⁻¹ * t = t * ((c * g) * z * (c * g)⁻¹) := by
        calc (c * g) * z * (c * g)⁻¹ * t
            = ((c * g) * z * (c * g)⁻¹) * t * ((c * g) * z * (c * g)⁻¹)⁻¹ *
              ((c * g) * z * (c * g)⁻¹) := by group
          _ = t * ((c * g) * z * (c * g)⁻¹) := by rw [ht]
      exact hd'.exists_conj_eq_of_comm_t hr hx' hsx₂ hsz₂ hst
    · have hsne : (c * g) * z * (c * g)⁻¹ ≠ z := by
        intro h
        rw [h] at ht
        have h1 : z * t * z⁻¹ = t := by rw [hzt, mul_inv_cancel_right]
        rw [h1] at ht
        exact hI.ne_one (mul_eq_left.mp ht.symm)
      have hss₂ : (c * g) * z * (c * g)⁻¹ * ((c * g) * z * (c * g)⁻¹) = 1 := by
        rw [show (c * g) * z * (c * g)⁻¹ * ((c * g) * z * (c * g)⁻¹) =
          (c * g) * (z * z) * (c * g)⁻¹ by group, hI.sq]
        group
      by_cases hw : ∃ w ∈ (S' : Subgroup G) ⊓ K, orderOf w = 4 ∧
          w * ((c * g) * z * (c * g)⁻¹) = ((c * g) * z * (c * g)⁻¹) * w
      · obtain ⟨w, hwR, hw4, hws⟩ := hw
        exact hd'.exists_conj_eq_of_comm_u hx' hsx₂ hsne hwR.2 hw4 hws
      · exact (hd'.false_of_outer hr hcs hss₂ ht hw).elim
  obtain ⟨h, hh, he⟩ := key
  refine ⟨c⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ hc.1) hh, ?_⟩
  calc c⁻¹ * h * z * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * z * h⁻¹) * c := by group
    _ = c⁻¹ * ((c * g) * z * (c * g)⁻¹) * c := by rw [he]
    _ = g * z * g⁻¹ := by group

end TightSylowDataTR

variable {R : Subgroup G} {S₀ : Sylow 2 R} {t₀ : G} {T : Sylow 2 G}

theorem StdR.comm_of_mem_of_inf_core_le (h : StdR r R S₀ t₀ T) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hS₀P : (T : Subgroup G) ⊓ tightCore R ≤ P) {p : G} (hp : p ∈ P) :
    p * t₀ = t₀ * p := by
  apply h.comm_of_mem_normalizer_inf_core
  rw [h.inf_core_eq] at hS₀P ⊢
  have hS2 : IsSylow2Of ((S₀ : Subgroup R).map R.subtype) (tightCore R) := h.sylow_core
  obtain ⟨Q₀, hQ₀⟩ := hS2.exists_sylow
  rw [← hQ₀] at hS₀P ⊢
  have hle : conjSub p ((Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype) ≤ P := by
    intro a ha
    rw [mem_conjSub_iff] at ha
    have := P.mul_mem (P.mul_mem hp (hS₀P ha)) (P.inv_mem hp)
    simpa [mul_assoc] using this
  exact mem_normalizer_iff_conjSub_eq.mpr (h.datum.sylow_eq h.edgeless Q₀ hP2 hS₀P hle)

theorem tightF1SR_holds {r : ℕ} (hr : 4 ≤ r) : TightF1SR r := by
  intro G _ _ _ _ R S t T W L t' V h hd x hx _ g hg
  have hss : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, t_mul_t h.datum]
    group
  have hs2 : IsPGroup 2 (Subgroup.zpowers (g * t * g⁻¹)) :=
    (S19Q.isPGroup_zpowers_iff_exists_pow _).mpr ⟨1, by rw [pow_one, sq, hss]⟩
  set H : Subgroup G := Subgroup.centralizer ({x} : Set G) with hH
  obtain ⟨P, hP, hTP⟩ := IsSylow2In.exists_ge
    (T.isPGroup'.to_le inf_le_left : IsPGroup 2 ↥((T : Subgroup G) ⊓ H)) inf_le_right
  obtain ⟨c, hcH, hsc⟩ := Sec7.exists_conj_le_of_isSylow2In hP hs2 (Subgroup.zpowers_le.mpr hg)
  have hcs : c⁻¹ * (g * t * g⁻¹) * c ∈ P := mem_conjSub_iff.mp (hsc (Subgroup.mem_zpowers _))
  have hS₀P : (T : Subgroup G) ⊓ tightCore R ≤ P := fun r hr =>
    hTP ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.1.1.2 r hr)⟩
  have hct := h.comm_of_mem_of_inf_core_le hP.2.1 hS₀P hcs
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcH
  have hgx : g * t * g⁻¹ * x = x * (g * t * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have e₁ : c⁻¹ * (g * t * g⁻¹) * c = (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ := by group
  rw [e₁] at hct
  have hcx' : c⁻¹ * x = x * c⁻¹ := by
    calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
      _ = x * c⁻¹ := by group
  have hsx : (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ * x = x * ((c⁻¹ * g) * t * (c⁻¹ * g)⁻¹) := by
    rw [← e₁]
    calc c⁻¹ * (g * t * g⁻¹) * c * x = c⁻¹ * (g * t * g⁻¹) * (c * x) := by group
      _ = c⁻¹ * (g * t * g⁻¹) * (x * c) := by rw [hcx]
      _ = c⁻¹ * ((g * t * g⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (g * t * g⁻¹)) * c := by rw [hgx]
      _ = (c⁻¹ * x) * (g * t * g⁻¹) * c := by group
      _ = (x * c⁻¹) * (g * t * g⁻¹) * c := by rw [hcx']
      _ = x * (c⁻¹ * (g * t * g⁻¹) * c) := by group
  obtain ⟨h₁, hh₁, he₁⟩ := hd.exists_conj_eq_of_comm_z hr hx hsx hct
  refine ⟨c * h₁, Subgroup.mul_mem _ hcH hh₁, ?_⟩
  calc c * h₁ * t * (c * h₁)⁻¹ = c * (h₁ * t * h₁⁻¹) * c⁻¹ := by group
    _ = c * ((c⁻¹ * g) * t * (c⁻¹ * g)⁻¹) * c⁻¹ := by rw [he₁]
    _ = g * t * g⁻¹ := by group

end CFSG.CGT.PushingUpLit.SolKNA.R4
