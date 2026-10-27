module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXRho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXDih

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

namespace S11sCtx

variable {G : Type} [Group G] [Finite G] {t z : G} {K1 K2 T R : Subgroup G}
  {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G} (c : S11sCtx t z K1 K2 T R ρ a x)

private lemma s11s_rearrange_five {A1 A2 A4 A5 m : G} (hA2m : A2 * m = m * A2)
    (hA1m : A1 * m = m * A1) (hA1A2 : A1 * A2 = A2 * A1) (hA1A4 : A1 * A4 = A4 * A1) :
    A1 * A2 * m * (A4 * A5) = m * (A2 * A4 * (A1 * A5)) := by
  calc A1 * A2 * m * (A4 * A5)
      = A1 * (A2 * m) * (A4 * A5) := by group
    _ = A1 * (m * A2) * (A4 * A5) := by rw [hA2m]
    _ = A1 * m * A2 * (A4 * A5) := by group
    _ = m * A1 * A2 * (A4 * A5) := by rw [hA1m]
    _ = m * (A1 * A2) * (A4 * A5) := by group
    _ = m * (A2 * A1) * (A4 * A5) := by rw [hA1A2]
    _ = m * A2 * A1 * (A4 * A5) := by group
    _ = m * A2 * (A1 * (A4 * A5)) := by group
    _ = m * A2 * (A4 * (A1 * A5)) := by
          rw [show A1 * (A4 * A5) = A4 * (A1 * A5) by
            rw [← mul_assoc A1 A4 A5, hA1A4, mul_assoc]]
    _ = m * (A2 * A4 * (A1 * A5)) := by group

include c

private lemma s11s_pair_comm : ∀ u ∈ K1, ∀ v ∈ K2, u * v = v * u := by
  intro u hu v hv
  have h := c.pair.comm ⟨u, Subgroup.mem_sup_left hu⟩
    (show (⟨u, Subgroup.mem_sup_left hu⟩ : ↥(K1 ⊔ K2)) ∈
      K1.subgroupOf (K1 ⊔ K2) from hu)
    ⟨v, Subgroup.mem_sup_right hv⟩
    (show (⟨v, Subgroup.mem_sup_right hv⟩ : ↥(K1 ⊔ K2)) ∈
      K2.subgroupOf (K1 ⊔ K2) from hv)
  simpa [Subgroup.coe_mul] using congrArg Subtype.val h

theorem caseB_e {s b e : G} (hQ1 : ∀ q ∈ twoCoreIn K1, s * q * s⁻¹ ∈ twoCoreIn K1)
    (hb : b ∈ twoCoreIn K1) (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z)
    {q : SL23} (hq : q ^ 4 = 1) (hq1 : q ≠ 1) (hqm : q ≠ -1)
    (he : e = s * b * s⁻¹ * b⁻¹ *
      (((c.pair.embB q * c.pair.embB (K5.k5g 0) * (c.pair.embB q)⁻¹)⁻¹ * c.pair.embB (K5.k5g 0) :
        ↥(K1 ⊔ K2)) : G)) :
    e ∈ K1 ⊔ K2 ∧ e * e = 1 ∧ e ∉ zpowers z := by
  set c2 : ↥(K1 ⊔ K2) :=
    (c.pair.embB q * c.pair.embB (K5.k5g 0) * (c.pair.embB q)⁻¹)⁻¹ *
      c.pair.embB (K5.k5g 0) with hc2
  set c1 : G := s * b * s⁻¹ * b⁻¹ with hc1
  have hc1Q : c1 ∈ twoCoreIn K1 := by
    rw [hc1]
    exact mul_mem (hQ1 b hb) (inv_mem hb)
  have hc1K1 : c1 ∈ K1 := twoCoreIn_le_self K1 hc1Q
  have hc1sq : c1 * c1 = z := c.sq_eq_z1 hc1Q hsb
  have hc2B : c2 ∈ K2.subgroupOf (K1 ⊔ K2) := by
    rw [hc2]
    exact mul_mem
      (inv_mem (mul_mem (mul_mem (c.pair.embB_mem q)
        (c.pair.embB_mem (K5.k5g 0))) (inv_mem (c.pair.embB_mem q))))
      (c.pair.embB_mem (K5.k5g 0))
  have hc2K2 : (c2 : G) ∈ K2 := Subgroup.mem_subgroupOf.mp hc2B
  have hc2sq : (c2 : G) * (c2 : G) = z := by
    have h : c2 * c2 = c.pair.embB (-1) := by
      rw [hc2]
      exact c.pair.s11s_caseB_elem hq hq1 hqm
    have h2 := congrArg (fun y : ↥(K1 ⊔ K2) => (y : G)) h
    simpa only [Subgroup.coe_mul, c.embB_neg_one] using h2
  have hcomm : c1 * (c2 : G) = (c2 : G) * c1 :=
    c.s11s_pair_comm c1 hc1K1 (c2 : G) hc2K2
  have heK : e ∈ K1 ⊔ K2 := by
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc1K1) (Subgroup.mem_sup_right hc2K2)
  have he2 : e * e = 1 := by
    rw [he]
    calc c1 * (c2 : G) * (c1 * (c2 : G))
        = c1 * ((c2 : G) * c1) * (c2 : G) := by group
      _ = c1 * (c1 * (c2 : G)) * (c2 : G) := by rw [← hcomm]
      _ = (c1 * c1) * ((c2 : G) * (c2 : G)) := by group
      _ = z * z := by rw [hc1sq, hc2sq]
      _ = 1 := c.q8.z_sq
  have hez : e ∉ zpowers z := by
    intro hez
    have heK2 : e ∈ K2 := Subgroup.zpowers_le.mpr c.z_K2 hez
    have hc1K2 : c1 ∈ K2 := by
      have h : c1 = e * (c2 : G)⁻¹ := by rw [he]; group
      rw [h]
      exact K2.mul_mem heK2 (K2.inv_mem hc2K2)
    exact hsb (c.inf c1 hc1K1 hc1K2)
  exact ⟨heK, he2, hez⟩

theorem caseB_u {s b : G} (hsR : s ∈ R) (hs2 : s * s = 1)
    (hQ1 : ∀ q ∈ twoCoreIn K1, s * q * s⁻¹ ∈ twoCoreIn K1) (hb : b ∈ twoCoreIn K1) {q : SL23}
    (hψ : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2),
      ρ ⟨s, hsR⟩ y = c.pair.embB q * y * (c.pair.embB q)⁻¹) :
    ∃ k ∈ secKD (secD K1 K2 R), ∃ m ∈ oddCoreIn (secK0 t z),
      s * k⁻¹ * s * k = m * (s * b * s⁻¹ * b⁻¹ *
        (((c.pair.embB q * c.pair.embB (K5.k5g 0) * (c.pair.embB q)⁻¹)⁻¹ * c.pair.embB (K5.k5g 0) :
          ↥(K1 ⊔ K2)) : G)) := by
  set ω : ↥(K1 ⊔ K2) := c.pair.embB (K5.k5g 0) with hω
  set ω' : ↥(K1 ⊔ K2) := c.pair.embB q * ω * (c.pair.embB q)⁻¹ with hω'
  set b' : ↥(K1 ⊔ K2) :=
    ⟨b⁻¹, Subgroup.mem_sup_left (twoCoreIn_le_self K1 (inv_mem hb))⟩ with hb'
  set κ : ↥(K1 ⊔ K2) := b' * ω with hκ
  obtain ⟨k, hk, n, hn, hkn⟩ := c.rho.lift κ
  obtain ⟨n', hn', hact⟩ := c.rho.act ⟨s, hsR⟩ k n κ hk hn hkn
  refine ⟨k, hk, n'⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hn') hn, ?_⟩
  have hb'Q : (b' : G) ∈ secQ K1 K2 :=
    c.Q1_le_Q (show b⁻¹ ∈ twoCoreIn K1 from inv_mem hb)
  have hWK2 : (ω : G) ∈ K2 := by
    rw [hω]
    exact Subgroup.mem_subgroupOf.mp (c.pair.embB_mem (K5.k5g 0))
  have hωB : ω ∈ K2.subgroupOf (K1 ⊔ K2) := Subgroup.mem_subgroupOf.mpr hWK2
  have hW'B : ω' ∈ K2.subgroupOf (K1 ⊔ K2) := by
    rw [hω']
    exact mul_mem (mul_mem (c.pair.embB_mem q) hωB) (inv_mem (c.pair.embB_mem q))
  have hW'K2 : (ω' : G) ∈ K2 := Subgroup.mem_subgroupOf.mp hW'B
  have hρb : ((ρ ⟨s, hsR⟩ b' : ↥(K1 ⊔ K2)) : G) = s * b⁻¹ * s⁻¹ := by
    have h := c.rho_Q ⟨s, hsR⟩ b' hb'Q
    simpa [hb'] using h
  have hρω : ρ ⟨s, hsR⟩ ω = ω' := by
    rw [hω']
    exact hψ ω hωB
  have hrhoκ : ((ρ ⟨s, hsR⟩ κ : ↥(K1 ⊔ K2)) : G) =
      (s * b⁻¹ * s⁻¹) * (ω' : G) := by
    rw [hκ, map_mul, Subgroup.coe_mul, hρb, hρω]
  have hact' : s * k * s⁻¹ = n' * ((s * b⁻¹ * s⁻¹) * (ω' : G)) := by
    rw [← hrhoκ]
    exact hact
  have hacti : s * k⁻¹ * s⁻¹ = (ω' : G)⁻¹ * (s * b * s⁻¹) * n'⁻¹ := by
    have h := congrArg Inv.inv hact'
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hk' : k = n * (b⁻¹ * (ω : G)) := by
    rw [hkn, hκ, Subgroup.coe_mul, hb']
  have hA2K1 : s * b * s⁻¹ ∈ K1 := twoCoreIn_le_self K1 (hQ1 b hb)
  have hA4K1 : b⁻¹ ∈ K1 := twoCoreIn_le_self K1 (inv_mem hb)
  have hA1K2 : (ω' : G)⁻¹ ∈ K2 := K2.inv_mem hW'K2
  have hA2K : s * b * s⁻¹ ∈ K1 ⊔ K2 := Subgroup.mem_sup_left hA2K1
  have hA1K : (ω' : G)⁻¹ ∈ K1 ⊔ K2 := Subgroup.mem_sup_right hA1K2
  have hm : n'⁻¹ * n ∈ oddCoreIn (secK0 t z) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hn') hn
  have hA2m : (s * b * s⁻¹) * (n'⁻¹ * n) = (n'⁻¹ * n) * (s * b * s⁻¹) :=
    c.set.split.comm' hm hA2K
  have hA1m : (ω' : G)⁻¹ * (n'⁻¹ * n) = (n'⁻¹ * n) * (ω' : G)⁻¹ :=
    c.set.split.comm' hm hA1K
  have hA1A2 : (ω' : G)⁻¹ * (s * b * s⁻¹) = (s * b * s⁻¹) * (ω' : G)⁻¹ :=
    (c.s11s_pair_comm (s * b * s⁻¹) hA2K1 ((ω' : G)⁻¹) hA1K2).symm
  have hA1A4 : (ω' : G)⁻¹ * b⁻¹ = b⁻¹ * (ω' : G)⁻¹ :=
    (c.s11s_pair_comm b⁻¹ hA4K1 ((ω' : G)⁻¹) hA1K2).symm
  have hc2G : ((ω'⁻¹ * ω : ↥(K1 ⊔ K2)) : G) = (ω' : G)⁻¹ * (ω : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have e1 : s * k⁻¹ * s * k =
      ((ω' : G)⁻¹ * (s * b * s⁻¹) * n'⁻¹) * (n * (b⁻¹ * (ω : G))) := by
    rw [show s * k⁻¹ * s = s * k⁻¹ * s⁻¹ by rw [inv_eq_of_mul_eq_one_left hs2]]
    rw [hacti, hk']
  have e2 : ((ω' : G)⁻¹ * (s * b * s⁻¹) * n'⁻¹) * (n * (b⁻¹ * (ω : G))) =
      (ω' : G)⁻¹ * (s * b * s⁻¹) * (n'⁻¹ * n) * (b⁻¹ * (ω : G)) := by group
  have e3 := s11s_rearrange_five (A1 := (ω' : G)⁻¹) (A2 := s * b * s⁻¹)
    (A4 := b⁻¹) (A5 := (ω : G)) (m := n'⁻¹ * n) hA2m hA1m hA1A2 hA1A4
  have hu : s * k⁻¹ * s * k =
      (n'⁻¹ * n) * (s * b * s⁻¹ * b⁻¹ * ((ω'⁻¹ * ω : ↥(K1 ⊔ K2)) : G)) := by
    rw [e1, e2, e3, ← hc2G]
  exact hu

theorem caseB {h s b : G} (hh : h ∈ centralizer ({z} : Set G)) (hs : s = h⁻¹ * t * h)
    (hsR : s ∈ R) (hQ1 : ∀ q ∈ twoCoreIn K1, s * q * s⁻¹ ∈ twoCoreIn K1)
    (hb : b ∈ twoCoreIn K1) (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z)
    {q : SL23} (hq : q ^ 4 = 1) (hq1 : q ≠ 1) (hqm : q ≠ -1)
    (hψ : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2),
      ρ ⟨s, hsR⟩ y = c.pair.embB q * y * (c.pair.embB q)⁻¹) : False := by
  have hs2 : s * s = 1 := by
    rw [hs]
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [c.t_sq]; group
  obtain ⟨k, hk, m, hm, hu⟩ := c.caseB_u hsR hs2 hQ1 hb hψ
  set e : G := s * b * s⁻¹ * b⁻¹ *
    (((c.pair.embB q * c.pair.embB (K5.k5g 0) * (c.pair.embB q)⁻¹)⁻¹ *
      c.pair.embB (K5.k5g 0) : ↥(K1 ⊔ K2)) : G) with he
  have hu' : s * k⁻¹ * s * k = m * e := hu
  obtain ⟨heK, he2, hez⟩ := c.caseB_e hQ1 hb hsb hq hq1 hqm he
  have hme : m * e = e * m := (c.set.split.comm' hm heK).symm
  have hmo : Odd (orderOf m) := odd_orderOf_of_mem_oddCoreIn hm
  obtain ⟨j, hj, hse⟩ := s11s_dihedral_trick hs2 hu' hme he2 hmo
  set Kx : G := k * (s * k⁻¹ * s * k) ^ j with hKx
  have hkC : k ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyz : y = z := by simpa using hy
    rw [hyz]
    exact Subgroup.mem_centralizer_iff.mp (sec11c_oTwoRes_le _ hk) z c.z_D
  have hsC : s ∈ centralizer ({z} : Set G) := c.R_H hsR
  have huC : s * k⁻¹ * s * k ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (mul_mem hsC (inv_mem hkC)) hsC) hkC
  have hKxC : Kx ∈ centralizer ({z} : Set G) := by
    rw [hKx]
    exact mul_mem hkC (pow_mem huC j)
  set g : G := h * Kx with hg
  have hgC : g ∈ centralizer ({z} : Set G) := by
    rw [hg]
    exact mul_mem hh hKxC
  have hgconj : g⁻¹ * t * g = s * e := by
    rw [hg]
    calc (h * Kx)⁻¹ * t * (h * Kx) = Kx⁻¹ * (h⁻¹ * t * h) * Kx := by group
      _ = Kx⁻¹ * s * Kx := by rw [← hs]
      _ = s * e := hj
  have hprem : (s * e) * s = s * (s * e) := by
    rw [show (s * e) * s = s * (e * s) by group, ← hse]
  have hstar := c.star h hh g hgC (by rw [hgconj, ← hs]; exact hprem)
  rw [hgconj, ← hs] at hstar
  have hemem : e ∈ zpowers z := by
    rcases hstar with h1 | h1
    · have he1 : e = 1 := by
        calc e = s * (s * e) := by rw [← mul_assoc, hs2, one_mul]
          _ = s * s := by rw [h1]
          _ = 1 := hs2
      rw [he1]
      exact one_mem _
    · have hez1 : e = z := by
        calc e = s * (s * e) := by rw [← mul_assoc, hs2, one_mul]
          _ = s * (s * z) := by rw [h1]
          _ = z := by rw [← mul_assoc, hs2, one_mul]
      rw [hez1]
      exact Subgroup.mem_zpowers z
  exact hez hemem

end S11sCtx

end CFSG.OddStandard.SmallF3.Omega
