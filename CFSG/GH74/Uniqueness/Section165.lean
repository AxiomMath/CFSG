module

public import CFSG.GH74.Uniqueness.Section165Defs
public import CFSG.GH74.Uniqueness.Section165Conf
public import CFSG.GH74.Uniqueness.Section165G
public import CFSG.GH74.Uniqueness.Section165Field
public import CFSG.GH74.Uniqueness.Section165K

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

omit [Finite X] in
theorem mem_of_mul_self_mem {H : Subgroup X} {x : X} (hx : Odd (orderOf x)) (hxx : x * x ∈ H) :
    x ∈ H := by
  obtain ⟨j, hj⟩ := hx
  have e : x = (x * x) ^ (j + 1) := by
    rw [← sq, ← pow_mul, show 2 * (j + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact pow_mem hxx _

omit [Finite X] in
theorem mem_commutator_of_inverted (hZ : IsInvariantInvolutionSet Z) {t y x : X} (ht : t ∈ Z)
    (hty : t * y = y * t) {D : Subgroup X} (hxD : x ∈ D) (hxy : x * y = y * x)
    (hxt : t * x * t⁻¹ = x⁻¹) (hodd : Odd (orderOf x)) :
    x ∈ ⁅zpowers t, D ⊓ cenHull Z y⁆ := by
  have htC : t ∈ cenHull Z y := subset_closure ⟨ht, mem_centralizer_singleton_iff.mpr hty⟩
  have hxN : x ∈ normalizer (cenHull Z y : Set X) :=
    le_normalizer_zHull hZ _ (mem_centralizer_singleton_iff.mpr hxy)
  have hcomm : ⁅t, x⁆ = x⁻¹ * x⁻¹ := by
    rw [commutatorElement_def, hxt]
  have hcC : ⁅t, x⁆ ∈ cenHull Z y := by
    rw [commutatorElement_def]
    have h1 : x * t⁻¹ * x⁻¹ ∈ cenHull Z y := (mem_normalizer_iff.mp hxN t⁻¹).mp (inv_mem htC)
    have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem htC h1
  have hxC : x ∈ cenHull Z y := by
    refine mem_of_mul_self_mem hodd ?_
    have : (x⁻¹ * x⁻¹)⁻¹ ∈ cenHull Z y := inv_mem (hcomm ▸ hcC)
    simpa [mul_inv_rev] using this
  have hmem : ⁅t, x⁆ ∈ ⁅zpowers t, D ⊓ cenHull Z y⁆ :=
    commutator_mem_commutator (mem_zpowers t) (mem_inf.mpr ⟨hxD, hxC⟩)
  refine mem_of_mul_self_mem hodd ?_
  have : (x⁻¹ * x⁻¹)⁻¹ ∈ ⁅zpowers t, D ⊓ cenHull Z y⁆ := inv_mem (hcomm ▸ hmem)
  simpa [mul_inv_rev] using this

theorem false_of_four
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M) (h164 : Lemma164Stmt Z M)
    (hgap : Prop165TuvStmt Z M) (c₀ : Conf16 Z M)
    (hV : ∃ V : Subgroup X, V ≤ c₀.D ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1) : False := by
  obtain ⟨c, -, v, hvD, hv2, hv1, hvu, huv, hvt, hvz⟩ := exists_conf_four S c₀ hV
  obtain ⟨⟨n, i, e, hB⟩, -, -, -⟩ := h163 c
  have hu164 := (h164 c n i e hB).1.2
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  obtain ⟨w, hwD, hw2, hw1, hwu, huw, hwt, hwz, huN, k', hk', hFT, hniu, hisou⟩ :=
    exists_16H S h121 h161 h162 h163 c hvD hv2 hv1 hvu huv hvt hvz
  obtain ⟨hwN, -, k, hk, hB0T, hniw, hisow⟩ := B0_structure S h162 c hB hu164 hw2 hw1 hwu huw hwt hwz
  have hw2o : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hwM : w ∈ M := (mem_inf.mp hwD).1
  have hCM : ¬ centralizer ({w} : Set X) ≤ M := fun h =>
    c.htM (h (mem_centralizer_singleton_iff.mpr hwt.symm))
  obtain ⟨n', i', e', hBw⟩ := S.benderSub_exists (S.cor714_centralizer_ne_top hw2o) hCM
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwz.symm, c.hzM⟩⟩
    (not_solvable_of_commute_t h163 c hwM hw2o hwt)
  have hkk : k = k' := eq_of_fixed S c hB hwN hwz hwt hk hisow huN hBw.invol hk' hisou
  subst hkk
  set p := Nat.minFac (2 ^ k + 1) with hp
  have hp1 : 2 ^ k + 1 ≠ 1 := by
    have : 0 < 2 ^ k := by positivity
    omega
  have hpp : p.Prime := Nat.minFac_prime hp1
  have hpk : p ∣ 2 ^ k + 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpk
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    omega
  have : Fact p.Prime := ⟨hpp⟩
  have hpodd : Odd p := hpp.odd_of_ne_two hp2
  obtain ⟨x, hxDB, hxo, hxt, hxw⟩ := exists_inverted_of_outer S hk hB0T c.hz c.hzM
    (Sec164.z_mem_B0 c) c.htM (Sec164.t_mem_B0 c) ht2 hwN hwD hw2 hwz hniw hisow hpp hp2 hpk
  have hzF : c.z ∈ cenHull Z w :=
    subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr hwz.symm⟩
  have htF : c.t ∈ cenHull Z w :=
    subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr hwt.symm⟩
  obtain ⟨x', hx'DF, hx'o, hx't, hx'u⟩ := exists_inverted_of_outer S hk hFT c.hz c.hzM hzF c.htM
    htF ht2 huN c.hu c.u_mul_self huz hniu hisou hpp hp2 hpk
  have hxD := (mem_inf.mp hxDB).1
  have hxB := (mem_inf.mp hxDB).2
  have hx'D := (mem_inf.mp hx'DF).1
  have hx'F := (mem_inf.mp hx'DF).2
  have hxu : x * c.u = c.u * x := mem_centralizer_singleton_iff.mp (Sec164.B0_le_B c hxB)
  have hx'w : x' * w = w * x' := mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ hx'F)
  set y := c.t * c.u * w with hy
  have hcomm_of_conj : ∀ g : X, y * g * y⁻¹ = g → g * y = y * g := by
    intro g hg
    calc g * y = (y * g * y⁻¹) * y := by rw [hg]
      _ = y * g := by group
  have hxu' : c.u * x⁻¹ * c.u⁻¹ = x⁻¹ := by
    calc c.u * x⁻¹ * c.u⁻¹ = (x * c.u * c.u⁻¹)⁻¹ * (c.u * c.u⁻¹) := by rw [hxu]; group
      _ = x⁻¹ := by group
  have hxt' : c.t * x⁻¹ * c.t⁻¹ = x := by
    calc c.t * x⁻¹ * c.t⁻¹ = (c.t * x * c.t⁻¹)⁻¹ := by group
      _ = x := by rw [hxt, inv_inv]
  have hxy : x * y = y * x := by
    refine hcomm_of_conj x ?_
    calc y * x * y⁻¹ = c.t * (c.u * (w * x * w⁻¹) * c.u⁻¹) * c.t⁻¹ := by rw [hy]; group
      _ = c.t * (c.u * x⁻¹ * c.u⁻¹) * c.t⁻¹ := by rw [hxw]
      _ = c.t * x⁻¹ * c.t⁻¹ := by rw [hxu']
      _ = x := hxt'
  have hx'w' : w * x' * w⁻¹ = x' := by
    calc w * x' * w⁻¹ = (x' * w) * w⁻¹ := by rw [hx'w]
      _ = x' := by group
  have hx'u' : c.u * x' * c.u⁻¹ = x'⁻¹ := hx'u
  have hx't' : c.t * x'⁻¹ * c.t⁻¹ = x' := by
    calc c.t * x'⁻¹ * c.t⁻¹ = (c.t * x' * c.t⁻¹)⁻¹ := by group
      _ = x' := by rw [hx't, inv_inv]
  have hx'y : x' * y = y * x' := by
    refine hcomm_of_conj x' ?_
    calc y * x' * y⁻¹ = c.t * (c.u * (w * x' * w⁻¹) * c.u⁻¹) * c.t⁻¹ := by rw [hy]; group
      _ = c.t * (c.u * x' * c.u⁻¹) * c.t⁻¹ := by rw [hx'w']
      _ = c.t * x'⁻¹ * c.t⁻¹ := by rw [hx'u']
      _ = x' := hx't'
  have hty : c.t * y = y * c.t := by
    rw [hy]
    calc c.t * (c.t * c.u * w) = c.t * (c.t * c.u) * w := by group
      _ = c.t * (c.u * c.t) * w := by rw [hut]
      _ = c.t * c.u * (c.t * w) := by group
      _ = c.t * c.u * (w * c.t) := by rw [hwt]
      _ = c.t * c.u * w * c.t := by group
  have hcyc := hgap c w hwD hw2o huw.symm hwt hwz
  have hxodd : Odd (orderOf x) := by rw [hxo]; exact hpodd
  have hx'odd : Odd (orderOf x') := by rw [hx'o]; exact hpodd
  have hxG := mem_commutator_of_inverted S.invariant c.ht hty hxD hxy hxt hxodd
  have hx'G := mem_commutator_of_inverted S.invariant c.ht hty hx'D hx'y hx't hx'odd
  have heq : zpowers x = zpowers x' := Bender.eq_of_card_eq_of_cyclic hcyc
    (zpowers_le.mpr hxG) (zpowers_le.mpr hx'G) (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hx'o])
  have hx'x : x' ∈ zpowers x := heq ▸ mem_zpowers x'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hx'x
  have hux' : c.u * x' * c.u⁻¹ = x' := by
    rw [← hj, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [show c.u * x * c.u⁻¹ = x by rw [← hxu]; group]
  rw [hux'] at hx'u
  have hx'2 : x' * x' = 1 := by
    calc x' * x' = x' * x'⁻¹ := by rw [← hx'u]
      _ = 1 := mul_inv_cancel x'
  have hdvd : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx'2)
  rw [hx'o] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hdvd)

omit [Finite X] in
theorem isElemAbelian_zpowers_two {x : X} (hx : orderOf x = 2) :
    Open.IsElemAbelian 2 (zpowers x) := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

end Sec165

theorem ZDSetup.prop165
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M) (h164 : Lemma164Stmt Z M)
    (hgap : Prop165TuvStmt Z M) : Prop165Stmt Z M := by
  intro c
  refine le_antisymm ?_ ?_
  · by_contra hge
    push Not at hge
    obtain ⟨a, b, haD, hbD, ha2, hb2, hab, hcomm⟩ :=
      exists_commuting_involutions_of_two_le_pRank (Nat.succ_le_of_lt hge)
    have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
    have hbb : b * b = 1 := by rw [← sq, ← hb2, pow_orderOf_eq_one]
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; omega
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; omega
    exact Sec165.false_of_four S h121 h161 h162 h163 h164 hgap c
      ⟨fourSub a b haa hbb hcomm, fourSub_le haD hbD, card_fourSub ha1 hb1 hab,
        mul_self_of_mem_fourSub⟩
  · exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (E := zpowers c.u)
      (zpowers_le.mpr c.hu) (Sec165.isElemAbelian_zpowers_two c.hu2) (k := 1)
      (by rw [Nat.card_zpowers, c.hu2, pow_one])

end CFSG.GH74.Uniqueness
