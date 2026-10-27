module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ConjV7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace P49T

section Abstract

variable {X : Type} [Group X]

theorem sq_of_four {U : Subgroup X} (hU : IVK.IsFourSubgroup U) {x : X} (hx : x ∈ U) :
    x * x = 1 := by
  have := hU.1
  simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx

theorem comm_of_four {U : Subgroup X} (hU : IVK.IsFourSubgroup U) {x y : X} (hx : x ∈ U)
    (hy : y ∈ U) : x * y = y * x := by
  have := hU.1.toIsMulCommutative
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)

theorem three_cycle {U : Subgroup X} (hU : IVK.IsFourSubgroup U) {a b : X}
    (ha : ∀ x ∈ U, a * x * a⁻¹ ∈ U) (hb : ∀ x ∈ U, b * x * b⁻¹ ∈ U) (hb2 : b * b = 1)
    (hnt : ∃ x ∈ U, a * x * a⁻¹ ≠ x)
    (hd : ∃ x ∈ U, a * x * a⁻¹ = x ∧ b * x * b⁻¹ ≠ x) :
    ∃ x ∈ U, ∀ m : ℕ, ¬ 3 ∣ m → (a * b) ^ m * x * ((a * b) ^ m)⁻¹ ≠ x := by
  obtain ⟨w0, hw0, haw0, hbw0⟩ := hd
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  set u1 := b * w0 * b⁻¹ with hu1def
  have hu1U : u1 ∈ U := hb w0 hw0
  have hw01 : w0 ≠ 1 := by
    intro h
    apply hbw0
    rw [hu1def, h]
    simp
  have hu11 : u1 ≠ 1 := by
    intro h
    apply hw01
    have e : w0 = b⁻¹ * u1 * b := by rw [hu1def]; group
    rw [e, h]
    group
  have hwu : w0 ≠ u1 := fun h => hbw0 h.symm
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => sq_of_four hU hx
  have hmem : ∀ x ∈ U, x = 1 ∨ x = w0 ∨ x = u1 ∨ x = w0 * u1 := fun x hx =>
    (CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hU.2 hsq hw0 hu1U hw01 hu11 hwu x).1 hx
  have hw0inv : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right (hsq w0 hw0)
  have hu1inv : u1⁻¹ = u1 := inv_eq_of_mul_eq_one_right (hsq u1 hu1U)
  have hcomm : w0 * u1 = u1 * w0 := comm_of_four hU hw0 hu1U
  have hau1 : a * u1 * a⁻¹ ≠ u1 := by
    intro h
    obtain ⟨x, hxU, hx⟩ := hnt
    apply hx
    rcases hmem x hxU with rfl | rfl | rfl | rfl
    · simp
    · exact haw0
    · exact h
    · have e : a * (w0 * u1) * a⁻¹ = (a * w0 * a⁻¹) * (a * u1 * a⁻¹) := by group
      rw [e, haw0, h]
  have hau1' : a * u1 * a⁻¹ = w0 * u1 := by
    rcases hmem _ (ha u1 hu1U) with h | h | h | h
    · exfalso
      apply hu11
      have := congrArg (fun y => a⁻¹ * y * a) h
      simpa [mul_assoc] using this
    · exfalso
      apply hwu
      have e2 : a⁻¹ * w0 * a = w0 := by
        have e3 : a⁻¹ * (a * w0 * a⁻¹) * a = w0 := by group
        have := congrArg (fun y => a⁻¹ * y * a) haw0
        rw [e3] at this
        exact this.symm
      calc w0 = a⁻¹ * w0 * a := e2.symm
        _ = a⁻¹ * (a * u1 * a⁻¹) * a := by rw [h]
        _ = u1 := by group
    · exact absurd h hau1
    · exact h
  have hs1 : (a * b) * w0 * (a * b)⁻¹ = w0 * u1 := by
    have e : (a * b) * w0 * (a * b)⁻¹ = a * (b * w0 * b⁻¹) * a⁻¹ := by group
    rw [e, ← hu1def, hau1']
  have hs2 : (a * b) * u1 * (a * b)⁻¹ = w0 := by
    have e : (a * b) * u1 * (a * b)⁻¹ = a * (b * u1 * b⁻¹) * a⁻¹ := by group
    have e2 : b * u1 * b⁻¹ = w0 := by
      rw [hu1def]
      have : b * (b * w0 * b⁻¹) * b⁻¹ = (b * b) * w0 * (b⁻¹ * b⁻¹) := by group
      rw [this, hb2, hbinv, hb2]
      simp
    rw [e, e2, haw0]
  have hs3 : (a * b) * (w0 * u1) * (a * b)⁻¹ = u1 := by
    have e : (a * b) * (w0 * u1) * (a * b)⁻¹ =
        ((a * b) * w0 * (a * b)⁻¹) * ((a * b) * u1 * (a * b)⁻¹) := by group
    rw [e, hs1, hs2, hcomm, mul_assoc, hsq w0 hw0, mul_one]
  let f : MulAut X := MulAut.conj (a * b)
  have hf : ∀ k : ℕ, ∀ x : X, (f ^ k) x = (a * b) ^ k * x * ((a * b) ^ k)⁻¹ := by
    intro k x
    simp only [f, ← map_pow, MulAut.conj_apply]
  have f1 : f w0 = w0 * u1 := hs1
  have f2 : f u1 = w0 := hs2
  have f3 : f (w0 * u1) = u1 := hs3
  have f3w : (f ^ 3) w0 = w0 := by
    rw [pow_succ', pow_succ', pow_one]
    simp only [MulAut.mul_apply]
    rw [f1, f3, f2]
  have hper : ∀ q r : ℕ, (f ^ (r + 3 * q)) w0 = (f ^ r) w0 := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have : r + 3 * (q + 1) = (r + 3 * q) + 3 := by ring
      rw [this, pow_add]
      simp only [MulAut.mul_apply]
      rw [f3w, ih]
  refine ⟨w0, hw0, fun m hm => ?_⟩
  rw [← hf m w0]
  have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hmd : m = m % 3 + 3 * (m / 3) := by omega
  have key := hper (m / 3) (m % 3)
  rw [← hmd] at key
  rw [key]
  rcases hm' with h | h
  · rw [h, pow_one, f1]
    intro h1
    apply hu11
    have : w0 * u1 = w0 * 1 := by rw [mul_one]; exact h1
    exact mul_left_cancel this
  · rw [h, pow_two]
    simp only [MulAut.mul_apply]
    rw [f1, f3]
    exact fun h1 => hwu h1.symm

theorem conj_comm {c z h₀ y : X} (hc : c * z * c⁻¹ = h₀) (h : y * h₀ = h₀ * y) :
    (c⁻¹ * y * c) * z = z * (c⁻¹ * y * c) := by
  have hz' : z = c⁻¹ * h₀ * c := by rw [← hc]; group
  rw [hz']
  have e1 : c⁻¹ * y * c * (c⁻¹ * h₀ * c) = c⁻¹ * (y * h₀) * c := by group
  have e2 : c⁻¹ * h₀ * c * (c⁻¹ * y * c) = c⁻¹ * (h₀ * y) * c := by group
  rw [e1, e2, h]

end Abstract

end P49T

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {U : Subgroup G}

theorem transport49 {h₀ t t' : G} (hz : IsConj z h₀) (hU4 : IVK.IsFourSubgroup U)
    (_h₀2 : orderOf h₀ = 2) (t2 : orderOf t = 2) (t'2 : orderOf t' = 2)
    (hh₀U : ∀ w ∈ U, h₀ * w = w * h₀) (hh₀t : h₀ * t = t * h₀) (hh₀t' : h₀ * t' = t' * h₀)
    (htU : ∀ w ∈ U, t * w * t⁻¹ ∈ U) (ht'U : ∀ w ∈ U, t' * w * t'⁻¹ ∈ U)
    (ht : ∃ w ∈ U, t * w * t⁻¹ ≠ w) (_ht' : ∃ w ∈ U, t' * w * t'⁻¹ ≠ w)
    (hdist : ∃ w ∈ U, t * w * t⁻¹ = w ∧ t' * w * t'⁻¹ ≠ w) :
    ∃ (V : Subgroup (CentralizerBar z)) (c : CentralizerBar z),
      IVK.IsFourSubgroup V ∧ V ≤ oPrimeResidual 2 (CentralizerBar z) ∧
      c ∈ oPrimeResidual 2 (CentralizerBar z) ∧ IsPGroup 3 ↥(zpowers c) ∧
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) ∧ ∃ v ∈ V, c * v * c⁻¹ ≠ v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hz
  set U' := conjugate U c with hU'
  have hU'4 : IVK.IsFourSubgroup U' := isFour_conjugate c hU4
  have hmemU' : ∀ x, x ∈ U' ↔ c * x * c⁻¹ ∈ U := fun x => mem_conjugate_iff
  set a := c⁻¹ * t * c with ha_def
  set b := c⁻¹ * t' * c with hb_def
  have hsq : ∀ s : G, orderOf s = 2 → s * s = 1 := fun s hs => by
    have := pow_orderOf_eq_one s
    rw [hs] at this
    simpa [pow_two] using this
  have ht2 : t * t = 1 := hsq t t2
  have ht'2 : t' * t' = 1 := hsq t' t'2
  have ha2 : a * a = 1 := by
    have e : a * a = c⁻¹ * (t * t) * c := by rw [ha_def]; group
    rw [e, ht2]; group
  have hb2 : b * b = 1 := by
    have e : b * b = c⁻¹ * (t' * t') * c := by rw [hb_def]; group
    rw [e, ht'2]; group
  have haz : a * z = z * a := P49T.conj_comm hc hh₀t.symm
  have hbz : b * z = z * b := P49T.conj_comm hc hh₀t'.symm
  have hU'le : U' ≤ Cen z := by
    intro x hx
    have h1 : h₀ * (c * x * c⁻¹) = (c * x * c⁻¹) * h₀ := hh₀U _ ((hmemU' x).1 hx)
    have h2 := P49T.conj_comm hc h1.symm
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [e] at h2
    exact Subgroup.mem_centralizer_singleton_iff.2 h2
  have haC : a ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.2 haz
  have hbC : b ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.2 hbz
  have ha : ∀ x ∈ U', a * x * a⁻¹ ∈ U' := by
    intro x hx
    rw [hmemU']
    have e : c * (a * x * a⁻¹) * c⁻¹ = t * (c * x * c⁻¹) * t⁻¹ := by rw [ha_def]; group
    rw [e]
    exact htU _ ((hmemU' x).1 hx)
  have hb : ∀ x ∈ U', b * x * b⁻¹ ∈ U' := by
    intro x hx
    rw [hmemU']
    have e : c * (b * x * b⁻¹) * c⁻¹ = t' * (c * x * c⁻¹) * t'⁻¹ := by rw [hb_def]; group
    rw [e]
    exact ht'U _ ((hmemU' x).1 hx)
  have hnt : ∃ x ∈ U', a * x * a⁻¹ ≠ x := by
    obtain ⟨w, hwU, hw⟩ := ht
    refine ⟨c⁻¹ * w * c, ?_, ?_⟩
    · rw [hmemU']
      have e : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
      rwa [e]
    · intro h
      apply hw
      have e : c * (a * (c⁻¹ * w * c) * a⁻¹) * c⁻¹ = t * w * t⁻¹ := by rw [ha_def]; group
      have e' : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
      have := congrArg (fun y => c * y * c⁻¹) h
      rw [e, e'] at this
      exact this
  have hd : ∃ x ∈ U', a * x * a⁻¹ = x ∧ b * x * b⁻¹ ≠ x := by
    obtain ⟨w, hwU, hw, hw'⟩ := hdist
    refine ⟨c⁻¹ * w * c, ?_, ?_, ?_⟩
    · rw [hmemU']
      have e : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
      rwa [e]
    · have e : a * (c⁻¹ * w * c) * a⁻¹ = c⁻¹ * (t * w * t⁻¹) * c := by rw [ha_def]; group
      rw [e, hw]
    · intro h
      apply hw'
      have e : c * (b * (c⁻¹ * w * c) * b⁻¹) * c⁻¹ = t' * w * t'⁻¹ := by rw [hb_def]; group
      have e' : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
      have := congrArg (fun y => c * y * c⁻¹) h
      rw [e, e'] at this
      exact this
  obtain ⟨x, hxU', hx⟩ := P49T.three_cycle hU'4 ha hb hb2 hnt hd
  have hnormU' : ∀ k : ℕ, ∀ y ∈ U', (a * b) ^ k * y * ((a * b) ^ k)⁻¹ ∈ U' := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have e : (a * b) ^ (k + 1) * y * ((a * b) ^ (k + 1))⁻¹ =
          a * (b * ((a * b) ^ k * y * ((a * b) ^ k)⁻¹) * b⁻¹) * a⁻¹ := by
        rw [pow_succ']
        generalize (a * b) ^ k = P
        group
      rw [e]
      exact ha _ (hb _ (ih y hy))
  let aC : ↥(Cen z) := ⟨a, haC⟩
  let bC : ↥(Cen z) := ⟨b, hbC⟩
  let wC : ↥(Cen z) := aC * bC
  have hwCpow : ∀ k : ℕ, (((wC ^ k : ↥(Cen z))) : G) = (a * b) ^ k := fun k => by
    simp [wC, aC, bC]
  have hn0 : orderOf wC ≠ 0 := (orderOf_pos wC).ne'
  obtain ⟨e, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  let c3 : ↥(Cen z) := wC ^ m
  let cbar : CentralizerBar z := toBar z c3
  have hc3pow : cbar ^ (3 ^ e) = 1 := by
    have h1 : c3 ^ (3 ^ e) = 1 := by
      show (wC ^ m) ^ (3 ^ e) = 1
      rw [← pow_mul, mul_comm, ← hnm]
      exact pow_orderOf_eq_one wC
    simp only [cbar, ← map_pow, h1, map_one]
  have hcbar3 : IsPGroup 3 ↥(zpowers cbar) := by
    apply IsPGroup.of_card_dvd_pow (n := e)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc3pow
  have hgen : ∀ y : CentralizerBar z, y ^ 2 = 1 → y ∈ oPrimeResidual 2 (CentralizerBar z) :=
    fun y hy => Subgroup.subset_closure ⟨1, by rw [pow_one]; exact hy⟩
  have hA2 : toBar z aC ^ 2 = 1 := by
    have : aC ^ 2 = 1 := Subtype.ext (by simp [aC, pow_two, ha2])
    rw [← map_pow, this, map_one]
  have hB2 : toBar z bC ^ 2 = 1 := by
    have : bC ^ 2 = 1 := Subtype.ext (by simp [bC, pow_two, hb2])
    rw [← map_pow, this, map_one]
  have hcbarmem : cbar ∈ oPrimeResidual 2 (CentralizerBar z) := by
    have : cbar = (toBar z aC * toBar z bC) ^ m := by
      simp only [cbar, c3, wC, map_pow, map_mul]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgen _ hA2) (hgen _ hB2)) m
  have hVle : barOf z U' ≤ oPrimeResidual 2 (CentralizerBar z) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    have hu' : (u : G) ∈ U' := Subgroup.mem_subgroupOf.1 hu
    have : u ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using P49T.sq_of_four hU'4 hu')
    apply hgen
    rw [← map_pow, this, map_one]
  have hcoe : ∀ u : ↥(Cen z), ((c3 * u * c3⁻¹ : ↥(Cen z)) : G) = (a * b) ^ m * (u : G) * ((a * b) ^ m)⁻¹ := by
    intro u
    simp only [c3, Subgroup.coe_mul, Subgroup.coe_inv, hwCpow]
  have hconj : ∀ u : ↥(Cen z), cbar * toBar z u * cbar⁻¹ = toBar z (c3 * u * c3⁻¹) := by
    intro u
    simp [cbar]
  have hnormV : ∀ v ∈ barOf z U', cbar * v * cbar⁻¹ ∈ barOf z U' := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    have hu' : (u : G) ∈ U' := Subgroup.mem_subgroupOf.1 hu
    rw [hconj]
    refine Subgroup.mem_map.2 ⟨c3 * u * c3⁻¹, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    rw [hcoe]
    exact hnormU' m _ hu'
  refine ⟨barOf z U', cbar, isFour_barOf z hU'le hU'4, hVle, hcbarmem, hcbar3, hnormV, ?_⟩
  let xC : ↥(Cen z) := ⟨x, hU'le hxU'⟩
  refine ⟨toBar z xC, Subgroup.mem_map.2 ⟨xC, Subgroup.mem_subgroupOf.2 hxU', rfl⟩, ?_⟩
  intro h
  rw [hconj] at h
  have h1 : toBar z ((c3 * xC * c3⁻¹) * xC⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hp : (a * b) ^ m * x * ((a * b) ^ m)⁻¹ ∈ U' := hnormU' m x hxU'
  have hq : (a * b) ^ m * x * ((a * b) ^ m)⁻¹ * x⁻¹ ∈ U' := U'.mul_mem hp (U'.inv_mem hxU')
  have hsq1 : ((c3 * xC * c3⁻¹) * xC⁻¹) ^ 2 = 1 := by
    apply Subtype.ext
    have := P49T.sq_of_four hU'4 hq
    simpa [pow_two, hcoe, xC] using this
  have h2 := eq_one_of_toBar_eq_one z hsq1 h1
  have h3 : (a * b) ^ m * x * ((a * b) ^ m)⁻¹ * x⁻¹ = 1 := by
    have := congrArg (fun y : ↥(Cen z) => (y : G)) h2
    simpa [hcoe, xC] using this
  apply hx m hm3
  exact mul_inv_eq_one.1 h3

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
