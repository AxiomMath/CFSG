module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem late_exists_pow_involE {b : G} (hb : IsPGroup 2 ↥(Subgroup.zpowers b)) (hb1 : b ≠ 1) :
    ∃ n : ℕ, b ^ n * b ^ n = 1 ∧ b ^ n ≠ 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hb) ⟨b, Subgroup.mem_zpowers b⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hb1
    · exact h0
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨2 ^ m, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk, pow_succ]
    have : 0 < 2 ^ m := by positivity
    omega

end Elementary

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

omit [Finite G] in
theorem late_mem_cmoE {H L : Subgroup G} {x : G} :
    x ∈ centralizerModOdd H L ↔ x ∈ H ∧ x ∈ Subgroup.normalizer (L : Set G) ∧
      x ∈ Subgroup.normalizer (oddCoreOf L : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oddCoreOf L := Iff.rfl

structure Std20G (K K' J : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G) (z t : G) :
    Prop extends Std20F K K' J S R R' W V z t where
  late_hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  late_t_mem_W : t ∈ W
  late_z_mem_W : z ∈ W
  late_hW : W = (W ⊓ K) ⊔ (W ⊓ J)
  late_JW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)
  late_exists_swap : ∃ u ∈ (S : Subgroup G), conjSub u K = K'
  late_swap_data : ∀ {u : G}, u ∈ (S : Subgroup G) → conjSub u K = K' →
    conjSub u K' = K ∧ conjSub u R = R' ∧ conjSub u W = W ∧ conjSub u (S : Subgroup G) = S

theorem Std20G.late_R'_le_cmo (d : Std20G K K' J S R R' W V z t) :
    R' ≤ centralizerModOdd (S : Subgroup G) K := by
  intro x hx
  have hxK' : x ∈ K' := d.hR'.1 hx
  rw [late_mem_cmoE]
  refine ⟨d.hR'S hx, d.late_K'_le hxK',
    Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (d.late_K'_le hxK'),
    fun k hk => ?_⟩
  have h := (Sec6Gen.comm_le_oddCore_of_twin d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm
    d.viol.hzK d.late_hzK' (Subgroup.commutator_mem_commutator hk hxK')).1
  have := (oddCoreOf K).inv_mem h
  rwa [commutatorElement_inv] at this

theorem Std20G.late_cmo_comm_W (d : Std20G K K' J S R R' W V z t) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) : ∀ w ∈ W ⊓ K, x * w = w * x := by
  intro w hw
  obtain ⟨hxS, -, -, hxc⟩ := late_mem_cmoE.mp hx
  have h1 : ⁅x, w⁆ ∈ oddCoreOf K := hxc w hw.2
  have h2 : ⁅x, w⁆ ∈ W := by
    have hxw : x * w * x⁻¹ ∈ W := by
      have := conj_mem_conjSub (n := x) hw.1
      rwa [mem_normalizer_iff_conjSub_eq.mp (d.hWN hxS)] at this
    rw [commutatorElement_def]
    exact W.mul_mem hxw (W.inv_mem hw.1)
  have h3 : IsPGroup 2 ↥(Subgroup.zpowers ⁅x, w⁆) :=
    S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr h2).trans d.hWS)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)

theorem Std20G.late_isSylow2In_oddK' (d : Std20G K K' J S R R' W V z t) :
    IsSylow2In R' (oddCoreOf K ⊔ K') := by
  have h := Sec7.isSylow2In_sup_of_sylow (N := oddCoreOf K) (C := K') (Q := ⊥) (V := R')
    (fun g hg => Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
      (d.late_K'_le hg))
    ⟨bot_le, IsPGroup.of_bot, fun T hT hT2 _ => by
      refine (Subgroup.eq_bot_iff_forall T).mpr fun y hy => ?_
      exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) (hT hy)
        (hT2.to_le (Subgroup.zpowers_le.mpr hy))⟩
    d.hR'
    (fun g _ => mem_normalizer_iff_conjSub_eq.mpr (by unfold conjSub; exact Subgroup.map_bot _))
    (fun g hg => by
      have : g = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hg.2
        (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hR'S hg.1)))
      rw [this]
      exact Subgroup.one_mem _)
  rwa [bot_sup_eq] at h

theorem Std20G.late_kappa (d : Std20G K K' J S R R' W V z t) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t := by
  obtain ⟨hxS, hxN, -, hxc⟩ := late_mem_cmoE.mp hx
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hxS
  have hxK : conjSub x K = K := mem_normalizer_iff_conjSub_eq.mp hxN
  have hxK' : conjSub x K' = K' := (d.late_conj_iff hxz).mp hxK
  have htW := d.late_t_mem_W
  have htS : t ∈ (S : Subgroup G) := d.hWS htW
  have ht : t ∈ K' ⊔ K := by rw [sup_comm]; exact d.htKK
  obtain ⟨k', hk', k, hk, htk⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer d.late_K_le ht
  have hk'1 : x * k' * x⁻¹ ∈ K' := by
    have := conj_mem_conjSub (n := x) hk'
    rwa [hxK'] at this
  have hc : ⁅x, k⁆ ∈ oddCoreOf K := hxc k hk
  have hc' : k' * ⁅x, k⁆ * k'⁻¹ ∈ oddCoreOf K :=
    CFSG.ClassicalInvolution.Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer
      (d.late_K'_le hk') hc
  have hκmem : (x * t * x⁻¹) * t⁻¹ ∈ oddCoreOf K ⊔ K' := by
    have e : (x * t * x⁻¹) * t⁻¹ = (x * k' * x⁻¹ * k'⁻¹) * (k' * ⁅x, k⁆ * k'⁻¹) := by
      rw [htk, commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K'.mul_mem hk'1 (K'.inv_mem hk')))
      (Subgroup.mem_sup_left hc')
  have hκS : (x * t * x⁻¹) * t⁻¹ ∈ (S : Subgroup G) :=
    S.mul_mem (S.mul_mem (S.mul_mem hxS htS) (S.inv_mem hxS)) (S.inv_mem htS)
  have hSR' : (S : Subgroup G) ⊓ (oddCoreOf K ⊔ K') = R' :=
    d.late_isSylow2In_oddK'.eq_of_le (S.isPGroup'.to_le inf_le_left) inf_le_right
      (le_inf d.hR'S (d.hR'.1.trans le_sup_right))
  have hκR' : (x * t * x⁻¹) * t⁻¹ ∈ R' := by rw [← hSR']; exact ⟨hκS, hκmem⟩
  have hxtW : x * t * x⁻¹ ∈ W := by
    have := conj_mem_conjSub (n := x) htW
    rwa [mem_normalizer_iff_conjSub_eq.mp (d.hWN hxS)] at this
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) := d.late_hWc _ hxtW t htW
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right d.viol.hzJ.sq
  have hsq1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [d.viol.hzJ.sq]; group
  have hκsq : ((x * t * x⁻¹) * t⁻¹) * ((x * t * x⁻¹) * t⁻¹) = 1 := by
    rw [hti]
    calc (x * t * x⁻¹ * t) * (x * t * x⁻¹ * t)
        = (x * t * x⁻¹) * (t * (x * t * x⁻¹)) * t := by group
      _ = (x * t * x⁻¹) * ((x * t * x⁻¹) * t) * t := by rw [hcomm]
      _ = ((x * t * x⁻¹) * (x * t * x⁻¹)) * (t * t) := by group
      _ = 1 := by rw [hsq1, d.viol.hzJ.sq, one_mul]
  rcases d.late_hzK'.unique _ (d.hR'.1 hκR') hκsq with h | h
  · left
    rw [hti] at h
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t) * t := by rw [mul_assoc _ t t, d.viol.hzJ.sq, mul_one]
      _ = t := by rw [h, one_mul]
  · right
    rw [hti] at h
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t) * t := by rw [mul_assoc _ t t, d.viol.hzJ.sq, mul_one]
      _ = z * t := by rw [h]

theorem Std20G.late_r'_t (d : Std20G K K' J S R R' W V z t) :
    ∃ r' ∈ R', r' * t * r'⁻¹ = z * t := by
  obtain ⟨r, hr, r', hr', hinv, hrt⟩ := d.late_tor d.late_JW d.late_hW
  have hrz : r * z * r⁻¹ = z := d.viol.hzK.conj_eq (conjSub_eq_self_of_mem (d.hR.1 hr))
  have hrz' : r⁻¹ * z * r = z := by
    have h2 : r * z = z * r := by
      calc r * z = (r * z * r⁻¹) * r := by group
        _ = z * r := by rw [hrz]
    calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
      _ = r⁻¹ * (r * z) := by rw [h2]
      _ = z := by group
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right d.viol.hzJ.sq
  have h1 : (r * r') * t * (r * r')⁻¹ = t := by
    have := hinv t d.late_t_mem_W
    rwa [hti] at this
  have h2 : r' * t * r'⁻¹ = r⁻¹ * t * r := by
    calc r' * t * r'⁻¹ = r⁻¹ * ((r * r') * t * (r * r')⁻¹) * r := by group
      _ = r⁻¹ * t * r := by rw [h1]
  have h3 : r⁻¹ * (z * t) * r = t := by rw [← hrt]; group
  have h4 : r⁻¹ * (z * t) * r = (r⁻¹ * z * r) * (r⁻¹ * t * r) := by group
  rw [h4, hrz'] at h3
  have h5 : r⁻¹ * t * r = z * t := by
    calc r⁻¹ * t * r = z * (z * (r⁻¹ * t * r)) := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]
      _ = z * t := by rw [h3]
  exact ⟨r', hr', by rw [h2, h5]⟩

theorem Std20G.late_inv_W (d : Std20G K K' J S R R' W V z t) :
    ∀ w ∈ W, w * w = 1 → w = 1 ∨ w = z ∨ w = t ∨ w = z * t := by
  intro w hw hw2
  have hbot : ∀ x ∈ W ⊓ K, x ∈ W ⊓ J → x = 1 := by
    intro x hxK hxJ
    by_contra hx1
    have hA : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr hxK.1).trans d.hWS)
    have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_J
      d.late_J_ne_K.symm hA (Subgroup.zpowers_le.mpr hxK.2) (Subgroup.zpowers_le.mpr hxJ.2)
    rw [Nat.card_zpowers] at hcard
    have hord : orderOf x = 2 := by
      have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf x := orderOf_pos x
      omega
    have hx2 : x * x = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
    have hxz : x = z := (d.viol.hzK.unique x hxK.2 hx2).resolve_left hx1
    have hxt : x = t := (d.viol.hzJ.unique x hxJ.2 hx2).resolve_left hx1
    exact d.late_ne_inv (hxt.symm.trans hxz)
  have hmem : w ∈ (W ⊓ K) ⊔ (W ⊓ J) := d.late_hW ▸ hw
  have hN : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer ((W ⊓ K : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh => d.late_hWc h hh.1 g hg.1)
  obtain ⟨a, ha, b, hb, hab⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN hmem
  have hba : b * a = a * b := d.late_hWc b hb.1 a ha.1
  have h1 : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hba]
      _ = (a * b) * (a * b) := by group
      _ = 1 := by rw [← hab]; exact hw2
  have h2 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have haa : a * a = 1 := by
    refine hbot _ ⟨W.mul_mem ha.1 ha.1, K.mul_mem ha.2 ha.2⟩ ?_
    rw [h2]
    exact ⟨W.inv_mem (W.mul_mem hb.1 hb.1), J.inv_mem (J.mul_mem hb.2 hb.2)⟩
  have hbb : b * b = 1 := by rw [haa, one_mul] at h1; exact h1
  rcases d.viol.hzK.unique a ha.2 haa with rfl | rfl <;>
    rcases d.viol.hzJ.unique b hb.2 hbb with rfl | rfl
  · left; rw [hab, one_mul]
  · right; right; left; rw [hab, one_mul]
  · right; left; rw [hab, mul_one]
  · right; right; right; exact hab

theorem Std20G.late_inv_conj (d : Std20G K K' J S R R' W V z t) {g : G}
    (hgz : g * z * g⁻¹ = z) (hgt : g * t * g⁻¹ = z * t) :
    g⁻¹ * z * g = z ∧ g⁻¹ * t * g = z * t := by
  have h2 : g * z = z * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  have hz' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [h2]
      _ = z := by group
  refine ⟨hz', ?_⟩
  have h3 : g⁻¹ * (z * t) * g = t := by rw [← hgt]; group
  have h4 : g⁻¹ * (z * t) * g = (g⁻¹ * z * g) * (g⁻¹ * t * g) := by group
  rw [h4, hz'] at h3
  calc g⁻¹ * t * g = z * (z * (g⁻¹ * t * g)) := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]
    _ = z * t := by rw [h3]

theorem Std20G.late_exists_y (d : Std20G K K' J S R R' W V z t) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) :
    ∃ r' ∈ R', (r'⁻¹ * x) * t * (r'⁻¹ * x)⁻¹ = t := by
  rcases d.late_kappa hx with h | h
  · exact ⟨1, Subgroup.one_mem _, by simpa using h⟩
  · obtain ⟨r', hr', hr't⟩ := d.late_r'_t
    refine ⟨r', hr', ?_⟩
    have hz' : r' * z * r'⁻¹ = z :=
      d.late_hzK'.conj_eq (conjSub_eq_self_of_mem (d.hR'.1 hr'))
    obtain ⟨hz'', h5⟩ := d.late_inv_conj hz' hr't
    calc (r'⁻¹ * x) * t * (r'⁻¹ * x)⁻¹ = r'⁻¹ * (x * t * x⁻¹) * r' := by group
      _ = r'⁻¹ * (z * t) * r' := by rw [h]
      _ = (r'⁻¹ * z * r') * (r'⁻¹ * t * r') := by group
      _ = z * (z * t) := by rw [hz'', h5]
      _ = t := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
