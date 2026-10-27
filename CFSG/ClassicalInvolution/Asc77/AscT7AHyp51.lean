module

public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Stmt
public import CFSG.ClassicalInvolution.Asc77.AscT7ATwin
public import CFSG.ClassicalInvolution.Asc77.WP3L54Thm54
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Eng
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Finite G] in
theorem quat_central {n : ℕ} [NeZero n] (hn : 2 ≤ n) (q : QuaternionGroup n)
    (h : ∀ r : QuaternionGroup n, r * q = q * r) : q * q = 1 := by
  cases q with
  | a i =>
    have h1 := h (QuaternionGroup.xa 0)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h1
    have h2 : (0 : ZMod (2 * n)) + i = 0 - i := QuaternionGroup.xa.inj h1
    have h3 : (2 : ZMod (2 * n)) * i = 0 := by
      have : i + i = 0 := by
        have h4 : i = - i := by simpa using h2
        calc i + i = i + (-i) := by rw [← h4]
          _ = 0 := by simp
      calc (2 : ZMod (2 * n)) * i = i + i := by ring
        _ = 0 := this
    have h5 : (2 * n) ∣ 2 * i.val := by
      have : ((2 * i.val : ℕ) : ZMod (2 * n)) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact h3
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    have h6 : n ∣ i.val := by
      have : 2 * n ∣ 2 * i.val := h5
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have h7 : i.val < 2 * n := ZMod.val_lt i
    obtain ⟨m, hm⟩ := h6
    have hm2 : m < 2 := by
      by_contra hcon
      have : 2 ≤ m := by omega
      have : n * 2 ≤ n * m := Nat.mul_le_mul_left n this
      omega
    interval_cases m
    · have : i = 0 := by
        have : i.val = 0 := by simpa using hm
        exact (ZMod.val_eq_zero i).mp this
      rw [this, QuaternionGroup.a_mul_a]
      simp
    · have hi : i = (n : ZMod (2 * n)) := by
        rw [← ZMod.natCast_zmod_val i, hm]
        simp
      rw [hi, QuaternionGroup.a_mul_a]
      have : ((n : ZMod (2 * n)) + n) = 0 := by
        have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
        push_cast at this
        calc (n : ZMod (2 * n)) + n = 2 * n := by ring
          _ = 0 := this
      rw [this]
      simp
  | xa j =>
    exfalso
    have h1 := h (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
    have h2 : j - 1 = j + 1 := QuaternionGroup.xa.inj h1
    have h3 : (2 : ZMod (2 * n)) = 0 := by
      have : j + 1 - (j - 1) = 0 := by rw [h2]; ring
      calc (2 : ZMod (2 * n)) = j + 1 - (j - 1) := by ring
        _ = 0 := this
    have h4 : (2 * n) ∣ 2 := by
      have : ((2 : ℕ) : ZMod (2 * n)) = 0 := by exact_mod_cast h3
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    have := Nat.le_of_dvd (by norm_num) h4
    omega

omit [Finite G] in
theorem eq_one_or_eq_of_central {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hR : IsQuatSub R) (hRK : R ≤ K) {x : G} (hx : x ∈ R) (hc : ∀ r ∈ R, r * x = x * r) :
    x = 1 ∨ x = z := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hR
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  have hq : ∀ r' : QuaternionGroup (2 ^ k), r' * e ⟨x, hx⟩ = e ⟨x, hx⟩ * r' := by
    intro r'
    obtain ⟨r, rfl⟩ := e.surjective r'
    have := hc (r : G) r.2
    have h3 : r * (⟨x, hx⟩ : ↥R) = (⟨x, hx⟩ : ↥R) * r := Subtype.ext this
    rw [← map_mul, ← map_mul, h3]
  have h4 := quat_central h2 _ hq
  have h5 : (⟨x, hx⟩ : ↥R) * ⟨x, hx⟩ = 1 := by
    apply e.injective
    rw [map_mul, h4, map_one]
  have h6 : x * x = 1 := congrArg Subtype.val h5
  exact hz.unique x (hRK hx) h6

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {a x : G} (ha : orderOf a = 2) (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.eq_one_or_eq_of_mem_zpowers_gen ha hx

omit [Finite G] in
theorem isElemAbelian2_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    IsElemAbelian2 (Subgroup.closure {a, b}) 2 := by
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hcl : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hcomm : Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a b from hc) i j)).eq
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases eq_one_or_eq_of_mem_zpowers ha2 he.1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exfalso
      rcases eq_one_or_eq_of_mem_zpowers hb2 he.2 with h' | h'
      · exact ha1 (h.symm.trans h')
      · exact hab (h.symm.trans h')
  refine ⟨?_, ?_⟩
  · have hN := card_sup_mul_card_inf (le_normalizer_of_commutes hcomm)
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, ha2, hb2, mul_one] at hN
    rw [hcl, sup_comm]
    omega
  · intro x hx
    rw [hcl] at hx
    obtain ⟨a', ha', b', hb', rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hx
    have hcm : a' * b' = b' * a' := hcomm a' ha' b' hb'
    have h1 : a' * a' = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ha2 ha' with h | h
      · rw [h, one_mul]
      · rw [h]; exact ha
    have h2 : b' * b' = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hb2 hb' with h | h
      · rw [h, one_mul]
      · rw [h]; exact hb
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [← hcm]
      _ = (a' * a') * (b' * b') := by group
      _ = 1 := by rw [h1, h2, one_mul]

omit [Finite G] in
theorem commutes_closure {s : Set G} (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.commutes_closure_gen h

omit [Finite G] in
theorem sq_closure {s : Set G} (hs : ∀ a ∈ s, a * a = 1)
    (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  exact CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng.sq_closure_gen hs h

omit [Finite G] in
theorem z_comm_of_mem_sup {K K' : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {w : G} (hw : w ∈ K ⊔ K') : z * w = w * z := by
  have h : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hk).symm)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hk).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h hw)).symm

end T7A

section Frame

variable {K K' J : Subgroup G} {z u t : G}

omit [Finite G] in
theorem TwinFrameData.comm_zu (h : TwinFrameData Ω K K' z u J t) : z * u = u * z :=
  T7A.z_comm_of_mem_sup h.hz (isUniqueInvolution_of_mem_twinSet h.hz h.hK') h.hu

theorem TwinFrameData.comm_zt (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h : TwinFrameData Ω K K' z u J t) : z * t = t * z := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 K (mem_twinSet_self h.mem h.hz)
  have hRsyl : IsSylow2In R J := hΩ.isSylow2In_of_mem_RSet_of_le hp h.hJ.1 hR hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN htR)).symm

theorem TwinFrameData.t_not_mem_closure (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : TwinFrameData Ω K K' z u J t) : t ∉ Subgroup.closure ({z, u} : Set G) := by
  intro htcl
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ h.mem h.hz h.hK' h.hne h.hJ
  have hQ := T7A.isSylow2In_sup_of_twin hp hΩ h.mem h.hK'.1 h.hne h.hz hzK' hRsyl hR'syl hRR'
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In h.hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have htQ : t ∈ K ⊔ K' := by
    have : Subgroup.closure ({z, u} : Set G) ≤ K ⊔ K' := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_left h.hz.mem
      · exact h.hu
    exact this htcl
  have hS2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) :=
    (Sylow.isPGroup' S).to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' :=
    hQ.eq_of_le hS2 inf_le_right (le_inf (sup_le hRS hR'S) hQ.1)
  have htRR' : t ∈ R ⊔ R' := by
    rw [← heq]
    exact ⟨hTS htT, htQ⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hRR' htRR'
  have hxc : ∀ r ∈ R, r * x = x * r := by
    intro r hr
    have h1 : r * t = t * r := hRT r hr t htT
    have h2 : r * y = y * r := hRR' r hr y hy
    have : (r * x) * y = (x * r) * y := by
      calc (r * x) * y = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
        _ = x * (r * y) := by rw [h2]
        _ = (x * r) * y := by group
    exact mul_right_cancel this
  have hyc : ∀ r ∈ R', r * y = y * r := by
    intro r hr
    have h1 : r * t = t * r := hR'T r hr t htT
    have h2 : x * r = r * x := hRR' x hx r hr
    have : x * (r * y) = x * (y * r) := by
      calc x * (r * y) = (x * r) * y := by group
        _ = (r * x) * y := by rw [h2]
        _ = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
    exact mul_left_cancel this
  have hxz := T7A.eq_one_or_eq_of_central h.hz
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.mem hRsyl)) hRsyl.1 hx hxc
  have hyz := T7A.eq_one_or_eq_of_central hzK'
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.hK'.1 hR'syl)) hR'syl.1 hy hyc
  have htz := h.t_ne_z
  have ht1 := h.ht.ne_one
  rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
  · exact ht1 (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, mul_one])
  · exact ht1 (by rw [← hxy, h1, h2]; exact h.hz.sq)

theorem TwinFrameData.comm_gen (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    ∀ a ∈ ({z, u, t} : Set G), ∀ b ∈ ({z, u, t} : Set G), a * b = b * a := by
  have hzu := h.comm_zu
  have hzt := h.comm_zt hp hΩ
  have hut : u * t = t * u := h.htu.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hzu
  · exact hzt
  · exact hzu.symm
  · rfl
  · exact hut
  · exact hzt.symm
  · exact hut.symm
  · rfl

theorem twinFrame_isElemAbelian (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hcomm := T7A.commutes_closure (h.comm_gen hp hΩ)
  have hsq : ∀ a ∈ ({z, u, t} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact h.hz.sq
    · exact h.hu2
    · exact h.ht.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (h.comm_gen hp hΩ) x hx

theorem twinFrame_natCard_eight (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    Nat.card ↥(Subgroup.closure ({z, u, t} : Set G)) = 8 := by
  have hzt := h.comm_zt hp hΩ
  have hD := T7A.isElemAbelian2_closure_pair h.hu2 h.hz.sq h.hu1 h.hz.ne_one h.huz h.comm_zu.symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  have hcl : Subgroup.closure ({z, u, t} : Set G) =
      Subgroup.closure ({u, z} : Set G) ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({u, z} : Set G)) (Subgroup.zpowers t) := by
    have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h.htu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, z} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers ht2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply h.t_not_mem_closure hp hq hΩ
      rw [Set.pair_comm]
      rw [← h1]
      exact he.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, ht2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end Frame

section C21_3

variable (p f)

theorem TwinFrameSetting.of_hyp21 {K K' J W : Subgroup G} {z u t : G}
    (h : Hyp21 p f Ω K K' z u J t W) : TwinFrameSetting p f Ω K K' J z u t where
  odd := h.std.stand.odd
  five := h.std.stand.five
  hyp := h.std.stand.hyp
  aEmpty := h.std.stand.aEmpty
  trans := h.std.stand.trans
  below := h.std.stand.below f h.std.stand.five
  thm7 := (h.std.stand.ih f h.std.stand.five).thm7
  frame := h.twinFrameData

theorem c21_3_of (hH : TwinFrameHyp51 p f) : C21_3 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  have hB : Hyp51 (Subgroup.closure ({z, u, t} : Set G)) :=
    hH G Ω K K' J z u t (TwinFrameSetting.of_hyp21 p f h)
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.hu2 h.std.hz.sq h.hu1 h.std.hz.ne_one h.huz
      h.twinFrameData.comm_zu.symm
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact lemma54_odd_and_eq hB hDB hD

end C21_3

end CFSG.ClassicalInvolution.Asc77
