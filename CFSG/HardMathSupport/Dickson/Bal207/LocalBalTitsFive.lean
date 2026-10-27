module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10
public import Certificates.Certificate17560
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Local

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.Schreier.Tits

section Generic

theorem no_order_thirteen_commutes_order_five {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 17971200)
    (h2 : ∀ u y : G, orderOf u = 2 → orderOf y = 13 → u * y ≠ y * u)
    (h3 : ∀ x y : G, orderOf x = 3 → orderOf y = 13 → x * y ≠ y * x)
    {y : G} (hy : orderOf y = 13) {x : G} (hx : orderOf x = 5) (hxy : x * y = y * x) : False := by
  have h13 : Fact (Nat.Prime 13) := ⟨by decide⟩
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have h5C : 5 ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    rwa [Subgroup.orderOf_mk, hx] at this
  have h13C : 13 ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : C)
    rwa [Subgroup.orderOf_mk, hy] at this
  have h65 : 65 ∣ Nat.card C := by
    have hco : Nat.Coprime 5 13 := by norm_num
    simpa using hco.mul_dvd_of_dvd_of_dvd h5C h13C
  have hdvd : Nat.card C ∣ 17971200 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hn2 : ¬ 2 ∣ Nat.card C := by
    intro h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h
    exact h2 (u : G) y (by rw [Subgroup.orderOf_coe]; exact hu) hy
      (Subgroup.mem_centralizer_singleton_iff.1 u.2)
  have hn3 : ¬ 3 ∣ Nat.card C := by
    intro h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h
    exact h3 (u : G) y (by rw [Subgroup.orderOf_coe]; exact hu) hy
      (Subgroup.mem_centralizer_singleton_iff.1 u.2)
  have hC65 : Nat.card C = 65 ∨ Nat.card C = 325 := by
    obtain ⟨m, hm⟩ := h65
    have hm' : m ∣ 2 ^ 11 * 3 ^ 3 * 5 := by
      rw [hm, show (17971200 : ℕ) = 65 * (2 ^ 11 * 3 ^ 3 * 5) by norm_num] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    have hm2 : ¬ 2 ∣ m := fun h => hn2 (hm ▸ h.mul_left 65)
    have hm3 : ¬ 3 ∣ m := fun h => hn3 (hm ▸ h.mul_left 65)
    have hc2 : Nat.Coprime m (2 ^ 11) :=
      Nat.Coprime.pow_right 11 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2).symm
    have hc3 : Nat.Coprime m (3 ^ 3) :=
      Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3).symm
    have hm5 : m ∣ 5 := (hc2.mul_right hc3).dvd_of_dvd_mul_left hm'
    rcases (Nat.dvd_prime Nat.prime_five).1 hm5 with h | h
    · left; rw [hm, h]
    · right; rw [hm, h]
  set Q : Subgroup G := Subgroup.zpowers y with hQ
  have hQcard : Nat.card Q = 13 := by rw [hQ, Nat.card_zpowers, hy]
  have hQp : IsPGroup 13 Q := IsPGroup.of_card (n := 1) (by rw [hQcard, pow_one])
  have hQidx : ¬ 13 ∣ Q.index := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, hcard] at h
    have : Q.index = 1382400 := by omega
    rw [this]
    norm_num
  have hS : (hQp.toSylow hQidx : Subgroup G) = Q := IsPGroup.toSylow_coe _ _
  have hmod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 G
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN
  have hindex : Nat.card (Sylow 13 G) = N.index := by
    rw [Sylow.card_eq_index_normalizer (hQp.toSylow hQidx)]
    exact congrArg (fun H : Subgroup G => (Subgroup.normalizer (H : Set G)).index) hS
  have hCQ : Subgroup.centralizer (Q : Set G) = C := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun z hz => by
        rw [Set.mem_singleton_iff.1 hz]
        exact Subgroup.mem_centralizer_iff.1 hx y (Subgroup.mem_zpowers y)
    · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hxy : Commute y x := (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
      exact (hxy.zpow_left k).eq
  have hCN : C ≤ N := by
    rw [← hCQ]
    exact Subgroup.centralizer_le_normalizer _
  have hrel : C.relIndex N ∣ 12 := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective Q.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex, hCQ] at key
    have hcyc : Nat.card (MulAut Q) = 12 := by
      rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime h13.out]
    rwa [hcyc] at key
  have hNcard : Nat.card N = Nat.card C * C.relIndex N := by
    have h := Subgroup.card_mul_index (C.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv] at h
    exact h.symm
  have hGN := Subgroup.card_mul_index N
  rw [hNcard, hcard] at hGN
  have hn : N.index % 13 = 1 := by
    have := hindex ▸ hmod
    exact this
  have hr : C.relIndex N ≤ 12 := Nat.le_of_dvd (by norm_num) hrel
  generalize C.relIndex N = r at hr hGN hrel
  rcases hC65 with h | h <;> rw [h] at hGN <;> interval_cases r <;> omega

theorem card_dvd_card_inf_centralizer_of_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M : Subgroup G} {m : ℕ} (hM : Nat.card M = p * m) (hpm : ¬ p ∣ m)
    {b k : G} (hbM : b ∈ M) (hkM : k ∈ M) (hb : orderOf b = p) (hk : orderOf k = p)
    {T : Subgroup G} (hTM : T ≤ M) (hTk : ∀ t ∈ T, t * k = k * t) :
    Nat.card T ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hb' : orderOf (⟨b, hbM⟩ : M) = p := by rw [Subgroup.orderOf_mk, hb]
  have hk' : orderOf (⟨k, hkM⟩ : M) = p := by rw [Subgroup.orderOf_mk, hk]
  have hQcard : Nat.card (Subgroup.zpowers (⟨b, hbM⟩ : M)) = p := by
    rw [Nat.card_zpowers, hb']
  have hQp : IsPGroup p (Subgroup.zpowers (⟨b, hbM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [hQcard, pow_one])
  have hQidx : ¬ p ∣ (Subgroup.zpowers (⟨b, hbM⟩ : M)).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers (⟨b, hbM⟩ : M))
    rw [hQcard, hM] at h
    rwa [Nat.eq_of_mul_eq_mul_left hp0 h]
  have hkp : IsPGroup p (Subgroup.zpowers (⟨k, hkM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk', pow_one])
  obtain ⟨w, hw⟩ := CFSG.Sporadic.Schreier.Tits.exists_conj_mem_sylow (hQp.toSylow hQidx) hkp
  rw [IsPGroup.toSylow_coe] at hw
  have hwk : orderOf (w * ⟨k, hkM⟩ * w⁻¹) = p := by
    have := orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective ⟨k, hkM⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this, hk']
  have hzp : Subgroup.zpowers (w * ⟨k, hkM⟩ * w⁻¹) = Subgroup.zpowers (⟨b, hbM⟩ : M) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw)
      (by rw [hQcard, Nat.card_zpowers, hwk])
  have hbw : (⟨b, hbM⟩ : M) ∈ Subgroup.zpowers (w * ⟨k, hkM⟩ * w⁻¹) := by
    rw [hzp]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hbw
  have hjG : ((w : G) * k * (w : G)⁻¹) ^ j = b := by
    have := congrArg Subtype.val hj
    simpa using this
  have hle : T.map (MulAut.conj (w : G)).toMonoidHom ≤
      M ⊓ Subgroup.centralizer ({b} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.2 ⟨M.mul_mem (M.mul_mem w.2 (hTM ht)) (M.inv_mem w.2), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hjG]
    have hc : (w : G) * t * (w : G)⁻¹ * ((w : G) * k * (w : G)⁻¹) =
        (w : G) * k * (w : G)⁻¹ * ((w : G) * t * (w : G)⁻¹) := by
      calc (w : G) * t * (w : G)⁻¹ * ((w : G) * k * (w : G)⁻¹)
          = (w : G) * (t * k) * (w : G)⁻¹ := by group
        _ = (w : G) * (k * t) * (w : G)⁻¹ := by rw [hTk t ht]
        _ = (w : G) * k * (w : G)⁻¹ * ((w : G) * t * (w : G)⁻¹) := by group
    exact ((show Commute ((w : G) * t * (w : G)⁻¹) ((w : G) * k * (w : G)⁻¹) from hc).zpow_right
      j).eq
  have := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective (f := (MulAut.conj (w : G)).toMonoidHom)
    (MulAut.conj (w : G)).injective] at this

theorem two_pow_le_two_of_dvd_of_five_dvd {n c : ℕ} (h : 2 ^ n ∣ c) (hc0 : 0 < c) (hc : c ≤ 10)
    (h5 : 5 ∣ c) : 2 ^ n ≤ 2 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num
  · have h4 : 4 ∣ c := (Nat.pow_dvd_pow 2 hn).trans h
    omega

end Generic

section BFive

theorem bFive_parts :
    ∃ b ∈ titsH, b ≠ 1 ∧ b ^ 5 = 1 ∧
      Nat.card ↥(titsH ⊓ Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin 1755)))) ≤ 10 :=
  Certificates.certificate17560

end BFive

section Tits


theorem titsD_no_thirteen_commutes_five {y : titsD}
    (hy : orderOf y = 13) {x : titsD} (hx : orderOf x = 5) (hxy : x * y = y * x) : False :=
  no_order_thirteen_commutes_order_five CFSG.Sporadic.Schreier.Tits.card_titsD
    (fun u y hu hy hc => by
      have hyC : y ∈ Subgroup.centralizer ({u} : Set titsD) :=
        Subgroup.mem_centralizer_singleton_iff.2 hc.symm
      have h13 := orderOf_dvd_natCard (⟨y, hyC⟩ : Subgroup.centralizer ({u} : Set titsD))
      rw [Subgroup.orderOf_mk, hy] at h13
      rcases RankThree.PartTwo.Sec4.Item434RemTits.card_centralizer_of_involution hu with h | h <;>
        rw [h] at h13 <;> norm_num at h13)
    (fun x y hx hy hc =>
      RankThree.PartTwo.Sec4.Item434RemTits.mul_ne_mul_of_orderOf hx (Or.inr rfl) hy hc)
    hy hx hxy

theorem titsD_card_le_two_of_commute_five {k : titsD}
    (hk : orderOf k = 5) {T : Subgroup titsD} {n : ℕ} (hT : Nat.card T = 2 ^ n)
    (hTk : ∀ t ∈ T, t * k = k * t) : Nat.card T ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hT]; norm_num
  obtain ⟨v, hvT, hv2, hTv⟩ : ∃ v ∈ T, orderOf v = 2 ∧ ∀ t ∈ T, t * v = v * t := by
    obtain ⟨j, hj0, hj⟩ := IsPGroup.card_center_eq_prime_pow hT hn
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
      (by rw [hj]; exact dvd_pow_self 2 hj0.ne')
    refine ⟨((u : T) : titsD), (u : T).2, ?_, fun t ht => ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 u.2 ⟨t, ht⟩)
  have hkv : k * v = v * k := (hTk v hvT).symm
  have h5v : 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set titsD)) := by
    have := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_centralizer_singleton_iff.2 hkv)
    rwa [hk] at this
  have hzv : IsConj titsZD v := by
    rcases titsD_involution_conj v hv2 with h | h
    · exact h
    · rw [← RankThree.PartTwo.Sec4.Item434RemTits.card_centralizer_eq_of_isConj h,
        titsD_centralizer_t.2.1] at h5v
      norm_num at h5v
  obtain ⟨g, hgv⟩ := isConj_iff.1 hzv.symm
  obtain ⟨b₀, hbH, hb1, hb5, hb10⟩ := bFive_parts
  obtain ⟨b, hbv⟩ : ∃ b : titsD, (b : Equiv.Perm (Fin 1755)) = b₀ :=
    ⟨⟨_, titsH_le_titsD hbH⟩, rfl⟩
  have hbo : orderOf b = 5 := by
    rw [← Subgroup.orderOf_coe, hbv]
    exact orderOf_eq_prime hb5 hb1
  have hbM : b ∈ Subgroup.centralizer ({titsZD} : Set titsD) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hbv]
    exact Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hbH)
  have hMb : Nat.card ↥(Subgroup.centralizer ({titsZD} : Set titsD) ⊓
      Subgroup.centralizer ({b} : Set titsD)) ≤ 10 := by
    rw [← Subgroup.card_map_of_injective titsD.subtype_injective]
    refine (Subgroup.card_le_of_le ?_).trans hb10
    rintro _ ⟨x, ⟨hxz, hxb⟩, rfl⟩
    have hxz' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hxz)
    have hxb' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hxb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at hxz' hxb'
    rw [hbv] at hxb'
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hxb'⟩
    rw [← titsD_centralizer_z]
    exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hxz'⟩
  have hbMb : b ∈ Subgroup.centralizer ({titsZD} : Set titsD) ⊓
      Subgroup.centralizer ({b} : Set titsD) :=
    ⟨hbM, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have h5b := Subgroup.orderOf_dvd_natCard _ hbMb
  rw [hbo] at h5b
  have hTM : T.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({titsZD} : Set titsD) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
      ← hgv]
    calc g * t * g⁻¹ * (g * v * g⁻¹) = g * (t * v) * g⁻¹ := by group
      _ = g * (v * t) * g⁻¹ := by rw [hTv t ht]
      _ = g * v * g⁻¹ * (g * t * g⁻¹) := by group
  have hkM : g * k * g⁻¹ ∈ Subgroup.centralizer ({titsZD} : Set titsD) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgv]
    calc g * k * g⁻¹ * (g * v * g⁻¹) = g * (k * v) * g⁻¹ := by group
      _ = g * (v * k) * g⁻¹ := by rw [hkv]
      _ = g * v * g⁻¹ * (g * k * g⁻¹) := by group
  have hko : orderOf (g * k * g⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective k
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this, hk]
  have hTk' : ∀ t ∈ T.map (MulAut.conj g).toMonoidHom, t * (g * k * g⁻¹) = g * k * g⁻¹ * t := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * t * g⁻¹ * (g * k * g⁻¹) = g * (t * k) * g⁻¹ := by group
      _ = g * (k * t) * g⁻¹ := by rw [hTk t ht]
      _ = g * k * g⁻¹ * (g * t * g⁻¹) := by group
  have hdvd := card_dvd_card_inf_centralizer_of_orderOf
    (show Nat.card (Subgroup.centralizer ({titsZD} : Set titsD)) = 5 * 2048 by
      rw [card_centralizer_titsZD]) (by norm_num) hbM hkM hbo hko hTM hTk'
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective, hT] at hdvd
  rw [hT]
  exact two_pow_le_two_of_dvd_of_five_dvd hdvd Nat.card_pos hMb h5b


theorem titsD_eq_bot_of_five {k : titsD} (hk : orderOf k = 5) {Y : Subgroup (MulAut titsD)}
    (hYk : ∀ y ∈ Y, y * MulAut.conj k = MulAut.conj k * y)
    (hYn : ∀ q : titsD, q * k = k * q → ∀ y ∈ Y, MulAut.conj q * y * (MulAut.conj q)⁻¹ ∈ Y)
    (hY5 : Nat.Coprime 5 (Nat.card Y)) : Y = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hinj := LocalTwoBalance.Cross.TitsAux.conj_injective_titsD
  obtain ⟨P, hP, hkP⟩ := Sylow.exists_subgroup_card_pow_prime_le 5 (n := 1) (m := 2)
    (by rw [CFSG.Sporadic.Schreier.Tits.card_titsD]; norm_num) (Subgroup.zpowers k)
    (by rw [Nat.card_zpowers, hk, pow_one]) (by norm_num)
  have hP25 : Nat.card P = 25 := by rw [hP]; norm_num
  have hkP' : k ∈ P := hkP (Subgroup.mem_zpowers k)
  have hPk : ∀ q ∈ P, q * k = k * q := fun q hq => congrArg Subtype.val
    ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hP).is_comm.comm ⟨q, hq⟩ ⟨k, hkP'⟩)
  have hIP : IsPGroup 5 (P.map (MulAut.conj : titsD →* MulAut titsD)) :=
    (IsPGroup.of_card hP).map _
  have hIPY : P.map (MulAut.conj : titsD →* MulAut titsD) ≤
      Subgroup.normalizer (Y : Set (MulAut titsD)) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hYn q (hPk q hq) y, fun h => ?_⟩
    have h1 := hYn q⁻¹ (show Commute q k from hPk q hq).inv_left.eq _ h
    have e : (MulAut.conj q)⁻¹ * (MulAut.conj q * y * (MulAut.conj q)⁻¹) *
        (MulAut.conj q)⁻¹⁻¹ = y := by group
    rw [map_inv] at h1
    rwa [e] at h1
  have hmod := CFSG.RankThree.PartTwo.Sec16.Res9A10.card_modEq_card_inf_centralizer hIP hIPY
  have hcen : Y ⊓ Subgroup.centralizer
      ((P.map (MulAut.conj : titsD →* MulAut titsD) : Subgroup (MulAut titsD)) :
        Set (MulAut titsD)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.1 hy
    refine LocalTwoBalance.Cross.TitsAux.tits_five_faithful hP25 y
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Y hyY) hY5) fun q hq => ?_
    have hc := Subgroup.mem_centralizer_iff.1 hyC (MulAut.conj q) (Subgroup.mem_map_of_mem _ hq)
    exact mem_fixSub.1 (mem_fixSub_of_commute hinj hc.symm)
  rw [hcen, Subgroup.card_bot] at hmod
  have hSk : ∀ s ∈ Y.comap (MulAut.conj : titsD →* MulAut titsD), s * k = k * s := by
    intro s hs
    apply hinj
    rw [map_mul, map_mul]
    exact hYk _ hs
  have hScard : Nat.card (Y.comap (MulAut.conj : titsD →* MulAut titsD)) =
      Nat.card ↥(innerAut titsD ⊓ Y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj : titsD →* MulAut titsD))
      (K := Y.comap (MulAut.conj : titsD →* MulAut titsD)) hinj, Subgroup.map_comap_eq]
    rfl
  have hS5 : Nat.Coprime 5 (Nat.card (Y.comap (MulAut.conj : titsD →* MulAut titsD))) := by
    rw [hScard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hY5
  have hS2 : Nat.card (Y.comap (MulAut.conj : titsD →* MulAut titsD)) =
      2 ^ (Nat.card (Y.comap (MulAut.conj : titsD →* MulAut titsD))).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqS => ?_
    have hqD : q ∣ 17971200 := hqS.trans
      (CFSG.Sporadic.Schreier.Tits.card_titsD ▸ Subgroup.card_subgroup_dvd_card _)
    rcases LocalTwoBalance.Cross.TitsAux.prime_dvd_card_titsD hq hqD with rfl | rfl | rfl | rfl
    · rfl
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hqS
      exact absurd (hSk x x.2) (RankThree.PartTwo.Sec4.Item434RemTits.mul_ne_mul_of_orderOf
        (by rw [Subgroup.orderOf_coe]; exact hx) (Or.inl rfl) hk)
    · exact absurd hqS ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hS5)
    · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 13 hqS
      exact (titsD_no_thirteen_commutes_five (by rw [Subgroup.orderOf_coe]; exact hy) hk
        (hSk y y.2).symm).elim
  have hSle := titsD_card_le_two_of_commute_five hk hS2 hSk
  haveI : (innerAut titsD).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal titsD
  have hrel : (innerAut titsD).relIndex Y ∣ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal (innerAut titsD) Y
    rwa [Subgroup.index_eq_card,
      show Nat.card (MulAut titsD ⧸ innerAut titsD) = 2 from card_outer_titsD] at h
  have hYeq : Nat.card ↥(innerAut titsD ⊓ Y) * (innerAut titsD).relIndex Y = Nat.card Y := by
    have h := Subgroup.card_mul_index ((innerAut titsD).subgroupOf Y)
    rw [← Subgroup.relIndex, ← Subgroup.card_map_of_injective (f := Y.subtype)
      (K := (innerAut titsD).subgroupOf Y) Y.subtype_injective,
      Subgroup.subgroupOf_map_subtype] at h
    exact h
  have hY4 : Nat.card Y ≤ 4 := by
    rw [← hYeq, ← hScard]
    exact Nat.mul_le_mul hSle (Nat.le_of_dvd (by norm_num) hrel)
  have hY0 : 0 < Nat.card Y := Nat.card_pos
  have hY1 : Nat.card Y = 1 := by
    unfold Nat.ModEq at hmod
    omega
  exact Subgroup.card_eq_one.1 hY1

theorem isLocallyBalancedAbs_five_one_titsD : IsLocallyBalancedAbs 5 1 titsD := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro D hD hcard H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime Nat.prime_five hcard
  have hd5 : d ^ 5 = 1 := hD.2 d hdD
  have hdin : d ∈ innerAut titsD :=
    mem_innerAut_of_pow_eq_one_of_hom
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD))
      (fun α hα => (QuotientGroup.eq_one_iff α).1 hα) (m := 2)
      (fun y => orderOf_dvd_iff_pow_eq_one.1
        ((orderOf_dvd_natCard y).trans (dvd_of_eq card_outer_titsD)))
      (by norm_num) hd5
  obtain ⟨k, rfl⟩ := hdin
  have hk5 : orderOf k = 5 := by
    rw [← orderOf_injective _ LocalTwoBalance.Cross.TitsAux.conj_injective_titsD k]
    exact orderOf_eq_prime hd5 hd1
  refine localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 ?_
  refine titsD_eq_bot_of_five hk5 (fun y hy => ?_) (fun q hq y hy => ?_)
    (coprime_card_GLAPPrimeCoreOf Nat.prime_five _)
  · exact Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ hy).2
  · have hqC : MulAut.conj q ∈
        H ⊓ Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)) := by
      refine Subgroup.mem_inf.2 ⟨hH (MonoidHom.mem_range.2 ⟨q, rfl⟩),
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have e1 := map_mul (MulAut.conj : titsD →* MulAut titsD) q k
      have e2 := map_mul (MulAut.conj : titsD →* MulAut titsD) k q
      rw [← e1, ← e2, hq]
    exact GLAPPrimeCoreOf_conj_mem _ hqC y hy


theorem isLocallyBalancedAbs_five_one_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    IsLocallyBalancedAbs 5 1 (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  obtain ⟨e⟩ := LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e isLocallyBalancedAbs_five_one_titsD

end Tits

end CFSG.HardMathSupport.Dickson.Bal207
