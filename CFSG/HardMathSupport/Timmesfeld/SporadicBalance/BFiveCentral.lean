module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveTwoB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMBaby
public import CFSG.RankThree.Native.BFiveLocalRel
public import CFSG.RankThree.Native.BFiveLocal

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.RankThree.Native

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem eq_one_of_pow_two_pow_of_odd [Finite G] {Q : Subgroup G} (hQ : Odd (Nat.card Q)) {q : G}
    (hq : q ∈ Q) {n : ℕ} (h : q ^ (2 ^ n) = 1) : q = 1 := by
  have h1 : orderOf (⟨q, hq⟩ : Q) ∣ 2 ^ n := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf (⟨q, hq⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
  have hc : Nat.Coprime (2 ^ n) (Nat.card Q) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hQ)
  have h3 : orderOf (⟨q, hq⟩ : Q) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
  rw [orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

theorem inv_of_fixedPointFree_involution' [Finite G] {Q : Subgroup G} {α : G}
    (hQ : ∀ q ∈ Q, α * q * α⁻¹ ∈ Q) (hα : α * α = 1) (hfix : ∀ q ∈ Q, α * q * α⁻¹ = q → q = 1) :
    ∀ q ∈ Q, α * q * α⁻¹ = q⁻¹ :=
  inv_of_fixedPointFree_involution hα hQ hfix

theorem conj_pow_eq_pow_pow {h z : G} {a : ℕ} (hz : h⁻¹ * z * h = z ^ a) (k : ℕ) :
    (h ^ k)⁻¹ * z * h ^ k = z ^ (a ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : (h ^ (k + 1))⁻¹ * z * h ^ (k + 1) = h⁻¹ * ((h ^ k)⁻¹ * z * h ^ k) * h := by
      rw [pow_succ]
      group
    have e2 : ∀ m : ℕ, h⁻¹ * z ^ m * h = (h⁻¹ * z * h) ^ m := fun m => by
      have := conj_pow (a := h⁻¹) (b := z) (i := m)
      rw [inv_inv] at this
      exact this.symm
    rw [e1, ih, e2, hz, ← pow_mul, pow_succ, mul_comm (a ^ k) a]

theorem conj_mul_comm_of_conj_pow {g x z : G} {b : ℕ} (hb : g⁻¹ * z ^ b * g = z)
    (hx : x * z = z * x) : (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) := by
  have hz : z ^ b = g * z * g⁻¹ := by
    calc z ^ b = g * (g⁻¹ * z ^ b * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hb]
  have hxb : x * z ^ b = z ^ b * x := ((Commute.pow_right hx b)).eq
  calc g⁻¹ * x * g * z = g⁻¹ * x * (g * z * g⁻¹) * g := by group
    _ = g⁻¹ * (x * z ^ b) * g := by rw [← hz]; group
    _ = g⁻¹ * (z ^ b * x) * g := by rw [hxb]
    _ = (g⁻¹ * z ^ b * g) * (g⁻¹ * x * g) := by group
    _ = z * (g⁻¹ * x * g) := by rw [hb]

theorem mem_zpowers_of_commute_P [Finite G] {x h z : G} {q : Fin 4 → G}
    (hR : FiveLocal.Rel x h q z) {s : G} (hsP : s ∈ FiveLocal.P x q)
    (hs : ∀ g ∈ FiveLocal.P x q, s * g = g * s) : s ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := FiveLocal.P x q with hP
  set Q := FiveLocal.Q q with hQ
  have hQP : Q ≤ P := le_sup_left
  have hL : ∀ b ∈ P, ∀ i, b⁻¹ * q i * b ∈ Subgroup.closure (Set.range q) := fun b hb i =>
    hR.conj_mem_of_mem_K (hR.P_le_K hb) (FiveLocal.q_mem i)
  set φ := hR.commData.actHom P hL with hφ
  have hQker : Q.subgroupOf P ≤ φ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker, hφ, CommData.actHom_apply]
    exact hR.commData.actMat_of_mem (Subgroup.mem_subgroupOf.1 hb)
  have hxP : x ∈ P := (le_sup_right : Subgroup.zpowers x ≤ P) (Subgroup.mem_zpowers x)
  have hxker : (⟨x, hxP⟩ : P) ∉ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, CommData.actHom_apply,
      hR.commData.actMat_eq f5X FiveLocal.xc hR.conj_x]
    intro h1
    have := congrFun (congrFun h1 0) 0
    simp [f5X] at this
  have hcardQ : Nat.card (Q.subgroupOf P) = 5 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv]
    exact hR.card_Q
  have hcardP : Nat.card P = 5 ^ 6 := hR.card_P
  have hker : Q.subgroupOf P = φ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hQker ?_
    have hdvd : Nat.card φ.ker ∣ 5 ^ 6 := hcardP ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
    have hne : j ≠ 6 := by
      rintro rfl
      apply hxker
      have htop : φ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hjeq, hcardP])
      rw [htop]
      exact Subgroup.mem_top _
    rw [hcardQ, hjeq]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsker : (⟨s, hsP⟩ : P) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, CommData.actHom_apply, ← hR.commData.actMat_one]
    ext i j
    have hqi : s⁻¹ * q i * s = 1⁻¹ * q i * 1 := by
      have := hs (q i) (hQP (FiveLocal.q_mem i))
      calc s⁻¹ * q i * s = s⁻¹ * (q i * s) := by group
        _ = s⁻¹ * (s * q i) := by rw [this]
        _ = 1⁻¹ * q i * 1 := by group
    simp only [CommData.actMat, Matrix.of_apply]
    rw [hqi]
  rw [← hker] at hsker
  have hsQ : s ∈ Q := Subgroup.mem_subgroupOf.1 hsker
  have hsZ : (⟨s, hsQ⟩ : Q) ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hs g (hQP g.2)).symm
  rw [hR.center_Q_eq] at hsZ
  exact Subgroup.mem_subgroupOf.1 hsZ

end Generic

section TwoBLocalP


theorem pow_two_pow_eq_one_of_babyInv_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : OPrimeCoreTrivialAt p Co2) {s t : B} (hs : orderOf s = p) (ht : BabyInv 1 t)
    (hts : t ∈ Subgroup.centralizer ({s} : Set B)) {q : B}
    (hq : q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set B)))
    (hqt : q ∈ Subgroup.centralizer ({t} : Set B)) : q ^ (2 ^ 23) = 1 := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  have hs' : orderOf (c * s * c⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  have hsx : c * s * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have h := Subgroup.mem_centralizer_singleton_iff.1 hts
    calc c * s * c⁻¹ * (c * t * c⁻¹) = c * (s * t) * c⁻¹ := by group
      _ = c * (t * s) * c⁻¹ := by rw [← h]
      _ = c * t * c⁻¹ * (c * s * c⁻¹) := by group
  have hq' := @conj_mem_gLAPPrimeCoreOf_centralizer B (inferInstance : Group B) p c s q hq
  have hqx : c * q * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have h := Subgroup.mem_centralizer_singleton_iff.1 hqt
    calc c * q * c⁻¹ * (c * t * c⁻¹) = c * (q * t) * c⁻¹ := by group
      _ = c * (t * q) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ * (c * q * c⁻¹) := by group
  obtain ⟨F, hF, hker⟩ := exists_hom_centralizer_xB
  have h1 := pow_two_pow_eq_one_of_local_quotient hp hp2 F hF hker hK hs' hsx hq' hqx
  have h2 : c * q ^ (2 ^ 23) * c⁻¹ = 1 := by
    rw [← conj_pow]
    exact h1
  calc q ^ (2 ^ 23) = c⁻¹ * (c * q ^ (2 ^ 23) * c⁻¹) * c := by group
    _ = 1 := by rw [h2]; group

end TwoBLocalP

section FiveOdd


theorem odd_card_gLAPPrimeCoreOf_B_of_five_central {s : B}
    (h6 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({s} : Set B))) :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set B)))) := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := Subgroup.centralizer ({s} : Set B) with hC
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 h6
  set P : Subgroup B := K.map C.subtype with hP
  have hPcard : Nat.card P = 5 ^ 6 := by
    rw [hP, Subgroup.card_map_of_injective C.subtype_injective, hK]
  have hPp : IsPGroup 5 P := IsPGroup.of_card hPcard
  have hPC : P ≤ C := Subgroup.map_subtype_le K
  refine odd_card_gLAPPrimeCoreOf_of_large_pGroup Nat.prime_five hPC hPp (k := 3) hPcard ?_ ?_
  · intro w hw hw1 R hRp hRw
    have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw) hw1
    obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 w hwo
    have h3 := card_isPGroup_five_le_of_babyInv hk hRp hRw
    calc Nat.card R * 5 ^ 3 ≤ 5 ^ 3 * 5 ^ 3 := Nat.mul_le_mul_right _ h3
      _ = 5 ^ 6 := by norm_num
  · intro m hm hmod
    rw [CFSG.RankThree.OddKernel.card_B_eq] at hm
    have hm41 : m ≤ 41 := by
      by_contra hlt
      have : 2 ^ 42 ∣ 4154781481226426191177580544000000 :=
        (pow_dvd_pow 2 (by omega : 42 ≤ m)).trans hm
      exact absurd this (by decide)
    have hcheck : ∀ m' < 42, 2 ^ m' % 125 = 1 → m' = 0 := by decide
    exact hcheck m (by omega) hmod

end FiveOdd

section Census


theorem exists_conj_mem_zpowers_zFive {s : B} (hs : orderOf s = 5)
    (h6 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({s} : Set B))) :
    ∃ c : B, c * s * c⁻¹ ∈ Subgroup.zpowers zFive := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hR := bFiveRel
  set C := Subgroup.centralizer ({s} : Set B) with hC
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 h6
  set S : Subgroup B := K.map C.subtype with hS
  have hScard : Nat.card S = 5 ^ 6 := by
    rw [hS, Subgroup.card_map_of_injective C.subtype_injective, hK]
  have hSC : S ≤ C := Subgroup.map_subtype_le K
  have h5 : (Nat.card B).factorization 5 = 6 := factorization_card_B_five
  let SS : Sylow 5 B := Sylow.ofCard S (by rw [hScard, h5])
  let PP : Sylow 5 B := Sylow.ofCard (FiveLocal.P xFive qFive) (by rw [hR.card_P, h5])
  have hsS : s ∈ S := by
    have hcs : ∀ y ∈ S, s * y = y * s := fun y hyS =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hSC hyS)).symm
    have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer (S : Set B) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hyS
        have e : s * y * s⁻¹ = y := by rw [hcs y hyS]; group
        rw [e]
        exact hyS
      · intro hyS
        have e : s * (s * y * s⁻¹) = (s * y * s⁻¹) * s := hcs _ hyS
        have e2 : s * y * s⁻¹ = y := by
          have e3 : s * y = y * s := by
            calc s * y = s⁻¹ * (s * (s * y * s⁻¹)) * s := by group
              _ = s⁻¹ * ((s * y * s⁻¹) * s) * s := by rw [e]
              _ = y * s := by group
          rw [e3]
          group
        rw [← e2]
        exact hyS
    have hpg : IsPGroup 5 (S ⊔ Subgroup.zpowers s : Subgroup B) :=
      IsPGroup.to_sup_of_normal_left' (IsPGroup.of_card hScard)
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])) hsN
    have hmax : S ⊔ Subgroup.zpowers s = S := SS.is_maximal' hpg le_sup_left
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B SS PP
  have hmemP : ∀ y : B, g * y * g⁻¹ ∈ FiveLocal.P xFive qFive ↔ y ∈ S := by
    intro y
    have e : (FiveLocal.P xFive qFive : Subgroup B) = ((g • SS : Sylow 5 B) : Subgroup B) := by
      rw [hg]
      rfl
    rw [e, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv]
    have e2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e2]
    try rfl
  refine ⟨g, mem_zpowers_of_commute_P hR ((hmemP s).2 hsS) fun p hp => ?_⟩
  have hy : g⁻¹ * p * g ∈ S := by
    rw [← hmemP]
    have e : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
    rw [e]
    exact hp
  have hcomm : s * (g⁻¹ * p * g) = (g⁻¹ * p * g) * s :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hSC hy)).symm
  calc g * s * g⁻¹ * p = g * (s * (g⁻¹ * p * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * p * g) * s) * g⁻¹ := by rw [hcomm]
    _ = p * (g * s * g⁻¹) := by group

end Census

section FiveCentral


theorem gLAPPrimeCoreOf_centralizer_zFive_eq_bot :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({zFive} : Set B)) = ⊥ := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hR := bFiveRel
  set C := Subgroup.centralizer ({zFive} : Set B) with hC
  set O := GLAPPrimeCoreOf 5 C with hO
  have hPC : FiveLocal.P xFive qFive ≤ C := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hR.mem_H0.1 (hR.P_le_H0 hg)).2
  have hodd : Odd (Nat.card O) := odd_card_gLAPPrimeCoreOf_B_of_five_central
    (hR.card_P ▸ Subgroup.card_dvd_of_le hPC)
  have hfix : ∀ w : B, BabyInv 1 w → w ∈ C → ∀ q ∈ O, w * q * w⁻¹ = q → q = 1 := by
    intro w hw hwC q hq hqw
    have hqw' : q ∈ Subgroup.centralizer ({w} : Set B) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc q * w = (w * q * w⁻¹) * w := by rw [hqw]
        _ = w * q := by group
    exact eq_one_of_pow_two_pow_of_odd hodd hq (pow_two_pow_eq_one_of_babyInv_one Nat.prime_five
      (by norm_num) oPrimeCoreTrivialAt_Co2_five hR.orderOf_z hw hwC hq hqw')
  have hinv : ∀ w : B, BabyInv 1 w → w ∈ C → ∀ q ∈ O, w * q * w⁻¹ = q⁻¹ := by
    intro w hw hwC
    have hww : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw.1, sq] at this
    exact inv_of_fixedPointFree_involution' (fun q hq => GLAPPrimeCoreOf_conj_mem w hwC q hq) hww
      (hfix w hw hwC)
  have hz5 : ∀ n : ℕ, n % 5 = 1 → zFive ^ n = zFive := fun n hn => by
    rw [← pow_mod_orderOf, hR.orderOf_z, hn, pow_one]
  have hconj := conj_pow_eq_pow_pow (G := B) hR.conj_hz
  have hzpow : ∀ (k b : ℕ), (hFive ^ k)⁻¹ * zFive ^ b * hFive ^ k = zFive ^ (2 ^ k * b) := by
    intro k b
    have := conj_pow (a := (hFive ^ k)⁻¹) (b := zFive) (i := b)
    rw [inv_inv] at this
    rw [← this, hconj k, ← pow_mul]
  have hxz : xFive * zFive = zFive * xFive := by
    have h := hR.conj_xz
    calc xFive * zFive = xFive * (xFive⁻¹ * zFive * xFive) := by rw [h]
      _ = zFive * xFive := by group
  have htC : tFive ∈ C := by
    have h : (hFive ^ 4)⁻¹ * zFive * hFive ^ 4 = zFive := by
      have := hzpow 4 1
      rw [pow_one, hz5 (2 ^ 4 * 1) (by norm_num)] at this
      exact this
    rw [hC, Subgroup.mem_centralizer_singleton_iff, tFive]
    calc hFive ^ 4 * zFive = hFive ^ 4 * ((hFive ^ 4)⁻¹ * zFive * hFive ^ 4) := by rw [h]
      _ = zFive * hFive ^ 4 := by group
  have hc1C : cOneFive ∈ C := by
    have h : hFive⁻¹ * zFive ^ 3 * hFive = zFive := by
      have := hzpow 1 3
      rw [pow_one, hz5 (2 ^ 1 * 3) (by norm_num)] at this
      exact this
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact conj_mul_comm_of_conj_pow (G := B) h hxz
  have hc2C : cTwoFive ∈ C := by
    have h : (hFive ^ 3)⁻¹ * zFive ^ 2 * hFive ^ 3 = zFive := by
      have := hzpow 3 2
      rw [hz5 (2 ^ 3 * 2) (by norm_num)] at this
      exact this
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact conj_mul_comm_of_conj_pow (G := B) h hxz
  have hxC : xFive ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxz
  have hconjB : ∀ c : B, BabyInv 1 (c * tFive * c⁻¹) := fun c =>
    ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact babyInv_one_tFive.1,
      (CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj (isConj_iff.2 ⟨c, rfl⟩)).symm.trans
        babyInv_one_tFive.2⟩
  have hTC : ∀ c ∈ C, c * tFive * c⁻¹ ∈ C := fun c hc => C.mul_mem (C.mul_mem hc htC) (C.inv_mem hc)
  have hT1 := hinv _ (hconjB cOneFive) (hTC _ hc1C)
  have hT2 := hinv _ (hconjB cTwoFive) (hTC _ hc2C)
  have hT3 := hinv _ (hconjB xFive) (hTC _ hxC)
  have ht := hinv _ babyInv_one_tFive htC
  have hu : ∀ q ∈ O, uFive * q * uFive⁻¹ = q := by
    intro q hq
    have hqi : q⁻¹ ∈ O := O.inv_mem hq
    set T1 := cOneFive * tFive * cOneFive⁻¹
    set T2 := cTwoFive * tFive * cTwoFive⁻¹
    set T3 := xFive * tFive * xFive⁻¹
    have hu : uFive = T1 * T2 * T3 * tFive := rfl
    calc uFive * q * uFive⁻¹ = T1 * (T2 * (T3 * (tFive * q * tFive⁻¹) * T3⁻¹) * T2⁻¹) * T1⁻¹ := by
          rw [hu]; group
      _ = T1 * (T2 * (T3 * q⁻¹ * T3⁻¹) * T2⁻¹) * T1⁻¹ := by rw [ht q hq]
      _ = T1 * (T2 * q⁻¹⁻¹ * T2⁻¹) * T1⁻¹ := by rw [hT3 q⁻¹ hqi]
      _ = T1 * q⁻¹ * T1⁻¹ := by rw [inv_inv, hT2 q hq]
      _ = q := by rw [hT1 q⁻¹ hqi, inv_inv]
  have huC : uFive ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem (hTC _ hc1C) (hTC _ hc2C)) (hTC _ hxC)) htC
  rw [eq_bot_iff]
  intro q hq
  exact (Subgroup.mem_bot).2 (hfix uFive babyInv_one_uFive huC q hq (hu q hq))

theorem gLAPPrimeCoreOf_B_eq_bot_of_five_central {s : B} (hs : orderOf s = 5)
    (h6 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({s} : Set B))) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set B)) = ⊥ := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hR := bFiveRel
  obtain ⟨c, hc⟩ := exists_conj_mem_zpowers_zFive hs h6
  rw [← gLAPPrimeCoreOf_centralizer_conj c s]
  have hco : orderOf (c * s * c⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  have hzp : Subgroup.zpowers (c * s * c⁻¹) = Subgroup.zpowers zFive := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hco, hR.orderOf_z]
  rw [centralizer_eq_of_zpowers_eq hzp]
  exact gLAPPrimeCoreOf_centralizer_zFive_eq_bot

end FiveCentral

@[expose] def BFiveNonCentral : Prop :=
  ∀ s : B, orderOf s = 5 → ¬ 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({s} : Set B)) →
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set B)) = ⊥

section Reduction


theorem oPrimeCoreTrivialAt_B_five_of_nonCentral (h : BFiveNonCentral) :
    OPrimeCoreTrivialAt 5 B := by
  intro s hs
  by_cases h6 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({s} : Set B))
  · exact gLAPPrimeCoreOf_B_eq_bot_of_five_central hs h6
  · exact h s hs h6

end Reduction

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
