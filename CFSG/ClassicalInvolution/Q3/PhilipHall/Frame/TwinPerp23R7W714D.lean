module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGenD
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7W14
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7ECent
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Mem
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
import CFSG.ClassicalInvolution.Q3.Q3CPSat
import CFSG.ClassicalInvolution.Q3.Q3CLSeven1
import CFSG.ClassicalInvolution.Q3.Q3CLSeven2
import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Q3.Q3T7P24A03
import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
import CFSG.ClassicalInvolution.Asc77.AscT8Layer
import CFSG.ClassicalInvolution.Asc77.AscE184Cent
import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
import CFSG.ClassicalInvolution.AschTight.Sec7L714D

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7V

section Act

variable {G : Type} [Group G]

theorem act_cases {Q W : Subgroup G} {a b t s j : G}
    (hidx : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ W → y ∉ W → x⁻¹ * y ∈ W) (hs : s ∈ Q) (hsW : s ∉ W)
    (hbW : ∀ x ∈ Q, x ∈ W → b⁻¹ * x * b = x)
    (hf : ∀ x ∈ Q, x ∉ W → Subgroup.zpowers (b⁻¹ * x * b * x⁻¹) = Q ⊓ W) (hQW : Q ⊓ W ≠ ⊥)
    (haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) (ha2 : a * a = 1)
    (hcomm : ∀ x ∈ Q, a * (b⁻¹ * x * b) * a⁻¹ = b⁻¹ * (a * x * a⁻¹) * b)
    (hj : ∀ d ∈ Q, d ∈ W → d * d = 1 → d = 1 ∨ d = j)
    (htW : ∀ x ∈ Q, x ∈ W → t * x * t⁻¹ = x) (hts : t * s * t⁻¹ = s * j) :
    (∀ x ∈ Q, a * x * a⁻¹ = x) ∨ (∀ x ∈ Q, a * x * a⁻¹ = t * x * t⁻¹) := by
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = b⁻¹ * s * b * s⁻¹ := ⟨_, rfl⟩
  have hconst : ∀ x ∈ Q, x ∉ W → b⁻¹ * x * b * x⁻¹ = c := by
    intro x hx hxW
    have hd : s⁻¹ * x ∈ W := hidx s hs x hx hsW hxW
    have hdQ : s⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hs) hx
    have h1 := hbW _ hdQ hd
    calc b⁻¹ * x * b * x⁻¹ = b⁻¹ * s * b * (b⁻¹ * (s⁻¹ * x) * b) * (s⁻¹ * x)⁻¹ * s⁻¹ := by group
      _ = c := by rw [h1, hcdef]; group
  have hc : Subgroup.zpowers c = Q ⊓ W := by rw [hcdef]; exact hf s hs hsW
  have hc1 : c ≠ 1 := by
    intro h
    apply hQW
    rw [← hc, h, Subgroup.zpowers_one_eq_bot]
  have hfW : ∀ x ∈ Q, x ∈ W → b⁻¹ * x * b * x⁻¹ = 1 := by
    intro x hx hxW
    rw [hbW x hx hxW, mul_inv_cancel]
  have hconj : ∀ x ∈ Q, a * (b⁻¹ * x * b * x⁻¹) * a⁻¹ =
      b⁻¹ * (a * x * a⁻¹) * b * (a * x * a⁻¹)⁻¹ := by
    intro x hx
    rw [← hcomm x hx]
    group
  have h4 : ∀ x ∈ Q, x ∈ W → a * x * a⁻¹ ∈ W := by
    intro x hx hxW
    by_contra h
    have h1 := hconst _ (haQ x hx) h
    rw [← hconj x hx, hfW x hx hxW, mul_one, mul_inv_cancel] at h1
    exact hc1 h1.symm
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haa : ∀ x : G, a * (a * x * a⁻¹) * a⁻¹ = x := by
    intro x
    rw [hainv]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group
  have h5 : a * s * a⁻¹ ∉ W := by
    intro h
    have := h4 _ (haQ s hs) h
    rw [haa] at this
    exact hsW this
  have h6 : a * c * a⁻¹ = c := by
    have h := hconj s hs
    rw [← hcdef, hconst _ (haQ s hs) h5] at h
    exact h
  have h6' : ∀ x ∈ Q, x ∈ W → a * x * a⁻¹ = x := by
    intro x hx hxW
    have hxc : x ∈ Subgroup.zpowers c := by rw [hc]; exact ⟨hx, hxW⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
    rw [← conj_zpow, h6]
  obtain ⟨d, hddef⟩ : ∃ d : G, d = s⁻¹ * (a * s * a⁻¹) := ⟨_, rfl⟩
  have hdW : d ∈ W := hddef ▸ hidx s hs _ (haQ s hs) hsW h5
  have hdQ : d ∈ Q := hddef ▸ Q.mul_mem (Q.inv_mem hs) (haQ s hs)
  have has : a * s * a⁻¹ = s * d := by rw [hddef]; group
  have hd2 : d * d = 1 := by
    have h1 : a * (a * s * a⁻¹) * a⁻¹ = s * d * d := by
      calc a * (a * s * a⁻¹) * a⁻¹ = a * (s * d) * a⁻¹ := by rw [has]
        _ = (a * s * a⁻¹) * (a * d * a⁻¹) := by group
        _ = s * d * d := by rw [has, h6' d hdQ hdW]
    rw [haa] at h1
    calc d * d = s⁻¹ * (s * d * d) := by group
      _ = s⁻¹ * s := by rw [← h1]
      _ = 1 := inv_mul_cancel s
  rcases hj d hdQ hdW hd2 with h1 | h1
  · left
    intro x hx
    by_cases hxW : x ∈ W
    · exact h6' x hx hxW
    · have he : s⁻¹ * x ∈ W := hidx s hs x hx hsW hxW
      have heQ : s⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hs) hx
      calc a * x * a⁻¹ = (a * s * a⁻¹) * (a * (s⁻¹ * x) * a⁻¹) := by group
        _ = x := by rw [has, h1, h6' _ heQ he]; group
  · right
    intro x hx
    by_cases hxW : x ∈ W
    · rw [h6' x hx hxW, htW x hx hxW]
    · have he : s⁻¹ * x ∈ W := hidx s hs x hx hsW hxW
      have heQ : s⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hs) hx
      calc a * x * a⁻¹ = (a * s * a⁻¹) * (a * (s⁻¹ * x) * a⁻¹) := by group
        _ = (t * s * t⁻¹) * (t * (s⁻¹ * x) * t⁻¹) := by
            rw [has, h1, h6' _ heQ he, htW _ heQ he, hts]
        _ = t * x * t⁻¹ := by group

theorem conj_eq_mul_of_mod {N : Subgroup G} {w₀ d b : G} (hw₀ : w₀ * b * w₀⁻¹ = b) (hd : d ∈ N)
    (hbN : b ∈ Subgroup.normalizer (N : Set G)) (hw₀N : w₀ ∈ Subgroup.normalizer (N : Set G)) :
    ∃ m ∈ N, (w₀ * d) * b * (w₀ * d)⁻¹ = b * m := by
  have h1 : b⁻¹ * d * b⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) d).mp hd
  have h2 : b⁻¹ * d * b⁻¹⁻¹ * d⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hd)
  refine ⟨w₀ * (b⁻¹ * d * b⁻¹⁻¹ * d⁻¹) * w₀⁻¹, (Subgroup.mem_normalizer_iff.mp hw₀N _).mp h2, ?_⟩
  calc (w₀ * d) * b * (w₀ * d)⁻¹ =
        (w₀ * b * w₀⁻¹) * (w₀ * (b⁻¹ * d * b⁻¹⁻¹ * d⁻¹) * w₀⁻¹) := by group
    _ = b * (w₀ * (b⁻¹ * d * b⁻¹⁻¹ * d⁻¹) * w₀⁻¹) := by rw [hw₀]

variable [Finite G]

theorem eq_of_inv_mul_mem {P N : Subgroup G} (hP : IsPGroup 2 P) (hN : Odd (Nat.card N))
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (h : x⁻¹ * y ∈ N) : x = y :=
  inv_mul_eq_one.mp
    (Sec13.L94T.eq_one_of_isPGroup_of_odd hP hN (P.mul_mem (P.inv_mem hx) hy) h)

theorem conj_comm_of_mod {Q N : Subgroup G} (hQ : IsPGroup 2 Q) (hN : Odd (Nat.card N))
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) {a b m : G} (hm : m ∈ N)
    (hab : a * b * a⁻¹ = b * m) (haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (hbQ : ∀ x ∈ Q, b⁻¹ * x * b ∈ Q) :
    ∀ x ∈ Q, a * (b⁻¹ * x * b) * a⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by
  intro x hx
  have hy : b⁻¹ * (a * x * a⁻¹) * b ∈ Q := hbQ _ (haQ x hx)
  have hl : a * (b⁻¹ * x * b) * a⁻¹ ∈ Q := haQ _ (hbQ x hx)
  have e : a * (b⁻¹ * x * b) * a⁻¹ = m⁻¹ * (b⁻¹ * (a * x * a⁻¹) * b) * m := by
    have h1 : a * (b⁻¹ * x * b) * a⁻¹ =
        (a * b * a⁻¹)⁻¹ * (a * x * a⁻¹) * (a * b * a⁻¹) := by group
    rw [h1, hab]
    group
  symm
  refine eq_of_inv_mul_mem hQ hN hy hl ?_
  rw [e]
  generalize b⁻¹ * (a * x * a⁻¹) * b = y at hy ⊢
  have hyN : y⁻¹ ∈ Subgroup.normalizer (N : Set G) := Subgroup.inv_mem _ (hQN hy)
  have h1 : y⁻¹ * m⁻¹ * y⁻¹⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hyN _).mp (N.inv_mem hm)
  have e2 : y⁻¹ * (m⁻¹ * y * m) = (y⁻¹ * m⁻¹ * y⁻¹⁻¹) * m := by group
  rw [e2]
  exact N.mul_mem h1 hm

end Act

section Gen

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_closure_three {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    IsPGroup 2 (Subgroup.closure ({a, b, c} : Set G)) := by
  have hsq := F7I.closure_sq_of_comm (X := ({a, b, c} : Set G))
    (by rintro x (rfl | rfl | rfl); exacts [ha, hb, hc])
    (by
      rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
      exacts [rfl, hab, hac, hab.symm, rfl, hbc, hac.symm, hbc.symm, rfl])
  intro x
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩

theorem closure_three_le {H : Subgroup G} {a b c : G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    Subgroup.closure ({a, b, c} : Set G) ≤ H := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl) <;> assumption

theorem exists_sylow_comm_pair {J V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hVN : V ≤ Subgroup.normalizer (J : Set G)) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (hJa : CentMod J a) (hJb : CentMod J b) :
    ∃ R' : Subgroup G, IsSylow2In R' J ∧ V ≤ Subgroup.normalizer (R' : Set G) ∧
      (∀ r ∈ R', r * a = a * r) ∧ ∀ r ∈ R', r * b = b * r := by
  obtain ⟨T, hT, hVT⟩ := Asc77.IsSylow2In.exists_ge hV2 (le_sup_right : V ≤ J ⊔ V)
  have hTJ : IsSylow2In (T ⊓ J) J :=
    Asc77.isSylow2In_inf_of_le_normalizer hT le_sup_left (sup_le Subgroup.le_normalizer hVN)
  have hcomm : ∀ x ∈ V, CentMod J x → ∀ r ∈ T ⊓ J, r * x = x * r := by
    intro x hxV hx r hr
    have hxT : x ∈ T := hVT hxV
    have hrT : r ∈ T := hr.1
    have hcT : x * r * x⁻¹ * r⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem hxT hrT) (T.inv_mem hxT)) (T.inv_mem hrT)
    have h1 := Sec13.L94T.eq_one_of_isPGroup_of_odd hT.2.1 (odd_natCard_oddCoreOf J) hcT
      (hx r hr.2)
    have := congrArg (· * (r * x)) h1
    simp only [one_mul] at this
    rw [← this]
    group
  refine ⟨T ⊓ J, hTJ, fun v hv => ?_, hcomm a ha hJa, hcomm b hb hJb⟩
  have hvT : v ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer (hVT hv)
  have hvJ : v ∈ Subgroup.normalizer (J : Set G) := hVN hv
  rw [Subgroup.mem_normalizer_iff] at hvT hvJ ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hvT x) (hvJ x)

theorem exists_D_conj' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {E J R' : Subgroup G}
    (hE : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set G)))
    (hR'E : R' ≤ E) (hJ : J ∈ Ω) (hR' : IsSylow2In R' J) {z : G} (hz : IsUniqueInvolution J z)
    (hzW : z ∈ W) (hfix : ∀ c : G, c * z = z * c → Odd (orderOf c) → conjSub c J = J) :
    ∃ o ∈ oddCoreOf E, conjSub o⁻¹ R' ∈ DSet Ω W ∧ IsSylow2In (conjSub o⁻¹ R') J := by
  obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hE hR'.2.1 hR'E
  set Q := conjSub o⁻¹ R' with hQdef
  have hmemQ : ∀ x ∈ Q, o * x * o⁻¹ ∈ R' := by
    intro x hx
    rw [hQdef, mem_conjSub_iff, inv_inv] at hx
    exact hx
  have hQN : Q ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    have := hoN _ (hmemQ x hx)
    have e : o⁻¹ * (o * x * o⁻¹) * o = x := by group
    rwa [e] at this
  have hQR : Q ∈ RSet Ω :=
    Q3CL.Thompson.conjSub_mem_RSet hΩ (Asc77.mem_RSet_of_isSylow2In hJ hR') o⁻¹
  have hQD : Q ∈ DSet Ω W := ⟨hQR, hQN⟩
  have hJo : conjSub o⁻¹ J ∈ Ω := hΩ.conjInvariant o⁻¹ J hJ
  have hQJo : IsSylow2In Q (conjSub o⁻¹ J) := hR'.conj o⁻¹
  have hzo : IsUniqueInvolution (conjSub o⁻¹ J) (o⁻¹ * z * o⁻¹⁻¹) :=
    TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz o⁻¹
  have hzoW : o⁻¹ * z * o⁻¹⁻¹ ∈ W := F7G.inv_mem_W hΩ hW hQD hJo hQJo hzo
  have hzR' : z ∈ R' := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hz hR'
  have hzE : z ∈ E := hR'E hzR'
  have hd1 : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) ∈ W := W.mul_mem (W.inv_mem hzW) hzoW
  have hd2 : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) ∈ oddCoreOf E := by
    have hzN := Sec7.le_normalizer_oddCoreOf E (E.inv_mem hzE)
    have h1 : z⁻¹ * o⁻¹ * z⁻¹⁻¹ ∈ oddCoreOf E :=
      (Subgroup.mem_normalizer_iff.mp hzN _).mp ((oddCoreOf E).inv_mem ho)
    have e : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) = (z⁻¹ * o⁻¹ * z⁻¹⁻¹) * o := by group
    rw [e]
    exact (oddCoreOf E).mul_mem h1 ho
  have hd := Sec13.L94T.eq_one_of_isPGroup_of_odd (Asc77.Thompson.isPGroup_of_mem_WSet hW)
    (odd_natCard_oddCoreOf E) hd1 hd2
  have hoz : o⁻¹ * z = z * o⁻¹ := by
    have h := congrArg (z * ·) hd
    simp only [mul_one, mul_inv_cancel_left] at h
    calc o⁻¹ * z = (o⁻¹ * z * o⁻¹⁻¹) * o⁻¹ := by group
      _ = z * o⁻¹ := by rw [h]
  have hodd : Odd (orderOf o⁻¹) := by
    rw [orderOf_inv]
    exact Odd.of_dvd_nat (odd_natCard_oddCoreOf E) (Subgroup.orderOf_dvd_natCard _ ho)
  have hfixJ := hfix o⁻¹ hoz hodd
  exact ⟨o, ho, hQD, hfixJ ▸ hQJo⟩

end Gen

end F7V

section Steps

variable {n : ℕ}

theorem p23E7W714_proved : P23E7W714 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd w hw hwN
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  haveI : Fact (Q3CL.ClassicalClause (Om R)) := ⟨hPG.cls⟩
  have hd := hc.data
  have hW : W ∈ WSet (Om R) := hd.hW
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hKg : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hzg : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    have := TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz g
    rwa [hd.hgt] at this
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have c : Q3CL.Thompson.Ctx (Om R) W := Q3CL.T8.ctxOf hPG hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hne_ue⟩ := e_decomp hc
  have hinv : ∀ {J : Subgroup Y}, IsUniqueInvolution J t → IsUniqueInvolution J (u * e) → False :=
    fun h1 h2 => by
      rcases h1.unique _ h2.mem h2.sq with h | h
      · exact h2.ne_one h
      · exact hne_ue h
  have hfixK : ∀ c : Y, c * t = t * c → Odd (orderOf c) → conjSub c (tightCore R) = tightCore R :=
    fun c hct hodd => (hc.conjSub_eq_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hct) hodd).1
  have hfixKg : ∀ c : Y, c * (u * e) = (u * e) * c → Odd (orderOf c) →
      conjSub c (conjSub g (tightCore R)) = conjSub g (tightCore R) :=
    fun c hc' hodd => hc.conjSub_eq_of_odd_ue hc' hodd
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have htW : t ∈ W := hd.hzW
  have hueW : u * e ∈ W := W.mul_mem hd.huW heW
  have hw2 : w * w = 1 := hZd.sq w hw
  have ht2 : t * t = 1 := hZd.sq t hZd.ht
  have he2 : e * e = 1 := hd.he2
  have hwe : w * e = e * w := hZd.comm w hw e hZd.he
  have hwt : w * t = t * w := hZd.comm w hw t hZd.ht
  have hte : t * e = e * t := hWab t htW e heW
  have htue : t * (u * e) = (u * e) * t := hWab t htW _ hueW
  obtain ⟨hKw, -⟩ := hZd.centMod hc hw
  obtain ⟨heK, -, heJ⟩ := hc.centMod_e
  have hKJ : tightCore R ≠ conjSub g (tightCore R) := fun h => hinv hz (by rw [h]; exact hzg)
  have hnot : conjSub g (tightCore R) ∉ omegaNbr (Om R) (tightCore R) := by
    intro h
    have h' : conjSub g (tightCore R) ∈ KPerp (Om R) (tightCore R) := Or.inr h
    rw [hperp] at h'
    rcases h' with h' | h'
    · exact hKJ h'.symm
    · have h'' : conjSub g (tightCore R) = K' := h'
      exact hinv hz' (by rw [← h'']; exact hzg)
  set E := rLayer (Om R) e with hEdef
  have hEc : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set Y)) := hE
  have hNodd : Odd (Nat.card (oddCoreOf E)) := odd_natCard_oddCoreOf E
  have hEN : E ≤ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) :=
    Sec7.le_normalizer_oddCoreOf E
  have hCeN : ∀ x : Y, x * e = e * x →
      x ∈ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({e} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hx
    have h1 : conjSub x E = E := Asc77.T8.rLayer_conjSub_eq hΩ.conjInvariant hxC
    rw [mem_normalizer_iff_conjSub_eq, ← Asc77.Thompson.oddCoreOf_conjSub_eq, h1]
  have hwNN := hCeN w hwe
  have htNN := hCeN t hte
  have hNe : Subgroup.normalizer (W : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) :=
    normalizer_le_centralizer_e hd
  have hDE : ∀ P ∈ DSet (Om R) W, P ≤ E := fun P hP => F7C.le_rLayer hP.1 (hP.2.trans hNe)
  have hle : ∀ {J' R' : Subgroup Y}, J' ∈ Om R → IsSylow2In R' J' →
      R' ≤ Subgroup.centralizer ({e} : Set Y) → R' ≤ E := fun hJ hR' hR'e =>
    F7C.le_rLayer (Asc77.mem_RSet_of_isSylow2In hJ hR') hR'e
  have hcenE : ∀ {R' : Subgroup Y}, (∀ r ∈ R', r * e = e * r) →
      R' ≤ Subgroup.centralizer ({e} : Set Y) := fun h r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h r hr)
  have heJN : e ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) :=
    F7E.mem_normalizer_of_centMod heJ he2
  have hV2 : IsPGroup 2 (Subgroup.closure ({w, t, e} : Set Y)) :=
    F7V.isPGroup_closure_three hw2 ht2 he2 hwt hwe hte
  have hwV : w ∈ Subgroup.closure ({w, t, e} : Set Y) := Subgroup.subset_closure (by simp)
  have htV : t ∈ Subgroup.closure ({w, t, e} : Set Y) := Subgroup.subset_closure (by simp)
  have heV : e ∈ Subgroup.closure ({w, t, e} : Set Y) := Subgroup.subset_closure (by simp)
  obtain ⟨R₀, hR₀, -, hR₀w, hR₀e⟩ := F7V.exists_sylow_comm_pair hV2
    (F7V.closure_three_le (F7E.mem_normalizer_of_centMod hKw hw2) (Subgroup.le_normalizer hz.mem)
      (F7E.mem_normalizer_of_centMod heK he2)) hwV heV hKw heK
  obtain ⟨o, ho, hQ₀D, hQ₀⟩ :=
    F7V.exists_D_conj' hΩ hW hEc (hle hK hR₀ (hcenE hR₀e)) hK hR₀ hz htW hfixK
  have htact : ∀ Q : Subgroup Y, Q ∈ DSet (Om R) W → IsSylow2In Q (conjSub g (tightCore R)) →
      ∀ x ∈ Q, x ∉ W → t * x * t⁻¹ = (u * e) * x := by
    intro Q hQD hQ x hx hxW
    have h := Q3CL.Thompson.conj_involution_eq_mul' Sec6Gen.l6_2Gen hΩ hW hK hKg hKJ hQ₀D hQD hQ₀ hQ
      hnot hz hzg hx hxW
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    calc t * x * t⁻¹ = t⁻¹ * (x * t * x⁻¹) * x := by rw [hti]; group
      _ = (u * e) * x := by rw [h]; group
  have htQ : ∀ Q : Subgroup Y, Q ∈ DSet (Om R) W → IsSylow2In Q (conjSub g (tightCore R)) →
      ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := by
    intro Q hQD hQ x hx
    by_cases hxW : x ∈ W
    · rw [hWab t htW x hxW, mul_inv_cancel_right]
      exact hx
    · rw [htact Q hQD hQ x hx hxW]
      exact Q.mul_mem (Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hzg hQ) hx
  have htNQ : ∀ Q : Subgroup Y, Q ∈ DSet (Om R) W → IsSylow2In Q (conjSub g (tightCore R)) →
      t ∈ Subgroup.normalizer (Q : Set Y) := by
    intro Q hQD hQ
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨htQ Q hQD hQ x, fun hx => ?_⟩
    have := htQ Q hQD hQ _ hx
    have e' : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [hti]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht2]; group
    rwa [e'] at this
  have hV'2 : IsPGroup 2 (Subgroup.closure ({w, e, e} : Set Y)) :=
    F7V.isPGroup_closure_three hw2 he2 he2 hwe hwe rfl
  have heV' : e ∈ Subgroup.closure ({w, e, e} : Set Y) := Subgroup.subset_closure (by simp)
  obtain ⟨R₂, hR₂, -, hR₂e, -⟩ := F7V.exists_sylow_comm_pair hV'2
    (F7V.closure_three_le hwN heJN heJN) heV' heV' heJ heJ
  obtain ⟨o₂, -, hQ₂D, hQ₂⟩ :=
    F7V.exists_D_conj' hΩ hW hEc (hle hKg hR₂ (hcenE hR₂e)) hKg hR₂ hzg hueW hfixKg
  have htJ : t ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) :=
    hc.mem_normalizer_of_sylow hQ₂ htue (htNQ _ hQ₂D hQ₂)
  obtain ⟨R₁, hR₁, hVR₁, hR₁e, -⟩ := F7V.exists_sylow_comm_pair hV2
    (F7V.closure_three_le hwN htJ heJN) heV heV heJ heJ
  have hR₁E : R₁ ≤ E := hle hKg hR₁ (hcenE hR₁e)
  obtain ⟨o₁, ho₁, hQ₁D, hQ₁⟩ := F7V.exists_D_conj' hΩ hW hEc hR₁E hKg hR₁ hzg hueW hfixKg
  have hwR₁ : ∀ r ∈ R₁, w * r * w⁻¹ ∈ R₁ := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hVR₁ hwV) r).mp hr
  have htR₁ : ∀ r ∈ R₁, t * r * t⁻¹ ∈ R₁ := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hVR₁ htV) r).mp hr
  have hoE : o ∈ E := oddCoreOf_le_self E ho
  have ho₁E : o₁ ∈ E := oddCoreOf_le_self E ho₁
  obtain ⟨b, hb⟩ := Q3.Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW hQ₀D
  obtain ⟨v, hv⟩ := Q3.Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW hQ₁D
  obtain ⟨r₀, hr₀, hr₀W⟩ := c.exists_not_mem_W hQ₀D hK hQ₀
  obtain ⟨s, hs, hsW⟩ := c.exists_not_mem_W hQ₁D hKg hQ₁
  have hbm : b ∈ conjSub o⁻¹ R₀ ⊓ W := hb ▸ Subgroup.mem_zpowers b
  let ρ : Asc77.Thompson.Rep (Om R) W := ⟨tightCore R, conjSub o⁻¹ R₀, r₀, hK, hQ₀D, hQ₀, hr₀, hr₀W⟩
  have hrel : ∀ x ∈ conjSub o₁⁻¹ R₁, x ∉ W →
      Subgroup.zpowers (b⁻¹ * x * b * x⁻¹) = conjSub o₁⁻¹ R₁ ⊓ W := by
    intro x hx hxW
    let σ : Asc77.Thompson.Rep (Om R) W := ⟨conjSub g (tightCore R), conjSub o₁⁻¹ R₁, x, hKg, hQ₁D,
      hQ₁, hx, hxW⟩
    obtain ⟨v', hv', h1, -⟩ := c.rel_exact (ρ := ρ) (σ := σ) hKJ hnot hb hv
    have h1' : x * b * x⁻¹ = b * v' := h1
    have e' : b⁻¹ * x * b * x⁻¹ = v' := by
      calc b⁻¹ * x * b * x⁻¹ = b⁻¹ * (x * b * x⁻¹) := by group
        _ = v' := by rw [h1']; group
    rw [e', hv', hv]
  have hbW' : ∀ x ∈ conjSub o₁⁻¹ R₁, x ∈ W → b⁻¹ * x * b = x := fun x _ hxW => by
    rw [mul_assoc, hWab x hxW b hbm.2, inv_mul_cancel_left]
  have hbQ₁ : ∀ x ∈ conjSub o₁⁻¹ R₁, b⁻¹ * x * b ∈ conjSub o₁⁻¹ R₁ := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hbW' x hx hxW]
      exact hx
    · have h1 : b⁻¹ * x * b * x⁻¹ ∈ conjSub o₁⁻¹ R₁ := by
        have := Subgroup.mem_zpowers (b⁻¹ * x * b * x⁻¹)
        rw [hrel x hx hxW] at this
        exact this.1
      have e' : b⁻¹ * x * b = (b⁻¹ * x * b * x⁻¹) * x := by group
      rw [e']
      exact (conjSub o₁⁻¹ R₁).mul_mem h1 hx
  have hw₀b : (o⁻¹ * w * o) * b * (o⁻¹ * w * o)⁻¹ = b := by
    have hr : o * b * o⁻¹ ∈ R₀ := by
      have : b ∈ conjSub o⁻¹ R₀ := hbm.1
      rw [mem_conjSub_iff, inv_inv] at this
      exact this
    have h1 := hR₀w _ hr
    calc (o⁻¹ * w * o) * b * (o⁻¹ * w * o)⁻¹ = o⁻¹ * (w * (o * b * o⁻¹)) * w⁻¹ * o := by group
      _ = o⁻¹ * ((o * b * o⁻¹) * w) * w⁻¹ * o := by rw [h1]
      _ = b := by group
  have hw₁Q : ∀ x ∈ conjSub o₁⁻¹ R₁,
      (o₁⁻¹ * w * o₁) * x * (o₁⁻¹ * w * o₁)⁻¹ ∈ conjSub o₁⁻¹ R₁ := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx ⊢
    have e' : o₁ * ((o₁⁻¹ * w * o₁) * x * (o₁⁻¹ * w * o₁)⁻¹) * o₁⁻¹ =
        w * (o₁ * x * o₁⁻¹) * w⁻¹ := by group
    rw [e']
    exact hwR₁ _ hx
  have hw₁2 : (o₁⁻¹ * w * o₁) * (o₁⁻¹ * w * o₁) = 1 := by
    calc (o₁⁻¹ * w * o₁) * (o₁⁻¹ * w * o₁) = o₁⁻¹ * (w * w) * o₁ := by group
      _ = 1 := by rw [hw2]; group
  have hdN : (o⁻¹ * w * o)⁻¹ * (o₁⁻¹ * w * o₁) ∈ oddCoreOf E := by
    have hwN' : w⁻¹ ∈ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) :=
      Subgroup.inv_mem _ hwNN
    have h1 : w⁻¹ * (o * o₁⁻¹) * w⁻¹⁻¹ ∈ oddCoreOf E :=
      (Subgroup.mem_normalizer_iff.mp hwN' _).mp
        ((oddCoreOf E).mul_mem ho ((oddCoreOf E).inv_mem ho₁))
    have e' : (o⁻¹ * w * o)⁻¹ * (o₁⁻¹ * w * o₁) = o⁻¹ * (w⁻¹ * (o * o₁⁻¹) * w⁻¹⁻¹) * o₁ := by
      group
    rw [e']
    exact (oddCoreOf E).mul_mem ((oddCoreOf E).mul_mem ((oddCoreOf E).inv_mem ho) h1) ho₁
  have hw₀N : o⁻¹ * w * o ∈ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hEN hoE)) hwNN) (hEN hoE)
  have hbN : b ∈ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) :=
    hEN (hDE _ hQ₀D hbm.1)
  obtain ⟨m, hm, hm'⟩ := F7V.conj_eq_mul_of_mod hw₀b hdN hbN hw₀N
  rw [mul_inv_cancel_left] at hm'
  have hcomm := F7V.conj_comm_of_mod hQ₁.2.1 hNodd ((hDE _ hQ₁D).trans hEN) hm hm' hw₁Q hbQ₁
  have hjc : s * (u * e) = (u * e) * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hzg (hQ₁.1 hs))
  have hts : t * s * t⁻¹ = s * (u * e) := by
    rw [htact _ hQ₁D hQ₁ s hs hsW, hjc]
  have htW' : ∀ x ∈ conjSub o₁⁻¹ R₁, x ∈ W → t * x * t⁻¹ = x := fun x _ hxW => by
    rw [hWab t htW x hxW, mul_inv_cancel_right]
  have hQW : conjSub o₁⁻¹ R₁ ⊓ W ≠ ⊥ := by
    intro h
    have h1 : u * e ∈ conjSub o₁⁻¹ R₁ ⊓ W :=
      ⟨Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hzg hQ₁, hueW⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hzg.ne_one h1
  have hcases := F7V.act_cases (fun x hx y hy hxW hyW =>
      Q3CL.Thompson.D_inv_mul_mem hΩ hW hQ₁D hx hy hxW hyW) hs hsW hbW' hrel hQW hw₁Q hw₁2 hcomm
    (fun d hd _ hd2 => hzg.unique d (hQ₁.1 hd) hd2) htW' hts
  have hback : ∀ r ∈ R₁, o₁⁻¹ * r * o₁ ∈ conjSub o₁⁻¹ R₁ := by
    intro r hr
    rw [mem_conjSub_iff, inv_inv]
    have e' : o₁ * (o₁⁻¹ * r * o₁) * o₁⁻¹ = r := by group
    rw [e']
    exact hr
  have hconjR : ∀ r ∈ R₁, (o₁⁻¹ * w * o₁) * (o₁⁻¹ * r * o₁) * (o₁⁻¹ * w * o₁)⁻¹ =
      o₁⁻¹ * (w * r * w⁻¹) * o₁ := fun r _ => by group
  rcases hcases with h | h
  · left
    refine F7W.centMod_of_sylow hzg hR₁ hw2 hwN fun r hr => ?_
    have h1 := h _ (hback r hr)
    rw [hconjR r hr] at h1
    have h2 : w * r * w⁻¹ = r := by
      calc w * r * w⁻¹ = o₁ * (o₁⁻¹ * (w * r * w⁻¹) * o₁) * o₁⁻¹ := by group
        _ = o₁ * (o₁⁻¹ * r * o₁) * o₁⁻¹ := by rw [h1]
        _ = r := by group
    calc r * w = (w * r * w⁻¹) * w := by rw [h2]
      _ = w * r := by group
  · right
    have hwr : ∀ r ∈ R₁, w * r * w⁻¹ = t * r * t⁻¹ := by
      intro r hr
      have h1 := h _ (hback r hr)
      rw [hconjR r hr] at h1
      have h2 : w * r * w⁻¹ = (o₁ * t * o₁⁻¹) * r * (o₁ * t * o₁⁻¹)⁻¹ := by
        calc w * r * w⁻¹ = o₁ * (o₁⁻¹ * (w * r * w⁻¹) * o₁) * o₁⁻¹ := by group
          _ = o₁ * (t * (o₁⁻¹ * r * o₁) * t⁻¹) * o₁⁻¹ := by rw [h1]
          _ = (o₁ * t * o₁⁻¹) * r * (o₁ * t * o₁⁻¹)⁻¹ := by group
      have hrE : r ∈ E := hR₁E hr
      symm
      refine F7V.eq_of_inv_mul_mem hR₁.2.1 hNodd (htR₁ r hr) (hwR₁ r hr) ?_
      rw [h2]
      have hn : t⁻¹ * o₁ * t⁻¹⁻¹ * o₁⁻¹ ∈ oddCoreOf E :=
        (oddCoreOf E).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htNN) _).mp ho₁)
          ((oddCoreOf E).inv_mem ho₁)
      have hn' : r⁻¹ * (t⁻¹ * o₁ * t⁻¹⁻¹ * o₁⁻¹) * r⁻¹⁻¹ * (t⁻¹ * o₁ * t⁻¹⁻¹ * o₁⁻¹)⁻¹ ∈
          oddCoreOf E :=
        (oddCoreOf E).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hEN hrE)) _).mp hn)
          ((oddCoreOf E).inv_mem hn)
      have e' : (t * r * t⁻¹)⁻¹ * ((o₁ * t * o₁⁻¹) * r * (o₁ * t * o₁⁻¹)⁻¹) =
          t * (r⁻¹ * (t⁻¹ * o₁ * t⁻¹⁻¹ * o₁⁻¹) * r⁻¹⁻¹ * (t⁻¹ * o₁ * t⁻¹⁻¹ * o₁⁻¹)⁻¹) * t⁻¹ := by
        group
      rw [e']
      exact (Subgroup.mem_normalizer_iff.mp htNN _).mp hn'
    refine F7W.centMod_of_sylow hzg hR₁ (hZd.sq _ (Z.mul_mem hw hZd.ht))
      (Subgroup.mul_mem _ hwN htJ) fun r hr => ?_
    have h1 := hwr _ (htR₁ r hr)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h2 : t * (t * r * t⁻¹) * t⁻¹ = r := by
      rw [hti]
      calc t * (t * r * t) * t = (t * t) * r * (t * t) := by group
        _ = r := by rw [ht2]; group
    calc r * (w * t) = (w * (t * r * t⁻¹) * w⁻¹) * (w * t) := by rw [h1, h2]
      _ = (w * t) * r := by group

theorem p23E7Not9C_of_LL (h1 : P23E7LL1 n) (h2 : P23E7LL2 n) (h3 : P23E7LL3 n) : P23E7Not9C n :=
  p23E7Not9C_of_w714' p23E7W714_proved h1 h2 h3

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
