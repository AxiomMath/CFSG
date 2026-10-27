module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem22A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem22

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem data_of_card_eq_prime_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    {T L V H P U I : Subgroup G} {h v : G} {p : ℕ} (hyp : Hyp1223 G T L V)
    (hpre : Pre12_2_21 T L V H P U I h p) (hUO : U ≤ pCoreOf 2 H) (hcard : Nat.card P = p)
    (hvV : v ∈ V) (hvU : v ∉ U) (hvh : v * h * v⁻¹ = h⁻¹) (hhI : h ∈ I)
    (hCU : ∀ y ∈ U, h * y * h⁻¹ = y → y = 1) :
    Data12_2_22 V H P U (conjClosure U P) v p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, hhP, hhM, hI, hUI, hUdec, -, hUe, -,
    -, hidx, hcV, htr⟩ := hpre
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hPz, hord⟩ := Lem21.eq_zpowers_of_card_eq_prime hp hcard hhP hh1
  have hhp : h ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic_F4 h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hOH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hIU : I ≤ Subgroup.normalizer (U : Set G) :=
    hUI ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  have hVI : V ≤ I := hI ▸ le_sup_left
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hIU hhI
  have hhH : h ∈ H := hPH hhP
  have hvH : v ∈ H := hTH (hVT hvV)
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := by
    rw [hPz]
    exact (Subgroup.zpowers_le).mpr hhU
  have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
      ∀ y ∈ X, g * y * g⁻¹ ∈ X := fun hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy

  have hW : conjClosure U P = U :=
    le_antisymm (conjClosure_le fun x hx y hy => hconj (hPU hx) y hy) (le_conjClosure U P)
  have hUcomm : U = ⁅U, P⁆ := by
    rw [hPz]
    exact eq_commutator_zpowers hhU hCU

  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hTUV : T ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
    rw [hUV]
    exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO (hTH ht), hTV ht⟩

  have hconjUV : ∀ g ∈ H, ∀ y ∈ U ⊓ V, g * y * g⁻¹ ∈ U := by
    intro g hg y hy
    obtain ⟨x, hx, t, ht, rfl⟩ :=
      Lem22.exists_mul_of_mem_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hHPT hg
    have h1 : t * y * t⁻¹ ∈ U ⊓ V := hconj (hTUV ht) y hy
    have e : x * t * y * (x * t)⁻¹ = x * (t * y * t⁻¹) * x⁻¹ := by group
    rw [e]
    exact hconj (hPU hx) _ h1.1
  have hconjU : ∀ g ∈ H, ∀ y ∈ U, g * y * g⁻¹ ∈ U := by
    intro g hg y hy
    have hmap : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      conv_lhs => rw [hUdec]
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact hconjUV g hg w hw
      · rintro _ ⟨w, ⟨hwU, hwV⟩, rfl⟩
        have hw' : h * w * h⁻¹ ∈ U ⊓ V :=
          ⟨hconj hhU w hwU, Lem21Post.mem_conjugate_iff.mp hwV⟩
        have e : (MulAut.conj g).toMonoidHom w = (g * h⁻¹) * (h * w * h⁻¹) * (g * h⁻¹)⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact hconjUV _ (H.mul_mem hg (H.inv_mem hhH)) _ hw'
    exact hmap ⟨y, hy, rfl⟩
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    Sec121Swap.mem_normalizer_of_conj_mem fun y hy => hconjU g hg y hy

  have hUH : U ≤ H := hUO.trans hOH
  have hUn : (U.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
  have hOh : ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ * q⁻¹ ∈ U := by
    intro q hq
    have h1 := comm_mem_of_inv (K := ↥H) (U₀ := U.subgroupOf H) (Q := (pCoreOf 2 H).subgroupOf H)
      (v := ⟨v, hvH⟩) (h := ⟨h, hhH⟩) hpodd (Subtype.ext (by simpa using hhp))
      (Subtype.ext (by simpa using hvh)) (fun r hr => by
        have hrO : (r : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hr
        rw [Subgroup.mem_subgroupOf]
        show v * (r : G) * v⁻¹ * (r : G)⁻¹ ∈ U
        have h2 : v * (r : G) * v⁻¹ * (r : G)⁻¹ ∈ pCoreOf 2 H ⊓ V := by
          refine ⟨Subgroup.mul_mem _ (hconj (hHO hvH) _ hrO) (Subgroup.inv_mem _ hrO), ?_⟩
          have e : v * (r : G) * v⁻¹ * (r : G)⁻¹ = v * ((r : G) * v⁻¹ * (r : G)⁻¹) := by group
          rw [e]
          exact V.mul_mem hvV (hconj (hTV (hQT hrO)) _ (V.inv_mem hvV))
        rw [← hUV] at h2
        exact h2.1)
      (fun r hr => by
        rw [Subgroup.mem_subgroupOf] at hr ⊢
        exact hconj (hHO hhH) _ hr) ⟨q, hOH hq⟩ (Subgroup.mem_subgroupOf.mpr hq)
    exact Subgroup.mem_subgroupOf.mp h1

  have hON : pCoreOf 2 H ≤ Subgroup.normalizer ((P ⊔ U : Subgroup G) : Set G) := by
    intro q hq
    have hqH := hOH hq
    have hqh : q * h * q⁻¹ ∈ P ⊔ U := by
      have e : q * h * q⁻¹ = (h * q * h⁻¹ * q⁻¹)⁻¹ * h := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (U.inv_mem (hOh q hq)))
        (Subgroup.mem_sup_left hhP)
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    have hmap : (P ⊔ U).map (MulAut.conj q).toMonoidHom ≤ P ⊔ U := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        rw [hPz] at hw
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ hqh k
      · rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.mem_sup_right (hconjU q hqH w hw)
    exact hmap ⟨y, hy, rfl⟩

  have hO2le : oTwoUpper H ≤ P ⊔ U := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, hk⟩ := Lem22.exists_pow_mem_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hx
    have hsup : P ⊔ pCoreOf 2 H = (P ⊔ U) ⊔ pCoreOf 2 H :=
      le_antisymm (sup_le_sup_right le_sup_left _) (sup_le (sup_le le_sup_left
        (hUO.trans le_sup_right)) le_sup_right)
    rw [hsup, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left (P ⊔ U) (pCoreOf 2 H) hON] at hk
    obtain ⟨b, hb, q, hq, hbq⟩ := hk
    have hbq' : b * q = x ^ 2 ^ k := hbq
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨q, hq⟩
    have hm' : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨b', hb', hpow⟩ := A4.exists_pow_mul_eq hb (hON hq) (2 ^ m)
    refine ⟨k + m, ?_⟩
    rw [pow_add, pow_mul, ← hbq', hpow, hm', mul_one]
    exact hb'

  have hle2 : P ⊔ U ≤ oTwoUpper H := by
    refine sup_le (Lem22.le_oTwoUpper hp hp2 hPp hPH) ?_
    calc U = ⁅U, P⁆ := hUcomm
      _ ≤ oTwoUpper H := by
        rw [Subgroup.commutator_le]
        intro u hu x hx
        have hxo : Odd (orderOf x) := by
          rw [hPz] at hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          have hkp : (h ^ k) ^ p = 1 := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hhp, one_zpow]
          exact hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hkp)
        have hxH := hPH hx
        have hux : Odd (orderOf (u * x * u⁻¹)) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact hxo
        rw [commutatorElement_def]
        refine Subgroup.mul_mem _ (mem_oTwoUpper_of_odd ?_ hux)
          (mem_oTwoUpper_of_odd (H.inv_mem hxH) (by rw [orderOf_inv]; exact hxo))
        exact H.mul_mem (H.mul_mem (hUH hu) hxH) (H.inv_mem (hUH hu))

  have hPM : P ⊓ Subgroup.normalizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨hPx, -⟩ := Lem21.eq_zpowers_of_card_eq_prime hp hcard hx.1 hx1
    exact hhM ((Subgroup.zpowers_le.mpr hx.2) (hPx ▸ hhP))
  have hUNV : U ≤ Subgroup.normalizer (V : Set G) := (hUO.trans hQT).trans hTV
  refine ⟨hvV, hvU, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl hcard⟩
  · rw [hPz]
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hvh]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers h)) k
  · rw [hW]
    exact hUcomm
  · rw [hW]
    exact hUO
  · rw [hW]
    exact hUe
  · rw [hW]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro u hu x hx
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact V.mul_mem (hconj (hUNV hu) x hx) (V.inv_mem hx)
      · have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact U.mul_mem hu (hconj (hIU (hVI hx)) _ (U.inv_mem hu))
    · rw [inf_comm]
      exact inf_le_commutator hUNV hV2 htr hidx hvV hvU
  · rw [hW, inf_comm]
    exact hidx
  · rw [hW]
    exact le_antisymm hO2le hle2
  · rw [← hΦ, hPM]
    exact bot_le

end Lem22

end CFSG.Quasithin.H13
