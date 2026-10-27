module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Img
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step17

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec3

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem oddCoreIn_le_centralizer_x
    (h17 : Step17G24Odd) :
    AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer ({x} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := H.q0
  have hD := hQ.dData
  have hSz := hD.suz
  have hS := hSz.setting
  set C := centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hCdef
  set R₃ := AS76b.oddCoreIn C with hR₃def
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxZ.1
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxZ.2 a ha)
  have hRx : R ≤ centralizer ({x} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hS.sylowR.le hr) x hxA).symm
  have hEx : E ≤ centralizer ({x} : Set G) := hS.frame.E_le.trans (sup_le hA₁x hRx)
  have hNR : ∀ n ∈ H.xsub.N, n ∈ normalizer (R₃ : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn C (mem_normalizer_centralizer hn)
  have hEN : E ≤ H.xsub.N := by
    intro e he
    have heT : e ∈ T := hSz.P_le ((hSz.P_cE.symm.le.trans inf_le_left) he)
    exact H.mem_normalizer_sup (centralizer_le_normalizer _ (H.T_le heT)) (hSz.T_Q heT)
  have hxN : zpowers x ≤ normalizer (R₃ : Set G) := zpowers_le.mpr (hNR x H.x_mem_N)
  set Y := R₃ ⊔ zpowers x with hYdef
  have hYodd : Odd (Nat.card Y) := by
    have h := card_sup_mul_card_inf hxN
    have h1 : Nat.card Y ∣ Nat.card R₃ * Nat.card (zpowers x) := ⟨_, h.symm⟩
    rw [Nat.card_zpowers, hS.order_x] at h1
    exact ((AS76b.odd_card_oddCoreIn C).mul (by decide : Odd 3)).of_dvd_nat h1
  have hEY : E ≤ normalizer (Y : Set G) := by
    intro e he
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rw [hYdef, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨o, ho, rfl⟩
      exact (mem_normalizer_iff.mp (hNR e (hEN he)) o).mp ho
    · rw [MonoidHom.map_zpowers, zpowers_le]
      have hex : e * x * e⁻¹ = x := by
        rw [mem_centralizer_singleton_iff.mp (hEx he), mul_inv_cancel_right]
      show e * x * e⁻¹ ∈ zpowers x
      rw [hex]
      exact mem_zpowers x
  obtain ⟨X, hYX, hX⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) ⟨hYodd, hEY⟩
  have hXo : Odd (Nat.card X) := hX.1.1
  obtain ⟨hXsyl, hXeq⟩ := h17 G A A₁ R g E F x hS X hX
  obtain ⟨hDx, hxD, hdec⟩ := sec3D_model hD
  have hD2 : IsPGroup 2 D := by
    rw [hD.D_eq]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hAK : ∀ w ∈ A, w ∈ centralizer (A : Set G) → w = 1 := by
    intro w hwA hwK
    have hw : (⟨w, hwA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
      Subtype.ext (mem_centralizer_iff.mp hwK a a.2)
    rw [hS.center_eq, mem_bot] at hw
    exact congrArg Subtype.val hw
  have hXA : X ⊓ A ≤ zpowers x := by
    intro w hw
    have hwC := hXsyl.le hw
    obtain ⟨k, hk, c, hc, hkc⟩ := hdec w (le_normalizer hwC.1) hwC.2
    have hcA : c ∈ A := (hDx hc).1
    have hkA : k ∈ A := by
      have h1 := A.mul_mem hwC.1 (A.inv_mem hcA)
      rwa [hkc, mul_inv_cancel_right] at h1
    rw [hAK k hkA hk, one_mul] at hkc
    have hc' : c ∈ ((D ⊔ zpowers x : Subgroup G) : Set G) := hc
    rw [coe_mul_of_right_le_normalizer_left D (zpowers x) (zpowers_le.mpr hxD),
      Set.mem_mul] at hc'
    obtain ⟨d, hd, xi, hxi, hdxi⟩ := hc'
    have hdX : d ∈ X := by
      have h1 : w ∈ X := (mem_inf.mp hw).1
      have h2 : xi ∈ X := hYX (mem_sup_right hxi)
      have h3 := X.mul_mem h1 (X.inv_mem h2)
      rwa [hkc, ← hdxi, mul_inv_cancel_right] at h3
    have hd1 : d = 1 := by
      obtain ⟨n, hn⟩ := hD2 ⟨d, hd⟩
      have hdn : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h1 : orderOf d ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hdn
      have h2 : orderOf d ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hdX
      have hcop : Nat.Coprime (Nat.card X) (2 ^ n) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hXo)
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
    rw [hkc, ← hdxi, hd1, one_mul]
    exact hxi
  have hXx : X ≤ centralizer ({x} : Set G) := by
    rw [hXeq]
    refine sup_le (hXA.trans (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))) ?_
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (AS76b.oddCoreIn_le _ hk) x hxA).symm
  exact (le_sup_left.trans hYX).trans hXx

end Sec38Hyp

end CFSG.ComponentClassification.AS81
