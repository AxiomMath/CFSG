module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec3 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem le_zpowers_sup_of_odd
    (h17 : Step17G24Odd)
    {W : Subgroup G} (hWo : Odd (Nat.card W)) (hEW : E ≤ normalizer (W : Set G))
    (hxW : x ∈ normalizer (W : Set G)) :
    W ≤ zpowers x ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := H.q0.dData
  have hS := hD.suz.setting
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxZ.2 a ha)
  have hxA : x ∈ A := hS.le hxZ.1
  have hRx : R ≤ centralizer ({x} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hS.sylowR.le hr) x hxA).symm
  have hEx : E ≤ centralizer ({x} : Set G) := hS.frame.E_le.trans (sup_le hA₁x hRx)
  have hxN : zpowers x ≤ normalizer (W : Set G) := zpowers_le.mpr hxW
  set Y := W ⊔ zpowers x with hYdef
  have hYodd : Odd (Nat.card Y) := by
    have h := card_sup_mul_card_inf hxN
    have h1 : Nat.card Y ∣ Nat.card W * Nat.card (zpowers x) := ⟨_, h.symm⟩
    rw [Nat.card_zpowers, hS.order_x] at h1
    exact (hWo.mul (by decide : Odd 3)).of_dvd_nat h1
  have hEY : E ≤ normalizer (Y : Set G) := by
    intro e he
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rw [hYdef, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨o, ho, rfl⟩
      exact (mem_normalizer_iff.mp (hEW he) o).mp ho
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
  rw [hXeq] at hYX
  exact le_sup_left.trans (hYX.trans (sup_le_sup_right hXA _))

theorem oddCoreIn_centralizer_le_normalizer
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i) :
    AS76b.oddCoreIn (centralizer (Zs : Set G)) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
  have hQ := H.q0
  have hD := hQ.dData
  have hSz := hD.suz
  have hS := hSz.setting
  set C := centralizer (Zs : Set G) with hCdef
  set W := AS76b.oddCoreIn C with hWdef
  have hEC : E ≤ C := by
    intro e he
    refine mem_centralizer_iff.mpr fun s hs => ?_
    have hs' : s ∈ sec2Z A₁ E F := by rw [← hSz.Zs_eq]; exact hs
    exact (mem_centralizer_iff.mp (mem_inf.mp hs').2.2 e (mem_sup_left he)).symm
  have hxC : x ∈ C := mem_centralizer_iff.mpr fun s hs => (H.x_comm_Zs hs).symm
  have hCW : C ≤ normalizer (W : Set G) := AS76b.le_normalizer_oddCoreIn C
  have hWX := H.le_zpowers_sup_of_odd h17 (AS76b.odd_card_oddCoreIn C) (hEC.trans hCW)
    (hCW hxC)
  obtain ⟨Kf, _, _, _, -, f, -, l, -, hDf, hQ₀⟩ := exists_sec3Model_Q₀ hQ
  have hQ₀D : Q₀ ≤ D := by
    rw [hQ₀, hDf]
    exact tr_mono
      ((G2.g2Q0_le_g2V l).trans (G2.g2V_le_g2V0.trans G2.g2V0_le_g2ShortParabolicRadical))
  have hDA : D ≤ A := by
    rw [hD.D_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxZ.1
  have hOK : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    AS76b.oddCoreIn_le _
  have hWQ₀ : W ≤ normalizer (Q₀ : Set G) := hWX.trans (sup_le (zpowers_le.mpr hQ.x_Q₀)
    (hOK.trans ((centralizer_le (SetLike.coe_subset_coe.mpr (hQ₀D.trans hDA))).trans
      (centralizer_le_normalizer _))))
  have hWx : W ≤ centralizer ({x} : Set G) := hWX.trans (sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    (fun k hk => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hOK hk) x hxA).symm))
  have hzC : z ∈ Zs := hSz.z_mem
  have hWQ : W ≤ normalizer (Q : Set G) := by
    intro w hw
    obtain ⟨b, hbB, hbc⟩ := hinner w (mem_centralizer_singleton_iff.mp (hWx hw))
    have hwz : w * z = z * w := (mem_centralizer_iff.mp (AS76b.oddCoreIn_le C hw) z hzC).symm
    have hcz : (b⁻¹ * w) * z = z * (b⁻¹ * w) :=
      (mem_centralizer_iff.mp hbc z (hSz.T_le (hSz.Q_le H.z_mem_Q))).symm
    have hbz : b ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc b * z = w * (b⁻¹ * w)⁻¹ * z := by group
        _ = w * ((b⁻¹ * w)⁻¹ * z * (b⁻¹ * w)) * (b⁻¹ * w)⁻¹ := by group
        _ = w * z * (b⁻¹ * w)⁻¹ := by rw [show (b⁻¹ * w)⁻¹ * z * (b⁻¹ * w) = z by
              rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]]
        _ = z * w * (b⁻¹ * w)⁻¹ := by rw [hwz]
        _ = z * b := by group
    obtain ⟨b₀, hb₀, i, hbi⟩ := hCBz b (mem_inf.mpr ⟨hbB, hbz⟩)
    have hbQ : b ∈ normalizer (Q : Set G) := by
      rw [hbi]
      exact mul_mem (H.B₀_quot.2 hb₀)
        (centralizer_le_normalizer _ (zpow_mem H.x_mem_centralizer_Q i))
    have hcQ : b⁻¹ * w ∈ normalizer (Q : Set G) :=
      centralizer_le_normalizer _ (Subgroup.centralizer_le (hSz.Q_le.trans hSz.T_le) hbc)
    rw [show w = b * (b⁻¹ * w) by group]
    exact mul_mem hbQ hcQ
  intro w hw
  exact H.mem_normalizer_sup (hWQ₀ hw) (hWQ hw)

end Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem sec3_oddCoreIn_centralizer_le_normalizer
    (h17 : Step17G24Odd) (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    AS76b.oddCoreIn (centralizer (Zs : Set G)) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
  obtain ⟨H, ⟨τ, hτ⟩, -⟩ := exists_sec38Hyp_omega h17 hQ
  have hS := hQ.dData.suz
  exact H.oddCoreIn_centralizer_le_normalizer h17
    (fun w hw => exists_mem_sec3B_of_comm hS hτ.normB hτ.inv_x hw)
    (fun k hk => exists_mem_B₀_of_mem_centralizer hS hk)

end CFSG.ComponentClassification.AS81
