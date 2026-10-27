module

public import CFSG.ClassicalInvolution.Sp62Rec.PkgNoHat
import CFSG.ClassicalInvolution.Sp62Rec.OddClass
import CFSG.ClassicalInvolution.Sp62Rec.Balance
import CFSG.ClassicalInvolution.Sp62Rec.OddConj
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open
open scoped Pointwise


private theorem eq_one_of_mem_odd_of_mul_self_eq_one {H : Type*} [Group H] (K : Subgroup H)
    (hK : Odd (Nat.card K)) {x : H} (hx : x ∈ K) (hx2 : x * x = 1) : x = 1 := by
  by_contra hx1
  have hp : (⟨x, hx⟩ : K) ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hx2
  have hne : (⟨x, hx⟩ : K) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord : orderOf (⟨x, hx⟩ : K) = 2 := orderOf_eq_prime hp hne
  have hdvd : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [hord] at hdvd
  exact hK.not_two_dvd_nat hdvd

theorem exists_conj_eq_pi12_or_pi3_B {G : Type} [Group G] [Finite G] {z e : G} {B : Subgroup G}
    (TB : Sylow 2 ↥B) (φ : ↥B →* ↥Hhat) (hφ : Function.Surjective φ) (hK : Odd (Nat.card φ.ker))
    (hzB : z ∈ B) (hzT : (⟨z, hzB⟩ : ↥B) ∈ (TB : Subgroup ↥B))
    (hzc : ∀ x ∈ (TB : Subgroup ↥B), (⟨z, hzB⟩ : ↥B) * x = x * ⟨z, hzB⟩) (heB : e ∈ B)
    (he : φ ⟨e, heB⟩ = ⟨alpha, alpha_mem_Hhat⟩) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hze : z ≠ e)
    (he2 : e * e = 1) (hcomm : z * e = e * z)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hZ : ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2)))) :
    ∃ c ∈ Hhat, c * ((φ ⟨z, hzB⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) * c⁻¹ = pi12 ∨
      c * ((φ ⟨z, hzB⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) * c⁻¹ = pi3 := by
  haveI : Finite ↥Hhat := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  let P : Sylow 2 ↥Hhat := TB.mapSurjective hφ
  have hzTB : (⟨z, hzB⟩ : ↥B) ∈ (TB : Subgroup ↥B) := hzT
  have hwP : φ ⟨z, hzB⟩ ∈ (P : Subgroup ↥Hhat) := by
    show φ ⟨z, hzB⟩ ∈ (TB : Subgroup ↥B).map φ
    exact Subgroup.mem_map.2 ⟨⟨z, hzB⟩, hzTB, rfl⟩
  have hPcomm : ∀ p ∈ (P : Subgroup ↥Hhat), φ ⟨z, hzB⟩ * p = p * φ ⟨z, hzB⟩ := by
    intro p hp
    have hp' : p ∈ (TB : Subgroup ↥B).map φ := hp
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hp'
    have hbz : (⟨z, hzB⟩ : ↥B) * b = b * ⟨z, hzB⟩ := hzc b hb
    rw [← map_mul, ← map_mul, hbz]
  have hS0card : Nat.card (S0.subgroupOf Hhat) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, hS0]
  have hS0p : IsPGroup 2 (S0.subgroupOf Hhat) :=
    IsPGroup.of_card (n := 9) (by rw [hS0card]; norm_num)
  have hS0idx : ¬ 2 ∣ (S0.subgroupOf Hhat).index := by
    have h := Subgroup.card_mul_index (S0.subgroupOf Hhat)
    rw [hS0card, hH] at h
    have h45 : (S0.subgroupOf Hhat).index = 45 := by omega
    rw [h45]
    norm_num
  let S1 : Sylow 2 ↥Hhat := IsPGroup.toSylow hS0p hS0idx
  have hS1coe : (S1 : Subgroup ↥Hhat) = S0.subgroupOf Hhat := rfl
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Hhat) P S1
  have hS1 : (S1 : Subgroup ↥Hhat) = MulAut.conj c • (P : Subgroup ↥Hhat) :=
    (congrArg (fun X : Sylow 2 ↥Hhat => (X : Subgroup ↥Hhat)) hc).symm.trans
      Sylow.coe_subgroup_smul
  have hconjP : ∀ y ∈ (S1 : Subgroup ↥Hhat), c⁻¹ * y * c ∈ (P : Subgroup ↥Hhat) := by
    intro y hy
    rw [hS1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact hy
  have hconjS : ∀ p ∈ (P : Subgroup ↥Hhat), c * p * c⁻¹ ∈ (S1 : Subgroup ↥Hhat) := by
    intro p hp
    rw [hS1]
    exact Subgroup.smul_mem_pointwise_smul p (MulAut.conj c) _ hp
  have hyS : c * φ ⟨z, hzB⟩ * c⁻¹ ∈ (S1 : Subgroup ↥Hhat) := hconjS _ hwP
  have hycomm : ∀ s ∈ (S1 : Subgroup ↥Hhat),
      (c * φ ⟨z, hzB⟩ * c⁻¹) * s = s * (c * φ ⟨z, hzB⟩ * c⁻¹) := by
    intro s hs
    have hp := hPcomm _ (hconjP s hs)
    calc (c * φ ⟨z, hzB⟩ * c⁻¹) * s = c * (φ ⟨z, hzB⟩ * (c⁻¹ * s * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * s * c) * φ ⟨z, hzB⟩) * c⁻¹ := by rw [hp]
      _ = s * (c * φ ⟨z, hzB⟩ * c⁻¹) := by group
  have hYS0 : ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0 := by
    have h := hyS
    rw [hS1coe] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hYcomm : ∀ s ∈ S0, ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) * s =
      s * ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) := by
    intro s hs
    have hsH : s ∈ Hhat := S0_le_Hhat hs
    have hs1 : (⟨s, hsH⟩ : ↥Hhat) ∈ (S1 : Subgroup ↥Hhat) := by
      rw [hS1coe]
      exact Subgroup.mem_subgroupOf.2 hs
    exact congrArg Subtype.val (hycomm _ hs1)
  rcases hZ _ hYS0 hYcomm with hY | hY | hY | hY
  ·
    exfalso
    have h : c * φ ⟨z, hzB⟩ * c⁻¹ = 1 := Subtype.ext hY
    have hw1 : φ ⟨z, hzB⟩ = 1 := by
      calc φ ⟨z, hzB⟩ = c⁻¹ * (c * φ ⟨z, hzB⟩ * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    have hker : (⟨z, hzB⟩ : ↥B) ∈ φ.ker := MonoidHom.mem_ker.2 hw1
    have hsq : (⟨z, hzB⟩ : ↥B) * ⟨z, hzB⟩ = 1 := Subtype.ext hz2
    exact hz1 (congrArg Subtype.val (eq_one_of_mem_odd_of_mul_self_eq_one φ.ker hK hker hsq))
  ·
    exfalso
    have hcent : ∀ g : ↥Hhat,
        (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) * g = g * ⟨alpha, alpha_mem_Hhat⟩ := by
      intro g
      apply Subtype.ext
      have hg := hα g.2
      rw [Subgroup.mem_centralizer_iff] at hg
      exact hg alpha (Set.mem_singleton alpha)
    have h : c * φ ⟨z, hzB⟩ * c⁻¹ = ⟨alpha, alpha_mem_Hhat⟩ := Subtype.ext hY
    have hwa : φ ⟨z, hzB⟩ = ⟨alpha, alpha_mem_Hhat⟩ := by
      calc φ ⟨z, hzB⟩ = c⁻¹ * (c * φ ⟨z, hzB⟩ * c⁻¹) * c := by group
        _ = c⁻¹ * (⟨alpha, alpha_mem_Hhat⟩ * c) := by rw [h]; group
        _ = c⁻¹ * (c * ⟨alpha, alpha_mem_Hhat⟩) := by rw [hcent c]
        _ = ⟨alpha, alpha_mem_Hhat⟩ := by group
    have he2' : (⟨e, heB⟩ : ↥B) * ⟨e, heB⟩ = 1 := Subtype.ext he2
    have haa : (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) * ⟨alpha, alpha_mem_Hhat⟩ = 1 := by
      rw [← he, ← map_mul, he2', map_one]
    have hzeK : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hwa, he, haa]
    have hsq : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ * ((⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩) = 1 := by
      apply Subtype.ext
      show z * e * (z * e) = 1
      calc z * e * (z * e) = z * (e * z) * e := by group
        _ = z * (z * e) * e := by rw [← hcomm]
        _ = (z * z) * (e * e) := by group
        _ = 1 := by rw [hz2, he2, one_mul]
    have hze1 : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ = 1 :=
      eq_one_of_mem_odd_of_mul_self_eq_one φ.ker hK hzeK hsq
    have hze1' : z * e = 1 := congrArg Subtype.val hze1
    apply hze
    calc z = z * (e * e) := by rw [he2, mul_one]
      _ = z * e * e := by group
      _ = e := by rw [hze1', one_mul]
  · exact ⟨(c : StatedSp 3 (ZMod 2)), c.2, Or.inl hY⟩
  · exact ⟨(c : StatedSp 3 (ZMod 2)), c.2, Or.inr hY⟩


variable {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}

theorem I1Six.oddCoreIn_centralizer_eq_bot (P : I1Six z e E B)
    (TB : Sylow 2 ↥B) (hzT : (⟨z, P.z_mem⟩ : ↥B) ∈ (TB : Subgroup ↥B))
    (hzc : ∀ x ∈ (TB : Subgroup ↥B), (⟨z, P.z_mem⟩ : ↥B) * x = x * ⟨z, P.z_mem⟩)
    (hz_sq : z * z = 1) (hz_ne_one : z ≠ 1) (hz_ne_e : z ≠ e) (he_sq : e * e = 1)
    (hoddC : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (heO2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hZ : ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))))
    (hfour : ∀ x : StatedSp 3 (ZMod 2), x = pi12 ∨ x = pi3 →
      ∃ D : Subgroup (StatedSp 3 (ZMod 2)), D ≤ Hhat ∧ Nat.card D = 4 ∧ (∀ d ∈ D, d * d = 1) ∧
        ∀ d ∈ D, d ≠ 1 → ∃ c ∈ Hhat, c * x * c⁻¹ = d) :
    oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ := by
  obtain ⟨φ, hsurj, hker, -, hφe, -⟩ := P.hat
  have hEB : oddCoreIn E ≤ B := (oddCoreIn_le E).trans P.E_le_B
  have hK : Odd (Nat.card φ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv]
    exact odd_card_oddCoreIn E
  have hcomm : z * e = e * z :=
    (Subgroup.mem_centralizer_iff.mp (P.B_le P.z_mem) e (Set.mem_singleton e)).symm
  obtain ⟨c, hc, hcx⟩ := exists_conj_eq_pi12_or_pi3_B TB φ hsurj hK P.z_mem hzT hzc
    (P.E_le_B P.e_mem) hφe hz_sq hz_ne_one hz_ne_e he_sq hcomm hS0 hH hZ hα
  obtain ⟨D, hDH, hD4, hD2, hDx⟩ := hfour _ hcx
  have hzz : (⟨z, P.z_mem⟩ : ↥B) * ⟨z, P.z_mem⟩ = 1 := Subtype.ext hz_sq
  have hD'4 : Nat.card (D.subgroupOf Hhat) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, hD4]
  have hD'2 : ∀ d ∈ D.subgroupOf Hhat, d * d = 1 := fun d hd =>
    Subtype.ext (hD2 _ (Subgroup.mem_subgroupOf.mp hd))
  have hD'z : ∀ d ∈ D.subgroupOf Hhat, d ≠ 1 → IsConj d (φ ⟨z, P.z_mem⟩) := by
    intro d hd hd1
    obtain ⟨c', hc', hcc⟩ := hDx _ (Subgroup.mem_subgroupOf.mp hd)
      (fun h => hd1 (Subtype.ext h))
    refine IsConj.symm (isConj_iff.mpr ⟨⟨c', hc'⟩ * ⟨c, hc⟩, Subtype.ext ?_⟩)
    show c' * c * (φ ⟨z, P.z_mem⟩ : StatedSp 3 (ZMod 2)) * (c' * c)⁻¹ =
      (d : StatedSp 3 (ZMod 2))
    rw [← hcc]
    group
  obtain ⟨D₀, hD₀4, hD₀2, hD₀z⟩ :=
    exists_four_isConj_of_surjective φ hsurj hK hzz (D.subgroupOf Hhat) hD'4 hD'2 hD'z
  have hsub1 : ∀ d ∈ D₀, d ≠ 1 →
      oddCoreIn (Subgroup.centralizer ({e} : Set G)) ⊓
        Subgroup.centralizer ({(d : G)} : Set G) = ⊥ := by
    intro d hd hd1
    obtain ⟨b, hb⟩ := isConj_iff.mp (hD₀z d hd hd1).symm
    have hdz : (d : G) = (b : G) * z * (b : G)⁻¹ := by
      subst hb
      rfl
    have hO : oddCoreIn (Subgroup.centralizer ({(d : G)} : Set G)) = ⊥ := by
      rw [hdz]
      exact oddCoreIn_centralizer_conj_eq_bot hoddC
    have hbe : (b : G) * e * (b : G)⁻¹ = e := by
      have h := Subgroup.mem_centralizer_iff.mp (P.B_le b.2) e (Set.mem_singleton e)
      rw [← h, mul_inv_cancel_right]
    have hmem : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({(d : G)} : Set G))).map
        (Subgroup.centralizer ({(d : G)} : Set G)).subtype := by
      have h := conj_mem_pCore_centralizer_conj (b := (b : G)) heO2
      rw [hbe] at h
      rw [hdz]
      exact h
    exact oddCoreIn_centralizer_inf_eq_bot hO hmem
  have hcardA : Nat.card (D₀.map B.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hD₀4]
  have hsqA : ∀ x ∈ D₀.map B.subtype, x * x = 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    exact congrArg Subtype.val (hD₀2 d hd)
  have hcommA : ∀ x ∈ D₀.map B.subtype, ∀ y ∈ D₀.map B.subtype, x * y = y * x := by
    intro x hx y hy
    have hxy : x * y ∈ D₀.map B.subtype := (D₀.map B.subtype).mul_mem hx hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsqA _ hxy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right (hsqA x hx), inv_eq_of_mul_eq_one_right (hsqA y hy)]
  have hAab : IsMulCommutative ↥(D₀.map B.subtype) :=
    ⟨⟨fun x y => Subtype.ext (hcommA x x.2 y y.2)⟩⟩
  have hA2 : CFSG.Open.IsElemAbelian 2 (D₀.map B.subtype) :=
    ⟨hAab, fun x hx => by rw [pow_two]; exact hsqA x hx⟩
  have hrank : 2 ^ 2 ≤ Nat.card (D₀.map B.subtype) := by
    rw [hcardA] <;> norm_num
  have hABe : D₀.map B.subtype ≤ Subgroup.centralizer ({e} : Set G) := by
    intro a ha
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.1 ha
    exact P.B_le d.2
  have hAX : D₀.map B.subtype ≤
      Subgroup.normalizer (oddCoreIn (Subgroup.centralizer ({e} : Set G)) : Set G) :=
    hABe.trans (normalizer_oddCoreIn _)
  have hX : Nat.Coprime 2 (Nat.card (oddCoreIn (Subgroup.centralizer ({e} : Set G)))) :=
    Nat.coprime_two_left.mpr (odd_card_oddCoreIn _)
  have hX1 := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hA2 hrank hAX hX
  have hsup : (⨆ (a : G) (_ : a ∈ D₀.map B.subtype) (_ : a ≠ 1),
      oddCoreIn (Subgroup.centralizer ({e} : Set G)) ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    refine iSup_eq_bot.2 fun a => iSup_eq_bot.2 fun ha => iSup_eq_bot.2 fun ha1 => ?_
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 ha
    have hd1 : d ≠ 1 := fun h => ha1 (by rw [h, map_one])
    exact hsub1 d hd hd1
  rw [hsup] at hX1
  exact hX1.symm

end CFSG.ClassicalInvolution.Sp62Rec
