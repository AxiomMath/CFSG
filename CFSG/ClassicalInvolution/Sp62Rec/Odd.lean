module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg
import CFSG.ClassicalInvolution.Sp62Rec.Balance
import CFSG.ClassicalInvolution.Sp62Rec.OddConj
import CFSG.ClassicalInvolution.Sp62Rec.OddClass
import CFSG.ClassicalInvolution.Sp62Rec.CEBasic
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}

theorem E8ZPkg.oddCoreIn_centralizer_eq_bot (P : E8ZPkg z e E B T A X)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hZ : ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))))
    (hfour : ∀ x : StatedSp 3 (ZMod 2), x = pi12 ∨ x = pi3 →
      ∃ D : Subgroup (StatedSp 3 (ZMod 2)), D ≤ Hhat ∧ Nat.card D = 4 ∧ (∀ d ∈ D, d * d = 1) ∧
        ∀ d ∈ D, d ≠ 1 → ∃ c ∈ Hhat, c * x * c⁻¹ = d) :
    oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ := by
  obtain ⟨φ, hsurj, hker, -, hφe⟩ := P.hat
  have hEB : oddCoreIn E ≤ B := (oddCoreIn_le E).trans P.E_le_B
  have hK : Odd (Nat.card φ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv]
    exact odd_card_oddCoreIn E
  have hcomm : z * e = e * z :=
    (Subgroup.mem_centralizer_iff.mp (P.B_le P.z_mem) e (Set.mem_singleton e)).symm
  obtain ⟨c, hc, hcx⟩ := exists_conj_eq_pi12_or_pi3 φ hsurj hK P.T_le P.z_center.1
    P.z_center.2 P.z_mem (P.E_le_B P.e_mem) hφe P.z_sq P.z_ne_one P.z_ne_e P.e_mul_self hcomm
    hS0 hH hZ hα
  obtain ⟨D, hDH, hD4, hD2, hDx⟩ := hfour _ hcx
  have hzz : (⟨z, P.z_mem⟩ : ↥B) * ⟨z, P.z_mem⟩ = 1 := Subtype.ext P.z_sq
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
      exact oddCoreIn_centralizer_conj_eq_bot P.oddC_z
    have hbe : (b : G) * e * (b : G)⁻¹ = e := by
      have h := Subgroup.mem_centralizer_iff.mp (P.B_le b.2) e (Set.mem_singleton e)
      rw [← h, mul_inv_cancel_right]
    have hmem : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({(d : G)} : Set G))).map
        (Subgroup.centralizer ({(d : G)} : Set G)).subtype := by
      have h := conj_mem_pCore_centralizer_conj (b := (b : G)) P.e_mem_O2
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
