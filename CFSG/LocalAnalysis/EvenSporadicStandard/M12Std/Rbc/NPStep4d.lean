module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPStep4

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

namespace NPSetting

section Normalized

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {h s : G}

theorem centralizer_zpowers_eq (g : G) :
    centralizer ((zpowers g : Subgroup G) : Set G) = centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem s_mul_h (hS : NPSetting G X u x (zpowers h) s) (hh2 : h * h = 1) (hh1 : h ≠ 1) :
    s * h * s⁻¹ = h := by
  have hk : s * h * s⁻¹ ∈ zpowers h :=
    (Subgroup.mem_set_normalizer_iff.mp hS.s_norm h).mp (Subgroup.mem_zpowers h)
  have hk1 : s * h * s⁻¹ ≠ 1 := by
    intro hh
    have h2 : s * h = s := mul_inv_eq_one.mp hh
    exact hh1 (mul_left_cancel (show s * h = s * 1 by simpa using h2))
  have hord : orderOf h = 2 := orderOf_eq_prime (by simpa [pow_two] using hh2) hh1
  exact eq_of_mem_zpowers_of_orderOf_eq_two hord hk hk1

theorem isCompIn_A_centralizer (hS : NPSetting G X u x (zpowers h) s) :
    IsCompIn (npA X x s) (centralizer ({h} : Set G)) := by
  rw [← centralizer_zpowers_eq]
  exact hS.isCompIn_A

theorem map_conj_u_A (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x (zpowers h) s) :
    (npA X x s).map (MulAut.conj u).toMonoidHom = npA X x s := by
  let B : Subgroup G := (npA X x s).map (MulAut.conj u).toMonoidHom
  change B = npA X x s
  by_contra hne
  have hAcomp : IsCompIn (npA X x s) (centralizer ({h} : Set G)) :=
    hS.isCompIn_A_centralizer
  have hu : u ∈ centralizer ({h} : Set G) := mem_centralizer_singleton_iff.2 hh.comm_u
  have hBcomp : IsCompIn B (centralizer ({h} : Set G)) := hAcomp.map_conj hu
  have hcomm : ∀ b ∈ B, ∀ a ∈ npA X x s, b * a = a * b :=
    hBcomp.commute_of_ne hAcomp hne
  have hBleD : B ≤ npD X x := by
    intro b hb
    have hb' : b ∈ (npA X x s).map (MulAut.conj u).toMonoidHom := hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 hb'
    change u * a₀ * u⁻¹ ∈ npD X x
    exact (npD X x).mul_mem ((npD X x).mul_mem hS.u_mem_D (hS.A_le_D ha₀))
      ((npD X x).inv_mem hS.u_mem_D)
  have hnormal : (oddBar (npD X x) (npA X x s)).Normal := hS.normal_Abar hNP h15
  have hcent_bar : center ↥(oddBar (npD X x) (npA X x s)) = ⊥ := by
    have h := Subgroup.map_center_eq hS.oddBarEquivA
    rw [hS.center_A_eq_bot, Subgroup.map_bot] at h
    exact h.symm
  have hkey : ∀ z : ↥(npD X x), z.1 ∈ B → oddProj (npD X x) z = 1 := by
    intro z hz'
    have hz'' : z.1 ∈ (npA X x s).map (MulAut.conj u).toMonoidHom := hz'
    obtain ⟨a₀, ha₀, ha₀eq⟩ := Subgroup.mem_map.1 hz''
    have hz1 : z.1 = u * a₀ * u⁻¹ := by rw [← ha₀eq]; rfl
    have hzeq : z = (⟨u, hS.u_mem_D⟩ : ↥(npD X x)) * ⟨a₀, hS.A_le_D ha₀⟩ *
        (⟨u, hS.u_mem_D⟩ : ↥(npD X x))⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hz1
    have hφ_eq : oddProj (npD X x) z =
        hS.ubar * oddProj (npD X x) ⟨a₀, hS.A_le_D ha₀⟩ * hS.ubar⁻¹ := by
      rw [hzeq, map_mul, map_mul, map_inv]
      rfl
    have hπa₀ : oddProj (npD X x) ⟨a₀, hS.A_le_D ha₀⟩ ∈
        oddBar (npD X x) (npA X x s) :=
      Subgroup.mem_map.2
        ⟨⟨a₀, hS.A_le_D ha₀⟩, (Subgroup.mem_subgroupOf).2 ha₀, rfl⟩
    have hφA : oddProj (npD X x) z ∈ oddBar (npD X x) (npA X x s) := by
      rw [hφ_eq]
      exact hnormal.conj_mem _ hπa₀ hS.ubar
    have hφcomm : ∀ g ∈ oddBar (npD X x) (npA X x s),
        g * oddProj (npD X x) z = oddProj (npD X x) z * g := by
      intro g hg
      obtain ⟨aD, haD, hae⟩ := Subgroup.mem_map.1 hg
      have haA : aD.1 ∈ npA X x s := (Subgroup.mem_subgroupOf).1 haD
      have hc := hcomm z.1 hz' aD.1 haA
      have hcD : z * aD = aD * z := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hc
      have hcong := congrArg (oddProj (npD X x)) hcD
      rw [map_mul, map_mul, hae] at hcong
      exact hcong.symm
    have hφcenter : (⟨oddProj (npD X x) z, hφA⟩ :
        ↥(oddBar (npD X x) (npA X x s))) ∈
        center ↥(oddBar (npD X x) (npA X x s)) :=
      Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hφcomm g.1 g.2))
    have hmem : (⟨oddProj (npD X x) z, hφA⟩ :
        ↥(oddBar (npD X x) (npA X x s))) ∈
        (⊥ : Subgroup ↥(oddBar (npD X x) (npA X x s))) := by
      rw [← hcent_bar]
      exact hφcenter
    simpa using congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hker : B.subgroupOf (npD X x) ≤ (oddProj (npD X x)).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    exact hkey z (Subgroup.mem_subgroupOf.1 hz)
  have hcardB : Nat.card ↥B = 60 := by
    change Nat.card ↥((npA X x s).map (MulAut.conj u).toMonoidHom) = 60
    rw [Subgroup.card_map_of_injective (fun a b hab => (MulAut.conj u).injective hab)]
    exact hS.card_A
  have h1 := Subgroup.card_dvd_of_le hker
  rw [ker_oddProj] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleD).toEquiv] at h1
  rw [hcardB] at h1
  exact not_two_dvd_natCard_oddCore (npD X x) (dvd_trans (by norm_num) h1)

end Normalized

end NPSetting

end CFSG.EvenSporadicStandard.M12Std.Rbc
