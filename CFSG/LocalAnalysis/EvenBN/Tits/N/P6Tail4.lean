module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Tail3
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Cmt
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Cop
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Tail2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {G : Type} [Group G] [Finite G]
variable (d : Data G)

theorem tail_core (z₀ : G) (hx5H : d.x₅ ∈ Hg d) (hx5 : orderOf d.x₅ = 5)
    (hV : IsElemAbelian 2 d.s56V) (hV10 : Nat.card d.s56V = 2 ^ 10)
    (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hXO : img d (Xg d) ≤ centralizer ((oddCoreSub (Hs d) : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)))
    (hZeq : Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G))
    (hN : ((H0 d z₀).subgroupOf (Hg d)).Normal)
    (hidx : (H0 d z₀).relIndex (Hg d) = 2 ∨ (H0 d z₀).relIndex (Hg d) = 6)
    (h19 : img d (Wg d z₀) = Ws d) (hWab : IsElemAbelian 2 (Ws d))
    (hWsyl : fusionIsSylowIn 2 (Ws d) (centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) ⊓ Hs d))
    (hdich : Nonempty (↥(Ja d) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(Ja d) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (hE1 : Nat.card (Ialpha d) ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2)
    (hVW : ⁅d.s56V, Wg d z₀⁆ = Zz d z₀)
    (hC1 : (∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
        Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) →
      ∀ o ∈ Hg d, (∀ j ∈ Jp d, o * j * o⁻¹ * j⁻¹ ∈ Kz d z₀) → o ∈ Kz d z₀)
    (hC2 : ∀ s ∈ Hg d, s * s = 1 →
      (Zz d z₀).relIndex (⁅d.s56V, zpowers s⁆ ⊔ Zz d z₀) = 8 →
      ∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
        Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6)))
    {s y : G} (hsH : s ∈ Hg d) (hs2 : s * s = 1) (hZs : ∀ z ∈ Zz d z₀, s * z = z * s)
    (hyH : y ∈ Hg d) (hy3 : IsPGroup 3 (zpowers y)) (hyz : ∃ z ∈ Zz d z₀, y * z ≠ z * y)
    (hZ4 : Nat.card (Zz d z₀) = 4)
    (hcard : Nat.card ↥(d.s56V ⊓ centralizer ({s} : Set G)) = 2 ^ 5) : False := by
  have hX : Xg d ≤ Hg d := fun x hx => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
    exact zpow_mem hx5H n
  have hZV : Zz d z₀ ≤ d.s56V := hZeq ▸ inf_le_left
  have hZC : Zz d z₀ ≤ d.s56V ⊓ centralizer ({s} : Set G) := fun z hz =>
    Subgroup.mem_inf.2 ⟨hZV hz, mem_centralizer_singleton_iff.2 (hZs z hz).symm⟩
  have hrel := relIndex_commutator_eq hV hsH hs2 hV10 hcard hZ4 hZC
  have hA6 := hC2 s hsH hs2 hrel
  obtain ⟨hNW, ⟨e⟩⟩ := hA6
  have h360 : (Wg d z₀).relIndex (Jp d) = 360 := by
    have h1 : (Wg d z₀).relIndex (Jp d) =
        Nat.card (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d)) := Subgroup.index_eq_card _
    rw [h1, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hx5' : d.x₅ ∈ H0 d z₀ := x5_mem_H0 d z₀ hx5H hx5 hN hidx
  have hJ : Jg d ≤ H0 d z₀ := Jg_le_H0 d z₀ (zpowers_le.2 hx5') hN
  have hyH0 : y ∉ H0 d z₀ := by
    intro hy0
    obtain ⟨z, hz, hne⟩ := hyz
    exact hne (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy0).2 z hz).symm
  obtain ⟨o, hoH, ho3, hoH0, hoC⟩ :=
    exists_three_element_C d z₀ hW hN hZV hJ h19 hWab hX h360 hdich hE1 hyH hy3 hyH0
  have hcent : ∀ c ∈ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ⊓ Hs d,
      ∀ w ∈ Ws d, c * w = w * c := fun c hc w hw =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 w hw).symm
  obtain ⟨N, hNC, hNodd, hNn, hNodd_mem⟩ := exists_normal_odd_subgroup (Hh := Hs d) inf_le_right
    (fun h hh c hc => centralizer_inf_Hs_conj_mem d hW hh hc) hWsyl hcent
  have hoStar : star d o ∈ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) ⊓ Hs d := Subgroup.mem_inf.2 ⟨hoC, actFun_mem_imgIn hoH hoH⟩
  have hoodd : Odd (orderOf (star d o)) := by
    obtain ⟨b, hb⟩ := ho3 ⟨o, mem_zpowers o⟩
    have hob : o ^ 3 ^ b = 1 := congrArg Subtype.val hb
    have h1 : star d o ^ 3 ^ b = 1 := by
      show actFun d.s56V o ^ 3 ^ b = 1
      rw [← actFun_pow d.s56V hoH, hob, actFun_one]
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)
  have hoN : star d o ∈ N := hNodd_mem _ hoStar hoodd
  have hNH : N ≤ Hs d := hNC.trans inf_le_right
  have hNO : N ≤ oddCoreSub (Hs d) := le_oddCoreSub_of_normal_odd d hNH hNn hNodd
  have hXN : ∀ x ∈ Xg d, ∀ n ∈ N, n * star d x = star d x * n := by
    intro x hx n hn
    have hxH := hX hx
    have h1 : star d x ∈ centralizer ((oddCoreSub (Hs d) : Subgroup (MulAut ↥d.s56V)) :
        Set (MulAut ↥d.s56V)) := hXO (actFun_mem_imgIn hx hxH)
    exact Subgroup.mem_centralizer_iff.1 h1 n (hNO hn)
  have hOtriv : ∀ a ∈ N, ∀ v : ↥d.s56V, ((a v : ↥d.s56V) : G) * (v : G)⁻¹ ∈ Zz d z₀ := by
    intro a ha v
    obtain ⟨o', ho'H, ho'N, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 (hNH ha)
    have hcomm : ∀ j ∈ Jp d, o' * j * o'⁻¹ * j⁻¹ ∈ Kz d z₀ := by
      intro j hj
      have hjH := Jp_le_Hg d hj
      have hc : star d o' * star d j = star d j * star d o' :=
        commute_star_of_mem_Jp d hNn hXN hX hj ha
      refine centralizer_le_Kz d z₀ hZV ?_
      have hcH : o' * j * o'⁻¹ * j⁻¹ ∈ Hg d :=
        mul_mem (mul_mem (mul_mem ho'H hjH) (inv_mem ho'H)) (inv_mem hjH)
      refine (actFun_eq_one_iff d.s56V hcH).1 ?_
      rw [actFun_mul d.s56V (mul_mem (mul_mem ho'H hjH) (inv_mem ho'H)) (inv_mem hjH),
        actFun_conj d.s56V ho'H hjH, actFun_inv d.s56V hjH]
      change star d o' * star d j * (star d o')⁻¹ * (star d j)⁻¹ = 1
      calc star d o' * star d j * (star d o')⁻¹ * (star d j)⁻¹
          = star d j * star d o' * (star d o')⁻¹ * (star d j)⁻¹ := by rw [hc]
        _ = 1 := by group
    have hKz : o' ∈ Kz d z₀ := hC1 ⟨hNW, ⟨e⟩⟩ o' ho'H hcomm
    have h1 := hKz.2.2 (v : G) v.2
    rw [actFun_apply_coe d.s56V ho'N v]
    exact h1
  have hWH : Wg d z₀ ≤ normalizer (d.s56V : Set G) := fun w hw =>
    preIn_le_normalizer d.s56V _ (Subgroup.mem_inf.1 hw).1
  have hNnorm : ∀ h ∈ normalizer (d.s56V : Set G), ∀ a ∈ N,
      actFun d.s56V h * a * (actFun d.s56V h)⁻¹ ∈ N :=
    fun h hh a ha => hNn _ (actFun_mem_imgIn hh hh) a ha
  have hWZ : ∀ w ∈ Wg d z₀, ∀ z ∈ Zz d z₀, w * z = z * w := by
    intro w hw z hz
    have h1 : z ∈ d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G) := hZeq ▸ hz
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h1).2 w hw
  have hnt : ∃ a ∈ N, ∃ v : ↥d.s56V, (v : G) ∈ Zz d z₀ ∧ a v ≠ v := by
    have h1 : ∃ z ∈ Zz d z₀, ¬ (z * o = o * z) := by
      by_contra h
      push Not at h
      exact hoH0 (Subgroup.mem_inf.2 ⟨hoH, Subgroup.mem_centralizer_iff.2 h⟩)
    obtain ⟨z, hz, hne⟩ := h1
    refine ⟨star d o, hoN, ⟨z, hZV hz⟩, hz, fun heq => hne ?_⟩
    have h2 := congrArg Subtype.val heq
    have e : ((star d o ⟨z, hZV hz⟩ : ↥d.s56V) : G) = o * z * o⁻¹ :=
      actFun_apply_coe d.s56V hoH ⟨z, hZV hz⟩
    rw [e] at h2
    have h3 : o * z * o⁻¹ = z := h2
    calc z * o = (o * z * o⁻¹) * o := by rw [h3]
      _ = o * z := by group
  exact false_of_odd_action hV hZV hWH hNodd hNnorm hOtriv hWZ hVW hnt

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
