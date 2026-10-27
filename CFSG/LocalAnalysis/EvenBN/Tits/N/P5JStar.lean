module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S20Set
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S22Abs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5VMod
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Quot

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem Jg_le_Hg : Jg d ≤ Hg d := Subgroup.map_subtype_le _

theorem Jg_conj {h j : G} (hh : h ∈ Hg d) (hj : j ∈ Jg d) : h * j * h⁻¹ ∈ Jg d := by
  obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.1 hj
  exact Subgroup.mem_map.2 ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹,
    (Subgroup.normalClosure_normal).conj_mem j' hj' ⟨h, hh⟩, rfl⟩

theorem Xg_le_Jg (hx : d.x₅ ∈ Hg d) : Xg d ≤ Jg d := by
  intro a ha
  have haH : a ∈ Hg d := zpowers_le.2 hx ha
  exact Subgroup.mem_map.2 ⟨⟨a, haH⟩, Subgroup.subset_normalClosure ha, rfl⟩

theorem Js_le_Hs : img d (Jg d) ≤ Hs d := imgIn_mono d.s56V Jg_le_Hg

theorem Js_conj {h o : MulAut ↥d.s56V} (hh : h ∈ Hs d) (ho : o ∈ img d (Jg d)) :
    h * o * h⁻¹ ∈ img d (Jg d) := by
  obtain ⟨g, hgH, hgN, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hh
  obtain ⟨j, hjJ, hjN, rfl⟩ := (mem_imgIn_iff d.s56V (Jg d)).1 ho
  rw [← actFun_conj d.s56V hgN hjN]
  exact actFun_mem_imgIn (Jg_conj hgH hjJ) (mul_mem (mul_mem hgN hjN) (Subgroup.inv_mem _ hgN))

theorem Ws_le_Js (h49 : d.Thm49Statement) (hd : d.Hyp) : Ws d ≤ img d (Jg d) := by
  have hW0Hs : W0s d ≤ Hs d := (CFSG.LieType.BorelTits.pCoreOf_le 2 (Ks d)).trans inf_le_right
  have hxJ : star d d.x₅ ∈ img d (Jg d) :=
    actFun_mem_imgIn (Xg_le_Jg (x5_mem_Hg h49 hd) (mem_zpowers d.x₅)) (x5_mem_Hg h49 hd)
  rw [Ws_eq h49 hd, Subgroup.commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  have hbJ : b ∈ img d (Jg d) := zpowers_le.2 hxJ hb
  exact mul_mem (Js_conj (hW0Hs ha) hbJ) (Subgroup.inv_mem _ hbJ)

theorem H0_subgroupOf_normal
    (hZn : ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀) :
    ((H0 d z₀).subgroupOf (Hg d)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ H0 d z₀ := hn
  refine Subgroup.mem_subgroupOf.2 ⟨mul_mem (mul_mem g.2 n.2) (Subgroup.inv_mem _ g.2),
    mem_centralizer_iff.2 fun x hx => ?_⟩
  have hx' : (g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹ ∈ Zz d z₀ := hZn _ (Subgroup.inv_mem _ g.2) x hx
  have h1 : ((g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹) * n = n * ((g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹) :=
    mem_centralizer_iff.1 hn'.2 _ hx'
  calc x * ((g : G) * n * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹) * n) * (g : G)⁻¹ := by group
    _ = (g : G) * (n * ((g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹)) * (g : G)⁻¹ := by rw [h1]
    _ = ((g : G) * n * (g : G)⁻¹) * x := by group

theorem Jg_le_H0 (hZn : ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀)
    (hxz : ∀ x ∈ Zz d z₀, d.x₅ * x = x * d.x₅) (hx : d.x₅ ∈ Hg d) : Jg d ≤ H0 d z₀ := by
  haveI hN : ((H0 d z₀).subgroupOf (Hg d)).Normal := H0_subgroupOf_normal hZn
  have hle : Subgroup.normalClosure (((Xg d).subgroupOf (Hg d) : Subgroup ↥(Hg d)) : Set ↥(Hg d)) ≤
      (H0 d z₀).subgroupOf (Hg d) := by
    refine Subgroup.normalClosure_le_normal fun a ha => ?_
    have haX : (a : G) ∈ Xg d := ha
    obtain ⟨n, hn⟩ := haX
    refine Subgroup.mem_subgroupOf.2 ⟨a.2, mem_centralizer_iff.2 fun x hx' => ?_⟩
    rw [← hn]
    exact ((Commute.zpow_left (show Commute d.x₅ x from hxz x hx') n).eq).symm
  intro j hj
  obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.1 hj
  exact Subgroup.mem_subgroupOf.1 (hle hj')

theorem Js_inf_centralizer (h10 : Node10 d z₀) (hWab : IsElemAbelian 2 (Ws d))
    (hWg : img d (Wg d z₀) = Ws d)
    (hZ : Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G))
    (hJZ : Jg d ≤ centralizer ((Zz d z₀ : Subgroup G) : Set G))
    (hSyl : fusionIsSylowIn 2 (Ws d) (centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) ⊓ Hs d))
    (hWJ : Ws d ≤ img d (Jg d)) :
    img d (Jg d) ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) =
      Ws d := by
  have hWD : Ws d ≤ img d (Jg d) ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) := le_inf hWJ (le_centralizer_of_isElemAbelian hWab)
  refine le_antisymm ?_ hWD
  refine (eq_of_odd_free hSyl hWD (fun x hx => ⟨hx.2, Js_le_Hs hx.1⟩) ?_).le
  intro c hc p hp hp2 hcp
  have hQodd : Odd (Nat.card (zpowers c)) := by
    rw [Nat.card_zpowers, hcp]
    exact hp.odd_of_ne_two hp2
  have hPQ : Ws d ≤ normalizer ((zpowers c : Subgroup (MulAut ↥d.s56V)) : Set _) := fun w hw =>
    normalizer_zpowers_of_commute (mem_centralizer_iff.1 hc.2 w hw)
  have hfix : ∀ v : ↥d.s56V, (∀ q ∈ Ws d, q v = v) → ∀ q ∈ zpowers c, q v = v := by
    intro v hv q hq
    have hvZ : (v : G) ∈ Zz d z₀ := by
      rw [hZ]
      refine ⟨v.2, mem_centralizer_iff.2 fun w hw => ?_⟩
      have hwH : w ∈ Hg d := preIn_le_normalizer d.s56V _ hw.1
      have hstar : star d w ∈ Ws d := hWg ▸ actFun_mem_imgIn hw hwH
      exact (actFun_fixes_iff d.s56V hwH v).1 (hv _ hstar)
    have hqJ : q ∈ img d (Jg d) := (zpowers_le.2 hc.1) hq
    obtain ⟨j, hjJ, hjN, rfl⟩ := (mem_imgIn_iff d.s56V (Jg d)).1 hqJ
    exact (actFun_fixes_iff d.s56V hjN v).2 (mem_centralizer_iff.1 (hJZ hjJ) v hvZ).symm
  have hQ1 := odd_eq_bot_of_fixed (fun a b => Subtype.ext (h10.comm_V a.2 b.2))
    (fun v => Subtype.ext (h10.sq_V v.2)) (zpowers c) (Ws d) hQodd hWab.isPGroup hPQ hfix
  have hcQ : c ∈ zpowers c := mem_zpowers c
  rw [hQ1] at hcQ
  exact Subgroup.mem_bot.1 hcQ

theorem Js_quotient (hx : d.x₅ ∈ Hg d)
    (hWn : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hJC : img d (Jg d) ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) = Ws d)
    (h21 : Node21 d z₀) :
    ∃ _ : ((Ws d).subgroupOf (img d (Jg d))).Normal,
      Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃*
          Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) := by
  obtain ⟨hn, ⟨e⟩⟩ := quotient_equiv_Ja d.s56V (Xg d) (Jg d) (zpowers_le.2 hx) rfl hWn hJC
  refine ⟨hn, ?_⟩
  rcases h21.1 with ⟨⟨e1⟩, -⟩ | ⟨⟨e2⟩⟩
  · exact Or.inl ⟨e.trans e1⟩
  · exact Or.inr ⟨e.trans e2⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
