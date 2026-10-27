module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf60SlotGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Aut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Sq
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

namespace AE5

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

theorem tail_sq_one {n : ℕ} (F : ExitO2.Q8Fam G P) (I : AEIdent P n) (Ψ : MulAut ↥(pSpan P))
    (θ : MulAut ↥(TL4.aeModel n)) (hθ : ∀ y, θ (I.toModel y) = I.toModel (Ψ y)) {J : Subgroup G}
    (hJ : J ∈ P) (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → Ψ y = y) (h1 : θ = 1) :
    ∀ y, Ψ y = y := by
  have hcent : ∀ g : ↥(pSpan P), g⁻¹ * Ψ g ∈ Subgroup.center ↥(pSpan P) := by
    intro g
    apply I.ker_le
    rw [← I.ker_toModel, MonoidHom.mem_ker, map_mul, map_inv]
    rw [← hθ g, h1, MulAut.one_apply, inv_mul_cancel]
  exact fixed_of_cent F.gen F.trans hJ Ψ.toMonoidHom hcent hfixJ

theorem tail_sq7 (F : ExitO2.Q8Fam G P) (I : AEIdent P 7)
    (Ψ : MulAut ↥(pSpan P)) (θ : MulAut ↥(TL4.aeModel 7))
    (hθ : ∀ y, θ (I.toModel y) = I.toModel (Ψ y)) {J : Subgroup G} (hJ : J ∈ P) {t : G}
    (ht : IsUniqueInvolution J t) {α : Finset (Fin 7)} {h : α.card = 4}
    (hζ : I.toModel ⟨t, le_pSpan hJ ht.mem⟩ = ⟨zBar α h, zBar_mem_aeModel α h⟩)
    (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → Ψ y = y)
    {p q : Fin 7} (hpq : p ≠ q) (hpα : p ∉ α) (hqα : q ∉ α)
    (hmodel : ∀ g : ↥(TL4.aeModel 7), ((θ g : ↥(TL4.aeModel 7)) : AEQ 7) =
      TL4.vbar 7 (TL4.pairVec p q) * g * (TL4.vbar 7 (TL4.pairVec p q))⁻¹) :
    Subgroup.closure ({y : ↥(pSpan P) | Ψ y = y} ∪
      {y : ↥(pSpan P) | (⟨t, le_pSpan hJ ht.mem⟩ : ↥(pSpan P)) * y =
        y * (⟨t, le_pSpan hJ ht.mem⟩ : ↥(pSpan P))}) = ⊤ := by
  classical
  have hn5 : 5 ≤ 7 := by norm_num
  set tt : ↥(pSpan P) := ⟨t, le_pSpan hJ ht.mem⟩ with htt
  set H : Subgroup ↥(pSpan P) :=
    Subgroup.closure ({y : ↥(pSpan P) | Ψ y = y} ∪ {y : ↥(pSpan P) | tt * y = y * tt}) with hH
  have hgen : pSpan P = ⊤ := F.gen
  have hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv
      ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm F.oddFree
  have hk2 : IsPGroup 2 I.toModel.ker := by
    rw [I.ker_toModel]
    exact I.isPGroup_ker hodd
  have hker : I.toModel.ker ≤ Subgroup.center ↥(pSpan P) := by
    rw [I.ker_toModel]
    exact I.ker_le
  have hS : ∀ b ∈ oddCent7 α h p q, b ∈ H.map I.φ := by
    rintro b ⟨hbM, hbodd, hcomm⟩
    have hodd' : Odd (orderOf (⟨b, hbM⟩ : ↥(TL4.aeModel 7))) := by
      rwa [Subgroup.orderOf_mk]
    have hbr : (⟨b, hbM⟩ : ↥(TL4.aeModel 7)) ∈ I.toModel.range :=
      MonoidHom.mem_range.mpr (I.toModel_surjective _)
    rcases hcomm with hc | hc
    · have hfix : θ ⟨b, hbM⟩ = ⟨b, hbM⟩ := by
        apply Subtype.ext
        rw [hmodel]
        calc TL4.vbar 7 (TL4.pairVec p q) * b * (TL4.vbar 7 (TL4.pairVec p q))⁻¹
            = (b * TL4.vbar 7 (TL4.pairVec p q)) * (TL4.vbar 7 (TL4.pairVec p q))⁻¹ := by
              rw [hc]
          _ = b := mul_inv_cancel_right _ _
      obtain ⟨y, hy, hΨ⟩ := exists_fixed_odd_lift_central I.toModel hker hk2 Ψ θ
        (fun x => (hθ x).symm) hbr hodd' hfix
      exact ⟨y, Subgroup.subset_closure (Or.inl hΨ), congrArg Subtype.val hy⟩
    · have hfix : (⟨b, hbM⟩ : ↥(TL4.aeModel 7)) * I.toModel tt = I.toModel tt * ⟨b, hbM⟩ := by
        rw [hζ]
        exact Subtype.ext hc
      obtain ⟨y, hy, hyt⟩ := exists_commuting_odd_lift_central I.toModel hker hk2 tt hbr hodd' hfix
      exact ⟨y, Subgroup.subset_closure (Or.inr hyt.symm), congrArg Subtype.val hy⟩
  have hMH : ∀ m ∈ TL4.aeModel 7, m ∈ H.map I.φ := by
    intro m hm
    rw [← closure_oddCent7 (α := α) h hpq hpα hqα] at hm
    exact (Subgroup.closure_le _).mpr hS hm
  have htrans : ∀ N ∈ P, ∃ y ∈ H, conjSub (y : G) J = N := by
    intro N hN
    obtain ⟨α₁, h₁, b₁, hlab⟩ := I.label J hJ
    obtain ⟨β₁, h₂, c₁, hlab'⟩ := I.label N hN
    obtain ⟨w, hw, hconj⟩ := exists_conj_label hn5 h₁ h₂ b₁ c₁
    obtain ⟨y, hyH, hy⟩ := hMH (mkQ 7 w) ⟨w, hw, rfl⟩
    refine ⟨y, hyH, same_of_imageN F hn5 I (F.hyp.conjInvariant (y : G) J hJ) hN ?_⟩
    rw [label_conj I hJ y, hlab, hlab', hy, ← hconj]
  have hall : ∀ N ∈ P, ∀ z (hz : z ∈ pSpan P), z ∈ N → (⟨z, hz⟩ : ↥(pSpan P)) ∈ H := by
    intro N hN z hz hzN
    obtain ⟨g, hgH, hgN⟩ := htrans N hN
    have hj : (g : G)⁻¹ * z * g ∈ J := by
      have : z ∈ conjSub (g : G) J := hgN ▸ hzN
      exact mem_conjSub_iff.mp this
    set j' : ↥(pSpan P) := ⟨(g : G)⁻¹ * z * g, (pSpan P).mul_mem ((pSpan P).mul_mem
      ((pSpan P).inv_mem g.2) hz) g.2⟩ with hj'
    have hjH : j' ∈ H := Subgroup.subset_closure (Or.inl (hfixJ j' hj))
    have hzeq : (⟨z, hz⟩ : ↥(pSpan P)) = g * j' * g⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hj']
      group)
    rw [hzeq]
    exact H.mul_mem (H.mul_mem hgH hjH) (H.inv_mem hgH)
  rw [eq_top_iff]
  intro y _
  set S : Subgroup G := H.map (pSpan P).subtype with hS'
  have hle : pSpan P ≤ S := pSpan_le fun N hN z hzN =>
    ⟨⟨z, le_pSpan hN hzN⟩, hall N hN z (le_pSpan hN hzN) hzN, rfl⟩
  obtain ⟨s, hs, hsy⟩ := hle y.2
  have : s = y := Subtype.ext hsy
  rw [← this]
  exact hs

theorem psi_sq_trichotomy7
    (F : ExitO2.Q8Fam G P) (I : AEIdent P 7) (ψ : MulAut ↥(pSpan P))
    (hψP : ∀ M ∈ P, ∃ M' ∈ P,
      (M.subgroupOf (pSpan P)).map ψ.toMonoidHom = M'.subgroupOf (pSpan P))
    (hψ4 : ∀ y, ψ (ψ (ψ (ψ y))) = y)
    {J J' : Subgroup G} (hJ : J ∈ P) (hJ' : J' ∈ P) (hne : J ≠ J') {t : G}
    (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t)
    (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ y = y)
    (hfixJ' : ∀ y : ↥(pSpan P), (y : G) ∈ J' → ψ y = y) :
    (∀ y, ψ (ψ y) = y) ∨
      Subgroup.closure ({y : ↥(pSpan P) | (ψ * ψ) y = y} ∪
        {y : ↥(pSpan P) | (⟨t, le_pSpan hJ ht.mem⟩ : ↥(pSpan P)) * y =
          y * (⟨t, le_pSpan hJ ht.mem⟩ : ↥(pSpan P))}) = ⊤ := by
  have hn5 : 5 ≤ 7 := by norm_num
  classical
  obtain ⟨α, h, b, hl⟩ := I.label J hJ
  obtain ⟨α', h', b', hl'⟩ := I.label J' hJ'
  have hz := phi_invN F hn5 I hJ ht h hl
  have hz' := phi_invN F hn5 I hJ' ht' h' hl'
  obtain rfl : α = α' := eq_of_zBar_eq (by omega) (hz.symm.trans hz')
  have hbb : b ≠ b' := by
    intro e
    apply hne
    refine same_of_imageN F hn5 I hJ hJ' ?_
    rw [hl, hl', e]
  set θ := inducedAutN hn5 I ψ with hθ
  have hperm : ∀ (γ : Finset (Fin 7)) (hγ : γ.card = 4) (c : Bool),
      ∃ (γ' : Finset (Fin 7)) (hγ' : γ'.card = 4) (c' : Bool),
        ((memBar γ hγ c).subgroupOf (TL4.aeModel 7)).map θ.toMonoidHom =
          (memBar γ' hγ' c').subgroupOf (TL4.aeModel 7) := by
    intro γ hγ c
    obtain ⟨L, hL, hLl⟩ := I.label_surj γ hγ c
    obtain ⟨M', hM', hM'e⟩ := hψP L hL
    obtain ⟨γ', hγ', c', hM'l⟩ := I.label M' hM'
    refine ⟨γ', hγ', c', ?_⟩
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨⟨g₀, hg₀⟩, hg₀m, hθg⟩
      have hg₀m' : g₀ ∈ memBar γ hγ c := hg₀m
      rw [← hLl] at hg₀m'
      obtain ⟨l, hl, hly⟩ := hg₀m'
      have e : (⟨g₀, hg₀⟩ : ↥(TL4.aeModel 7)) = I.toModel l := Subtype.ext hly.symm
      rw [e, inducedAutN_apply hn5] at hθg
      have hψl : ψ l ∈ (M'.subgroupOf (pSpan P)) := by
        rw [← hM'e]
        exact ⟨l, hl, rfl⟩
      have : (g : AEQ 7) ∈ (M'.subgroupOf (pSpan P)).map I.φ := by
        refine ⟨ψ l, hψl, ?_⟩
        have := congrArg Subtype.val hθg
        exact this
      rw [hM'l] at this
      exact this
    · intro hg'
      have hg'' : g ∈ (M'.subgroupOf (pSpan P)).map I.φ := by rw [hM'l]; exact hg'
      obtain ⟨m, hm, hmy⟩ := hg''
      rw [← hM'e] at hm
      obtain ⟨l, hl, hlm⟩ := hm
      have hlmem : (I.φ l) ∈ memBar γ hγ c := by
        rw [← hLl]
        exact ⟨l, hl, rfl⟩
      refine ⟨I.toModel l, hlmem, ?_⟩
      rw [inducedAutN_apply hn5]
      apply Subtype.ext
      show I.φ (ψ l) = g
      rw [show ψ l = m from hlm, hmy]
  have hfixα : ∀ c, ∀ y (hy : y ∈ memBar α h c), θ ⟨y, memBar_le_aeModel α h c hy⟩ =
      ⟨y, memBar_le_aeModel α h c hy⟩ := by
    intro c y hy
    have hc : c = b ∨ c = b' := by
      revert hbb
      cases b <;> cases b' <;> cases c <;> simp
    rcases hc with rfl | rfl
    · exact theta_fixN hn5 I ψ hJ hfixJ hl y hy
    · exact theta_fixN hn5 I ψ hJ' hfixJ' hl' y hy
  have hθ4 : ∀ g, θ (θ (θ (θ g))) = g := by
    intro g
    obtain ⟨y, rfl⟩ := I.toModel_surjective g
    rw [hθ, inducedAutN_apply hn5, inducedAutN_apply hn5, inducedAutN_apply hn5,
      inducedAutN_apply hn5, hψ4]
  have hmodel := aut_sq7 θ hperm hθ4 α h (hfixα true) (hfixα false)
  have hζ : I.toModel ⟨t, le_pSpan hJ ht.mem⟩ = ⟨zBar α h, zBar_mem_aeModel α h⟩ :=
    Subtype.ext (phi_invN F hn5 I hJ ht h hl)
  have hθθ : ∀ y, (θ * θ) (I.toModel y) = I.toModel ((ψ * ψ) y) := by
    intro y
    show θ (θ (I.toModel y)) = I.toModel (ψ (ψ y))
    rw [hθ, inducedAutN_apply hn5, inducedAutN_apply hn5]
  have hfix2 : ∀ y : ↥(pSpan P), (y : G) ∈ J → (ψ * ψ) y = y := by
    intro y hy
    show ψ (ψ y) = y
    rw [hfixJ y hy, hfixJ y hy]
  rcases hmodel with h1 | ⟨p, q, hpq, hpα, hqα, h1⟩
  · left
    exact tail_sq_one F I (ψ * ψ) (θ * θ) hθθ hJ hfix2 (MulEquiv.ext h1)
  · right
    exact tail_sq7 F I (ψ * ψ) (θ * θ) hθθ hJ ht hζ hfix2 hpq hpα hqα (fun g => h1 g)

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
