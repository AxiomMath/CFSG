module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcY
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups


section Generic

variable {G : Type} [Group G] [Finite G]

theorem lc_oddCore_section {u s : G} {M : Subgroup G}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set G)) M s)
    (hO : oddCoreIn (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥M = ⊥ := by
  have h1 : oddCoreIn M ≤ oddCoreIn (Subgroup.centralizer ({s} : Set G) ⊓
      Subgroup.centralizer ({u} : Set G)) := oddCoreIn_le_of_isSubnormal hM.subnormal
  rw [inf_comm] at h1
  have h2 : oddCoreIn M = ⊥ := le_bot_iff.mp (h1.trans hO.le)
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn h2

theorem lc_hnorm {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {J Λ : Subgroup G} {t w x : G}
    (hJ : J ∈ Ω) (hz : IsUniqueInvolution J t)
    (hΛ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({w} : Set G)) Λ t) (hJΛ : J ≤ Λ)
    (hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) = ⊥)
    (hxt : x * t = t * x) (hxw : x * w = w * x) (hxJ : ∀ j ∈ J, x * j = j * x) :
    ∀ l ∈ Λ, x * l * x⁻¹ ∈ Λ := by
  have hxC : x ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxw
  have h₂ : TwinSecXg.IsClassicalMember3On (Subgroup.centralizer ({w} : Set G)) Λ t := hΛ.toIn
  have h₁ : TwinSecXg.IsClassicalMember3On (Subgroup.centralizer ({w} : Set G)) (conjSub x Λ) t :=
    TwinConnT.isClassicalMember3On_conj (Subgroup.le_normalizer hxC)
      (by rw [hxt]; group) h₂
  have hJ₁ : J ≤ conjSub x Λ := by
    intro j hj
    have := conj_mem_conjSub (n := x) (hJΛ hj)
    rwa [show x * j * x⁻¹ = j by rw [hxJ j hj]; group] at this
  have hL₁ : conjSub x Λ ≤ Subgroup.centralizer ({w} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlw : l * w = w * l := Subgroup.mem_centralizer_singleton_iff.mp (hΛ.le hl)
    show x * l * x⁻¹ * w = w * (x * l * x⁻¹)
    calc x * l * x⁻¹ * w = x * l * (x⁻¹ * w) := by group
      _ = x * l * (w * x⁻¹) := by
        rw [show x⁻¹ * w = w * x⁻¹ from by
          have := congrArg (fun z => x⁻¹ * z * x⁻¹) hxw.symm
          simpa [mul_assoc] using this]
      _ = x * (l * w) * x⁻¹ := by group
      _ = x * (w * l) * x⁻¹ := by rw [hlw]
      _ = x * w * l * x⁻¹ := by group
      _ = w * x * l * x⁻¹ := by rw [hxw]
      _ = w * (x * l * x⁻¹) := by group
  have heq : conjSub x Λ = Λ :=
    TwinConnT.liftUnique_on hΩ hJ hz hJ₁ hJΛ hL₁ hΛ.le h₁ h₂ hOC
  intro l hl
  have := conj_mem_conjSub (n := x) hl
  rwa [heq] at this

end Generic

section Cfg

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem lc_w_mem_B (hc : P23Cfg n Y R S t K' W u e g) :
    g⁻¹ * u * g ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
  have hN := g_mem_normalizer_B hc
  have hu : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) u).mp hu
  simpa using this

theorem lc_one_twin_aux (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    {P P' Λ Λ' M L : Subgroup Y}
    (hPΩ : P ∈ Om R) (hP'Ω : P' ∈ Om R) (hne : P ≠ P')
    (hzP : IsUniqueInvolution P t) (hzP' : IsUniqueInvolution P' t)
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c P = P ∨ conjSub c P = P') ∧ (conjSub c P' = P ∨ conjSub c P' = P'))
    (hFeq : Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y) = twinCent R K')
    (hΛ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({g⁻¹ * u * g} : Set Y)) Λ t)
    (hΛ' : Q3NL.IsSectionMember3 (Subgroup.centralizer ({g⁻¹ * u * g} : Set Y)) Λ' t)
    (hPΛ : P ≤ Λ) (hP'Λ' : P' ≤ Λ') (hΛcomm : ∀ a ∈ Λ, ∀ b ∈ Λ', a * b = b * a)
    (hΛM : Λ = conjSub g⁻¹ M)
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e))
    (hOus : oddCoreIn (Subgroup.centralizer ({u} : Set Y) ⊓
      Subgroup.centralizer ({u * e} : Set Y)) = ⊥)
    (hML : M ≤ L) (hLu : L ≤ Subgroup.centralizer ({u} : Set Y))
    (hLn : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hLtype : Lc.LuGroup ↥L) (hKL : conjSub g (tightCore R) ≤ L) (hK'L : conjSub g K' ≤ L)
    (hOut : Lc.LuOutFact) (hRes : Lc.LuResFact) (hA6 : Lc.A6AutFact) :
    ∀ l ∈ Λ, ∀ x ∈ twinCent R K', l * x = x * l := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hq8 := lc_members_q8 hP hc hno hα
  have hPq := hq8 _ hPΩ
  have hP'q := hq8 _ hP'Ω
  have hP8 := lc_card_eq_eight hPq
  set w : Y := g⁻¹ * u * g with hw
  have hΛw : ∀ l ∈ Λ, l * w = w * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hΛ.le hl)
  have hΛ'w : ∀ l ∈ Λ', l * w = w * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hΛ'.le hl)
  have hw2 : w * w = 1 := by
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hd.hu2]; group
  have hOM : classicalInvolutionOddCore ↥M = ⊥ := lc_oddCore_section hM hOus
  have hΛO : classicalInvolutionOddCore ↥Λ = ⊥ := by
    rw [hΛM]; exact lc_oddCore_conj g⁻¹ hOM
  obtain ⟨eΛ⟩ := lc_equiv_sl2 hΛ hΛO
  have hOw : classicalInvolutionOddCore ↥(Subgroup.centralizer ({w} : Set Y) ⊓
      Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    have h1 := lc_oddCore_conj g⁻¹ (TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hOus)
    have e1 : conjSub g⁻¹ (Subgroup.centralizer ({u} : Set Y)) =
        Subgroup.centralizer ({w} : Set Y) := by
      rw [conjSub_centralizer_singleton g⁻¹ u]; simp [hw]
    have e2 : conjSub g⁻¹ (Subgroup.centralizer ({u * e} : Set Y)) =
        Subgroup.centralizer ({t} : Set Y) := by
      rw [conjSub_centralizer_singleton g⁻¹ (u * e)]
      have : g⁻¹ * (u * e) * g⁻¹⁻¹ = t := by rw [← hd.hgt]; group
      rw [this]
    have e3 : conjSub g⁻¹ (Subgroup.centralizer ({u} : Set Y) ⊓
        Subgroup.centralizer ({u * e} : Set Y)) = Subgroup.centralizer ({w} : Set Y) ⊓
        Subgroup.centralizer ({t} : Set Y) := by
      rw [conjSub, Subgroup.map_inf_eq _ _ (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective]
      rw [← e1, ← e2]
      rfl
    rwa [e3] at h1
  have hFu := twinCent_le_cu hc
  have hFt := twinCent_le_ct hc
  have hxP : ∀ x ∈ twinCent R K', ∀ k ∈ P, k * x = x * k := by
    intro x hx
    rw [← hFeq] at hx
    exact (Lc.mem_centralizer_sup_iff.mp hx).1
  have hxP' : ∀ x ∈ twinCent R K', ∀ k ∈ P', k * x = x * k := by
    intro x hx
    rw [← hFeq] at hx
    exact (Lc.mem_centralizer_sup_iff.mp hx).2
  have hwF : w ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y) := by
    rw [Lc.mem_centralizer_sup_iff]
    exact ⟨fun k hk => hΛw k (hPΛ hk), fun k hk => hΛ'w k (hP'Λ' hk)⟩
  have hwF' : w ∈ twinCent R K' := hFeq ▸ hwF
  have hnorm : ∀ x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y), x * w = w * x →
      ∀ l ∈ Λ, x * l * x⁻¹ ∈ Λ := by
    intro x hx hxw
    rw [hFeq] at hx
    have hxt : x * t = t * x := by
      have := hxP x hx t hzP.mem
      exact this.symm
    exact lc_hnorm hC.hyp hPΩ hzP hΛ hPΛ hOw hxt hxw (fun j hj => (hxP x hx j hj).symm)
  have hOF : oddCore ↥(Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y)) = ⊥ := by
    rw [hFeq]; exact lc_oddCore_twinCent hc hodd
  have hFL : ∀ f ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y), ∀ l ∈ L,
      f * l * f⁻¹ ∈ L := fun f hf l hl => hLn f (hFu (hFeq ▸ hf)) l hl
  have hDw : ∀ x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup Y) : Set Y),
      (∀ l ∈ L, x * l = l * x) → x * w = w * x := by
    intro x hx hxL
    have hx' : x ∈ twinCent R K' := hFeq ▸ hx
    have hxs : x * (u * e) = (u * e) * x := hxL _ (hML hM.mem)
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hFu hx')
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hFt hx')
    have hBx : Subgroup.closure ({u * e, u, t} : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxs.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hBx (lc_w_mem_B hc))).symm
  obtain ⟨y, hyL, hy2, hyc, hty⟩ := lc_y_exists hP hc hno hα hLu hKL hK'L
  have hAex := Lc.exists_A_of_fact hRes hLtype hyL hy2 hyc
  have key := Lc.central_main (P := P) (P' := P') (Λ := Λ) (L := L) (t := t) (w := w) (y := y)
    hP8 hPq hP'q hne hperm hzP.mem eΛ hPΛ
    (fun l hl x hx => hΛcomm l hl x (hP'Λ' hx)) hwF hw2 hΛw hnorm hOF hFL hDw hyL hty hAex
    (hOut ↥L hLtype) hA6
  intro l hl x hx
  exact key l hl x (by rw [hFeq]; exact hx)

theorem lc_two_twins (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    {M M' L : Subgroup Y}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e))
    (hM' : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e))
    (hJM : conjSub g (tightCore R) ≤ M) (hJ'M' : conjSub g K' ≤ M')
    (hcomm : ∀ a ∈ M, ∀ b ∈ M', a * b = b * a)
    (hOus : oddCoreIn (Subgroup.centralizer ({u} : Set Y) ⊓
      Subgroup.centralizer ({u * e} : Set Y)) = ⊥)
    (hML : M ≤ L) (hM'L : M' ≤ L) (hLu : L ≤ Subgroup.centralizer ({u} : Set Y))
    (hLn : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hLtype : Lc.LuGroup ↥L)
    (hOut : Lc.LuOutFact) (hRes : Lc.LuResFact) (hA6 : Lc.A6AutFact) :
    (∀ l ∈ conjSub g⁻¹ M, ∀ x ∈ twinCent R K', l * x = x * l) ∧
    (∀ l ∈ conjSub g⁻¹ M', ∀ x ∈ twinCent R K', l * x = x * l) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨hΛ, hΛ', hKΛ, hK'Λ', hΛcomm⟩ := Q3CH.liftsAt_z_of_conj hd.hgt hM hM' hJM hJ'M' hcomm
  have hKΩ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hKL : conjSub g (tightCore R) ≤ L := hJM.trans hML
  have hK'L : conjSub g K' ≤ L := hJ'M'.trans hM'L
  refine ⟨?_, ?_⟩
  · exact lc_one_twin_aux hP hc hno hα hodd (P := tightCore R) (P' := K')
      (Λ := conjSub g⁻¹ M) (Λ' := conjSub g⁻¹ M') (M := M) (L := L) hKΩ hK'Ω hc.std.hne.symm hz hz'
      (fun c hct => lc_perm hc hct) rfl hΛ hΛ' hKΛ hK'Λ' hΛcomm rfl hM hOus hML hLu hLn hLtype
      hKL hK'L hOut hRes hA6
  · refine lc_one_twin_aux hP hc hno hα hodd (P := K') (P' := tightCore R)
      (Λ := conjSub g⁻¹ M') (Λ' := conjSub g⁻¹ M) (M := M') (L := L) hK'Ω hKΩ hc.std.hne hz' hz
      (fun c hct => ⟨(lc_perm hc hct).2.symm, (lc_perm hc hct).1.symm⟩) ?_ hΛ' hΛ hK'Λ' hKΛ
      (fun a ha b hb => (hΛcomm b hb a ha).symm) rfl hM' hOus hM'L hLu hLn hLtype hKL hK'L hOut
      hRes hA6
    rw [sup_comm]; rfl

end Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
