module

public import CFSG.CGT.PushingUpLit.Orth.OrthCount
public import CFSG.CGT.PushingUpLit.Orth.OrthSolVec
public import CFSG.CGT.PushingUpLit.J42.S5Halves

public section

namespace CFSG.CGT.PushingUpLit.Orth

open CFSG CFSG.Assembly CFSG.RankThree.PartOne Equiv Equiv.Perm
open CFSG.CGT.PushingUpLit.SolK
open CFSG.Quasithin.G6 (coreMod coreAct)
open CFSG.CGT.PushingUpLit.BHS (vcoord vcoord_ext)

section Wpart

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

noncomputable def wpart (S : SolCfg G M X 2) (v : Vec5) : ↥S.D.W := S.D.β.symm (evenPart v)

theorem wpart_add (S : SolCfg G M X 2) (v w : Vec5) :
    wpart S (v + w) = wpart S v * wpart S w := by
  unfold wpart
  rw [evenPart_add, map_mul]

end Wpart

structure Setup {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2) where
  hT : TightData S
  hR : RSmall S
  hA : ∃ m : ↥M, sign (S.θ m) = -1
  r0 : G
  hr0 : r0 ∈ rOf M X
  hr01 : r0 ≠ 1

namespace Setup

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {S : SolCfg G M X 2} (U : Setup S)

include U

theorem rpart_mem (c : ZMod 2) : rpart U.r0 c ∈ rOf M X := by
  unfold rpart
  split_ifs
  · exact U.hr0
  · exact (rOf M X).one_mem

theorem r0_mul_self : U.r0 * U.r0 = 1 := by
  have := SolCfg.RSmall.sq S U.hR U.hr0
  rwa [pow_two] at this

theorem rOf_ne_bot : rOf M X ≠ ⊥ := fun h => U.hr01 (by
  have := U.hr0
  rw [h] at this
  exact Subgroup.mem_bot.1 this)

noncomputable def elt (v : Vec5) : G := (wpart S v : G) * rpart U.r0 (par v)

theorem elt_add (v w : Vec5) : U.elt (v + w) = U.elt v * U.elt w := by
  have hcomm : rpart U.r0 (par v) * (wpart S w : G) = (wpart S w : G) * rpart U.r0 (par v) :=
    (S.W_comm_R (wpart S w).2 (U.rpart_mem _)).symm
  unfold elt
  rw [wpart_add S, par_add, rpart_add U.r0_mul_self]
  calc ((wpart S v * wpart S w : ↥S.D.W) : G) * (rpart U.r0 (par v) * rpart U.r0 (par w))
      = (wpart S v : G) * ((wpart S w : G) * rpart U.r0 (par v)) * rpart U.r0 (par w) := by
        show (wpart S v : G) * (wpart S w : G) * _ = _
        group
    _ = (wpart S v : G) * (rpart U.r0 (par v) * (wpart S w : G)) * rpart U.r0 (par w) := by
        rw [hcomm]
    _ = _ := by group

theorem elt_inj : Function.Injective U.elt := by
  intro v w h
  obtain ⟨h1, h2⟩ := S.decomp_unique (wpart S v).2 (wpart S w).2 (U.rpart_mem _)
    (U.rpart_mem _) h
  have h3 : wpart S v = wpart S w := Subtype.ext h1
  have h4 : par v = par w := rpart_inj U.hr01 h2
  have h5 : evenPart v = evenPart w := S.D.β.symm.injective h3
  funext i
  have := congrArg (fun u => vcoord u i) h5
  simp only [vcoord_evenPart, h4] at this
  exact add_right_cancel this

theorem elt_shift (u : ↥(coreMod 5)) (c : ZMod 2) :
    U.elt (fun i => vcoord u i + c) = ((S.D.β.symm u : ↥S.D.W) : G) * rpart U.r0 c := by
  obtain ⟨hp, he⟩ := evenPart_shift u c
  unfold elt wpart
  rw [hp, he]

theorem mem_Q_iff (x : G) : x ∈ pCoreOf 2 M ↔ ∃ v, U.elt v = x := by
  constructor
  · intro hx
    obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq x hx
    have hr' : r = 1 ∨ r = U.r0 := by
      by_cases h1 : r = 1
      · exact Or.inl h1
      · right
        exact eq_of_card_le_two (H := ↥(rOf M X)) U.hR (a := ⟨r, hr⟩) (b := ⟨U.r0, U.hr0⟩)
          (fun h => h1 (congrArg Subtype.val h)) (fun h => U.hr01 (congrArg Subtype.val h))
          |> congrArg Subtype.val
    have hu : S.D.β.symm (S.D.β ⟨w, hw⟩) = ⟨w, hw⟩ := S.D.β.symm_apply_apply _
    rcases hr' with rfl | rfl
    · refine ⟨fun i => vcoord (S.D.β ⟨w, hw⟩) i + 0, ?_⟩
      rw [U.elt_shift, hu, rpart_zero]
    · refine ⟨fun i => vcoord (S.D.β ⟨w, hw⟩) i + 1, ?_⟩
      rw [U.elt_shift, hu, rpart_one]
  · rintro ⟨v, rfl⟩
    exact (pCoreOf 2 M).mul_mem (S.W_le_Q (wpart S v).2) (U.rpart_mem _).1

theorem theta_surj : Function.Surjective S.θ := by
  obtain ⟨m₀, hm₀⟩ := U.hA
  intro σ
  have hX : ∀ τ ∈ alternatingGroup (Fin (2 * 2 + 1)), ∃ m : ↥M, S.θ m = τ := by
    intro τ hτ
    obtain ⟨c, hc⟩ := S.D.ρ_surj τ hτ
    exact ⟨⟨(c : G), S.hyp.le c.2⟩, by rw [S.θ_X c, hc]⟩
  by_cases hs : sign σ = 1
  · exact hX σ (Equiv.Perm.mem_alternatingGroup.2 hs)
  · have hs' : sign σ = -1 := (Int.units_eq_one_or _).resolve_left hs
    have : σ * (S.θ m₀)⁻¹ ∈ alternatingGroup (Fin (2 * 2 + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs', hm₀]
      decide
    obtain ⟨m₁, hm₁⟩ := hX _ this
    exact ⟨m₁ * m₀, by rw [map_mul, hm₁, inv_mul_cancel_right]⟩

theorem equivar (m : ↥M) (v : Vec5) :
    (m : G) * U.elt v * (m : G)⁻¹ = U.elt (permAct (S.θ m) v) := by
  have hw' : (m : G) * (wpart S v : G) * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 (wpart S v).2
  have h1 : S.D.β ⟨(m : G) * (wpart S v : G) * (m : G)⁻¹, hw'⟩ =
      coreAct (2 * 2 + 1) (S.θ m) (S.D.β (wpart S v)) := S.θ_spec m (wpart S v) hw'
  have h3 : (⟨(m : G) * (wpart S v : G) * (m : G)⁻¹, hw'⟩ : ↥S.D.W) =
      wpart S (permAct (S.θ m) v) := by
    apply S.D.β.injective
    rw [h1]
    unfold wpart
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, evenPart_permAct]
  have h4 : (m : G) * rpart U.r0 (par v) * (m : G)⁻¹ = rpart U.r0 (par v) :=
    SolCfg.RSmall.central S U.hR m.2 (U.rpart_mem _)
  have h5 : ((wpart S (permAct (S.θ m) v) : ↥S.D.W) : G) =
      (m : G) * (wpart S v : G) * (m : G)⁻¹ := (congrArg Subtype.val h3).symm
  unfold elt
  rw [h5, par_permAct]
  calc (m : G) * ((wpart S v : G) * rpart U.r0 (par v)) * (m : G)⁻¹
      = ((m : G) * (wpart S v : G) * (m : G)⁻¹) * ((m : G) * rpart U.r0 (par v) * (m : G)⁻¹) := by
        group
    _ = _ := by rw [h4]

noncomputable def orthCfg : OrthCfg G M (pCoreOf 2 M) where
  elt := U.elt
  elt_add := U.elt_add
  elt_inj := U.elt_inj
  mem_Q_iff := U.mem_Q_iff
  θ := S.θ
  θ_surj := U.theta_surj
  θ_ker := fun m =>
    ⟨fun h => S.mem_Q_of_theta_eq_one U.hR m.2 h, fun h => S.theta_eq_one_of_mem_Q h⟩
  equivar := U.equivar
  Q_le_M := pCoreOf_le_self M
  normalizer_Q := S.normalizer_Q_eq
  centralizer_Q := (S.centralizer_Q_eq U.hT).le

theorem rigid_cent {v : Vec5} (hv : Rigid v) : Subgroup.centralizer ({U.elt v} : Set G) ≤ M := by
  rw [centralizer_singleton_eq_zpowers]
  obtain ⟨hv0, hw⟩ := hv
  by_cases h5 : wt v = 5
  · have hvo := eq_ones_of_wt_five v h5
    subst hvo
    have hel : U.elt ones = U.r0 := by
      unfold elt wpart
      rw [evenPart_ones, par_ones, rpart_one]
      simp
    rw [hel]
    have hN := (S.centralizer_eq_of_len S.hyp.charTwo U.hT U.hr0.1 U.hr01
      (S.hasLen_zero U.hr0) (by norm_num) (by norm_num)).2
    exact (Subgroup.centralizer_le_normalizer _).trans hN
  · have h14 : wt v = 1 ∨ wt v = 4 := by omega
    have hcard : (vsupp (S.D.β ⟨(wpart S v : G), (wpart S v).2⟩)).card = 4 := by
      have h1 : S.D.β ⟨(wpart S v : G), (wpart S v).2⟩ = evenPart v := S.D.β.apply_symm_apply _
      rw [h1]
      exact card_supp_evenPart v h14
    by_contra hKM
    exact U.rOf_ne_bot (S.rOf_eq_bot U.hT (SolCfg.RSmall.elem S U.hR) U.hR (wpart S v).2
      (U.rpart_mem (par v)) hcard hKM)

theorem two_constrained {v : Vec5} (hv : v ≠ 0) : ∃ P : Subgroup G,
    IsO2 (Subgroup.centralizer ({U.elt v} : Set G)) P ∧
      Subgroup.centralizer ({U.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P := by
  have hx1 : U.elt v ≠ 1 := U.orthCfg.elt_ne_one hv
  have hxQ : U.elt v ∈ pCoreOf 2 M := (U.mem_Q_iff _).2 ⟨v, rfl⟩
  have hB : Subgroup.zpowers (U.elt v) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers (U.elt v)) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB hB2
  rw [centralizer_singleton_eq_zpowers]
  exact ⟨_, ⟨pCoreOf_le_self _, fun k hk p hp => pCoreOf_normalized _ hk hp,
    isPGroup_pCoreOf' _, fun N hNK hnorm hN => le_pCoreOf_of_normalized hNK hnorm hN⟩, hcons⟩

theorem centInM : CentInM S := by
  intro x hx hx1
  obtain ⟨v, rfl⟩ := (U.mem_Q_iff x).1 hx
  have hv : v ≠ 0 := fun h => hx1 (by rw [h]; exact U.orthCfg.elt_zero)
  exact U.orthCfg.centralizer_le_M (fun w hw => U.rigid_cent hw) (fun w hw => U.two_constrained hw)
    hv

end Setup

end CFSG.CGT.PushingUpLit.Orth

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.GH74 Equiv Equiv.Perm
open CFSG.Assembly (InCatalog KProper)
open CFSG.CGT.PushingUpLit.Orth

theorem jankoU42Gen4S5RNe1_holds : JankoU42Gen4S5RNe1 := by
  intro G _ _ M X S _hKP hT hR hC hA hRne
  obtain ⟨⟨r0, hr0⟩, hr01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRne
  exact absurd (Setup.centInM (⟨hT, hR, hA, r0, hr0, fun h => hr01 (Subtype.ext h)⟩ : Setup S)) hC

end CFSG.CGT.PushingUpLit.SolK
