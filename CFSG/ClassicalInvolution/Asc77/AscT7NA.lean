module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscT7FD
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Abstract

variable {Q : Type*} [Group Q] {Δ : Set Q}

theorem eq_of_noncomm_closed (hS : Star3T.IsStar Δ) {S : Set Q} (hSΔ : S ⊆ Δ)
    (hcomm : ∀ x ∈ S, ∀ y ∈ Δ, y * x = x * y → y ∈ S)
    (hconj : ∀ x ∈ S, ∀ y ∈ S, x * y * x ∈ S) {p q : Q} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p * q ≠ q * p) : S = Δ := by
  refine Set.Subset.antisymm hSΔ fun c hc => ?_
  rcases hS p (hSΔ hp) q (hSΔ hq) hpq c hc with h1 | h2 | h3
  · exact hcomm p hp c hc h1
  · exact hcomm q hq c hc h2
  · exact hcomm _ (hconj p hp q hq) c hc h3

end Abstract

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem false_of_mGrp_le_sigmaNorm (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) (ρ : Rep Ω W) (hρ : ρ.K ∈ dComp Ω K)
    (hMN : MGrp Ω W ≤ sigmaNorm Ω K) : False := by
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  have c : Ctx p f Ω W := MuTab.muTabCtx hP hW
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hK hne hW
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := exists_boundary_of_dComp_ne hP.1 hP.2.1 hΩ hK hne
  have hK₁Ω : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁Ω hJ₁
  obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hnc ρ ρ₁
  obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hnc ρ σ₁
  rw [hρ₁] at hm₁K
  rw [hσ₁] at hm₂K
  have h1 : conjSub g K₁ ∈ dComp Ω K := by
    rw [← hm₁K]
    exact (hMN hm₁ ρ.K).mp hρ
  have h2 : conjSub g J₁ ∈ dComp Ω K := by
    rw [← hm₂K]
    exact (hMN hm₂ ρ.K).mp hρ
  have hgN : g ∈ sigmaNorm Ω K := T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hK₁d h1
  exact hJ₁n ((hgN J₁).mpr h2)

theorem rep_comm_of_mem_dComp (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) (ρ σ : Rep Ω W)
    (hρ : ρ.K ∈ dComp Ω K) (hσ : σ.K ∈ dComp Ω K) :
    σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  have c : Ctx p f Ω W := MuTab.muTabCtx hP hW
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta hP.1 hP.2.1 hΩ hW (thompsonCube G Ω hP W hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta hP.1 hP.2.1 hΩ hW (thompsonStar G Ω hP W hW)
  let S : Set ↥(muGroup Ω W) := {x | ∃ τ : Rep Ω W, τ.K ∈ dComp Ω K ∧ x = T7D.imgQ τ}
  have hSΔ : S ⊆ muDelta Ω W := by
    rintro x ⟨τ, -, rfl⟩
    exact T7D.imgQ_mem τ
  have hcomm : ∀ x ∈ S, ∀ y ∈ muDelta Ω W, y * x = x * y → y ∈ S := by
    rintro x ⟨τ, hτ, rfl⟩ y hy hyx
    obtain ⟨τ₂, hτ₂⟩ := exists_rep_of_mem_muDelta hy
    have hy' : y = T7D.imgQ τ₂ := Subtype.ext hτ₂.symm
    refine ⟨τ₂, ?_, hy'⟩
    by_cases hKK : τ.K = τ₂.K
    · rw [← hKK]; exact hτ
    · have hcm : τ.img * τ₂.img = τ₂.img * τ.img := by
        have := congrArg Subtype.val hyx
        rw [hy'] at this
        exact this.symm
      have hnb : τ₂.K ∈ omegaNbr Ω τ.K := c.omega_of_comm τ τ₂ hKK hcm
      have hcomp : dComp Ω τ.K = dComp Ω K := T7A.dComp_eq_of_mem hK hτ
      rw [← hcomp]
      exact T8.mem_dComp_of_mem_omegaNbr hnb
  have hconj : ∀ x ∈ S, ∀ y ∈ S, x * y * x ∈ S := by
    rintro x ⟨τ₁, hτ₁, rfl⟩ y ⟨τ₂, hτ₂, rfl⟩
    have hn : τ₁.r ∈ Subgroup.normalizer (W : Set G) := τ₁.r_mem_normalizer
    refine ⟨T7D.conjRep hΩ hn τ₂, ?_, ?_⟩
    · have hr : τ₁.r ∈ sigmaNorm Ω K :=
        T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hτ₁
          (Subgroup.le_normalizer (τ₁.hRK.1 τ₁.hr))
      exact (hr τ₂.K).mp hτ₂
    · apply Subtype.ext
      show (T7D.imgQ τ₁ * T7D.imgQ τ₂ * T7D.imgQ τ₁ : ↥(muGroup Ω W)).1 =
        (T7D.conjRep hΩ hn τ₂).img
      rw [T7D.conjRep_img]
      have hinv : (Thompson.piG W τ₁.r)⁻¹ = Thompson.piG W τ₁.r := by
        have := hTT.inv_eq (T7D.imgQ_mem τ₁)
        exact congrArg Subtype.val this
      rw [hinv]
      rfl
  have hpq : T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ := fun h =>
    c.noncomm ρ σ (fun e => hne1 e.symm) hne2 (congrArg Subtype.val h)
  have hSall : S = muDelta Ω W :=
    eq_of_noncomm_closed hS hSΔ hcomm hconj ⟨ρ, hρ, rfl⟩ ⟨σ, hσ, rfl⟩ hpq
  have hall : ∀ τ : Rep Ω W, τ.K ∈ dComp Ω K := by
    intro τ
    have : T7D.imgQ τ ∈ S := by rw [hSall]; exact T7D.imgQ_mem τ
    obtain ⟨τ', hτ', hτe⟩ := this
    have := c.K_eq_of_img_eq τ τ' (congrArg Subtype.val hτe)
    rw [this]
    exact hτ'
  have hMN : MGrp Ω W ≤ sigmaNorm Ω K := by
    refine iSup₂_le fun R hR => ?_
    obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR.1
    obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hP.1 hP.2.1 hΩ hW hR
    have hK₁d : K₁ ∈ dComp Ω K := hall ⟨K₁, R, r, hK₁, hR, hRK₁, hr, hrW⟩
    exact hRK₁.1.trans (Subgroup.le_normalizer.trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hK₁d))
  exact false_of_mGrp_le_sigmaNorm hP hW hK hne ρ hρ hMN

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
