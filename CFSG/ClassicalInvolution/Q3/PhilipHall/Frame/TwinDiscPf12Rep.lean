module

public import CFSG.ClassicalInvolution.Asc77.AscT7NA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuStar
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc


section Rep

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y}

@[expose] def conjRepG (hΩ : HypOmegaGen Ω) {n : Y} (hn : n ∈ Subgroup.normalizer (W : Set Y))
    (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

theorem conjRepG_img (hΩ : HypOmegaGen Ω) {n : Y} (hn : n ∈ Subgroup.normalizer (W : Set Y))
    (ρ : Thompson.Rep Ω W) :
    (conjRepG hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

theorem false_of_mGrp_le_sigmaNorm_gen (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    {K : Subgroup Y} (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) (ρ : Thompson.Rep Ω W)
    (hρ : ρ.K ∈ dComp Ω K) (hMN : MGrp Ω W ≤ sigmaNorm Ω K) : False := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hnc : ¬ DbarConnected Ω W := Q3T6.Mu.thompsonGraphAll hP hK hne hW
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := Q3T6.Mu.exists_boundary_of_dComp_ne hΩ hK hne
  have hK₁Ω : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁Ω hJ₁
  obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hP.cls hnc ρ ρ₁
  obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ₁
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

theorem rep_comm_of_mem_dComp_gen (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K : Subgroup Y}
    (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) (ρ σ : Thompson.Rep Ω W)
    (hρ : ρ.K ∈ dComp Ω K) (hσ : σ.K ∈ dComp Ω K) :
    σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hTT : Star3T.IsTT (muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (muDelta Ω W) := Q3T6.Mu.isStar_muDelta c
  let S : Set ↥(muGroup Ω W) := {x | ∃ τ : Thompson.Rep Ω W, τ.K ∈ dComp Ω K ∧ x = T7D.imgQ τ}
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
    have hn : τ₁.r ∈ Subgroup.normalizer (W : Set Y) := τ₁.r_mem_normalizer
    refine ⟨conjRepG hΩ hn τ₂, ?_, ?_⟩
    · have hr : τ₁.r ∈ sigmaNorm Ω K :=
        T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hτ₁
          (Subgroup.le_normalizer (τ₁.hRK.1 τ₁.hr))
      exact (hr τ₂.K).mp hτ₂
    · apply Subtype.ext
      show (T7D.imgQ τ₁ * T7D.imgQ τ₂ * T7D.imgQ τ₁ : ↥(muGroup Ω W)).1 =
        (conjRepG hΩ hn τ₂).img
      rw [conjRepG_img]
      have hinv : (Thompson.piG W τ₁.r)⁻¹ = Thompson.piG W τ₁.r := by
        have := hTT.inv_eq (T7D.imgQ_mem τ₁)
        exact congrArg Subtype.val this
      rw [hinv]
      rfl
  have hpq : T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ := fun h =>
    c.noncomm ρ σ (fun e => hne1 e.symm) hne2 (congrArg Subtype.val h)
  have hSall : S = muDelta Ω W :=
    T7N.eq_of_noncomm_closed hS hSΔ hcomm hconj ⟨ρ, hρ, rfl⟩ ⟨σ, hσ, rfl⟩ hpq
  have hall : ∀ τ : Thompson.Rep Ω W, τ.K ∈ dComp Ω K := by
    intro τ
    have : T7D.imgQ τ ∈ S := by rw [hSall]; exact T7D.imgQ_mem τ
    obtain ⟨τ', hτ', hτe⟩ := this
    have := c.K_eq_of_img_eq τ τ' (congrArg Subtype.val hτe)
    rw [this]
    exact hτ'
  have hMN : MGrp Ω W ≤ sigmaNorm Ω K := by
    refine iSup₂_le fun R hR => ?_
    obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR.1
    obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR
    have hK₁d : K₁ ∈ dComp Ω K := hall ⟨K₁, R, r, hK₁, hR, hRK₁, hr, hrW⟩
    exact hRK₁.1.trans (Subgroup.le_normalizer.trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hK₁d))
  exact false_of_mGrp_le_sigmaNorm_gen hP hW hK hne ρ hρ hMN

theorem rep_not_mem_sigmaNorm_gen (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K : Subgroup Y}
    (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) (ρ₁ ρ_L : Thompson.Rep Ω W) (hρ₁ : ρ₁.K = K)
    (hL1 : ρ_L.K ≠ K) (hL2 : ρ_L.K ∉ omegaNbr Ω K) : ρ_L.r ∉ sigmaNorm Ω K := by
  classical
  intro hr
  have hΩ : HypOmegaGen Ω := hP.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hTT : Star3T.IsTT (muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hn : ρ_L.r ∈ Subgroup.normalizer (W : Set Y) := ρ_L.r_mem_normalizer
  have hSig : (conjRepG hΩ hn ρ₁).K ∈ dComp Ω K := by
    show conjSub ρ_L.r ρ₁.K ∈ dComp Ω K
    rw [hρ₁]
    exact (hr K).mp Relation.ReflTransGen.refl
  have hρ₁S : ρ₁.K ∈ dComp Ω K := by rw [hρ₁]; exact Relation.ReflTransGen.refl
  have hcomm := rep_comm_of_mem_dComp_gen hP hW hK hne ρ₁ (conjRepG hΩ hn ρ₁) hρ₁S hSig
  have hL1' : ρ₁.K ≠ ρ_L.K := fun e => hL1 (by rw [← hρ₁]; exact e.symm)
  have hL2' : ρ_L.K ∉ omegaNbr Ω ρ₁.K := by rw [hρ₁]; exact hL2
  set a := T7D.imgQ ρ_L with ha
  set b := T7D.imgQ ρ₁ with hb
  have haΔ : a ∈ muDelta Ω W := T7D.imgQ_mem ρ_L
  have hbΔ : b ∈ muDelta Ω W := T7D.imgQ_mem ρ₁
  have hba : b * a ≠ a * b := fun e => c.noncomm ρ₁ ρ_L hL1' hL2' (congrArg Subtype.val e)
  have hab : a * b ≠ b * a := fun e => hba e.symm
  have hx : (T7D.imgQ (conjRepG hΩ hn ρ₁) : NQuot (W ⊔ OCW W)) =
      ((a * b * a⁻¹ : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) := by
    show (conjRepG hΩ hn ρ₁).img = _
    rw [conjRepG_img]
    rfl
  have hainv : a⁻¹ = a := hTT.inv_eq haΔ
  rcases hcomm with e | e
  · have h1 : T7D.imgQ (conjRepG hΩ hn ρ₁) = b :=
      Subtype.ext (c.img_eq_of_K_eq (conjRepG hΩ hn ρ₁) ρ₁ e)
    have h2 : a * b * a⁻¹ = b := by
      apply Subtype.ext
      rw [← hx]
      exact congrArg Subtype.val h1
    rw [hainv] at h2
    have h3 : a * b = b * a := by
      have h4 : a * b * a * a = b * a := by rw [h2]
      have haa : a * a = 1 := hTT.mul_self a haΔ
      calc a * b = a * b * (a * a) := by rw [haa, mul_one]
        _ = a * b * a * a := by rw [mul_assoc (a * b) a a]
        _ = b * a := h4
    exact hab h3
  · have hc := c.comm_of_omega ρ₁ (conjRepG hΩ hn ρ₁) e
    have hc' : b * (a * b * a⁻¹) = (a * b * a⁻¹) * b := by
      apply Subtype.ext
      have := hc
      rw [show ρ₁.img = (b : NQuot (W ⊔ OCW W)) from rfl] at this
      have hy : (conjRepG hΩ hn ρ₁).img = ((a * b * a⁻¹ : ↥(muGroup Ω W)) :
          NQuot (W ⊔ OCW W)) := hx
      rw [hy] at this
      exact this
    rw [hainv] at hc'
    have hbr : a * b * a = b * a * b := hTT.braid haΔ hbΔ hab
    have haa : a * a = 1 := hTT.mul_self a haΔ
    have hbb : b * b = 1 := hTT.mul_self b hbΔ
    have h1 : b * (a * b * a) = a * b := by
      rw [hbr]
      calc b * (b * a * b) = (b * b) * a * b := by group
        _ = a * b := by rw [hbb, one_mul]
    have h2 : (a * b * a) * b = b * a := by
      rw [hbr]
      calc b * a * b * b = b * a * (b * b) := by group
        _ = b * a := by rw [hbb, mul_one]
    have h3 : a * b = b * a := by
      calc a * b = b * (a * b * a) := h1.symm
        _ = (a * b * a) * b := hc'
        _ = b * a := h2
    exact hab h3

end Rep

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
