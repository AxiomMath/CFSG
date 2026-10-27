module

public import CFSG.ClassicalInvolution.Asc77.AscT7NA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Reps

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_noncomm_rep (c : Thompson.Ctx p f Ω W) (hnc : ¬ DbarConnected Ω W)
    (ρ₁ : Rep Ω W) : ∃ ρ_L : Rep Ω W, ρ_L.K ≠ ρ₁.K ∧ ρ_L.K ∉ omegaNbr Ω ρ₁.K := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd, a, ha, hna⟩ := exists_not_conn_of_not_connected c.hp c.hq c.hΩ c.hW hnc
  have hx₁ : T7D.imgQ ρ₁ ∈ muDelta Ω W := T7D.imgQ_mem ρ₁
  have hall : ∀ y ∈ muDelta Ω W, y * T7D.imgQ ρ₁ = T7D.imgQ ρ₁ * y := by
    intro y hy
    obtain ⟨τ, hτ⟩ := exists_rep_of_mem_muDelta hy
    have hy' : y = T7D.imgQ τ := Subtype.ext hτ.symm
    rw [hy']
    by_cases hK : τ.K = ρ₁.K
    · have : T7D.imgQ τ = T7D.imgQ ρ₁ := Subtype.ext (c.img_eq_of_K_eq τ ρ₁ hK)
      rw [this]
    · exact Subtype.ext (c.comm_of_omega ρ₁ τ (hcon τ hK)).symm
  exact hna ((Star3T.conn_of_commute hx₁ hd (hall d hd).symm).symm.trans
    (Star3T.conn_of_commute hx₁ ha (hall a ha).symm))

end Reps

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.r_not_mem_sigmaNorm (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) (ρ₁ ρ_L : Rep Ω W) (hρ₁ : ρ₁.K = K)
    (hL1 : ρ_L.K ≠ K) (hL2 : ρ_L.K ∉ omegaNbr Ω K) : ρ_L.r ∉ sigmaNorm Ω K := by
  classical
  intro hr
  have hst := h.std.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have c : Ctx p f Ω W := MuTab.muTabCtx hP h.hW
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta hP.1 hP.2.1 hΩ h.hW (thompsonCube G Ω hP W h.hW)
  have hn : ρ_L.r ∈ Subgroup.normalizer (W : Set G) := ρ_L.r_mem_normalizer
  have hSig : (T7D.conjRep hΩ hn ρ₁).K ∈ dComp Ω K := by
    show conjSub ρ_L.r ρ₁.K ∈ dComp Ω K
    rw [hρ₁]
    exact (hr K).mp Relation.ReflTransGen.refl
  have hρ₁S : ρ₁.K ∈ dComp Ω K := by rw [hρ₁]; exact Relation.ReflTransGen.refl
  have hcomm := rep_comm_of_mem_dComp hP h.hW hK hne ρ₁ (T7D.conjRep hΩ hn ρ₁) hρ₁S hSig
  have hL1' : ρ₁.K ≠ ρ_L.K := fun e => hL1 (by rw [← hρ₁]; exact e.symm)
  have hL2' : ρ_L.K ∉ omegaNbr Ω ρ₁.K := by rw [hρ₁]; exact hL2
  set a := T7D.imgQ ρ_L with ha
  set b := T7D.imgQ ρ₁ with hb
  have haΔ : a ∈ muDelta Ω W := T7D.imgQ_mem ρ_L
  have hbΔ : b ∈ muDelta Ω W := T7D.imgQ_mem ρ₁
  have hba : b * a ≠ a * b := fun e => c.noncomm ρ₁ ρ_L hL1' hL2' (congrArg Subtype.val e)
  have hab : a * b ≠ b * a := fun e => hba e.symm
  have hx : (T7D.imgQ (T7D.conjRep hΩ hn ρ₁) : NQuot (W ⊔ OCW W)) =
      ((a * b * a⁻¹ : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) := by
    show (T7D.conjRep hΩ hn ρ₁).img = _
    rw [T7D.conjRep_img]
    rfl
  have hainv : a⁻¹ = a := hTT.inv_eq haΔ
  rcases hcomm with e | e
  · have h1 : T7D.imgQ (T7D.conjRep hΩ hn ρ₁) = b :=
      Subtype.ext (c.img_eq_of_K_eq (T7D.conjRep hΩ hn ρ₁) ρ₁ e)
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
  · have hc := c.comm_of_omega ρ₁ (T7D.conjRep hΩ hn ρ₁) e
    have hc' : b * (a * b * a⁻¹) = (a * b * a⁻¹) * b := by
      apply Subtype.ext
      have := hc
      rw [show ρ₁.img = (b : NQuot (W ⊔ OCW W)) from rfl] at this
      have hy : (T7D.conjRep hΩ hn ρ₁).img = ((a * b * a⁻¹ : ↥(muGroup Ω W)) :
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

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
