module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Trans
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Catalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

theorem map_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ g
    obtain ⟨a', rfl⟩ := e.surjective g
    show e a' * e a = e a * e a'
    rw [← map_mul, ← map_mul, ha]
  · intro hb
    refine ⟨e.symm b, fun g => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hb (e g)

theorem transfer_cover {Y A : Type*} [Group Y] [Group A] (Hs : Subgroup Y) (e : A ≃* ↥Hs)
    (hper : commutator A = ⊤) (hcard : Nat.card (center A) = 2)
    (hq : Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 6))) :
    ⁅Hs, Hs⁆ = Hs ∧ Nat.card (center ↥Hs) = 2 ∧
      Nonempty (↥Hs ⧸ center ↥Hs ≃* alternatingGroup (Fin 6)) := by
  have hc : (center A).map e.toMonoidHom = center ↥Hs := map_center_equiv e
  refine ⟨?_, ?_, ?_⟩
  · have h1 : commutator ↥Hs = ⊤ := by
      have := Subgroup.map_commutator (⊤ : Subgroup A) (⊤ : Subgroup A) e.toMonoidHom
      rw [Subgroup.map_top_of_surjective _ e.surjective] at this
      rw [commutator_def, ← this, ← commutator_def, hper, Subgroup.map_top_of_surjective _ e.surjective]
    rw [← Subgroup.map_subtype_commutator, h1, Subgroup.map_top, Subgroup.range_subtype]
  · rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]
  · obtain ⟨q⟩ := hq
    exact ⟨((QuotientGroup.congr (center A) (center ↥Hs) e hc).symm).trans q⟩

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

include c

theorem u_not_mem_Zc : c.u ∉ c.Zc := by
  intro h
  obtain ⟨a, ha, w, hw, hauw⟩ := c.mem_Zc_iff.1 h
  have ha3 := c.X_cube a ha
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hw with rfl | rfl
  · rw [mul_one] at hauw
    subst hauw
    apply c.u_ne_one
    have : c.u ^ 3 = c.u := by rw [pow_succ, pow_two, c.u_sq, one_mul]
    rw [← this, ha3]
  · have hc : Commute a c.u₁ := (c.cm_X_u₁.comm ha (mem_zpowers _) : a * c.u₁ = c.u₁ * a)
    have h2 : a ^ 2 = 1 := by
      have := hc.mul_pow 2
      rw [← hauw, pow_two c.u, c.u_sq, pow_two c.u₁, c.u₁_sq, mul_one] at this
      exact this.symm
    have ha1 : a = 1 := by
      have : a ^ 3 = a := by rw [pow_succ, h2, one_mul]
      rw [← this, ha3]
    rw [ha1, one_mul] at hauw
    exact c.u₁_ne_u hauw.symm

theorem conjSub_le_Jc : conjSub t c.L₁ ≤ c.Jc := by
  have h1 : Cm (conjSub t c.L₁) c.L₁ := fun b hb =>
    mem_centralizer_iff.2 fun a ha => (c.comm_L₁_conj ha hb).eq
  have h2 : Cm (conjSub t c.L₁) (zpowers c.u₁) :=
    (cm_zpowers_left fun b hb => (c.u₁_comm_L₁t hb).symm).symm
  exact Cm.sup_right (h1.mono le_rfl c.X_le_L₁) h2

@[expose] noncomputable def phiH : ↥(conjSub t c.L₁) →* c.Yq :=
  c.mkY.comp (Subgroup.inclusion c.conjSub_le_Jc)

theorem phiH_injective : Function.Injective c.phiH := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, ha⟩ h
  have hZ : a ∈ c.Zc := (c.mkY_eq_one_iff _).1 h
  obtain ⟨a', ha', rfl⟩ := mem_conjSub.1 ha
  have hcent : ∀ b ∈ c.L₁, a' * b = b * a' := by
    intro b hb
    have hbt : t * b * t⁻¹ ∈ conjSub t c.L₁ := mem_conjSub.2 ⟨b, hb, rfl⟩
    have h1 : (t * b * t⁻¹) * (t * a' * t⁻¹) = (t * a' * t⁻¹) * (t * b * t⁻¹) :=
      (mem_centralizer_iff.1 (c.conjSub_le_Jc hbt) _ hZ).symm
    have h2 : t * (b * a') * t⁻¹ = t * (a' * b) * t⁻¹ := by
      calc t * (b * a') * t⁻¹ = (t * b * t⁻¹) * (t * a' * t⁻¹) := by group
        _ = (t * a' * t⁻¹) * (t * b * t⁻¹) := h1
        _ = t * (a' * b) * t⁻¹ := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3.symm
  apply Subtype.ext
  show t * a' * t⁻¹ = 1
  rcases c.center_le a' ha' hcent with rfl | rfl
  · simp
  · exfalso
    apply c.u_not_mem_Zc
    have : t * c.u * t⁻¹ = c.u := by rw [c.t_inv]; exact c.tut
    rw [this] at hZ
    exact hZ

@[expose] noncomputable def Hsub : Subgroup c.Yq := c.phiH.range

@[expose] noncomputable def eH : ↥c.L₁ ≃* ↥c.Hsub :=
  (MulEquiv.subgroupMap (MulAut.conj t) c.L₁).trans (MonoidHom.ofInjective c.phiH_injective)

theorem isKGroupCat_Yq {L : Subgroup G} (hStd : StdHyp G L) :
    CFSG.SectionRank.IsKGroupCat c.Yq := by
  have hu₁Zc : c.u₁ ∈ c.Zc := mem_sup_right (mem_zpowers _)
  have hJle : c.Jc ≤ centralizer ({c.u₁} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.2 hu₁Zc)
  exact ((hStd.isKGroupCat_centralizer_of_orderOf (n := 2) le_rfl c.u₁_ord).of_injective
    (Subgroup.inclusion hJle) (Subgroup.inclusion_injective hJle)).quotient _

theorem false_of_cover (hA : AutFacts ↥c.L₁) (hKY : CFSG.SectionRank.IsKGroupCat c.Yq)
    (hON : ONan77S5) (hNo : ONanNoSL29Y)
    (hper : commutator ↥c.L₁ = ⊤) (hcard : Nat.card (center ↥c.L₁) = 2)
    (hq : Nonempty (↥c.L₁ ⧸ center ↥c.L₁ ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨N, hN, hNc, hNL⟩ := hON c.Yq hKY (fun A hA' hAab => c.eq_bot_of_normal hA A hA' hAab)
    c.Pbar c.Pbar_comm c.Pbar_cube c.card_Pbar
    (fun a ha ha1 => c.centralizer_equiv_of_mem_Pbar hA ha ha1)
  obtain ⟨h1, h2, h3⟩ := transfer_cover c.Hsub c.eH hper hcard hq
  exact hNo c.Yq N hN hNc hNL c.Hsub h1 h2 h3

end S14Cfg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
