module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Quot

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Setting

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u : G}

omit [Finite G] in
theorem FusionSetup.t_mem_Cen_u (S : FusionSetup G L A t u) : t ∈ Cen u := by
  rw [mem_Cen]
  exact S.tu

omit [Finite G] in
theorem FusionSetup.A_mem_Cen_u (S : FusionSetup G L A t u) {a : G} (ha : a ∈ A) :
    a ∈ Cen u := mem_Cen.2 (S.A_u a ha)

@[expose] def tBarU (S : FusionSetup G L A t u) : QuotT u :=
  mkT u ⟨t, S.t_mem_Cen_u⟩

@[expose] def fBarU (S : FusionSetup G L A t u) : ↥A →* QuotT u :=
  (mkT u).comp (Subgroup.inclusion (fun _ ha => S.A_mem_Cen_u ha) : ↥A →* ↥(Cen u))

theorem fBarU_apply (S : FusionSetup G L A t u) (a : ↥A) :
    fBarU S a = mkT u ⟨a, S.A_mem_Cen_u a.2⟩ := rfl

theorem tBarU_sq (S : FusionSetup G L A t u) : tBarU S * tBarU S = 1 := by
  rw [tBarU, ← map_mul]
  have : (⟨t, S.t_mem_Cen_u⟩ : ↥(Cen u)) * ⟨t, S.t_mem_Cen_u⟩ = 1 := Subtype.ext S.t_sq
  rw [this, map_one]

theorem fBarU_injective (S : FusionSetup G L A t u) : Function.Injective (fBarU S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [fBarU_apply, ← map_one (mkT u), mkT_eq_mkT_iff S.u_sq] at ha
  rcases ha with h | h
  · exact Subtype.ext (congrArg Subtype.val h).symm
  · exfalso
    have h1 : (1 : G) = a * u := congrArg Subtype.val h
    have h2 : u = (a : G)⁻¹ := by
      have : (a : G)⁻¹ = (a : G)⁻¹ * (a * u) := by rw [← h1, mul_one]
      rw [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact this.symm
    have : u ∈ A := by rw [h2]; exact inv_mem a.2
    exact S.u_ne ((Subgroup.disjoint_def.1 S.disj) (mem_zpowers u) this)

theorem tBarU_not_mem_range (S : FusionSetup G L A t u) (a : ↥A) : fBarU S a ≠ tBarU S := by
  intro h
  rw [fBarU_apply, tBarU, mkT_eq_mkT_iff S.u_sq] at h
  apply S.t_nmem
  rcases h with h | h
  · have h1 : t = (a : G) := congrArg Subtype.val h
    rw [h1]
    exact S.A_le a.2
  · have h1 : t = (a : G) * u := congrArg Subtype.val h
    rw [h1]
    exact mul_mem (S.A_le a.2) S.u_mem

theorem fBarU_comm_tBarU (S : FusionSetup G L A t u) (a : ↥A) :
    fBarU S a * tBarU S = tBarU S * fBarU S a := by
  rw [fBarU_apply, tBarU, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (S.t_comm a (S.A_le a.2))

theorem cent_tBarU_decomp (S : FusionSetup G L A t u) (hn : ¬ IsConj t (t * u)) (h : ↥(Cen u))
    (hc : mkT u h * tBarU S = tBarU S * mkT u h) :
    ∃ a : ↥A, mkT u h = fBarU S a ∨ mkT u h = tBarU S * fBarU S a := by
  have hc' : mkT u (h * ⟨t, S.t_mem_Cen_u⟩) = mkT u (⟨t, S.t_mem_Cen_u⟩ * h) := by
    rw [map_mul, map_mul]
    exact hc
  rw [mkT_eq_mkT_iff S.u_sq] at hc'
  have hth : (h : G) * t = t * h := by
    rcases hc' with h1 | h1
    · exact (congrArg Subtype.val h1).symm
    · exfalso
      have h2 : t * (h : G) = (h : G) * t * u := congrArg Subtype.val h1
      apply hn
      refine isConj_iff.2 ⟨(h : G)⁻¹, ?_⟩
      rw [inv_inv]
      calc (h : G)⁻¹ * t * h = (h : G)⁻¹ * (t * h) := by rw [mul_assoc]
        _ = (h : G)⁻¹ * (h * t * u) := by rw [h2]
        _ = t * u := by group
  have hu : (h : G) * u = u * h := mem_Cen.1 h.2
  have hcV : (h : G) ∈ centralizer ((Vsub t u : Subgroup G) : Set G) :=
    mem_centralizer_Vsub.2 ⟨hth, hu⟩
  obtain ⟨v, hv, a, ha, hva⟩ := S.cent_V_decomp hcV
  refine ⟨⟨a, ha⟩, ?_⟩
  have haH : a ∈ Cen u := S.A_mem_Cen_u ha
  have hau : a * u = u * a := S.A_u a ha
  rcases (mem_Vsub_iff S.t_sq S.u_sq S.tu).1 hv with h1 | h1 | h1 | h1
  · left
    rw [h1] at hva
    have : h = ⟨a, haH⟩ := Subtype.ext (by rw [hva, one_mul])
    rw [this, fBarU_apply]
  · right
    rw [h1] at hva
    have : h = ⟨t, S.t_mem_Cen_u⟩ * ⟨a, haH⟩ := Subtype.ext hva
    rw [this, map_mul, fBarU_apply]
    rfl
  · left
    rw [h1] at hva
    have : h = ⟨a, haH⟩ * wOf u := Subtype.ext (by rw [hva]; exact hau.symm)
    rw [this, mkT_mul_wOf, fBarU_apply]
  · right
    rw [h1] at hva
    have : h = ⟨t, S.t_mem_Cen_u⟩ * (⟨a, haH⟩ * wOf u) := Subtype.ext (by
      rw [hva]
      change t * u * a = t * (a * u)
      rw [hau, mul_assoc])
    rw [this, map_mul, mkT_mul_wOf, fBarU_apply]
    rfl

theorem exists_mulEquiv_cent_u (S : FusionSetup G L A t u) (hn : ¬ IsConj t (t * u)) {B : Type*}
    [Group B] (eA : ↥A ≃* B) :
    Nonempty (↥(centralizer ({tBarU S} : Set (QuotT u))) ≃* Multiplicative (ZMod 2) × B) := by
  set Γ : Subgroup (QuotT u) := centralizer ({tBarU S} : Set (QuotT u)) with hΓ
  have hzΓ : tBarU S ∈ Γ := mem_centralizer_singleton_iff.2 rfl
  let z : ↥Γ := ⟨tBarU S, hzΓ⟩
  have hz : ∀ g : ↥Γ, g * z = z * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hz2 : z * z = 1 := Subtype.ext (tBarU_sq S)
  have hfΓ : (fBarU S).range ≤ Γ := by
    rintro _ ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.2 (fBarU_comm_tBarU S a)
  let Bs : Subgroup ↥Γ := (fBarU S).range.subgroupOf Γ
  have hzB : z ∉ Bs := by
    rintro ⟨a, ha⟩
    exact tBarU_not_mem_range S a ha
  have hcov : ∀ g : ↥Γ, g ∈ Bs ∨ z * g ∈ Bs := by
    intro g
    obtain ⟨h, hh⟩ := mkT_surjective u g.1
    have hc : mkT u h * tBarU S = tBarU S * mkT u h := by
      rw [hh]
      exact mem_centralizer_singleton_iff.1 g.2
    obtain ⟨a, ha | ha⟩ := cent_tBarU_decomp S hn h hc
    · left
      refine ⟨a, ?_⟩
      show fBarU S a = g.1
      rw [← ha, hh]
    · right
      refine ⟨a, ?_⟩
      show fBarU S a = tBarU S * g.1
      rw [← hh, ha, ← mul_assoc, tBarU_sq, one_mul]
  have e : ↥Bs ≃* B :=
    ((Subgroup.subgroupOfEquivOfLe hfΓ).trans
      (MonoidHom.ofInjective (fBarU_injective S)).symm).trans eA
  exact exists_mulEquiv_prod hz hz2 Bs hzB hcov e

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
