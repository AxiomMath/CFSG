module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3L34Odd

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Quot

variable {G : Type} [Group G] [Finite G]

@[expose] def wOf (T : G) : ↥(Cen T) := ⟨T, mem_Cen.2 rfl⟩

theorem wOf_central (T : G) (g : ↥(Cen T)) : g * wOf T = wOf T * g :=
  Subtype.ext (mem_Cen.1 g.2)

instance wOf_normal (T : G) : (zpowers (wOf T)).Normal := s3l_normal_zpowers (wOf_central T)

abbrev QuotT (T : G) : Type := ↥(Cen T) ⧸ zpowers (wOf T)

@[expose] def mkT (T : G) : ↥(Cen T) →* QuotT T := QuotientGroup.mk' _

theorem mkT_surjective (T : G) : Function.Surjective (mkT T) := QuotientGroup.mk'_surjective _

theorem mkT_eq_mkT_iff {T : G} (hT : T * T = 1) {g h : ↥(Cen T)} :
    mkT T g = mkT T h ↔ h = g ∨ h = g * wOf T := by
  have hw : wOf T * wOf T = 1 := Subtype.ext hT
  change (QuotientGroup.mk g : QuotT T) = QuotientGroup.mk h ↔ _
  rw [QuotientGroup.eq]
  constructor
  · intro hmem
    rcases s3l_mem_zpowers_two hw hmem with h1 | h1
    · left
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    · right
      rw [inv_mul_eq_iff_eq_mul] at h1
      exact h1
  · rintro (h1 | h1)
    · rw [h1]; simp
    · rw [h1]
      simpa using mem_zpowers (wOf T)

theorem mkT_wOf (T : G) : mkT T (wOf T) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (mem_zpowers _)

theorem mkT_mul_wOf (T : G) (g : ↥(Cen T)) : mkT T (g * wOf T) = mkT T g := by
  rw [map_mul, mkT_wOf, mul_one]

end Quot

section Setting

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u : G}

theorem FusionSetup.t_mem_Cen_tu (S : FusionSetup G L A t u) : t ∈ Cen (t * u) := by
  rw [mem_Cen]
  calc t * (t * u) = t * (u * t) := by rw [S.tu]
    _ = (t * u) * t := (mul_assoc _ _ _).symm

theorem FusionSetup.u_mem_Cen_tu (S : FusionSetup G L A t u) : u ∈ Cen (t * u) := by
  rw [mem_Cen]
  calc u * (t * u) = u * (u * t) := by rw [S.tu]
    _ = (u * u) * t := (mul_assoc _ _ _).symm
    _ = t * (u * u) := by rw [S.u_sq, mul_one, one_mul]
    _ = (t * u) * u := (mul_assoc _ _ _).symm

theorem FusionSetup.A_mem_Cen_tu (S : FusionSetup G L A t u) {a : G} (ha : a ∈ A) :
    a ∈ Cen (t * u) := by
  rw [mem_Cen]
  calc a * (t * u) = (a * t) * u := (mul_assoc _ _ _).symm
    _ = (t * a) * u := by rw [S.t_comm a (S.A_le ha)]
    _ = t * (a * u) := mul_assoc _ _ _
    _ = t * (u * a) := by rw [S.A_u a ha]
    _ = (t * u) * a := (mul_assoc _ _ _).symm

theorem FusionSetup.tu_sq (S : FusionSetup G L A t u) : (t * u) * (t * u) = 1 := by
  calc t * u * (t * u) = t * (u * t) * u := by simp only [mul_assoc]
    _ = t * (t * u) * u := by rw [S.tu]
    _ = (t * t) * (u * u) := by simp only [mul_assoc]
    _ = 1 := by rw [S.t_sq, S.u_sq, one_mul]

@[expose] def tBar (S : FusionSetup G L A t u) : QuotT (t * u) :=
  mkT (t * u) ⟨t, S.t_mem_Cen_tu⟩

@[expose] def fBar (S : FusionSetup G L A t u) : ↥A →* QuotT (t * u) :=
  (mkT (t * u)).comp (Subgroup.inclusion (fun a ha => S.A_mem_Cen_tu ha) :
    ↥A →* ↥(Cen (t * u)))

theorem fBar_apply (S : FusionSetup G L A t u) (a : ↥A) :
    fBar S a = mkT (t * u) ⟨a, S.A_mem_Cen_tu a.2⟩ := rfl

theorem mkT_u (S : FusionSetup G L A t u) :
    mkT (t * u) ⟨u, S.u_mem_Cen_tu⟩ = tBar S := by
  have h : (⟨u, S.u_mem_Cen_tu⟩ : ↥(Cen (t * u))) = ⟨t, S.t_mem_Cen_tu⟩ * wOf (t * u) := by
    refine Subtype.ext ?_
    change u = t * (t * u)
    rw [← mul_assoc, S.t_sq, one_mul]
  rw [h, mkT_mul_wOf]
  rfl

theorem tBar_sq (S : FusionSetup G L A t u) : tBar S * tBar S = 1 := by
  rw [tBar, ← map_mul]
  have : (⟨t, S.t_mem_Cen_tu⟩ : ↥(Cen (t * u))) * ⟨t, S.t_mem_Cen_tu⟩ = 1 := Subtype.ext S.t_sq
  rw [this, map_one]

theorem fBar_injective (S : FusionSetup G L A t u) : Function.Injective (fBar S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [fBar_apply, ← map_one (mkT (t * u)), mkT_eq_mkT_iff S.tu_sq] at ha
  rcases ha with h | h
  · exact Subtype.ext (congrArg Subtype.val h).symm
  · exfalso
    have h1 : (1 : G) = a * (t * u) := congrArg Subtype.val h
    have h2 : t * u = (a : G)⁻¹ := by
      have : (a : G)⁻¹ = (a : G)⁻¹ * (a * (t * u)) := by rw [← h1, mul_one]
      rw [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact this.symm
    apply S.t_nmem
    have : t = (t * u) * u := by rw [mul_assoc, S.u_sq, mul_one]
    rw [this, h2]
    exact mul_mem (inv_mem (S.A_le a.2)) S.u_mem

theorem tBar_not_mem_range (S : FusionSetup G L A t u) (a : ↥A) : fBar S a ≠ tBar S := by
  intro h
  rw [fBar_apply, tBar, mkT_eq_mkT_iff S.tu_sq] at h
  rcases h with h | h
  · apply S.t_nmem
    have h1 : t = (a : G) := congrArg Subtype.val h
    rw [h1]
    exact S.A_le a.2
  · have h1 : t = (a : G) * (t * u) := congrArg Subtype.val h
    have h2 : (a : G) = t * (t * u)⁻¹ := eq_mul_inv_of_mul_eq h1.symm
    rw [inv_eq_of_mul_eq_one_right S.tu_sq, ← mul_assoc, S.t_sq, one_mul] at h2
    have h3 := Subgroup.disjoint_def.1 S.disj (mem_zpowers u) (h2 ▸ a.2)
    exact S.u_ne h3

theorem fBar_comm_tBar (S : FusionSetup G L A t u) (a : ↥A) :
    fBar S a * tBar S = tBar S * fBar S a := by
  rw [fBar_apply, tBar, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (S.t_comm a (S.A_le a.2))

theorem cent_tBar_decomp (S : FusionSetup G L A t u) (hn : ¬ IsConj t u) (h : ↥(Cen (t * u)))
    (hc : mkT (t * u) h * tBar S = tBar S * mkT (t * u) h) :
    ∃ a : ↥A, mkT (t * u) h = fBar S a ∨ mkT (t * u) h = tBar S * fBar S a := by
  have hc' : mkT (t * u) (h * ⟨t, S.t_mem_Cen_tu⟩) = mkT (t * u) (⟨t, S.t_mem_Cen_tu⟩ * h) := by
    rw [map_mul, map_mul]
    exact hc
  rw [mkT_eq_mkT_iff S.tu_sq] at hc'
  have hth : (h : G) * t = t * h := by
    rcases hc' with h1 | h1
    · exact (congrArg Subtype.val h1).symm
    · exfalso
      have h2 : t * (h : G) = (h : G) * t * (t * u) := congrArg Subtype.val h1
      have h3 : t * (h : G) = h * u := by
        rw [h2, mul_assoc, ← mul_assoc t t u, S.t_sq, one_mul]
      apply hn
      refine isConj_iff.2 ⟨(h : G)⁻¹, ?_⟩
      rw [inv_inv, mul_assoc, h3]
      group
  have hT : (h : G) * (t * u) = (t * u) * h := mem_Cen.1 h.2
  have hu : (h : G) * u = u * h := by
    apply mul_left_cancel (a := t)
    calc t * ((h : G) * u) = (t * h) * u := (mul_assoc _ _ _).symm
      _ = (h * t) * u := by rw [hth]
      _ = h * (t * u) := mul_assoc _ _ _
      _ = (t * u) * h := hT
      _ = t * (u * h) := mul_assoc _ _ _
  have hcV : (h : G) ∈ centralizer ((Vsub t u : Subgroup G) : Set G) :=
    mem_centralizer_Vsub.2 ⟨hth, hu⟩
  obtain ⟨v, hv, a, ha, hva⟩ := S.cent_V_decomp hcV
  refine ⟨⟨a, ha⟩, ?_⟩
  have haH : a ∈ Cen (t * u) := S.A_mem_Cen_tu ha
  rcases (mem_Vsub_iff S.t_sq S.u_sq S.tu).1 hv with rfl | rfl | rfl | rfl
  · left
    have : h = ⟨a, haH⟩ := Subtype.ext (by rw [hva, one_mul])
    rw [this, fBar_apply]
  · right
    have : h = ⟨v, S.t_mem_Cen_tu⟩ * ⟨a, haH⟩ := Subtype.ext hva
    rw [this, map_mul, fBar_apply]
    rfl
  · right
    have : h = ⟨v, S.u_mem_Cen_tu⟩ * ⟨a, haH⟩ := Subtype.ext hva
    rw [this, map_mul, mkT_u, fBar_apply]
  · left
    have : h = wOf (t * u) * ⟨a, haH⟩ := Subtype.ext hva
    rw [this, map_mul, mkT_wOf, one_mul, fBar_apply]

theorem exists_mulEquiv_cent (S : FusionSetup G L A t u) (hn : ¬ IsConj t u) {B : Type*}
    [Group B] (eA : ↥A ≃* B) :
    Nonempty (↥(centralizer ({tBar S} : Set (QuotT (t * u)))) ≃*
      Multiplicative (ZMod 2) × B) := by
  set Γ : Subgroup (QuotT (t * u)) := centralizer ({tBar S} : Set (QuotT (t * u))) with hΓ
  have hzΓ : tBar S ∈ Γ := mem_centralizer_singleton_iff.2 rfl
  let z : ↥Γ := ⟨tBar S, hzΓ⟩
  have hz : ∀ g : ↥Γ, g * z = z * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hz2 : z * z = 1 := Subtype.ext (tBar_sq S)
  have hfΓ : (fBar S).range ≤ Γ := by
    rintro _ ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.2 (fBar_comm_tBar S a)
  let Bs : Subgroup ↥Γ := (fBar S).range.subgroupOf Γ
  have hzB : z ∉ Bs := by
    rintro ⟨a, ha⟩
    exact tBar_not_mem_range S a ha
  have hcov : ∀ g : ↥Γ, g ∈ Bs ∨ z * g ∈ Bs := by
    intro g
    obtain ⟨h, hh⟩ := mkT_surjective (t * u) g.1
    have hc : mkT (t * u) h * tBar S = tBar S * mkT (t * u) h := by
      rw [hh]
      exact mem_centralizer_singleton_iff.1 g.2
    obtain ⟨a, ha | ha⟩ := cent_tBar_decomp S hn h hc
    · left
      refine ⟨a, ?_⟩
      show fBar S a = g.1
      rw [← ha, hh]
    · right
      refine ⟨a, ?_⟩
      show fBar S a = tBar S * g.1
      rw [← hh, ha, ← mul_assoc, tBar_sq, one_mul]
  have e : ↥Bs ≃* B :=
    ((Subgroup.subgroupOfEquivOfLe hfΓ).trans (MonoidHom.ofInjective (fBar_injective S)).symm).trans
      eA
  exact exists_mulEquiv_prod hz hz2 Bs hzB hcov e

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
