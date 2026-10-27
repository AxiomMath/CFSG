module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeXE
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeIdentCode
public import CFSG.Quasithin.Background.SmithB45MatIndM24

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Blueprint.NativeSporadic CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem not_mathieuCode24_XE (hm : M24Out G E t) :
    ¬ @MathieuCode24 ↥E (commGroupOfM24Out hm) (S44.XE E) ⊤ ⊥ := by
  intro h
  letI := commGroupOfM24Out hm
  obtain ⟨x, hx1, hdvd⟩ := exists_ne_one_card_orbit_dvd_of_mathieuCode24 h
  rcases card_orbit_cases hm hx1 with ⟨-, h276⟩ | ⟨-, h1771⟩
  · rw [h276] at hdvd
    exact absurd hdvd (by norm_num)
  · rw [h1771] at hdvd
    exact absurd hdvd (by norm_num)

theorem exists_equiv_w11
    (hm : M24Out G E t) :
    ∃ e : ↥E ≃* W11,
      (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
        img11 AutPerm := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  have hirr := isIrrOn_XE hm
  have hcard : Nat.card ↥E ≤ 2 ^ 36 := by
    rw [hm.card_E]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  rcases mathieuSmallIrr24_holds ↥E (m24Out_E_mul_self hm) (S44.XE E) (xe_equiv_m24 hm)
      hirr.2 hcard with hcode | hcocode
  · exact absurd hcode (not_mathieuCode24_XE hm)
  · obtain ⟨e, he⟩ := cocode24_std hcocode
    exact ⟨e, he.trans (range_rho11_eq_img11 _ le_rfl)⟩

theorem coc24_z0_ne_one : CFSG.Quasithin.H.Coc24.z0 ≠ 1 := by
  intro h
  have h' : toW 11 31 = toW 11 0 := by
    rw [toW_zero]
    exact h
  exact absurd (toW_inj (by norm_num) (by norm_num) h') (by norm_num)

theorem mem_normClass_iff_notMem_orbit_z0 (hm : M24Out G E t) (e : ↥E ≃* W11)
    (he : (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
      img11 AutPerm)
    {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    x ∈ normClass E t ↔
      e ⟨x, hxE⟩ ∉ orbit ↥(img11 AutPerm) CFSG.Quasithin.H.Coc24.z0 := by
  letI := commGroupOfM24Out hm
  obtain ⟨y, -, -, -, -, hcover⟩ := exists_two_orbits hm
  have horb : ∀ v : W11, orbit ↥((S44.XE E).map (CFSG.Quasithin.H.congrHom e)) v =
      orbit ↥(img11 AutPerm) v := by
    intro v
    rw [he]
  obtain ⟨w, hw⟩ : ∃ w : ↥E, w = e.symm CFSG.Quasithin.H.Coc24.z0 := ⟨_, rfl⟩
  have hew : e w = CFSG.Quasithin.H.Coc24.z0 := by
    rw [hw, MulEquiv.apply_symm_apply]
  have hw1 : w ≠ 1 := by
    intro h
    apply coc24_z0_ne_one
    rw [← hew, h, map_one]
  have hcw : 1771 ≤ Nat.card ↥(orbit ↥(S44.XE E) w) := by
    have h1 := card_orbit_map_congrHom e (S44.XE E) w
    rw [hew, horb] at h1
    rw [← h1, Nat.card_coe_set_eq]
    exact CFSG.Quasithin.H.Coc24.le_card_orbit
  have hwt : w ∉ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) := by
    rcases card_orbit_cases hm hw1 with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h
  have hwy : w ∈ orbit (S44.XE E) y := (hcover w hw1).resolve_left hwt
  have hx'1 : (⟨x, hxE⟩ : ↥E) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hmem : e ⟨x, hxE⟩ ∈ orbit ↥(img11 AutPerm) CFSG.Quasithin.H.Coc24.z0 ↔
      (⟨x, hxE⟩ : ↥E) ∈ orbit (S44.XE E) w := by
    have h1 := mem_orbit_map_congrHom_iff e (S44.XE E) w (e ⟨x, hxE⟩)
    rw [MulEquiv.symm_apply_apply, hew, horb] at h1
    exact h1
  have hcls : x ∈ normClass E t ↔
      (⟨x, hxE⟩ : ↥E) ∈ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) :=
    mem_normClass_iff_mem_orbit (⟨t, hm.t_mem⟩ : ↥E) ⟨x, hxE⟩
  rw [hcls, hmem]
  constructor
  · intro h hxw
    apply hwt
    have e1 : orbit (S44.XE E) (⟨x, hxE⟩ : ↥E) = orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) :=
      MulAction.orbit_eq_iff.2 h
    have e2 : orbit (S44.XE E) (⟨x, hxE⟩ : ↥E) = orbit (S44.XE E) w :=
      MulAction.orbit_eq_iff.2 hxw
    rw [← e2.symm.trans e1]
    exact mem_orbit_self w
  · intro h
    rcases hcover ⟨x, hxE⟩ hx'1 with h1 | h1
    · exact h1
    · exfalso
      apply h
      have e1 : orbit (S44.XE E) (⟨x, hxE⟩ : ↥E) = orbit (S44.XE E) y :=
        MulAction.orbit_eq_iff.2 h1
      have e2 : orbit (S44.XE E) w = orbit (S44.XE E) y := MulAction.orbit_eq_iff.2 hwy
      rw [e2, ← e1]
      exact mem_orbit_self _

theorem mem_orbit_z0_iff_notMem_normClass (hm : M24Out G E t) (e : ↥E ≃* W11)
    (he : (S44.XE E).map (@CFSG.Quasithin.H.congrHom ↥E W11 (commGroupOfM24Out hm) _ e) =
      img11 AutPerm)
    {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    e ⟨x, hxE⟩ ∈ orbit ↥(img11 AutPerm) CFSG.Quasithin.H.Coc24.z0 ↔ x ∉ normClass E t := by
  rw [mem_normClass_iff_notMem_orbit_z0 hm e he hxE hx1, not_not]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
