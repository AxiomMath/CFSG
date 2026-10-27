module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDSetting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G Pr : Type} [Group G] [Group Pr] {L : Subgroup G} {s : G} {X : Subgroup Pr} [X.Normal]
  {y : Pr} {ρ : ↥L →* ↥X}

theorem Sec4FDCover.image_comm (h : Sec4FDCover L s X y ρ) {d : G} (hdL : d ∈ L)
    (hds : d * s = s * d) :
    ((ρ ⟨d, hdL⟩ : ↥X) : Pr) * y = y * ((ρ ⟨d, hdL⟩ : ↥X) : Pr) := by
  have hfix : ((ρ ⟨d, hdL⟩ : ↥X) : Pr) =
      y * ((ρ ⟨d, hdL⟩ : ↥X) : Pr) * y⁻¹ :=
    h.equi ⟨d, hdL⟩ ⟨d, hdL⟩ (by show d = s * d * s⁻¹; rw [← hds]; group)
  exact eq_mul_inv_iff_mul_eq.mp hfix

theorem Sec4FDCover.exists_lift (h : Sec4FDCover L s X y ρ) {x : Pr} (hxX : x ∈ X)
    (hxy : x * y = y * x) :
    ∃ (d : G) (hdL : d ∈ L), d * s = s * d ∧ ((ρ ⟨d, hdL⟩ : ↥X) : Pr) = x := by
  have hσ : sec4IConj L h.s_norm * sec4IConj L h.s_norm = 1 := by
    ext l
    change ((sec4IConj L h.s_norm (sec4IConj L h.s_norm l) : ↥L) : G) = (l : G)
    rw [coe_sec4IConj, coe_sec4IConj]
    calc s * (s * (l : G) * s⁻¹) * s⁻¹
        = (s * s) * (l : G) * (s * s)⁻¹ := by group
      _ = (l : G) := by rw [h.s_sq]; group
  have hρσ : ∀ l : ↥L, ρ (sec4IConj L h.s_norm l) = MulAut.conjNormal y (ρ l) := by
    intro l
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact h.equi l (sec4IConj L h.s_norm l) (coe_sec4IConj L h.s_norm l)
  have hxfix : (⟨x, hxX⟩ : ↥X) ∈ fixSub (MulAut.conjNormal y) := by
    rw [mem_fixSub_iff]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hxy]
    group
  obtain ⟨dF, hdF⟩ := h.cover.fixHom_surjective hσ hρσ
    (⟨⟨x, hxX⟩, hxfix⟩ : ↥(fixSub (MulAut.conjNormal y)))
  have hdFval : ρ (dF : ↥L) = (⟨x, hxX⟩ : ↥X) := by
    have h1 := congrArg Subtype.val hdF
    rw [coe_fixHom] at h1
    simpa using h1
  have himg : ((ρ (dF : ↥L) : ↥X) : Pr) = x := by
    have h1 := congrArg Subtype.val hdFval
    simpa using h1
  have hdfix : (sec4IConj L h.s_norm) (dF : ↥L) = (dF : ↥L) := dF.2
  have hcoed : s * ((dF : ↥L) : G) * s⁻¹ = ((dF : ↥L) : G) := by
    have h1 := congrArg (fun t : ↥L => (t : G)) hdfix
    rwa [coe_sec4IConj] at h1
  have hds : ((dF : ↥L) : G) * s = s * ((dF : ↥L) : G) :=
    (mul_inv_eq_iff_eq_mul.mp hcoed).symm
  exact ⟨((dF : ↥L) : G), (dF : ↥L).2, hds, himg⟩

theorem Sec4FDCover.exists_lift_invol (h : Sec4FDCover L s X y ρ) {x : Pr} (hxX : x ∈ X)
    (hxy : x * y = y * x) (hxx : x * x = 1) :
    ∃ (v : G) (hvL : v ∈ L), v * s = s * v ∧ v * v = 1 ∧ ((ρ ⟨v, hvL⟩ : ↥X) : Pr) = x := by
  obtain ⟨d, hdL, hds, himg⟩ := h.exists_lift hxX hxy
  have haa : ρ (⟨d, hdL⟩ : ↥L) * ρ (⟨d, hdL⟩ : ↥L) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [himg, hxx]
  obtain ⟨hvv, hpow⟩ := h.cover.pow_card_ker haa
  have hvcomm : (((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L) : G) * s =
      s * (((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L) : G) := by
    rw [Subgroup.coe_pow]
    simpa only [Subgroup.coe_mk] using (Commute.pow_left hds (Nat.card ρ.ker)).eq
  have hvv' : (((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L) : G) *
      (((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L) : G) = 1 := by
    rw [← Subgroup.coe_mul, hvv, Subgroup.coe_one]
  have himg' : ((ρ ((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker) : ↥X) : Pr) = x :=
    (congrArg Subtype.val hpow).trans himg
  exact ⟨(((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L) : G),
    ((⟨d, hdL⟩ : ↥L) ^ Nat.card ρ.ker : ↥L).2, hvcomm, hvv', himg'⟩

theorem Sec4FDCover.mem_conjClassIn (h : Sec4FDCover L s X y ρ) {v v' : G} (hvL : v ∈ L)
    (hv'L : v' ∈ L) (hvs : v * s = s * v) (hv's : v' * s = s * v') (hvv : v * v = 1)
    (hv'v' : v' * v' = 1) {c : Pr} (hcX : c ∈ X) (hcy : c * y = y * c)
    (hc : ((ρ ⟨v', hv'L⟩ : ↥X) : Pr) = c * ((ρ ⟨v, hvL⟩ : ↥X) : Pr) * c⁻¹) :
    v' ∈ conjClassIn (L ⊓ centralizer ({s} : Set G)) v := by
  obtain ⟨g, hgL, hgs, hgc⟩ := h.exists_lift hcX hcy
  have hvvL : (⟨v, hvL⟩ : ↥L) * (⟨v, hvL⟩ : ↥L) = 1 := by
    apply Subtype.ext
    simpa using hvv
  have hv'v'L : (⟨v', hv'L⟩ : ↥L) * (⟨v', hv'L⟩ : ↥L) = 1 := by
    apply Subtype.ext
    simpa using hv'v'
  have hwwL : ((⟨g, hgL⟩ : ↥L) * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹) *
      ((⟨g, hgL⟩ : ↥L) * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹) = 1 := by
    calc ((⟨g, hgL⟩ : ↥L) * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹) *
          ((⟨g, hgL⟩ : ↥L) * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹)
        = (⟨g, hgL⟩ : ↥L) * (⟨v, hvL⟩ * ⟨v, hvL⟩) * ⟨g, hgL⟩⁻¹ := by group
      _ = 1 := by rw [hvvL]; group
  have hρw : ρ (⟨g, hgL⟩ * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹) = ρ (⟨v', hv'L⟩ : ↥L) := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgc, hc]
  have hw_eq : (⟨g, hgL⟩ * ⟨v, hvL⟩ * ⟨g, hgL⟩⁻¹ : ↥L) = (⟨v', hv'L⟩ : ↥L) :=
    h.cover.eq_of_mul_self_eq_one hwwL hv'v'L hρw
  refine ⟨g, Subgroup.mem_inf.mpr ⟨hgL, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hgs
  · simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using
      (congrArg Subtype.val hw_eq).symm

end CFSG.OddStandard.SmallF3.Omega
