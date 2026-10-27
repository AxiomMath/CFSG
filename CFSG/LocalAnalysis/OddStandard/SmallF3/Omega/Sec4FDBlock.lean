module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4FD_fixSp_dichotomy {t : OGroup Q} (h1 : Module.finrank (ZMod 3) (fixSp t) = 1)
    {u : OGroup Q} (huC : u * t = t * u) (huu : u * u = 1) :
    fixSp t ≤ commSp u ∨ ∀ x ∈ fixSp t, (u : V ≃ₗ[ZMod 3] V) x = x := by
  obtain ⟨x₀, hx₀0, hspan⟩ := finrank_eq_one_iff'.mp h1
  have hu_coe : (t : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V) =
      (u : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) huC.symm
  have hu_mem : (u : V ≃ₗ[ZMod 3] V) (x₀ : V) ∈ fixSp t := by
    rw [mem_fixSp_iff]
    have hx : (t : V ≃ₗ[ZMod 3] V) (x₀ : V) = (x₀ : V) := mem_fixSp_iff.mp x₀.2
    rw [← LinearEquiv.mul_apply, hu_coe, LinearEquiv.mul_apply, hx]
  obtain ⟨a, ha⟩ := hspan ⟨(u : V ≃ₗ[ZMod 3] V) (x₀ : V), hu_mem⟩
  have ha' : (u : V ≃ₗ[ZMod 3] V) (x₀ : V) = a • (x₀ : V) := by
    simpa using (congrArg Subtype.val ha).symm
  have hu2 : (u : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) huu
  have hux0 : (u : V ≃ₗ[ZMod 3] V) ((u : V ≃ₗ[ZMod 3] V) (x₀ : V)) = (x₀ : V) := by
    rw [← LinearEquiv.mul_apply, hu2, LinearEquiv.coe_one, id]
  have ha2 : a * a = 1 := by
    have hEq : (a * a) • (x₀ : V) = (1 : ZMod 3) • (x₀ : V) := by
      calc (a * a) • (x₀ : V) = a • (a • (x₀ : V)) := by rw [smul_smul]
        _ = a • ((u : V ≃ₗ[ZMod 3] V) (x₀ : V)) := by rw [← ha']
        _ = (u : V ≃ₗ[ZMod 3] V) (a • (x₀ : V)) := by rw [map_smul]
        _ = (u : V ≃ₗ[ZMod 3] V) ((u : V ≃ₗ[ZMod 3] V) (x₀ : V)) := by rw [← ha']
        _ = (x₀ : V) := hux0
        _ = (1 : ZMod 3) • (x₀ : V) := by rw [one_smul]
    have hsub : ((a * a) - 1) • (x₀ : V) = 0 := by
      rw [sub_smul, hEq, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (Subtype.ext h) hx₀0
  have hcases : a = 1 ∨ a = -1 := by
    have hfac : (a - 1) * (a + 1) = 0 := by
      rw [← show a * a - 1 = (a - 1) * (a + 1) by ring]
      exact sub_eq_zero.mpr ha2
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with ha1 | haneg
  · right
    intro x hx
    obtain ⟨c, hc⟩ := hspan ⟨x, hx⟩
    have hcx : x = c • (x₀ : V) := by simpa using (congrArg Subtype.val hc).symm
    calc (u : V ≃ₗ[ZMod 3] V) x = (u : V ≃ₗ[ZMod 3] V) (c • (x₀ : V)) := by rw [hcx]
      _ = c • (u : V ≃ₗ[ZMod 3] V) (x₀ : V) := by rw [map_smul]
      _ = c • (a • (x₀ : V)) := by rw [ha']
      _ = c • (x₀ : V) := by rw [ha1, one_smul]
      _ = x := hcx.symm
  · left
    intro x hx
    rw [mem_commSp_iff huu]
    obtain ⟨c, hc⟩ := hspan ⟨x, hx⟩
    have hcx : x = c • (x₀ : V) := by simpa using (congrArg Subtype.val hc).symm
    calc (u : V ≃ₗ[ZMod 3] V) x = (u : V ≃ₗ[ZMod 3] V) (c • (x₀ : V)) := by rw [hcx]
      _ = c • (u : V ≃ₗ[ZMod 3] V) (x₀ : V) := by rw [map_smul]
      _ = c • (a • (x₀ : V)) := by rw [ha']
      _ = c • ((-1 : ZMod 3) • (x₀ : V)) := by rw [haneg]
      _ = -(c • (x₀ : V)) := by rw [smul_smul, mul_neg, mul_one, neg_smul]
      _ = -x := by rw [hcx]

theorem sec4FD_exists_blockInr (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {u : OGroup Q} (huC : u * t = t * u) (hF : ∀ x ∈ fixSp t, (u : V ≃ₗ[ZMod 3] V) x = x) :
    ∃ b : OGroup (Q.restrict (commSp t)), u = blockInr htt b := by
  have hu_mem : u ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huC
  rw [← range_blockHom hQ htt] at hu_mem
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hu_mem
  have hp1 : p.1 = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    have happ := blockHom_apply htt p w 0
    have hw : ((blockHom htt p : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) = (w : V) := by
      rw [hp]
      exact hF (w : V) w.2
    rw [Submodule.coe_zero, add_zero, hw, map_zero, Submodule.coe_zero, add_zero] at happ
    simpa using happ.symm
  refine ⟨p.2, ?_⟩
  have hp_eq : p = (1, p.2) := by
    rw [Prod.ext_iff]
    exact ⟨hp1, rfl⟩
  rw [← hp, hp_eq]
  exact (blockInr_apply htt p.2).symm

theorem sec4FD_exists_block_neg (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {u : OGroup Q} (huC : u * t = t * u) (huu : u * u = 1) (hF : fixSp t ≤ commSp u) :
    ∃ b : OGroup (Q.restrict (commSp t)), b * b = 1 ∧ u = (piOrth Q * t) * blockInr htt b := by
  have hπt_center : t * piOrth Q = piOrth Q * t :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
  have hπu_center : u * piOrth Q = piOrth Q * u :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) u
  let u' : OGroup Q := (piOrth Q * t) * u
  have hu' : u' = (piOrth Q * t) * u := rfl
  have hu't : u' * t = t * u' := by
    have hpt : (piOrth Q * t) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (piOrth Q * t) * t = piOrth Q := by rw [mul_assoc, htt, mul_one]
        _ = t * (piOrth Q * t) := by
              rw [← mul_assoc, hπt_center, mul_assoc, htt, mul_one]
    have hum : u ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr huC
    rw [hu']
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mul_mem _ hpt hum)
  have hu'F : ∀ x ∈ fixSp t, (u' : V ≃ₗ[ZMod 3] V) x = x := by
    intro x hx
    have hxt : (t : V ≃ₗ[ZMod 3] V) x = x := mem_fixSp_iff.mp hx
    have hxu : (u : V ≃ₗ[ZMod 3] V) x = -x := (mem_commSp_iff huu).mp (hF hx)
    show (((piOrth Q * t) * u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hxu, map_neg, hxt, map_neg, coe_piOrth_apply, neg_neg]
  obtain ⟨b, hb⟩ := sec4FD_exists_blockInr hQ htt hu't hu'F
  have hu'sq : u' * u' = 1 := by
    have hπtu : (piOrth Q * t) * u = u * (piOrth Q * t) := by
      calc (piOrth Q * t) * u = piOrth Q * (t * u) := by rw [mul_assoc]
        _ = piOrth Q * (u * t) := by rw [huC]
        _ = (piOrth Q * u) * t := by rw [mul_assoc]
        _ = (u * piOrth Q) * t := by rw [hπu_center.symm]
        _ = u * (piOrth Q * t) := by rw [mul_assoc]
    rw [hu']
    calc ((piOrth Q * t) * u) * ((piOrth Q * t) * u)
        = (piOrth Q * t) * (u * (piOrth Q * t)) * u := by group
      _ = (piOrth Q * t) * ((piOrth Q * t) * u) * u := by rw [hπtu.symm]
      _ = ((piOrth Q * t) * (piOrth Q * t)) * (u * u) := by group
      _ = 1 := by rw [piOrth_mul_mul_self htt, huu]; simp
  have hb_sq : b * b = 1 := by
    have hmap : blockInr htt (b * b) = 1 := by rw [map_mul, ← hb, hu'sq]
    exact blockInr_injective htt (hmap.trans (map_one (blockInr htt)).symm)
  refine ⟨b, hb_sq, ?_⟩
  rw [← hb, hu']
  rw [← mul_assoc, piOrth_mul_mul_self htt, one_mul]

theorem sec4FD_block_neg_sq (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    ((piOrth Q * t) * blockInr htt b) * ((piOrth Q * t) * blockInr htt b) = 1 := by
  have hc_cent : blockInr htt b ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    blockInr_mem_centralizer hQ htt b
  have hct : blockInr htt b * t = t * blockInr htt b :=
    Subgroup.mem_centralizer_singleton_iff.mp hc_cent
  have hπc : blockInr htt b * piOrth Q = piOrth Q * blockInr htt b :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (blockInr htt b)
  have hcomm : (piOrth Q * t) * blockInr htt b = blockInr htt b * (piOrth Q * t) := by
    calc (piOrth Q * t) * blockInr htt b = piOrth Q * (t * blockInr htt b) := by
          rw [mul_assoc]
      _ = piOrth Q * (blockInr htt b * t) := by rw [hct]
      _ = (piOrth Q * blockInr htt b) * t := by rw [mul_assoc]
      _ = (blockInr htt b * piOrth Q) * t := by rw [hπc.symm]
      _ = blockInr htt b * (piOrth Q * t) := by rw [mul_assoc]
  have hc_sq : blockInr htt b * blockInr htt b = 1 := by rw [← map_mul, hbb, map_one]
  calc ((piOrth Q * t) * blockInr htt b) * ((piOrth Q * t) * blockInr htt b)
      = (piOrth Q * t) * (blockInr htt b * (piOrth Q * t)) * blockInr htt b := by group
    _ = (piOrth Q * t) * ((piOrth Q * t) * blockInr htt b) * blockInr htt b := by
          rw [hcomm.symm]
    _ = ((piOrth Q * t) * (piOrth Q * t)) * (blockInr htt b * blockInr htt b) := by group
    _ = 1 := by rw [piOrth_mul_mul_self htt, hc_sq]; simp

theorem sec4FD_invType_mul_block (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1))
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    invType ((piOrth Q * t) * blockInr htt b) = (1 + invDim b, invSign b * (-1) ^ invDim b) := by
  have hg : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
  have hh : blockInr htt b * blockInr htt b = 1 := by rw [← map_mul, hbb, map_one]
  have horth : ∀ v ∈ commSp (piOrth Q * t), ∀ w ∈ commSp (blockInr htt b),
      QuadraticMap.polar Q v w = 0 := by
    intro v hv w hw
    rw [commSp_piOrth_mul htt] at hv
    rw [commSp_blockInr htt b] at hw
    obtain ⟨x, _hx, rfl⟩ := Submodule.mem_map.mp hw
    simpa using polar_fixSp_commSp htt hv x.2
  have hn : Odd (Module.finrank (ZMod 3) V) := by rw [hdim]; decide
  have ht_fst : invDim t = 6 := by
    have := congrArg Prod.fst ht6
    simpa only [invType] using this
  have ht_snd : invSign t = 1 := by
    have := congrArg Prod.snd ht6
    simpa only [invType] using this
  have htype_pt : invType (piOrth Q * t) = (1, 1) := by
    rw [invType_piOrth_mul_of_odd hQ htt hn hσ, ht_fst, ht_snd, hdim]
  have hpt1 : invDim (piOrth Q * t) = 1 := by
    have := congrArg Prod.fst htype_pt
    simpa only [invType] using this
  have hpt2 : invSign (piOrth Q * t) = 1 := by
    have := congrArg Prod.snd htype_pt
    simpa only [invType] using this
  have htype_b : invType (blockInr htt b) = invType b := invType_blockInr hQ htt hbb
  have hb1 : invDim (blockInr htt b) = invDim b := by
    have := congrArg Prod.fst htype_b
    simpa only [invType] using this
  have hb2 : invSign (blockInr htt b) = invSign b := by
    have := congrArg Prod.snd htype_b
    simpa only [invType] using this
  rw [invType_mul_of_orth hQ hg hh horth, hpt1, hpt2, hb1, hb2]
  simp

theorem sec4FD_invType_pi_block (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1)
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    invType (piOrth Q * blockInr htt b) = (7 - invDim b, invSign b) := by
  have hh : blockInr htt b * blockInr htt b = 1 := by rw [← map_mul, hbb, map_one]
  have hn : Odd (Module.finrank (ZMod 3) V) := by rw [hdim]; decide
  have hb1 : invDim (blockInr htt b) = invDim b := by
    have := congrArg Prod.fst (invType_blockInr hQ htt hbb)
    simpa only [invType] using this
  have hb2 : invSign (blockInr htt b) = invSign b := by
    have := congrArg Prod.snd (invType_blockInr hQ htt hbb)
    simpa only [invType] using this
  rw [invType_piOrth_mul_of_odd hQ hh hn hσ, hdim, hb1, hb2]

theorem sec4FD_invDim_mul_blockInr (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    invDim (t * blockInr htt b) = Module.finrank (ZMod 3) (commSp t) - invDim b := by
  have hQU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hb_inv : (piOrth (Q.restrict (commSp t)) * b) * (piOrth (Q.restrict (commSp t)) * b) = 1 :=
    piOrth_mul_mul_self hbb
  have htype := invType_blockInr hQ htt hb_inv
  have h1a : invDim (blockInr htt (piOrth (Q.restrict (commSp t)) * b)) =
      invDim (piOrth (Q.restrict (commSp t)) * b) := by
    have := congrArg Prod.fst htype
    simpa only [invType] using this
  have h1b : invDim (piOrth (Q.restrict (commSp t)) * b) =
      Module.finrank (ZMod 3) (commSp t) - invDim b := by
    have := congrArg Prod.fst (invType_piOrth_mul hQU hbb)
    simpa only [invType] using this
  have ht_eq : t * blockInr htt b = blockInr htt (piOrth (Q.restrict (commSp t)) * b) :=
    (congrArg (fun x => x * blockInr htt b) (blockInr_piOrth htt).symm).trans
      (map_mul (blockInr htt) (piOrth (Q.restrict (commSp t))) b).symm
  rw [ht_eq, h1a, h1b]

end CFSG.OddStandard.SmallF3.Omega
