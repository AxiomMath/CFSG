module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDComp5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma blockInr_commSp_apply {s : OGroup Q} (hs : s * s = 1)
    (b : OGroup (Q.restrict (commSp s))) (x : commSp s) :
    (((blockInr hs b : OGroup Q) : V ≃ₗ[ZMod 3] V) (x : V)) =
      (((b : commSp s ≃ₗ[ZMod 3] commSp s) x : commSp s) : V) := by
  have h := blockHom_apply hs (1, b) (0 : fixSp s) x
  rw [blockInr_apply]
  simpa using h

private lemma piOrth_mul_t_eq_blockHom {t : OGroup Q} (htt : t * t = 1) :
    (piOrth Q * t : OGroup Q) =
      blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
  have h1 := blockHom_piOrth_piOrth htt
  have h2 := blockHom_one_piOrth htt
  calc piOrth Q * t
      = blockHom htt (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          blockHom htt (1, piOrth (Q.restrict (commSp t))) := by rw [h1, h2]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          (1, piOrth (Q.restrict (commSp t)))) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
          rw [Prod.mk_mul_mk, mul_one, piOrth_mul_self]

private lemma piOrth_mul_t_mul_blockInr {t : OGroup Q} (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) :
    (piOrth Q * t) * blockInr htt b =
      blockHom htt (piOrth (Q.restrict (fixSp t)), b) := by
  calc (piOrth Q * t) * blockInr htt b
      = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) * blockHom htt (1, b) := by
          rw [piOrth_mul_t_eq_blockHom htt, blockInr_apply]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), 1) * (1, b)) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), b) := by
          rw [Prod.mk_mul_mk, mul_one, one_mul]

private lemma piOrth_mul_t_mul_blockInr_commute (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) (b : OGroup (Q.restrict (commSp t))) :
    ((piOrth Q * t) * blockInr htt b) * t = t * ((piOrth Q * t) * blockInr htt b) := by
  have hpit : Commute (piOrth Q) t :=
    (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t).symm
  have hbt : Commute (blockInr htt b) t :=
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt b)
  exact ((hpit.mul_left (Commute.refl t)).mul_left hbt).eq

private lemma mul_blockInr_comm (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {b b₅ : OGroup (Q.restrict (commSp t))} (hcomm : b * b₅ = b₅ * b) :
    ((piOrth Q * t) * blockInr htt b) * blockInr htt b₅ =
      blockInr htt b₅ * ((piOrth Q * t) * blockInr htt b) := by
  have hbb : Commute (blockInr htt b) (blockInr htt b₅) := by
    show blockInr htt b * blockInr htt b₅ = blockInr htt b₅ * blockInr htt b
    rw [← map_mul, ← map_mul, hcomm]
  have hpi5 : Commute (piOrth Q) (blockInr htt b₅) :=
    (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (blockInr htt b₅)).symm
  have hb5t : Commute t (blockInr htt b₅) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt b₅)).symm
  exact ((hpi5.mul_left hb5t).mul_left hbb).eq

private lemma u_apply_on_commSp {t : OGroup Q} (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) {x : V} (hx : x ∈ commSp t) :
    ((((piOrth Q * t) * blockInr htt b : OGroup Q) : V ≃ₗ[ZMod 3] V) x) =
      (((b : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hx⟩ : commSp t) : V) := by
  rw [piOrth_mul_t_mul_blockInr htt b]
  have h := blockHom_apply htt (piOrth (Q.restrict (fixSp t)), b) (0 : fixSp t) ⟨x, hx⟩
  have h0 : (((0 : fixSp t) : V) + ((⟨x, hx⟩ : commSp t) : V)) = x := by simp
  rw [h0] at h
  simpa using h

private lemma blockInr_neg_on_commSp {t : OGroup Q} (htt : t * t = 1)
    {b₅ : OGroup (Q.restrict (commSp t))} {x : V} (hx : x ∈ commSp t)
    (hxneg : ((blockInr htt b₅ : OGroup Q) : V ≃ₗ[ZMod 3] V) x = -x) :
    (b₅ : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hx⟩ = -⟨x, hx⟩ := by
  apply Subtype.ext
  have h1 := blockInr_commSp_apply htt b₅ ⟨x, hx⟩
  rw [← h1]
  simpa using hxneg

private lemma centralizer_comm_blockInr (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) {b b₅ : OGroup (Q.restrict (commSp t))}
    (hb₅ : b₅ = piOrth (Q.restrict (commSp t)) * b ∨ b₅ = b) :
    ∀ g : OGroup Q, g * t = t * g →
      g * ((piOrth Q * t) * blockInr htt b) = ((piOrth Q * t) * blockInr htt b) * g →
      g * blockInr htt b₅ = blockInr htt b₅ * g := by
  intro g hgt hgu
  have hgR : g ∈ (blockHom htt).range := by
    rw [range_blockHom hQ htt]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgt
  obtain ⟨p, rfl⟩ := hgR
  have hu : blockHom htt p * blockHom htt (piOrth (Q.restrict (fixSp t)), b) =
      blockHom htt (piOrth (Q.restrict (fixSp t)), b) * blockHom htt p := by
    rw [← piOrth_mul_t_mul_blockInr htt b]
    exact hgu
  have h2 : p.2 * b = b * p.2 := by
    have heq : blockHom htt ((p.1, p.2) * (piOrth (Q.restrict (fixSp t)), b)) =
        blockHom htt ((piOrth (Q.restrict (fixSp t)), b) * (p.1, p.2)) := by
      rw [map_mul, map_mul]
      exact hu
    simpa using congrArg Prod.snd (blockHom_injective htt heq)
  have hcen2 : p.2 * piOrth (Q.restrict (commSp t)) =
      piOrth (Q.restrict (commSp t)) * p.2 :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q.restrict (commSp t))) p.2
  have h25 : p.2 * b₅ = b₅ * p.2 := by
    rcases hb₅ with h | h
    · calc p.2 * b₅ = p.2 * (piOrth (Q.restrict (commSp t)) * b) := by rw [h]
        _ = (p.2 * piOrth (Q.restrict (commSp t))) * b := by rw [mul_assoc]
        _ = (piOrth (Q.restrict (commSp t)) * p.2) * b := by rw [hcen2]
        _ = piOrth (Q.restrict (commSp t)) * (p.2 * b) := by rw [mul_assoc]
        _ = piOrth (Q.restrict (commSp t)) * (b * p.2) := by rw [h2]
        _ = (piOrth (Q.restrict (commSp t)) * b) * p.2 := by rw [mul_assoc]
        _ = b₅ * p.2 := by rw [h]
    · rw [h]
      exact h2
  calc blockHom htt p * blockInr htt b₅
      = blockHom htt p * blockHom htt (1, b₅) := by rw [blockInr_apply]
    _ = blockHom htt ((p.1, p.2) * (1, b₅)) := (map_mul _ _ _).symm
    _ = blockHom htt ((1, b₅) * (p.1, p.2)) := by
        congr 1
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul, h25]
    _ = blockHom htt (1, b₅) * blockHom htt p := map_mul _ _ _
    _ = blockInr htt b₅ * blockHom htt p := by rw [blockInr_apply]

theorem sec4FD_exists_two (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    ∃ u : OGroup Q, u ∈ Sec4FDDt hQ t ∧ u * u = 1 ∧ u ≠ 1 ∧ invType u = (2, -1) ∧
      ∃ K : Subgroup (OGroup Q),
        IsComponentIn K (Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q))) ∧
          oddCore ↥K = ⊥ ∧ LieModel ↥K .PSp 2 3 1 := by
  have hQU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hfinU : Module.finrank (ZMod 3) (commSp t) = 6 := by
    simpa only [invType, invDim] using congrArg Prod.fst ht6
  have hsignU : quadSign (Q.restrict (commSp t)) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd ht6
  obtain ⟨b, hbb, hbtype⟩ := (exists_involution_of_type hQU 1 1).mpr
    ⟨by rw [hfinU]; norm_num, by intro _; rfl, by rw [hfinU, hsignU]; intro _; rfl⟩
  have hbdim : invDim b = 1 := by
    simpa only [invType] using congrArg Prod.fst hbtype
  have hbsign : invSign b = 1 := by
    simpa only [invType] using congrArg Prod.snd hbtype
  set b₅ : OGroup (Q.restrict (commSp t)) := piOrth (Q.restrict (commSp t)) * b with hb₅
  have hb₅b₅ : b₅ * b₅ = 1 := by
    rw [hb₅]
    exact piOrth_mul_mul_self hbb
  have hcomm : b * b₅ = b₅ * b := by
    have hcen : b * piOrth (Q.restrict (commSp t)) =
        piOrth (Q.restrict (commSp t)) * b :=
      Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q.restrict (commSp t))) b
    calc b * b₅ = b * (piOrth (Q.restrict (commSp t)) * b) := by rw [hb₅]
      _ = (b * piOrth (Q.restrict (commSp t))) * b := by rw [mul_assoc]
      _ = (piOrth (Q.restrict (commSp t)) * b) * b := by rw [hcen]
      _ = b₅ * b := by rw [hb₅]
  have hb₅fin : Module.finrank (ZMod 3) (commSp b₅) = 5 := by
    have h : Module.finrank (ZMod 3) (commSp (piOrth (Q.restrict (commSp t)) * b)) =
        Module.finrank (ZMod 3) (commSp t) - Module.finrank (ZMod 3) (commSp b) := by
      simpa only [invType, invDim] using congrArg Prod.fst (invType_piOrth_mul hQU hbb)
    have hbfin : Module.finrank (ZMod 3) (commSp b) = 1 := by
      simpa only [invDim] using hbdim
    rw [hb₅, h, hfinU, hbfin] <;> norm_num
  set u : OGroup Q := (piOrth Q * t) * blockInr htt b with hu
  have huu : u * u = 1 := by
    rw [hu]
    exact sec4FD_block_neg_sq hQ htt hbb
  have htype : invType u = (2, -1) := by
    rw [hu, sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb, hbdim, hbsign] <;> simp
  have hdimu : invDim u = 2 := by
    simpa only [invType] using congrArg Prod.fst htype
  have hsignu : invSign u = -1 := by
    simpa only [invType] using congrArg Prod.snd htype
  have hune : u ≠ 1 := by
    intro hone
    have h0 := htype
    rw [hone, invType_one] at h0
    exact absurd (congrArg Prod.fst h0) (by norm_num)
  have hu_comm : u * t = t * u := by
    rw [hu]
    exact piOrth_mul_t_mul_blockInr_commute hQ htt b
  have hu_omega : u ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ huu, hdimu, hsignu]
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    have hpow : (-1 : ℤˣ) ^ (2 / 2) = -1 := by
      rw [neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)]
      decide
    exact hpow.symm
  have humem : u ∈ Sec4FDDt hQ t := (mem_sec4FDDt_iff hQ).mpr ⟨hu_omega, hu_comm⟩
  set s' : OGroup Q := blockInr htt b₅ with hs'
  have hs's' : s' * s' = 1 := by
    rw [hs', ← map_mul, hb₅b₅, map_one]
  have hts' : t * s' = s' * t := by
    rw [hs']
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (blockInr_mem_centralizer hQ htt b₅)).symm
  have hneg : commSp s' ≤ commSp t := by
    rw [hs', commSp_blockInr]
    rintro x ⟨y, _hy, rfl⟩
    exact y.2
  have hfin5 : Module.finrank (ZMod 3) (commSp s') = 5 := by
    have h : Module.finrank (ZMod 3) (commSp (blockInr htt b₅)) =
        Module.finrank (ZMod 3) (commSp b₅) := by
      simpa only [invType, invDim] using congrArg Prod.fst (invType_blockInr hQ htt hb₅b₅)
    rw [hs', h, hb₅fin]
  have hus' : u * s' = s' * u := by
    rw [hu, hs']
    exact mul_blockInr_comm hQ htt hcomm
  have hsign : (∀ x ∈ commSp s', ((u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x) ∨
      (∀ x ∈ commSp s', ((u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = -x) := by
    left
    intro x hx
    have hxU : x ∈ commSp t := hneg hx
    have hxneg : (((blockInr htt b₅ : OGroup Q)) : V ≃ₗ[ZMod 3] V) x = -x := by
      have h := (mem_commSp_iff hs's').mp hx
      rw [hs'] at h
      exact h
    have hb₅x : (b₅ : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩ = -⟨x, hxU⟩ :=
      blockInr_neg_on_commSp htt hxU hxneg
    have hbx : (b : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩ = ⟨x, hxU⟩ := by
      have h2 : (b₅ : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩ =
          (((piOrth (Q.restrict (commSp t)) * b : OGroup (Q.restrict (commSp t))) :
            commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩) := by rw [hb₅]
      rw [h2] at hb₅x
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_piOrth_apply] at hb₅x
      exact neg_injective hb₅x
    rw [hu, u_apply_on_commSp htt b hxU, hbx]
  have hcen : ∀ g : OGroup Q, g * t = t * g → g * u = u * g → g * s' = s' * g := by
    intro g hgt hgu
    rw [hu] at hgu
    rw [hs']
    exact centralizer_comm_blockInr hQ htt (Or.inl hb₅) g hgt hgu
  exact ⟨u, humem, huu, hune, htype,
    sec4FD_component_omega5 hQ htt humem hs's' hts' hneg hfin5 hus' hsign hcen⟩

theorem sec4FD_exists_six (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    ∃ u : OGroup Q, u ∈ Sec4FDDt hQ t ∧ u * u = 1 ∧ u ≠ 1 ∧ invType u = (6, -1) ∧
      ∃ K : Subgroup (OGroup Q),
        IsComponentIn K (Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q))) ∧
          oddCore ↥K = ⊥ ∧ LieModel ↥K .PSp 2 3 1 := by
  have hQU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hfinU : Module.finrank (ZMod 3) (commSp t) = 6 := by
    simpa only [invType, invDim] using congrArg Prod.fst ht6
  have hsignU : quadSign (Q.restrict (commSp t)) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd ht6
  obtain ⟨b, hbb, hbtype⟩ := (exists_involution_of_type hQU 5 1).mpr
    ⟨by rw [hfinU]; norm_num, by intro _; rfl, by rw [hfinU, hsignU]; intro _; rfl⟩
  have hbdim : invDim b = 5 := by
    simpa only [invType] using congrArg Prod.fst hbtype
  have hbsign : invSign b = 1 := by
    simpa only [invType] using congrArg Prod.snd hbtype
  set b₅ : OGroup (Q.restrict (commSp t)) := b with hb₅
  have hb₅b₅ : b₅ * b₅ = 1 := by
    rw [hb₅]
    exact hbb
  have hcomm : b * b₅ = b₅ * b := by rw [hb₅]
  set u : OGroup Q := (piOrth Q * t) * blockInr htt b with hu
  have huu : u * u = 1 := by
    rw [hu]
    exact sec4FD_block_neg_sq hQ htt hbb
  have htype : invType u = (6, -1) := by
    have hpow : (-1 : ℤˣ) ^ 5 = -1 := by
      rw [neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)]
      decide
    rw [hu, sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb, hbdim, hbsign, hpow] <;> simp
  have hdimu : invDim u = 6 := by
    simpa only [invType] using congrArg Prod.fst htype
  have hsignu : invSign u = -1 := by
    simpa only [invType] using congrArg Prod.snd htype
  have hune : u ≠ 1 := by
    intro hone
    have h0 := htype
    rw [hone, invType_one] at h0
    exact absurd (congrArg Prod.fst h0) (by norm_num)
  have hu_comm : u * t = t * u := by
    rw [hu]
    exact piOrth_mul_t_mul_blockInr_commute hQ htt b
  have hu_omega : u ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ huu, hdimu, hsignu]
    refine ⟨⟨3, by norm_num⟩, ?_⟩
    have hpow : (-1 : ℤˣ) ^ (6 / 2) = -1 := by
      rw [neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)]
      decide
    exact hpow.symm
  have humem : u ∈ Sec4FDDt hQ t := (mem_sec4FDDt_iff hQ).mpr ⟨hu_omega, hu_comm⟩
  set s' : OGroup Q := blockInr htt b₅ with hs'
  have hs's' : s' * s' = 1 := by
    rw [hs', ← map_mul, hb₅b₅, map_one]
  have hts' : t * s' = s' * t := by
    rw [hs']
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (blockInr_mem_centralizer hQ htt b₅)).symm
  have hneg : commSp s' ≤ commSp t := by
    rw [hs', commSp_blockInr]
    rintro x ⟨y, _hy, rfl⟩
    exact y.2
  have hfin5 : Module.finrank (ZMod 3) (commSp s') = 5 := by
    have h : Module.finrank (ZMod 3) (commSp (blockInr htt b₅)) =
        Module.finrank (ZMod 3) (commSp b₅) := by
      simpa only [invType, invDim] using congrArg Prod.fst (invType_blockInr hQ htt hb₅b₅)
    have hb₅fin : Module.finrank (ZMod 3) (commSp b₅) = 5 := by
      rw [hb₅]
      simpa only [invDim] using hbdim
    rw [hs', h, hb₅fin]
  have hus' : u * s' = s' * u := by
    rw [hu, hs']
    exact mul_blockInr_comm hQ htt hcomm
  have hsign : (∀ x ∈ commSp s', ((u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x) ∨
      (∀ x ∈ commSp s', ((u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = -x) := by
    right
    intro x hx
    have hxU : x ∈ commSp t := hneg hx
    have hxneg : (((blockInr htt b₅ : OGroup Q)) : V ≃ₗ[ZMod 3] V) x = -x := by
      have h := (mem_commSp_iff hs's').mp hx
      rw [hs'] at h
      exact h
    have hb₅x : (b₅ : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩ = -⟨x, hxU⟩ :=
      blockInr_neg_on_commSp htt hxU hxneg
    have hbx : (b : commSp t ≃ₗ[ZMod 3] commSp t) ⟨x, hxU⟩ = -⟨x, hxU⟩ := by
      rw [hb₅] at hb₅x
      exact hb₅x
    rw [hu, u_apply_on_commSp htt b hxU, hbx]
    simp
  have hcen : ∀ g : OGroup Q, g * t = t * g → g * u = u * g → g * s' = s' * g := by
    intro g hgt hgu
    rw [hu] at hgu
    rw [hs']
    exact centralizer_comm_blockInr hQ htt (Or.inr hb₅) g hgt hgu
  exact ⟨u, humem, huu, hune, htype,
    sec4FD_component_omega5 hQ htt humem hs's' hts' hneg hfin5 hus' hsign hcen⟩

end CFSG.OddStandard.SmallF3.Omega
