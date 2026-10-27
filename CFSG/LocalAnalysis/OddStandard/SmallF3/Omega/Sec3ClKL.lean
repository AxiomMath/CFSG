module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClSmall
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma conj_eq_of_mem_fixSub (hQ : Q.Nondegenerate) {x : OGroup Q} {c : omegaGroup hQ}
    (hc : omegaToProj hQ c ∈ fixSub (projAut hQ x)) :
    (c : OGroup Q) * x * (c : OGroup Q)⁻¹ = x ∨
      (c : OGroup Q) * x * (c : OGroup Q)⁻¹ = piOrth Q * x := by
  have hcomm := (mem_fixSub_projAut_iff hQ x (omegaToProj hQ c)).mp hc
  have h1 : toProj Q ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) = toProj Q x := by
    rw [map_mul, map_mul, map_inv, ← coe_omegaToProj]
    rw [← hcomm]
    group
  have h2 : ((c : OGroup Q) * x * (c : OGroup Q)⁻¹)⁻¹ * x ∈ piGroup Q :=
    QuotientGroup.eq.mp h1
  rcases mem_piGroup_iff.mp h2 with h3 | h3
  · left
    exact inv_mul_eq_one.mp h3
  · right
    have hb : x = ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) * piOrth Q := by
      rw [← h3, mul_inv_cancel_left]
    calc (c : OGroup Q) * x * (c : OGroup Q)⁻¹
        = ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) * 1 := (mul_one _).symm
      _ = ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) * (piOrth Q * piOrth Q) := by
            rw [piOrth_mul_self]
      _ = (((c : OGroup Q) * x * (c : OGroup Q)⁻¹) * piOrth Q) * piOrth Q := by group
      _ = (piOrth Q * ((c : OGroup Q) * x * (c : OGroup Q)⁻¹)) * piOrth Q := by
            rw [mul_piOrth_comm ((c : OGroup Q) * x * (c : OGroup Q)⁻¹)]
      _ = piOrth Q * (((c : OGroup Q) * x * (c : OGroup Q)⁻¹) * piOrth Q) := by group
      _ = piOrth Q * x := by rw [← hb]

private lemma conj_mem_cOmega_of_mem_fix (hQ : Q.Nondegenerate) {x : OGroup Q}
    {c g : omegaGroup hQ} (hc : omegaToProj hQ c ∈ fixSub (projAut hQ x))
    (hg : g ∈ cOmega hQ x) : c * g * c⁻¹ ∈ cOmega hQ x := by
  have hcx := conj_eq_of_mem_fixSub hQ hc
  rw [mem_cOmega_iff]
  have hgx := (mem_cOmega_iff hQ x g).mp hg
  change ((c : OGroup Q) * (g : OGroup Q) * (c : OGroup Q)⁻¹) * x =
    x * ((c : OGroup Q) * (g : OGroup Q) * (c : OGroup Q)⁻¹)
  rcases hcx with h | h
  · exact commute_conj_of_central (z := 1) (Subgroup.one_mem _) (one_mul 1) hgx
      (by rw [h, one_mul])
  · exact commute_conj_of_central (z := piOrth Q) piOrth_mem_center piOrth_mul_self hgx h

private lemma mul_self_mem_cOmega_of_mem_fix (hQ : Q.Nondegenerate) {x : OGroup Q}
    {c : omegaGroup hQ} (hc : omegaToProj hQ c ∈ fixSub (projAut hQ x)) :
    c * c ∈ cOmega hQ x := by
  have hcx := conj_eq_of_mem_fixSub hQ hc
  rw [mem_cOmega_iff]
  change ((c : OGroup Q) * (c : OGroup Q)) * x = x * ((c : OGroup Q) * (c : OGroup Q))
  have key : ((c : OGroup Q) * (c : OGroup Q)) * x *
      ((c : OGroup Q) * (c : OGroup Q))⁻¹ = x := by
    rcases hcx with h | h
    · calc ((c : OGroup Q) * (c : OGroup Q)) * x *
            ((c : OGroup Q) * (c : OGroup Q))⁻¹
          = (c : OGroup Q) * ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) *
              (c : OGroup Q)⁻¹ := by group
        _ = (c : OGroup Q) * x * (c : OGroup Q)⁻¹ := by rw [h, h]
        _ = x := h
    · calc ((c : OGroup Q) * (c : OGroup Q)) * x *
            ((c : OGroup Q) * (c : OGroup Q))⁻¹
          = (c : OGroup Q) * ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) *
              (c : OGroup Q)⁻¹ := by group
        _ = (c : OGroup Q) * (piOrth Q * x) * (c : OGroup Q)⁻¹ := by rw [h]
        _ = (c : OGroup Q) * piOrth Q * x * (c : OGroup Q)⁻¹ := by group
        _ = piOrth Q * (c : OGroup Q) * x * (c : OGroup Q)⁻¹ := by
              rw [mul_piOrth_comm (c : OGroup Q)]
        _ = piOrth Q * ((c : OGroup Q) * x * (c : OGroup Q)⁻¹) := by group
        _ = piOrth Q * (piOrth Q * x) := by rw [h]
        _ = x := by rw [← mul_assoc, piOrth_mul_self, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp key

private lemma blockOmega_conj_mem (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {a b : OGroup Q} (ha : a ∈ Subgroup.centralizer ({s} : Set (OGroup Q)))
    (hb : b ∈ blockOmega hQ hs) : a * b * a⁻¹ ∈ blockOmega hQ hs := by
  have hle : blockOmega hQ hs ≤ Subgroup.centralizer ({s} : Set (OGroup Q)) := by
    rw [blockOmega, Subgroup.map_le_iff_le_comap]
    intro p _
    rw [Subgroup.mem_comap, ← range_blockHom hQ hs]
    exact MonoidHom.mem_range.mpr ⟨p, rfl⟩
  have hnorm := blockOmega_normal_in_centralizer hQ hs
  have hx : (⟨b, hle hb⟩ : ↥(Subgroup.centralizer ({s} : Set (OGroup Q)))) ∈
      (blockOmega hQ hs).subgroupOf (Subgroup.centralizer ({s} : Set (OGroup Q))) :=
    Subgroup.mem_subgroupOf.mpr hb
  have hconj := hnorm.conj_mem ⟨b, hle hb⟩ hx ⟨a, ha⟩
  simpa using (Subgroup.mem_subgroupOf.mp hconj)

theorem cl_commutator_fixSub_projAut_le (hQ : Q.Nondegenerate) (x : OGroup Q) :
    ⁅fixSub (projAut hQ x), fixSub (projAut hQ x)⁆ ≤ (cOmega hQ x).map (omegaToProj hQ) := by
  refine cl_commutator_le_of_mul_self_mem ?hn ?hsq
  · intro h hh n hn
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨g, hg, rfl⟩ := hn
    obtain ⟨c, hc⟩ := omegaToProj_surjective hQ h
    rw [← hc] at hh ⊢
    exact ⟨c * g * c⁻¹, conj_mem_cOmega_of_mem_fix hQ hh hg, by
      rw [map_mul, map_mul, map_inv]⟩
  · intro h hh
    rw [Subgroup.mem_map]
    obtain ⟨c, hc⟩ := omegaToProj_surjective hQ h
    rw [← hc] at hh ⊢
    exact ⟨c * c, mul_self_mem_cOmega_of_mem_fix hQ hh, by rw [map_mul]⟩

theorem cl_commutator_cOmega_le (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    ⁅cOmega hQ s, cOmega hQ s⁆ ≤ (blockOmega hQ hs).comap (omegaGroup hQ).subtype := by
  refine cl_commutator_le_of_mul_self_mem ?hn ?hsq
  · intro h hh n hn
    rw [Subgroup.mem_comap] at hn ⊢
    simpa using blockOmega_conj_mem hQ hs (Subgroup.mem_comap.mp hh) hn
  · intro h hh
    rw [Subgroup.mem_comap]
    simpa using mul_self_mem_blockOmega hQ hs (Subgroup.mem_comap.mp hh)

@[expose] noncomputable def clFixHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    omegaGroup (nondegenerate_restrict_fixSp hQ hs) →* omegaProj hQ :=
  (omegaToProj hQ).comp ((((blockHom hs).comp (MonoidHom.inl _ _)).comp
    (omegaGroup (nondegenerate_restrict_fixSp hQ hs)).subtype).codRestrict (omegaGroup hQ)
    (fun a => cl_blockHom_left_mem_omegaGroup hQ hs a.2))

@[expose] noncomputable def clCommHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    omegaGroup (nondegenerate_restrict_commSp hQ hs) →* omegaProj hQ :=
  (omegaToProj hQ).comp ((((blockHom hs).comp (MonoidHom.inr _ _)).comp
    (omegaGroup (nondegenerate_restrict_commSp hQ hs)).subtype).codRestrict (omegaGroup hQ)
    (fun b => cl_blockHom_right_mem_omegaGroup hQ hs b.2))

theorem coe_clFixHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (a : omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :
    ((clFixHom hQ hs a : omegaProj hQ) : ProjOrth Q) =
      toProj Q (blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1)) :=
  rfl

theorem coe_clCommHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (b : omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    ((clCommHom hQ hs b : omegaProj hQ) : ProjOrth Q) =
      toProj Q (blockHom hs (1, (b : OGroup (Q.restrict (commSp s))))) :=
  rfl

private lemma clFixHom_mem_fix (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (a : omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :
    clFixHom hQ hs a ∈ fixSub (projAut hQ s) := by
  rw [mem_fixSub_projAut_iff, coe_clFixHom]
  have h1 : toProj Q s = toProj Q (blockHom hs (1, piOrth (Q.restrict (commSp s)))) := by
    rw [blockHom_one_piOrth hs]
  rw [h1, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  rw [show (1, piOrth (Q.restrict (commSp s))) * ((a : OGroup (Q.restrict (fixSp s))), 1) =
      ((a : OGroup (Q.restrict (fixSp s))), 1) * (1, piOrth (Q.restrict (commSp s))) by
    ext <;> simp]

private lemma clCommHom_mem_fix (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (b : omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    clCommHom hQ hs b ∈ fixSub (projAut hQ s) := by
  rw [mem_fixSub_projAut_iff, coe_clCommHom]
  have h1 : toProj Q s = toProj Q (blockHom hs (1, piOrth (Q.restrict (commSp s)))) := by
    rw [blockHom_one_piOrth hs]
  rw [h1, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact congrArg (blockHom hs) (by
    ext <;> simp [mul_piOrth_comm (Q := Q.restrict (commSp s))
      (b : OGroup (Q.restrict (commSp s)))])

theorem cl_clFixHom_mul_clCommHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (a : omegaGroup (nondegenerate_restrict_fixSp hQ hs))
    (b : omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    clFixHom hQ hs a * clCommHom hQ hs b = clCommHom hQ hs b * clFixHom hQ hs a := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_clFixHom, coe_clCommHom]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  rw [show ((a : OGroup (Q.restrict (fixSp s))), 1) *
        (1, (b : OGroup (Q.restrict (commSp s)))) =
      (1, (b : OGroup (Q.restrict (commSp s)))) *
        ((a : OGroup (Q.restrict (fixSp s))), 1) by ext <;> simp]

theorem cl_map_blockOmega_le (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    ((blockOmega hQ hs).comap (omegaGroup hQ).subtype).map (omegaToProj hQ) ≤
      (clFixHom hQ hs).range ⊔ (clCommHom hQ hs).range := by
  rintro g ⟨x, hx, rfl⟩
  have hx' : (x : OGroup Q) ∈ blockOmega hQ hs := Subgroup.mem_comap.mp hx
  rw [blockOmega, Subgroup.mem_map] at hx'
  obtain ⟨p, hp, hp_eq⟩ := hx'
  rw [Subgroup.mem_prod] at hp
  have heq : omegaToProj hQ x =
      clFixHom hQ hs ⟨p.1, hp.1⟩ * clCommHom hQ hs ⟨p.2, hp.2⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_clFixHom, coe_clCommHom, coe_omegaToProj]
    rw [← hp_eq, ← map_mul, ← map_mul]
    rw [show (p.1, 1) * (1, p.2) = p by ext <;> simp]
  rw [heq]
  exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem cl_isComponentIn_range_of_fix (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {K : Subgroup (omegaProj hQ)} (hK : IsComponentIn K (fixSub (projAut hQ s))) :
    IsComponentIn K (clFixHom hQ hs).range ∨ IsComponentIn K (clCommHom hQ hs).range := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaProj hQ) := inferInstance
  have hKH : K ≤ (cOmega hQ s).map (omegaToProj hQ) :=
    (IsComponentIn.le_commutator hK hK.le).trans (cl_commutator_fixSub_projAut_le hQ s)
  have hcomm_le : ⁅(cOmega hQ s).map (omegaToProj hQ),
      (cOmega hQ s).map (omegaToProj hQ)⁆ ≤
      (clFixHom hQ hs).range ⊔ (clCommHom hQ hs).range := by
    rw [← Subgroup.map_commutator]
    exact (Subgroup.map_mono (cl_commutator_cOmega_le hQ hs)).trans (cl_map_blockOmega_le hQ hs)
  have hKAB : K ≤ (clFixHom hQ hs).range ⊔ (clCommHom hQ hs).range :=
    (IsComponentIn.le_commutator hK hKH).trans hcomm_le
  have hABF : (clFixHom hQ hs).range ⊔ (clCommHom hQ hs).range ≤ fixSub (projAut hQ s) :=
    sup_le (by rintro x ⟨a, rfl⟩; exact clFixHom_mem_fix hQ hs a)
      (by rintro x ⟨b, rfl⟩; exact clCommHom_mem_fix hQ hs b)
  have hKAB' : IsComponentIn K ((clFixHom hQ hs).range ⊔ (clCommHom hQ hs).range) :=
    hK.mono hKAB hABF
  have hc : ∀ a ∈ (clFixHom hQ hs).range, ∀ b ∈ (clCommHom hQ hs).range, a * b = b * a := by
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    exact cl_clFixHom_mul_clCommHom hQ hs a' b'
  rcases IsComponentIn.le_or_le_of_commute hKAB' hc with hKA | hKB
  · exact Or.inl (hKAB'.mono hKA le_sup_left)
  · exact Or.inr (hKAB'.mono hKB le_sup_right)

end CFSG.OddStandard.SmallF3.Omega
