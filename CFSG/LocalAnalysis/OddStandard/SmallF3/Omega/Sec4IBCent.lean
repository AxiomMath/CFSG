module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4IPsi_conj_mono (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u v : Fin 7 → ZMod 2) :
    toProj Q (sec4IMono fr σ u) * sec4IPsi fr v * (toProj Q (sec4IMono fr σ u))⁻¹ =
      sec4IPsi fr (permVec σ v) := by
  rw [sec4IPsi, sec4IPsi, ← map_inv, ← map_mul, ← map_mul, sec4IMono_conj_T]

theorem sec4I_mono_of_normalizes_B0 (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) {g : OGroup Q}
    (hg : toProj Q g ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q))) :
    ∃ (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2), g = sec4IMono fr σ u := by
  refine sec4I_eq_mono_of_normalizes fr g fun s hs => ?_
  have hnorm : ∀ h : ProjOrth Q,
      h ∈ (sec4IB0 fr : Set (ProjOrth Q)) ↔
        (toProj Q g)⁻¹ * h * toProj Q g ∈ (sec4IB0 fr : Set (ProjOrth Q)) :=
    (Subgroup.mem_normalizer_iff'' (H := sec4IB0 fr) (g := toProj Q g)).mp hg
  have hmem : (toProj Q g)⁻¹ * sec4IPsi fr s * toProj Q g ∈ sec4IB0 fr :=
    (hnorm (sec4IPsi fr s)).mp (sec4IPsi_mem_sec4IB0 fr hs)
  obtain ⟨s', hs'even, hs'eq⟩ := (mem_sec4IB0_iff fr).mp hmem
  have hconj : (toProj Q g)⁻¹ * sec4IPsi fr s * toProj Q g =
      toProj Q (g⁻¹ * sec4IT fr s * g) := by
    rw [sec4IPsi, ← map_inv, ← map_mul, ← map_mul]
  have hmul : toProj Q (g⁻¹ * sec4IT fr s * g) = toProj Q (sec4IT fr s') := by
    rw [← hconj, ← hs'eq, sec4IPsi]
  have hb_inv : (sec4IT fr s')⁻¹ = sec4IT fr s' :=
    inv_eq_of_mul_eq_one_right (sec4IT_mul_self fr s')
  have hb : sec4IT fr s' * (g⁻¹ * sec4IT fr s * g) ∈ piGroup Q := by
    have hq : ((sec4IT fr s' : OGroup Q) : ProjOrth Q) =
        ((g⁻¹ * sec4IT fr s * g : OGroup Q) : ProjOrth Q) := by
      change toProj Q (sec4IT fr s') = toProj Q (g⁻¹ * sec4IT fr s * g)
      exact hmul.symm
    have h := (QuotientGroup.eq (s := piGroup Q)).mp hq
    simpa only [hb_inv] using h
  rcases (mem_piGroup_iff (Q := Q)).mp hb with h1 | h1
  · refine ⟨s', hs'even, ?_⟩
    have h : g⁻¹ * sec4IT fr s * g = (sec4IT fr s')⁻¹ :=
      (mul_eq_one_iff_eq_inv' (a := sec4IT fr s') (b := g⁻¹ * sec4IT fr s * g)).mp h1
    rwa [hb_inv] at h
  · have hba : g⁻¹ * sec4IT fr s * g = sec4IT fr s' * piOrth Q := by
      calc g⁻¹ * sec4IT fr s * g
          = (sec4IT fr s')⁻¹ * piOrth Q := by rw [← h1]; group
        _ = sec4IT fr s' * piOrth Q := by rw [hb_inv]
    have haeq : g⁻¹ * sec4IT fr s * g = sec4IT fr (s' + sec4IOnes) := by
      rw [hba, ← sec4IT_ones, ← sec4IT_add]
    refine ⟨s' + sec4IOnes, ?_, haeq⟩
    have htype : invType (sec4IT fr (s' + sec4IOnes)) = invType (sec4IT fr s) := by
      rw [← haeq]
      simpa only [inv_inv] using invType_conj hQ (sec4IT_mul_self fr s) g⁻¹
    have hw : vecWeight (s' + sec4IOnes) = vecWeight s := by
      have h1' : invDim (sec4IT fr (s' + sec4IOnes)) = invDim (sec4IT fr s) :=
        congrArg Prod.fst htype
      rwa [sec4IT_invDim, sec4IT_invDim] at h1'
    have hev : Even (vecWeight (s' + sec4IOnes)) := by
      rw [hw]
      exact (sec4I_isEvenVec_iff_even_vecWeight s).mp hs
    exact (sec4I_isEvenVec_iff_even_vecWeight (s' + sec4IOnes)).mpr hev

theorem sec4I_centralizer_B0 (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    Subgroup.centralizer (sec4IB0 fr : Set (ProjOrth Q)) = sec4IB0 fr := by
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) :=
      Subgroup.centralizer_le_normalizer (sec4IB0 fr : Set (ProjOrth Q)) hx
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (piGroup Q) x
    have hgN : toProj Q g ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) := by
      rwa [hg]
    obtain ⟨σ, u, hgu⟩ := sec4I_mono_of_normalizes_B0 hQ fr hgN
    have hfix : ∀ v : Fin 7 → ZMod 2, IsEvenVec v → permVec σ v = v := by
      intro v hv
      have hmem : sec4IPsi fr v ∈ sec4IB0 fr := sec4IPsi_mem_sec4IB0 fr hv
      have hcomm := (Subgroup.mem_centralizer_iff).mp hx (sec4IPsi fr v) hmem
      have hconj : x * sec4IPsi fr v * x⁻¹ = sec4IPsi fr (permVec σ v) := by
        rw [← hg, hgu]
        exact sec4IPsi_conj_mono fr σ u v
      have heq : sec4IPsi fr (permVec σ v) = sec4IPsi fr v := by
        rw [← hconj]
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact sec4IPsi_injOn fr (sec4I_isEvenVec_permVec σ hv) hv heq
    have hσ : σ = 1 := sec4I_perm_eq_one_of_fix σ hfix
    have hxpsi : x = sec4IPsi fr u := by
      rw [← hg, hgu, hσ]
      rfl
    rcases em (IsEvenVec u) with hu | hu
    · rw [hxpsi]
      exact sec4IPsi_mem_sec4IB0 fr hu
    · rw [hxpsi, ← sec4IPsi_add_ones fr u]
      exact sec4IPsi_mem_sec4IB0 fr (sec4I_isEvenVec_add_ones hu)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨v, hv, rfl⟩ := (mem_sec4IB0_iff fr).mp hh
    obtain ⟨u, hu, rfl⟩ := (mem_sec4IB0_iff fr).mp hx
    rw [sec4IPsi_comm]

end CFSG.OddStandard.SmallF3.Omega
