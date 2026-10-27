module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_piOrth_mem_omega (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) : piOrth Q ∈ omegaGroup hQ :=
  (piOrth_mem_omegaGroup_iff hQ).mpr ⟨by rw [hdim]; decide, by rw [hdim, hsgn]; decide⟩

theorem ff6m_mem_ffFix_sim_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (ρ : ↥(simGroup Q)) (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) ↔
      ∃ g ∈ omegaGroup hQ, (simAct Q ρ g = g ∨ simAct Q ρ g = piOrth Q * g) ∧
        toProj Q g = (w : ProjOrth Q) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨g₀, hg₀, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  constructor
  · intro hfix
    have h1 : toProj Q (simAct Q ρ g₀) = toProj Q g₀ := by
      have h0 := congrArg Subtype.val (mem_fixSub_iff.mp hfix)
      rwa [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj] at h0
    have h3 : (simAct Q ρ g₀)⁻¹ * g₀ ∈ piGroup Q := QuotientGroup.eq.mp h1
    refine ⟨g₀, hg₀, ?_, rfl⟩
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · exact Or.inl (inv_mul_eq_one.mp h4)
    · right
      have h5 : g₀ = simAct Q ρ g₀ * piOrth Q := inv_mul_eq_iff_eq_mul.mp h4
      have h6 : simAct Q ρ g₀ = g₀ * piOrth Q :=
        calc simAct Q ρ g₀ = simAct Q ρ g₀ * (piOrth Q * piOrth Q) := by
              rw [piOrth_mul_self, mul_one]
          _ = (simAct Q ρ g₀ * piOrth Q) * piOrth Q := by rw [mul_assoc]
          _ = g₀ * piOrth Q := by rw [← h5]
      rw [h6]
      exact Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g₀
  · rintro ⟨g, hg, hgc, hgw⟩
    apply mem_fixSub_iff.mpr
    apply Subtype.ext
    rw [coe_ffSimOmegaAct, projSimAct_mk, ← hgw, projActAux_toProj]
    rcases hgc with h | h
    · rw [h]
    · rw [h, map_mul, toProj_piOrth, one_mul]

theorem ff6m_mem_ffFix_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) ↔
      ∃ g ∈ omegaGroup hQ, (t * g * t⁻¹ = g ∨ t * g * t⁻¹ = piOrth Q * g) ∧
        toProj Q g = (w : ProjOrth Q) := by
  have hx : projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk (orthToSim Q t) := rfl
  rw [hx, ff6m_mem_ffFix_sim_iff hQ hdim hsgn (orthToSim Q t) w]
  simp only [simAct_orthToSim]

theorem ff6m_mem_ffFix_iff_of_not_conj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) (hnc : ¬ IsConj (piOrth Q * t) t) (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) ↔
      ∃ g ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)),
        toProj Q g = (w : ProjOrth Q) := by
  rw [ff6m_mem_ffFix_iff hQ hdim hsgn w]
  constructor
  · rintro ⟨g, hg, hgc, hgw⟩
    refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, ?_⟩, hgw⟩
    rcases hgc with h | h
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = (t * g * t⁻¹) * t := by rw [h]
        _ = t * g := by group
    · exfalso
      apply hnc
      rw [isConj_iff]
      have h1 : t * g = piOrth Q * g * t := by
        calc t * g = (t * g * t⁻¹) * t := by group
          _ = piOrth Q * g * t := by rw [h]
      have e1 : g⁻¹ * piOrth Q = piOrth Q * g⁻¹ :=
        Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g⁻¹
      have hgt : g⁻¹ * t * g = piOrth Q * t :=
        calc g⁻¹ * t * g = g⁻¹ * (t * g) := by group
          _ = g⁻¹ * (piOrth Q * g * t) := by rw [h1]
          _ = (g⁻¹ * piOrth Q) * g * t := by group
          _ = piOrth Q * t := by rw [e1]; group
      refine ⟨g⁻¹, ?_⟩
      calc g⁻¹ * (piOrth Q * t) * g⁻¹⁻¹ = (g⁻¹ * piOrth Q) * t * g := by group
        _ = piOrth Q * (g⁻¹ * t * g) := by rw [e1]; group
        _ = piOrth Q * (piOrth Q * t) := by rw [hgt]
        _ = t := by rw [← mul_assoc, piOrth_mul_self, one_mul]
  · rintro ⟨g, hg, hgw⟩
    refine ⟨g, (Subgroup.mem_inf.mp hg).1, Or.inl ?_, hgw⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
    calc t * g * t⁻¹ = (g * t) * t⁻¹ := by rw [h]
      _ = g := by group

end CFSG.OddStandard.SmallF3.Omega
