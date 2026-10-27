module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeF3Check
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZModel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS

namespace HeGS

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.GrSLitHeZStar
  Certificates.GrSLitHeF3

theorem heF3_model :
    ∃ w₁ ∈ heK0, ∃ w₂ ∈ heK0, w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧ w₁ * w₂ = w₂ * w₁ ∧
      w₁ ∉ heZ0 ∧ w₂ ∉ heZ0 ∧ w₁ * w₂ ∉ heZ0 := by
  obtain ⟨h11, h22, h12, n1a, n1b, n1c, n1d, n2a, n2b, n2c, n2d, n3a, n3b, n3c, n3d⟩ :=
    heF3_check
  set w₁ : Equiv.Perm (Fin 8330) := (heGSEC [2, 4, 2, 4] : Equiv.Perm (Fin 8330)) with hw₁
  set w₂ : Equiv.Perm (Fin 8330) := (heGSEC [1] : Equiv.Perm (Fin 8330)) with hw₂
  have hT1 : TabRep heF3W1Tab w₁ := by
    rw [hw₁, coe_heGSEC]
    exact tabRep_heGSKTab (heGSEW_lt _)
  have hT2 : TabRep heF3W2Tab w₂ := by
    rw [hw₂, coe_heGSEC]
    exact tabRep_heGSKTab (heGSEW_lt _)
  have hT12 : TabRep heF3W12Tab (w₁ * w₂) := hT1.comp hT2
  have hK1 : w₁ ∈ heK0 := mem_heK0_of_rho0_mem (rho0_heGSEC_mem (by decide))
  have hK2 : w₂ ∈ heK0 := mem_heK0_of_rho0_mem (rho0_heGSEC_mem (by decide))
  have hT0 : TabRep (heGen 0) (heGenPerm 0) := tabRep_heGen0
  have hTU : TabRep heZUTab (heGSU : Equiv.Perm (Fin 8330)) := tabRep_heZUTab
  have hT0U : TabRep heZT0UTab (heGenPerm 0 * (heGSU : Equiv.Perm (Fin 8330))) :=
    hT0.comp hTU
  have hZ : ∀ {t : CFSG.PSL3Four.Native.Tab} {p : Equiv.Perm (Fin 8330)}, TabRep t p →
      t ≠ idTab 8330 → t ≠ heGen 0 → t ≠ heZUTab → t ≠ heZT0UTab → p ∉ heZ0 := by
    intro t p hp ha hb hc hd hpZ
    rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff] at hpZ
    obtain ⟨hpK, hpc⟩ := hpZ
    rcases eq_of_comm_heK0 (mem_inf.mp (gsFixedLayer_le_inf heP _ hpK)).1
      (fun k hk => (hpc k hk).symm) with h | h | h | h
    · exact ha ((hp.eq_iff TabRep.idTab).mpr h)
    · exact hb ((hp.eq_iff hT0).mpr h)
    · exact hc ((hp.eq_iff hTU).mpr h)
    · exact hd ((hp.eq_iff hT0U).mpr h)
  exact ⟨w₁, hK1, w₂, hK2, ((hT1.comp hT1).eq_iff TabRep.idTab).mp h11,
    ((hT2.comp hT2).eq_iff TabRep.idTab).mp h22, (hT12.eq_iff (hT2.comp hT1)).mp h12,
    hZ hT1 n1a n1b n1c n1d, hZ hT2 n2a n2b n2c n2d, hZ hT12 n3a n3b n3c n3d⟩

end HeGS

namespace HeF3

open HeFM in
theorem exists_noncentral_pair
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) {u : X} (hu : HeldTwoA L u) :
    ∃ w₁ ∈ gsFixedLayer L u, ∃ w₂ ∈ gsFixedLayer L u, w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧
      w₁ * w₂ = w₂ * w₁ ∧
      w₁ ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype ∧
      w₂ ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype ∧
      w₁ * w₂ ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hKle : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 ↔
      (y : X) ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro y
    rw [← mem_center_trS_iff φ hKle y, hK]
    rfl
  obtain ⟨p₁, hp₁, p₂, hp₂, h1, h2, hc, hn1, hn2, hn3⟩ := HeGS.heF3_model
  rw [← hK] at hp₁ hp₂
  obtain ⟨x₁, hx₁K, hx₁e⟩ := (HeT.mem_trS φ).mp hp₁
  obtain ⟨x₂, hx₂K, hx₂e⟩ := (HeT.mem_trS φ).mp hp₂
  have hinv : ∀ x : ↥L, ∀ p : Equiv.Perm (Fin 8330), (φ x : Equiv.Perm (Fin 8330)) = p →
      p * p = 1 → (x : X) * x = 1 := by
    intro x p hxp hp
    have h : φ (x * x) = 1 := Subtype.ext (by rw [map_mul, coe_mul, hxp, hp]; rfl)
    rw [MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  refine ⟨x₁, hx₁K, x₂, hx₂K, hinv x₁ p₁ hx₁e h1, hinv x₂ p₂ hx₂e h2, ?_,
    fun h => hn1 (hx₁e ▸ (hZ x₁).mpr h), fun h => hn2 (hx₂e ▸ (hZ x₂).mpr h), fun h => hn3 ?_⟩
  · have h : φ (x₁ * x₂) = φ (x₂ * x₁) :=
      Subtype.ext (by rw [map_mul, map_mul, coe_mul, coe_mul, hx₁e, hx₂e, hc])
    exact congrArg Subtype.val (φ.injective h)
  · have h' := (hZ (x₁ * x₂)).mpr h
    rwa [map_mul, coe_mul, hx₁e, hx₂e] at h'

end HeF3

end CFSG.ComponentClassification.GrSLit
