module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic CFSG.LieType.Multipliers.U43

@[expose] def FixSet (K : Subgroup (Equiv.Perm (Fin 820))) (ρ : Equiv.Perm (Fin 820)) :
    Set (Subgroup (Equiv.Perm (Fin 820))) :=
  {C | (∃ g ∈ P, conjSub g K = C) ∧ ∀ c ∈ C, ρ * c = c * ρ}

@[expose] noncomputable def Yb (K : Subgroup (Equiv.Perm (Fin 820))) (ρ : Equiv.Perm (Fin 820)) :
    Subgroup (Equiv.Perm (Fin 820)) :=
  ⨆ C ∈ FixSet K ρ, C

@[expose] def Concl (K : Subgroup (Equiv.Perm (Fin 820))) (ρ : Equiv.Perm (Fin 820)) : Prop :=
  Nonempty (↥(Yb K ρ) ≃* StatedSU 3 3 F9) ∧
    ∀ C ∈ FixSet K ρ, ∃ y ∈ Yb K ρ, conjSub y C = C ∧ y ^ 3 = 1 ∧ ∃ c ∈ C, y * c ≠ c * y

variable {K : Subgroup (Equiv.Perm (Fin 820))} {ρ g : Equiv.Perm (Fin 820)}

theorem conjSub_conj (g h : Equiv.Perm (Fin 820)) (K : Subgroup (Equiv.Perm (Fin 820))) :
    conjSub (g * h * g⁻¹) (conjSub g K) = conjSub g (conjSub h K) := by
  rw [← conjSub_mul, ← conjSub_mul]
  congr 1
  group

theorem comm_conj_iff (g ρ c : Equiv.Perm (Fin 820)) :
    g * ρ * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * ρ * g⁻¹) ↔ ρ * c = c * ρ := by
  constructor
  · intro h
    have h1 : g * (ρ * c) * g⁻¹ = g * (c * ρ) * g⁻¹ := by
      calc g * (ρ * c) * g⁻¹ = g * ρ * g⁻¹ * (g * c * g⁻¹) := by group
        _ = g * c * g⁻¹ * (g * ρ * g⁻¹) := h
        _ = g * (c * ρ) * g⁻¹ := by group
    simpa using h1
  · intro h
    calc g * ρ * g⁻¹ * (g * c * g⁻¹) = g * (ρ * c) * g⁻¹ := by group
      _ = g * (c * ρ) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * (g * ρ * g⁻¹) := by group

theorem fixSet_conj_left (hg : g ∈ P) : FixSet (conjSub g K) ρ = FixSet K ρ := by
  ext C
  simp only [FixSet, Set.mem_ofPred_eq]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, P.mul_mem hh hg, (conjSub_mul h g K)⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h * g⁻¹, P.mul_mem hh (P.inv_mem hg), ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]

theorem fixSet_conj (hg : g ∈ P) :
    FixSet (conjSub g K) (g * ρ * g⁻¹) = conjSub g '' FixSet K ρ := by
  ext C
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hc⟩
    refine ⟨conjSub (g⁻¹ * h * g) K, ⟨⟨_, P.mul_mem (P.mul_mem (P.inv_mem hg) hh) hg, rfl⟩,
      fun c hc' => ?_⟩, ?_⟩
    · have hmem : g * c * g⁻¹ ∈ conjSub h (conjSub g K) := by
        rw [← conjSub_mul, show h * g = g * (g⁻¹ * h * g) by group, conjSub_mul]
        exact conj_mem_conjSub hc'
      exact (comm_conj_iff g ρ c).1 (hc _ hmem)
    · rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
  · rintro ⟨C₀, ⟨⟨h, hh, rfl⟩, hc⟩, rfl⟩
    refine ⟨⟨g * h * g⁻¹, P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg), conjSub_conj g h K⟩, ?_⟩
    rintro _ ⟨c, hc', rfl⟩
    exact (comm_conj_iff g ρ c).2 (hc c hc')

theorem yb_conj (hg : g ∈ P) : Yb (conjSub g K) (g * ρ * g⁻¹) = conjSub g (Yb K ρ) := by
  rw [Yb, Yb, fixSet_conj hg, iSup_image, conjSub, Subgroup.map_iSup]
  congr 1
  ext C
  rw [Subgroup.map_iSup]
  rfl

theorem concl_conj (hg : g ∈ P) (h : Concl K ρ) : Concl (conjSub g K) (g * ρ * g⁻¹) := by
  obtain ⟨⟨e⟩, h3⟩ := h
  refine ⟨⟨?_⟩, ?_⟩
  · rw [yb_conj hg]
    exact ((Yb K ρ).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e
  · rw [fixSet_conj hg]
    rintro _ ⟨C₀, hC₀, rfl⟩
    obtain ⟨y, hy, hyC, hy3, c, hc, hyc⟩ := h3 C₀ hC₀
    refine ⟨g * y * g⁻¹, ?_, ?_, ?_, g * c * g⁻¹, conj_mem_conjSub hc, ?_⟩
    · rw [yb_conj hg]
      exact conj_mem_conjSub hy
    · rw [conjSub_conj, hyC]
    · rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    · intro he
      apply hyc
      have h1 : g * (y * c) * g⁻¹ = g * (c * y) * g⁻¹ := by
        calc g * (y * c) * g⁻¹ = g * y * g⁻¹ * (g * c * g⁻¹) := by group
          _ = g * c * g⁻¹ * (g * y * g⁻¹) := he
          _ = g * (c * y) * g⁻¹ := by group
      simpa using h1

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
