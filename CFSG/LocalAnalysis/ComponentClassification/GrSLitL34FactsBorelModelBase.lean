
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

private theorem decomp_D4 : ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), ∃ i j : Fin 2,
    ∃ f : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
      d = (Multiplicative.ofAdd (i.val : ZMod 4), Multiplicative.ofAdd (j.val : ZMod 4)) *
        (f * f) := by
  decide

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

variable {G : Type} [Group G] {J P : Subgroup G} {q' : Jhat J →* Equiv.Perm (Fin 42)}

theorem comm_of_mem_Z [Finite G] (hP : IsSylowTwoIn P J) {z : G} (hz : z ∈ P ⊓ zStarIn J)
    {p : G} (hp : p ∈ P) : z * p = p * z := by
  obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
  have hc := (mem_zStarIn_iff (hP.1 hzP)).1 hzZ
  apply eq_of_jq_eq hP.1 (GrS4.isPGroup_of_isSylowTwoIn hP) (P.mul_mem hzP hp) (P.mul_mem hp hzP)
  show jq J (⟨z, hP.1 hzP⟩ * ⟨p, hP.1 hp⟩) = jq J (⟨p, hP.1 hp⟩ * ⟨z, hP.1 hzP⟩)
  rw [map_mul, map_mul]
  exact ((mem_center_iff.mp hc) _).symm

theorem mem_Z0_iff_comm
    (hP : IsSylowTwoIn P J) (hqsurj : ∀ s ∈ S, ∃ e, q' e = s)
    (hqker : q'.ker = center (Jhat J))
    (hT : ∀ e, q' e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) {y : G} (hy : y ∈ P) :
    q' (jq J ⟨y, hP.1 hy⟩) ∈ Z0 ↔ ∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J := by
  have hTP : ∀ {a : G} (ha : a ∈ P), q' (jq J ⟨a, hP.1 ha⟩) ∈ T0 := fun ha =>
    (hT _).2 ⟨_, ha, _, rfl⟩
  have hcomm : ∀ {w : G} (hw : w ∈ P), y⁻¹ * w⁻¹ * y * w ∈ zStarIn J ↔
      q' (jq J ⟨y, hP.1 hy⟩) * q' (jq J ⟨w, hP.1 hw⟩) =
        q' (jq J ⟨w, hP.1 hw⟩) * q' (jq J ⟨y, hP.1 hy⟩) := by
    intro w hw
    have hm : y⁻¹ * w⁻¹ * y * w ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hy) (P.inv_mem hw)) hy) hw
    rw [mem_zStarIn_iff (hP.1 hm), ← hqker, MonoidHom.mem_ker]
    have e : (⟨y⁻¹ * w⁻¹ * y * w, hP.1 hm⟩ : J) = (⟨y, hP.1 hy⟩ : J)⁻¹ *
        (⟨w, hP.1 hw⟩ : J)⁻¹ * ⟨y, hP.1 hy⟩ * ⟨w, hP.1 hw⟩ := rfl
    rw [e]
    simp only [map_mul, map_inv]
    generalize q' (jq J ⟨y, hP.1 hy⟩) = a
    generalize q' (jq J ⟨w, hP.1 hw⟩) = b
    constructor
    · intro h
      calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
        _ = b * a := by rw [h, mul_one]
    · intro h
      rw [mul_assoc a⁻¹ b⁻¹ a, ← mul_assoc, mul_assoc _ a b, h]
      group
  constructor
  · intro hyZ w hw
    exact (hcomm hw).2 ((mem_centralizer_iff.mp hyZ.1) _ (hTP hw)).symm
  · intro h
    refine ⟨mem_centralizer_iff.mpr fun t ht => ?_, hTP hy⟩
    obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht)
    obtain ⟨w, hwP, hwJ, rfl⟩ := (hT e).1 (he ▸ ht)
    rw [← he]
    exact ((hcomm hwP).1 (h w hwP)).symm

end CFSG.ComponentClassification.GrSLit.L34Facts
