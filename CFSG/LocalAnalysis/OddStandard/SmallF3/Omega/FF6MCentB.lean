module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

theorem ff6m_cent_B_of_le [Finite G] (h : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) {x : G} (hxN : x ∈ normalizer (L : Set G))
    (hx : ∀ b ∈ B, x * b = b * x) :
    (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
      (∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α) ∨ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α := by
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hB1⟩ := ff_exists_model_B1 h hBL hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  have hh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  let z : ProjSim Q := ffTheta hQ hh e ⟨x, hxN⟩
  have hzI : InducesViaP L (Subgroup.center ↥L) hQ e x z := ffTheta_induces hQ hh e ⟨x, hxN⟩
  have hz : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 z b = b := by
    intro b hb
    rw [← hB1] at hb
    obtain ⟨l, hlB, rfl⟩ := mem_ffImg_iff.mp hb
    have hxl : x * (l : G) = (l : G) * x := hx (l : G) hlB
    exact ff6m_phi_conj hQ h2 e hzI l l (by rw [hxl]; group)
  rcases ff_star_cent_kinds hQ hdim hsgn h2 fr hz with ⟨b, hb, hzb⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
  · rw [← hB1] at hb
    obtain ⟨l, hlB, rfl⟩ := mem_ffImg_iff.mp hb
    left
    refine ⟨l, hlB, ?_⟩
    let m : G := x * (l : G)⁻¹
    have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem hxN (Subgroup.le_normalizer (L.inv_mem l.2))
    have hm_eq : (⟨m, hmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hxN⟩ * ⟨(l : G), Subgroup.le_normalizer l.2⟩⁻¹ := by
      apply Subtype.ext
      rfl
    have htheta_m : ffTheta hQ hh e ⟨m, hmN⟩ =
        z * (ffTheta hQ hh e ⟨(l : G), Subgroup.le_normalizer l.2⟩)⁻¹ := by
      rw [hm_eq, map_mul, map_inv]
    have htheta_l : ffTheta hQ hh e ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
        projOrthToProjSim Q ((ff6mPhi e l : ↥(omegaProj hQ)) : ProjOrth Q) := by
      rw [ffTheta_of_mem hQ hh e l, ff6mPhi_apply]
    have hone : ffTheta hQ hh e ⟨m, hmN⟩ = 1 := by
      rw [htheta_m, htheta_l, ← hzb, mul_inv_cancel]
    have hcent : m ∈ centralizer (L : Set G) :=
      (ff6m_centralizer_iff_eq_one h.1 hQ h5 e (ffTheta_induces hQ hh e ⟨m, hmN⟩)).mpr hone
    change x * (l : G)⁻¹ ∈ centralizer (L : Set G)
    exact hcent
  · right; left
    exact ⟨α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, z, hdim, hsgn, hzI, hα⟩
  · right; right
    exact ⟨α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, z, hdim, hsgn, hzI, hα⟩

theorem ff6m_cent_B (G : Type) [Group G] [Finite G] (L : Subgroup G) (h : IsOm6M L)
    (P : Subgroup G) (hP : IsSylow2Of P L) (B : Subgroup G) (hBP : B ≤ P) (hB : IsElemAb2 B 4)
    (x : G) (hxN : x ∈ normalizer (L : Set G)) (hx : ∀ b ∈ B, x * b = b * x) :
    (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
      (∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α) ∨ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α :=
  ff6m_cent_B_of_le h (hBP.trans hP.1) hB hxN hx

end CFSG.OddStandard.SmallF3.Omega
