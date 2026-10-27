module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81P5b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight

variable {G : Type*} [Group G]

theorem conj_conj3 (v y w : G) :
    (v * y * v⁻¹)⁻¹ * w * (v * y * v⁻¹) = v * (y⁻¹ * (v⁻¹ * w * v) * y) * v⁻¹ := by group

theorem conj3_distrib (n x y w : G) :
    n⁻¹ * (x * y * w) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) * (n⁻¹ * w * n) := by group

theorem conj3_distrib' (n x y w : G) :
    n * (x * y * w) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) * (n * w * n⁻¹) := by group

theorem mul4_assoc (x y z w : G) : x * (y * z) * w = x * y * (z * w) := by group

end Eight

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

omit [Finite H] in
theorem commutator_conjugate (X : Subgroup H) (v : H) :
    ⁅conjugate X v, conjugate X v⁆ = conjugate ⁅X, X⁆ v := by
  change ⁅X.map (MulAut.conj v⁻¹).toMonoidHom, X.map (MulAut.conj v⁻¹).toMonoidHom⁆ =
    (⁅X, X⁆).map (MulAut.conj v⁻¹).toMonoidHom
  rw [map_commutator]

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem sq_mem_commutator_D (hSy : CFL2Sylow) (F : d.Facts) {e : H} (he : e ∈ h.D) :
    e * e ∈ ⁅h.D, h.D⁆ := by
  obtain ⟨-, hprod⟩ := d.D_facts hSy F
  obtain ⟨i, hi, j, hj, hi2, hj2, rfl⟩ := hprod e he
  have h1 : i * j * (i * j) = ⁅i, j⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hi2, inv_eq_of_mul_eq_one_right hj2]
    group
  rw [h1]
  exact commutator_mem_commutator hi hj

theorem z_mem_commutator_D (hSy : CFL2Sylow) (F : d.Facts) : d.z ∈ ⁅h.D, h.D⁆ := by
  obtain ⟨⟨t, htD, ht1, htc⟩, -⟩ := d.D_facts hSy F
  have h1 := sq_mem_commutator_D hSy F htD
  rcases center_D_cases hSy F (mul_mem htD htD) htc with h2 | h2
  · exact absurd h2 ht1
  · rwa [h2] at h1

section Seven

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
  {y : H} (hyS : y ∈ h.S) (hya : y⁻¹ * h.a * y = h.a) (hyz : y⁻¹ * d.z * y = d.z)
  (hyσ : y⁻¹ * d.sigma * y = h.a * d.z * d.sigma)
include hv I F h3 hyS hya hyz hyσ

omit hyS in
theorem conj_v_sigma :
    (v * y * v⁻¹)⁻¹ * d.sigma * (v * y * v⁻¹) = h.a * d.z * d.sigma := by
  have haz : h.a * d.z * (h.a * d.z) = 1 := by
    calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
      _ = h.a * (h.a * d.z) * d.z := by rw [d.z_comm_a]
      _ = (h.a * h.a) * (d.z * d.z) := by group
      _ = 1 := by rw [Six.a_mul_a_self h.toHyp52, d.z_mul_self, one_mul]
  have hza' : h.a * d.z * (d.z * h.a) = 1 := by
    calc h.a * d.z * (d.z * h.a) = h.a * (d.z * d.z) * h.a := by group
      _ = 1 := by rw [d.z_mul_self, mul_one, Six.a_mul_a_self h.toHyp52]
  have hva : v * h.a * v⁻¹ = d.z := by rw [← hv.conj_z]; group
  have hvz : v * d.z * v⁻¹ = h.a := by rw [← hv.conj_a]; group
  have hvN : v ∈ normalizer (h.F32 : Set H) := h.normalizer_S_le_normalizer_F32 hv.mem_N
  rw [Eight.conj_conj3]
  rcases conj_sigma_cases hv I F h3 hvN with h1 | h1
  · have hvσ : v * d.sigma * v⁻¹ = d.sigma := by
      calc v * d.sigma * v⁻¹ = v * (v⁻¹ * d.sigma * v) * v⁻¹ := by rw [h1]
        _ = d.sigma := Eight.mul_conj_inv_cancel v d.sigma
    rw [h1, hyσ, Eight.conj3_distrib', hva, hvz, hvσ, ← d.z_comm_a]
  · have hyazσ : y⁻¹ * (h.a * d.z * d.sigma) * y = d.sigma := by
      rw [Eight.conj3_distrib, hya, hyz, hyσ, ← mul_assoc (h.a * d.z) (h.a * d.z) d.sigma, haz,
        one_mul]
    have hvσ : v * d.sigma * v⁻¹ = h.a * d.z * d.sigma := by
      have h2 : d.sigma = d.z * h.a * (v * d.sigma * v⁻¹) := by
        calc d.sigma = v * (v⁻¹ * d.sigma * v) * v⁻¹ := (Eight.mul_conj_inv_cancel v d.sigma).symm
          _ = v * (h.a * d.z * d.sigma) * v⁻¹ := by rw [h1]
          _ = d.z * h.a * (v * d.sigma * v⁻¹) := by rw [Eight.conj3_distrib', hva, hvz]
      calc v * d.sigma * v⁻¹ = h.a * d.z * (d.z * h.a * (v * d.sigma * v⁻¹)) := by
            rw [← mul_assoc (h.a * d.z) (d.z * h.a), hza', one_mul]
        _ = h.a * d.z * d.sigma := by rw [← h2]
    rw [h1, hyazσ, hvσ]

theorem y_nontrivial_Dv (hDg : CF81Diag) :
    ∃ e ∈ conjugate h.D v, y * e * y⁻¹ * e⁻¹ ∉ ⁅conjugate h.D v, conjugate h.D v⁆ := by
  have hy'S : v * y * v⁻¹ ∈ h.S := (mem_normalizer_iff.mp hv.mem_N y).mp hyS
  obtain ⟨e, he, hnot⟩ := y_nontrivial_D I F hDg hy'S (conj_v_sigma hv I F h3 hya hyz hyσ)
  refine ⟨v⁻¹ * e * v, ?_, fun hmem => hnot ?_⟩
  · rw [mem_conjugate_iff, show v * (v⁻¹ * e * v) * v⁻¹ = e by group]
    exact he
  · rw [commutator_conjugate, mem_conjugate_iff] at hmem
    rwa [show v * (y * (v⁻¹ * e * v) * y⁻¹ * (v⁻¹ * e * v)⁻¹) * v⁻¹ =
      v * y * v⁻¹ * e * (v * y * v⁻¹)⁻¹ * e⁻¹ by group] at hmem

end Seven

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
