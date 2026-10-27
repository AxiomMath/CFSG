module

public import CFSG.GF2Type.Smith1980Orth.S2Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

private theorem coord_add_coord (p q p' q' : Vt S D.g D.t) :
    D.coord (p, q) + D.coord (p', q') = D.coord (p + p', q + q') := by
  rw [← map_add]
  rfl

private theorem eq_of_add_eq_zero_Vt {a b : Vt S D.g D.t} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, ZModModule.neg_eq_self]

private theorem coord_mem_orbitMbar_iff {p q : Vt S D.g D.t} :
    D.coord (p, q) ∈ D.orbitMbar ↔ (q = 0 ∧ p ≠ 0 ∧ D.QV p = 0) ∨ (p = 0 ∧ q ≠ 0 ∧ D.QV q = 0) ∨
      (p = q ∧ p ≠ 0 ∧ D.QV p = 0) := by
  rw [D.mem_orbitMbar_iff_coord]
  constructor
  · rintro ⟨s, hs0, hsQ, h | h | h⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inl ⟨rfl, hs0, hsQ⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inr (Or.inl ⟨rfl, hs0, hsQ⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inr (Or.inr ⟨rfl, hs0, hsQ⟩)
  · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact ⟨p, h1, h2, Or.inl rfl⟩
    · exact ⟨q, h1, h2, Or.inr (Or.inl rfl)⟩
    · exact ⟨p, h1, h2, Or.inr (Or.inr rfl)⟩

private theorem QV_add_of_singular {σ τ : Vt S D.g D.t} (hσ : D.QV σ = 0) (hτ : D.QV τ = 0) :
    D.QV (σ + τ) = D.betaV σ τ := by
  rw [← D.polar_QV, polar, hσ, hτ]
  simp

private theorem not_mem_orbitMbar_same {σ τ : Vt S D.g D.t} (hσ : D.QV σ = 0) (hτ : D.QV τ = 0)
    (hβ : D.betaV σ τ ≠ 0) :
    D.coord (σ + τ, 0) ∉ D.orbitMbar ∧ D.coord (0, σ + τ) ∉ D.orbitMbar ∧
      D.coord (σ + τ, σ + τ) ∉ D.orbitMbar := by
  have hQ : D.QV (σ + τ) ≠ 0 := by
    rw [D.QV_add_of_singular hσ hτ]
    exact hβ
  refine ⟨?_, ?_, ?_⟩ <;> rw [D.coord_mem_orbitMbar_iff] <;>
    rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
    first | exact hQ h3 | exact h2 h1 | exact h2 rfl | exact h2 h1.symm

private theorem not_mem_orbitMbar_diff {σ τ : Vt S D.g D.t} (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (hne : τ ≠ σ) :
    D.coord (σ, τ) ∉ D.orbitMbar ∧ D.coord (τ, σ) ∉ D.orbitMbar ∧
      D.coord (σ + τ, τ) ∉ D.orbitMbar ∧ D.coord (τ, σ + τ) ∉ D.orbitMbar ∧
      D.coord (σ + τ, σ) ∉ D.orbitMbar ∧ D.coord (σ, σ + τ) ∉ D.orbitMbar := by
  have hsum0 : σ + τ ≠ 0 := fun h => hne (D.eq_of_add_eq_zero_Vt h).symm
  have hσs : σ + τ ≠ τ := fun h => hσ (by simpa using h)
  have hτs : σ + τ ≠ σ := fun h => hτ (by simpa using h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [D.coord_mem_orbitMbar_iff] <;>
    rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
    first | exact hτ h1 | exact hσ h1 | exact hne h1 | exact hne h1.symm | exact hsum0 h1 |
      exact hσs h1 | exact hσs h1.symm | exact hτs h1 | exact hτs h1.symm

include D in
theorem not_isConj_mul_of_not_mem_Qa {h b : G} (hcQ : h * S.z * h⁻¹ ∈ S.QG) (hb : IsConj S.z b)
    (hbQ : b ∈ S.QG) (_hcb : Commute (h * S.z * h⁻¹) b) (hbQa : b ∉ S.Qa h) :
    ¬ IsConj S.z (h * S.z * h⁻¹ * b) := by
  set c := h * S.z * h⁻¹
  have hcz : c ≠ S.z := fun hcz => hbQa (by rw [S.Qa_eq_QG_of_conj_eq hcz]; exact hbQ)
  have hbz : b ≠ S.z := fun hbz => hbQa (hbz ▸ S.z_mem_Qa hcQ hcz)
  have hzX : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa hcQ hcz⟩
  have hyP : S.cl b ∉ S.clSub (S.QG ⊓ S.Qa h) := fun hmem => hbQa (by
    have hb' : b ∈ S.clPre (S.clSub (S.QG ⊓ S.Qa h)) := ⟨hbQ, hmem⟩
    rw [S.clPre_clSub inf_le_left hzX] at hb'
    exact hb'.2)
  intro hconj
  have hcbQ : c * b ∈ S.QG := S.QG.mul_mem hcQ hbQ
  rcases D.conj_mem_Q_iff.mp ⟨hconj, hcbQ⟩ with hcbz | ⟨-, hsum⟩
  ·
    apply hyP
    have h0 : S.cl c + S.cl b = 0 := by rw [← S.cl_mul hcQ hbQ, hcbz, S.cl_z]
    rw [eq_neg_of_add_eq_zero_right h0, ZModModule.neg_eq_self]
    exact S.cl_mem_clSub ⟨hcQ, S.conj_z_mem_Qa h⟩ hcQ
  · rw [S.cl_mul hcQ hbQ] at hsum
    obtain ⟨σ, hσ0, hσQ, hx⟩ := (D.isConj_z_iff_coord hcQ hcz).mp (isConj_iff.mpr ⟨h, rfl⟩)
    obtain ⟨τ, hτ0, hτQ, hy⟩ := (D.isConj_z_iff_coord hbQ hbz).mp hb
    rcases hx with hx | hx | hx
    · rw [D.clSub_QG_inf_Qa_eq_Pfst hcQ hcz hx] at hyP
      rcases hy with hy | hy | hy
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hβ : D.betaV σ τ ≠ 0 := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pfst_iff.mpr ⟨τ, 0, h', by rw [zero_smul]⟩)
        exact (D.not_mem_orbitMbar_same hσQ hτQ hβ).1 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pfst_iff.mpr ⟨0, 1, map_zero _, by rw [h', one_smul]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).1 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pfst_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by rw [h', one_smul]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).2.2.1 hsum
    · rw [D.clSub_QG_inf_Qa_eq_Psnd hcQ hcz hx] at hyP
      rcases hy with hy | hy | hy
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Psnd_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by
            rw [h', one_smul, OrthoF2.vec_add_self]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).2.1 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hβ : D.betaV σ τ ≠ 0 := fun h' => hyP (by
          rw [hy]
          exact D.mem_Psnd_iff.mpr ⟨τ, 0, h', by rw [zero_smul, add_zero]⟩)
        exact (D.not_mem_orbitMbar_same hσQ hτQ hβ).2.1 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Psnd_iff.mpr ⟨0, 1, map_zero _, by rw [h', one_smul, zero_add]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).2.2.2.1 hsum
    · rw [D.clSub_QG_inf_Qa_eq_Pdiag hcQ hcz hx] at hyP
      rcases hy with hy | hy | hy
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pdiag_iff.mpr ⟨0, 1, map_zero _, by rw [h', one_smul, zero_add]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).2.2.2.2.1 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hne : τ ≠ σ := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pdiag_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by
            rw [h', one_smul, OrthoF2.vec_add_self]⟩)
        exact (D.not_mem_orbitMbar_diff hσ0 hτ0 hne).2.2.2.2.2 hsum
      ·
        rw [hx, hy] at hsum
        simp only [D.coord_add_coord, add_zero, zero_add] at hsum
        have hβ : D.betaV σ τ ≠ 0 := fun h' => hyP (by
          rw [hy]
          exact D.mem_Pdiag_iff.mpr ⟨τ, 0, h', by rw [zero_smul, add_zero]⟩)
        exact (D.not_mem_orbitMbar_same hσQ hτQ hβ).2.2 hsum

private theorem mem_Qa_iff_inv_conj (S : Setting G) (h x : G) :
    x ∈ S.Qa h ↔ h⁻¹ * x * h ∈ S.QG := by
  have := S.mem_Qa_mul_iff (g := 1) (h := h) (x := x)
  rwa [mul_one, S.Qa_one] at this

include D in
theorem not_isConj_mul_z_of_mem {x k h : G} (hk : k * S.z * k⁻¹ = x) (hxM : x ∈ S.M)
    (hxQ : x ∉ S.QG) (hh : h * S.z * h⁻¹ ∈ S.QG ⊓ S.Qa k) : ¬ IsConj S.z (x * S.z) := by
  have hxz : x ≠ S.z := fun h' => hxQ (h' ▸ S.z_mem_QG)
  have haQ : h * S.z * h⁻¹ ∈ S.QG := hh.1
  have haQk : h * S.z * h⁻¹ ∈ S.Qa k := hh.2
  have hzk : S.z ∉ S.Qa k := fun hz => hxQ (by
    have h1 := S.mem_Qa_symm (g₁ := 1) (g₂ := k) (by simpa [hk] using hxz.symm)
      (by simpa using hz)
    rw [S.Qa_one, hk] at h1
    exact h1)
  have haz : h * S.z * h⁻¹ ≠ S.z := fun h' => hzk (h' ▸ haQk)
  have hax : h * S.z * h⁻¹ ≠ k * S.z * k⁻¹ := fun h' => hxQ (by rw [← hk, ← h']; exact haQ)
  have hzh : S.z ∈ S.Qa h := S.z_mem_Qa_of_mem_QG rfl haQ haz
  have hxh : k * S.z * k⁻¹ ∈ S.Qa h := S.mem_Qa_symm hax haQk
  rw [hk] at hxh
  have hcQ : h⁻¹ * S.z * h⁻¹⁻¹ ∈ S.QG := by
    rw [inv_inv]
    exact (mem_Qa_iff_inv_conj S h S.z).mp hzh
  have hdQ : h⁻¹ * x * h ∈ S.QG := (mem_Qa_iff_inv_conj S h x).mp hxh
  have hdc : IsConj S.z (h⁻¹ * x * h) := isConj_iff.mpr ⟨h⁻¹ * k, by rw [← hk]; group⟩
  have hcom : Commute (h⁻¹ * S.z * h⁻¹⁻¹) (h⁻¹ * x * h) := by
    show h⁻¹ * S.z * h⁻¹⁻¹ * (h⁻¹ * x * h) = h⁻¹ * x * h * (h⁻¹ * S.z * h⁻¹⁻¹)
    have := S.z_comm hxM
    calc h⁻¹ * S.z * h⁻¹⁻¹ * (h⁻¹ * x * h) = h⁻¹ * (S.z * x) * h := by group
      _ = h⁻¹ * (x * S.z) * h := by rw [this]
      _ = h⁻¹ * x * h * (h⁻¹ * S.z * h⁻¹⁻¹) := by group
  have hdQa : h⁻¹ * x * h ∉ S.Qa h⁻¹ := fun hd => hxQ (by
    have := (mem_Qa_iff_inv_conj S h⁻¹ _).mp hd
    simpa [mul_assoc] using this)
  intro hconj
  refine D.not_isConj_mul_of_not_mem_Qa hcQ hdc hdQ hcom hdQa ?_
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine isConj_iff.mpr ⟨h⁻¹ * g, ?_⟩
  have hxz' : x * S.z = S.z * x := S.z_comm hxM
  calc h⁻¹ * g * S.z * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * S.z * g⁻¹) * h := by group
    _ = h⁻¹ * (x * S.z) * h := by rw [hg]
    _ = h⁻¹ * S.z * h⁻¹⁻¹ * (h⁻¹ * x * h) := by rw [hxz']; group

end S2Data

end CFSG.GF2Type.Smith1980Orth
