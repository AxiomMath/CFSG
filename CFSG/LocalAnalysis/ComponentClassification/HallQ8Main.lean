module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallInd
public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Fin

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

namespace Q8Cfg

theorem exists_setup (h : Q8Cfg D c)
    (hex : ∃ x ∈ normalizer (D : Set G), x ∉ D ∧
      ∃ d ∈ D, d * d = cz c ∧ ∃ g : G, g⁻¹ * x * g = d) :
    ∃ (S : Subgroup G) (y' u : G) (l : ℤ), Nonempty (Setup h S y' u l) := by
  obtain ⟨x, hxN, hxD, d, hd, hd2, g, hg⟩ := hex
  obtain ⟨u, huD, huK⟩ := exists_refl' h
  have hdK : d ∈ zpowers c := sq_cz_mem_K h hd hd2
  have hx : x = g * d * g⁻¹ := by rw [← hg]; group
  have hTh : Th c x := by
    rcases eq_cy_or_inv h hdK hd2 with e | e
    · exact ⟨g⁻¹, by rw [hx, e]; group⟩
    · have := Th_inv h huD huK (show Th c (g * cy c * g⁻¹) from ⟨g⁻¹, by group⟩)
      rw [hx, e]
      rwa [show (g * cy c * g⁻¹)⁻¹ = g * (cy c)⁻¹ * g⁻¹ by group] at this
  have hxsq : x * x = cz c := Th_sq h hTh
  have hx4 : x ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by rfl, pow_add, sq, hxsq]
    exact cz_mul_cz h.h4
  have hR2 : IsPGroup 2 (D ⊔ zpowers x : Subgroup G) :=
    h.isPGroup_D.to_sup_of_normal_left' (isPGroup_zpowers_of_pow hx4) (zpowers_le.mpr hxN)
  obtain ⟨S, hS, hRS⟩ :=
    FooteLit.exists_isSylowOf_ge_of_le (le_top : (D ⊔ zpowers x : Subgroup G) ≤ ⊤) hR2
  have hDS : D ≤ S := le_sup_left.trans hRS
  have hxS : x ∈ S := hRS (mem_sup_right (mem_zpowers x))
  obtain ⟨l, hl⟩ := conj_refl h hxN huD huK
  obtain ⟨hinv, hodd⟩ := struct_inv h hS hDS hxS hTh hxD huD huK hl
  exact ⟨S, x, u, l, ⟨⟨hS, hDS, huD, huK, hxS, hTh, hxD,
    ⟨hinv, hl, hxsq, (refl_data h huD huK).1, (refl_data h huD huK).2⟩, hodd⟩⟩⟩

theorem weak_conclusion (h : Q8Cfg D c)
    (hex : ∃ x ∈ normalizer (D : Set G), x ∉ D ∧
      ∃ d ∈ D, d * d = cz c ∧ ∃ g : G, g⁻¹ * x * g = d) :
    HallWeakConclusion D := by
  obtain ⟨S, y', u, l, ⟨hs⟩⟩ := exists_setup h hex
  exact ⟨hs.Q, S, hs.hS, hs.D_le_Q, hs.Q_le_S, hs.Q_stronglyClosed,
    fun x hx hx2 => hs.inv_Q_le_D hx hx2, hs.card_Q⟩

end Q8Cfg

theorem hallQ8Residual : HallQ8Residual := by
  intro G _ _ _ D c m hm hco hcD hcard hD hcl hz hex
  exact (Q8Cfg.mk ⟨m, hm, hco⟩ hcD hcard hD hcl hz).weak_conclusion hex

end CFSG.ComponentClassification.Foote5.HallGen
