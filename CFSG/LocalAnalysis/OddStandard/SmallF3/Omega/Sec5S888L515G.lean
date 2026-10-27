module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515Q
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5_gamma_eq (h514 : Asc82Lemma514) (hF2 : Asc82FactPocketsTwo) (hb : Asc82Lemma515b)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h))
    {S'' : Subgroup G} {r'' : G} {B'' A'' P₁ P₂ : Subgroup G} {h'' : G}
    (c'' : Sec5HCtx G d (layerC5 d) S'' z r'' B'' A'' P₁ P₂ h'') :
    Gamma5 P₁ P₂ h'' = Gamma5 K₁ K₂ h := by
  have hd2 : orderOf d = 2 := hd.1
  have hdz : d ≠ z := hd.2.1
  obtain ⟨i, j, hij, hdij⟩ := sec5_delta_support h514 c hd
  obtain ⟨l, m, hlm, hli, hlj, hmi, hmj⟩ := sec5_exists_compl i j hij
  have hP := sec5_pockets_eq h514 hF2 hb c hij hlm hli hlj hmi hmj hd2 hdz hdij c''
  have hPP : P₁ ⊔ P₂ = Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hcomm : Commute h'' z := Subgroup.mem_centralizer_singleton_iff.mp c''.h_z
  have hz : h''⁻¹ * z * h'' = z := hcomm.inv_mul_cancel
  have hz' : h'' * z * h''⁻¹ = z := hcomm.mul_inv_cancel
  have hd'2 : orderOf (h''⁻¹ * d * h'') = 2 := by rw [orderOf_conjugate_eq, hd2]
  have hd'z : h''⁻¹ * d * h'' ≠ z := by
    intro heq
    apply hdz
    calc d = h'' * (h''⁻¹ * d * h'') * h''⁻¹ := by group
      _ = h'' * z * h''⁻¹ := by rw [heq]
      _ = z := hz'
  have hd'lj : h''⁻¹ * d * h'' ∈ Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m := hPP ▸ c''.h_t
  have hd' : h''⁻¹ * d * h'' ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
    sec5_mem_delta_of_pair h514 c hlm hd'2 hd'z hd'lj
  have hlayer : layerC5 (h''⁻¹ * d * h'') = CFSG.conjugate (layerC5 d) h'' :=
    sec5b517_layerC5_conj d h''
  have c3 : Sec5HCtx G (h''⁻¹ * d * h'') (layerC5 (h''⁻¹ * d * h'')) (CFSG.conjugate S'' h'')
      z (h''⁻¹ * r'' * h'') (CFSG.conjugate B'' h'') (CFSG.conjugate A'' h'')
      (CFSG.conjugate P₁ h'') (CFSG.conjugate P₂ h'') (h''⁻¹ * h'' * h'') := by
    have h := sec5HCtx_conj c'' h''
    rw [← hlayer, hz] at h
    exact h
  have hQ := sec5_pockets_eq h514 hF2 hb c hlm hij (Ne.symm hli) (Ne.symm hmi)
    (Ne.symm hlj) (Ne.symm hmj) hd'2 hd'z hd'lj c3
  have hquad := sec5_gamma_eq_quad (K₁ := K₁) (K₂ := K₂) (h := h) hij hlm hli hlj hmi hmj
  rw [hquad]
  unfold Gamma5
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hQ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    · rw [h3, h4]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

end CFSG.OddStandard.SmallF3.Omega
