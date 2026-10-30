module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STEven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec9ci_irred_F (h6 : Module.finrank (ZMod 3) V = 6) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {F : Subgroup (ProjSim Q)}
    (hb : IsEvenFrame b (F.comap (phiSim Q)))
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f) (j : Fin n)
    (F' : Subgroup (ProjSim Q)) (hF'F : F' ≤ F)
    (hinv : ∀ u v w z : Fin n, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      u ≠ j → v ≠ j → w ≠ j → z ≠ j →
      ∃ g : OGroup Q, (∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) =
        b ((Equiv.swap u v * Equiv.swap w z) i)) ∧
        ∀ f ∈ F', phiSim Q g * f * (phiSim Q g)⁻¹ ∈ F') :
    F' = ⊥ ∨ F' = F := by
  have hn6 : n = 6 := by
    have h := Module.finrank_eq_card_basis b
    rw [h6, Fintype.card_fin] at h
    exact h.symm
  have hpre : ∀ f ∈ F, ∃ (t : OGroup Q) (S : Finset (Fin n)), phiSim Q t = f ∧ Even S.card ∧
      ∀ i, (t : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ S then (-1 : ZMod 3) else 1) • b i := by
    intro f hf
    by_cases h1 : f = 1
    · exact ⟨1, ∅, by rw [h1, map_one], by simp, fun i => by simp⟩
    · obtain ⟨t, -, htf⟩ := hlift f hf h1
      have htFt : t ∈ F.comap (phiSim Q) := by
        rw [Subgroup.mem_comap, htf]
        exact hf
      obtain ⟨S, hSe, hSd⟩ := (IsEvenFrame.mem_iff hb).mp htFt
      exact ⟨t, S, htf, hSe, hSd⟩
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Set (Finset (Fin n)), ∀ S, S ∈ 𝒮 ↔ (Even S.card ∧
      ∃ d : OGroup Q, (∀ i, (d : V ≃ₗ[ZMod 3] V) (b i) =
        (if i ∈ S then (-1 : ZMod 3) else 1) • b i) ∧ phiSim Q d ∈ F') :=
    ⟨{S | Even S.card ∧ ∃ d : OGroup Q, (∀ i, (d : V ≃ₗ[ZMod 3] V) (b i) =
        (if i ∈ S then (-1 : ZMod 3) else 1) • b i) ∧ phiSim Q d ∈ F'}, fun S => Iff.rfl⟩
  have hev : ∀ S ∈ 𝒮, Even S.card := fun S hS => ((h𝒮 S).mp hS).1
  have hsd : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, symmDiff S S' ∈ 𝒮 := by
    intro S hS S' hS'
    obtain ⟨hSe, d, hd, hdF⟩ := (h𝒮 S).mp hS
    obtain ⟨hSe', d', hd', hdF'⟩ := (h𝒮 S').mp hS'
    refine (h𝒮 _).mpr ⟨?_, d * d', sec9g_mul_diag hd hd', ?_⟩
    · have h1 := Finset.card_union_add_card_inter S S'
      have h2 : (symmDiff S S').card = (S ∪ S').card - (S ∩ S').card := by
        rw [symmDiff_eq_sup_sdiff_inf]
        exact Finset.card_sdiff_of_subset Finset.inter_subset_union
      rw [h2]
      rw [Nat.even_iff] at hSe hSe' ⊢
      omega
    · rw [map_mul]
      exact F'.mul_mem hdF hdF'
  have hcompl : ∀ S ∈ 𝒮, Sᶜ ∈ 𝒮 := by
    intro S hS
    obtain ⟨hSe, d, hd, hdF⟩ := (h𝒮 S).mp hS
    refine (h𝒮 _).mpr ⟨?_, piOrth Q * d, ?_, ?_⟩
    · rw [Finset.card_compl, Fintype.card_fin]
      have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
      rw [Nat.even_iff] at hSe ⊢
      omega
    · intro i
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hd i, map_smul, coe_piOrth_apply]
      by_cases hi : i ∈ S <;> simp [hi]
    · rw [map_mul, (phiSim_eq_one_iff).mpr (Or.inr rfl), one_mul]
      exact hdF
  have hperm : ∀ u v w z : Fin n, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      u ≠ j → v ≠ j → w ≠ j → z ≠ j →
      ∀ S ∈ 𝒮, S.map (Equiv.swap u v * Equiv.swap w z).toEmbedding ∈ 𝒮 := by
    intro u v w z huv huw huz hvw hvz hwz huj hvj hwj hzj S hS
    obtain ⟨g, hg, hgF⟩ := hinv u v w z huv huw huz hvw hvz hwz huj hvj hwj hzj
    obtain ⟨hSe, d, hd, hdF⟩ := (h𝒮 S).mp hS
    refine (h𝒮 _).mpr ⟨?_, g * d * g⁻¹, sec9ci_perm_conj_diag hg hd, ?_⟩
    · rw [Finset.card_map]
      exact hSe
    · rw [map_mul, map_mul, map_inv]
      exact hgF _ hdF
  by_cases hbot : F' = ⊥
  · exact Or.inl hbot
  right
  have hex : ∃ f' ∈ F', f' ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall F').mpr hcon)
  obtain ⟨f', hf'F', hf'1⟩ := hex
  obtain ⟨t, S, htf, hSe, hSd⟩ := hpre f' (hF'F hf'F')
  have hS𝒮 : S ∈ 𝒮 := (h𝒮 S).mpr ⟨hSe, t, hSd, by rw [htf]; exact hf'F'⟩
  have hSne : S ≠ ∅ := by
    rintro rfl
    apply hf'1
    rw [← htf, show t = 1 from sec9ci_ext (b := b) fun i => by rw [hSd i]; simp, map_one]
  have hSuniv : S ≠ Finset.univ := by
    rintro rfl
    apply hf'1
    rw [← htf, show t = piOrth Q from sec9ci_ext (b := b) fun i => by
      rw [hSd i, coe_piOrth_apply]; simp, (phiSim_eq_one_iff).mpr (Or.inr rfl)]
  have hall := sec9ci_comb hn6 j 𝒮 hev hsd hcompl hperm ⟨S, hS𝒮, hSne, hSuniv⟩
  refine le_antisymm hF'F (fun f hf => ?_)
  obtain ⟨t', S', htf', hSe', hSd'⟩ := hpre f hf
  obtain ⟨-, d, hd, hdF⟩ := (h𝒮 S').mp (hall S' hSe')
  have htd : t' = d := sec9ci_ext (b := b) fun i => by rw [hSd' i, hd i]
  rw [← htf', htd]
  exact hdF

end CFSG.OddStandard.SmallF3.Omega
