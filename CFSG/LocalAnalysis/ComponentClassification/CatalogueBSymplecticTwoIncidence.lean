module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoParabolics

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Matrix Module Submodule Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher

variable {K : Type} [Field K]

theorem projStabilizer_mem_spExtremalParabolics [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) :
    projStabilizer 2 K W ∈ spExtremalParabolics 2 K p :=
  (extremal_parabolics (K := K) p rfl).2.2.2.2.2.1.mapsTo ⟨hW0, hW⟩

theorem exists_eq_projStabilizer [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hM : M ∈ spExtremalParabolics 2 K p) :
    ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ ∧
      IsTotallyIsotropic (pairedSympForm K 2) W ∧ M = projStabilizer 2 K W := by
  obtain ⟨W, hW, rfl⟩ := (extremal_parabolics (K := K) p rfl).2.2.2.2.2.1.surjOn hM
  exact ⟨W, hW.1, hW.2, rfl⟩

theorem eq_map_flag_of_le {r : ℕ} {g : StatedSp r K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W)
    (h : (projBorel r K).map (MulAut.conj (proj r K g)).toMonoidHom ≤ projStabilizer r K W) :
    W = (flag r K (finrank K W)).map (spAct g) := by
  set X := W.map (spAct g⁻¹) with hX
  have hB : borelSubgroup r K ≤ stabilizer r K X := by
    intro b hb
    have h1 : proj r K (g * b * g⁻¹) ∈ projStabilizer r K W := by
      refine h ⟨proj r K b, ⟨b, hb, rfl⟩, ?_⟩
      change proj r K g * proj r K b * (proj r K g)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
    rw [← Subgroup.mem_comap, comap_projStabilizer] at h1
    rw [hX, stabilizer_map_spAct]
    refine ⟨g * b * g⁻¹, h1, ?_⟩
    change g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b
    group
  have hXiso : IsTotallyIsotropic (pairedSympForm K r) X := isTotallyIsotropic_map_spAct g⁻¹ hW
  have hXU : ∀ u ∈ unipotent r K, ∀ v ∈ X,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ X := by
    intro u hu v hv
    have := mem_stabilizer.mp (hB (unipotent_le_borelSubgroup hu))
    rw [← this]
    exact ⟨v, hv, rfl⟩
  obtain ⟨d, hd, hXd⟩ :=
    ((unitriangular_invariant_isotropic_subspaces (r := r) (K := K)).2.1 X).mp ⟨hXiso, hXU⟩
  have hdim : finrank K X = finrank K W := finrank_map_spAct g⁻¹ W
  rw [hXd, finrank_flag (by omega)] at hdim
  rw [← hdim, ← hXd, hX, ← map_spAct_mul, mul_inv_cancel, map_spAct_one]

theorem le_or_le_of_le_inf [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W W' : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW : IsTotallyIsotropic (pairedSympForm K 2) W)
    (hW' : IsTotallyIsotropic (pairedSympForm K 2) W')
    {B₀ : Subgroup (StatedProj (StatedSp 2 K))}
    (hB₀ : B₀ ∈ LinearFlag.sylowNormalizers (StatedProj (StatedSp 2 K)) p)
    (hle : B₀ ≤ projStabilizer 2 K W ⊓ projStabilizer 2 K W') : W ≤ W' ∨ W' ≤ W := by
  have hsyl : LinearFlag.sylowNormalizers (StatedProj (StatedSp 2 K)) p = _ :=
    spSylowNormalizers_eq (K := K) p (by norm_num)
  rw [hsyl] at hB₀
  obtain ⟨x, rfl⟩ := hB₀
  obtain ⟨g, rfl⟩ := proj_surjective x
  have h1 := eq_map_flag_of_le hW (hle.trans inf_le_left)
  have h2 := eq_map_flag_of_le hW' (hle.trans inf_le_right)
  rcases le_total (finrank K W) (finrank K W') with hd | hd
  · left
    rw [h1, h2]
    exact map_mono (flag_mono hd)
  · right
    rw [h1, h2]
    exact map_mono (flag_mono hd)

theorem exists_le_inf_of_lt [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W W' : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hW' : IsTotallyIsotropic (pairedSympForm K 2) W') (hlt : W < W') :
    ∃ B₀ ∈ LinearFlag.sylowNormalizers (StatedProj (StatedSp 2 K)) p,
      B₀ ≤ projStabilizer 2 K W ⊓ projStabilizer 2 K W' := by
  classical
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  have h1 := one_le_finrank_of_ne_bot hW0
  have h2 := finrank_le_two hW'
  have hW1 : finrank K W = 1 := by omega
  have hW2 : finrank K W' = 2 := by omega
  set F : ℕ → Submodule K (Fin 2 ⊕ Fin 2 → K) := fun i => if i = 0 then ⊥ else if i = 1 then W
    else W' with hF
  have hF1 : F 1 = W := by simp [hF]
  have hF2 : F 2 = W' := by simp [hF]
  have hFflag : IsCompleteIsotropicFlag (pairedSympForm K 2) 2 F := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · interval_cases i
      · simp [hF]
      · rw [hF1, hW1]
      · rw [hF2, hW2]
    · interval_cases i
      · simp [hF]
      · rw [hF1, hF2]
        exact hlt.le
    · interval_cases i
      · rw [show F 0 = ⊥ by simp [hF]]
        intro x hx y _
        rw [(Submodule.mem_bot K).mp hx, map_zero, LinearMap.zero_apply]
      · rw [hF1]
        exact hW'.mono hlt.le
      · rw [hF2]
        exact hW'
  refine ⟨projIsoFlagStabilizer 2 K F, ?_, le_inf ?_ ?_⟩
  · rw [(sylow_normalizers (K := K) p (by norm_num : 1 ≤ 2)).2.2.1]
    exact ⟨F, hFflag, rfl⟩
  · rw [projIsoFlagStabilizer, projStabilizer, ← hF1]
    exact map_mono fun g hg => mem_isoFlagStabilizer.mp hg 1 le_rfl (by norm_num)
  · rw [projIsoFlagStabilizer, projStabilizer, ← hF2]
    exact map_mono fun g hg => mem_isoFlagStabilizer.mp hg 2 (by norm_num) le_rfl

theorem adj_iff_lt_or_lt [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W W' : Submodule K (Fin 2 ⊕ Fin 2 → K)} {M N : spExtremalParabolics 2 K p} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) (hW0' : W' ≠ ⊥)
    (hW' : IsTotallyIsotropic (pairedSympForm K 2) W')
    (hM : (M : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W)
    (hN : (N : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W') :
    (incidenceGraph K p).Adj M N ↔ W < W' ∨ W' < W := by
  rw [LinearFlag.parabolicGraph_adj, hM, hN]
  have hMN : M = N ↔ W = W' := by
    rw [← Subtype.coe_inj, hM, hN]
    exact ⟨projStabilizer_inj hW0 hW hW0' hW', fun h => h ▸ rfl⟩
  rw [Ne, hMN]
  constructor
  · rintro ⟨hne, B₀, hB₀, hle⟩
    rcases le_or_le_of_le_inf p hW hW' hB₀ hle with h | h
    · exact Or.inl (lt_of_le_of_ne h hne)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne))
  · rintro (h | h)
    · exact ⟨h.ne, exists_le_inf_of_lt p hW0 hW' h⟩
    · obtain ⟨B₀, hB₀, hle⟩ := exists_le_inf_of_lt p hW0' hW h
      exact ⟨h.ne', B₀, hB₀, by rwa [inf_comm]⟩

theorem adj_iff_le [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {L W : Submodule K (Fin 2 ⊕ Fin 2 → K)} {M N : spExtremalParabolics 2 K p}
    (hL : finrank K L = 1) (hW : IsTotallyIsotropic (pairedSympForm K 2) W)
    (hW2 : finrank K W = 2) (hM : (M : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K L)
    (hN : (N : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W) :
    (incidenceGraph K p).Adj M N ↔ L ≤ W := by
  rw [adj_iff_lt_or_lt p (ne_bot_of_finrank_pos (by omega))
    (isTotallyIsotropic_of_finrank_eq_one hL) (ne_bot_of_finrank_pos (by omega)) hW hM hN]
  constructor
  · rintro (h | h)
    · exact h.le
    · have := Submodule.finrank_lt_finrank_of_lt h
      omega
  · intro h
    refine Or.inl (lt_of_le_of_ne h fun hLW => ?_)
    rw [hLW, hW2] at hL
    exact absurd hL (by norm_num)

theorem common_normalizer_incidence [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    (∀ (W W' : Submodule K (Fin 2 ⊕ Fin 2 → K)) (M N : spExtremalParabolics 2 K p),
      W ≠ ⊥ → IsTotallyIsotropic (pairedSympForm K 2) W → W' ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K 2) W' →
      (M : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W →
      (N : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W' →
      ((incidenceGraph K p).Adj M N ↔ W < W' ∨ W' < W)) ∧
    (∀ M N : spExtremalParabolics 2 K p, (incidenceGraph K p).Adj M N →
      ((M : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K ∧
          (N : Subgroup (StatedProj (StatedSp 2 K))) ∈ planeParabolics K) ∨
        ((M : Subgroup (StatedProj (StatedSp 2 K))) ∈ planeParabolics K ∧
          (N : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K)) ∧
    ∀ (L W : Submodule K (Fin 2 ⊕ Fin 2 → K)) (M N : spExtremalParabolics 2 K p),
      finrank K L = 1 → IsTotallyIsotropic (pairedSympForm K 2) W → finrank K W = 2 →
      (M : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K L →
      (N : Subgroup (StatedProj (StatedSp 2 K))) = projStabilizer 2 K W →
      ((incidenceGraph K p).Adj M N ↔ L ≤ W) := by
  refine ⟨fun W W' M N hW0 hW hW0' hW' hM hN => adj_iff_lt_or_lt p hW0 hW hW0' hW' hM hN,
    fun M N hadj => ?_, fun L W M N hL hW hW2 hM hN => adj_iff_le p hL hW hW2 hM hN⟩
  obtain ⟨W, hW0, hW, hMW⟩ := exists_eq_projStabilizer p M.2
  obtain ⟨W', hW0', hW', hNW'⟩ := exists_eq_projStabilizer p N.2
  have h1 := one_le_finrank_of_ne_bot hW0
  have h1' := one_le_finrank_of_ne_bot hW0'
  have h2 := finrank_le_two hW
  have h2' := finrank_le_two hW'
  rcases (adj_iff_lt_or_lt p hW0 hW hW0' hW' hMW hNW').mp hadj with h | h
  · have := Submodule.finrank_lt_finrank_of_lt h
    exact Or.inl ⟨⟨W, by omega, hMW⟩, ⟨W', hW', by omega, hNW'⟩⟩
  · have := Submodule.finrank_lt_finrank_of_lt h
    exact Or.inr ⟨⟨W, hW, by omega, hMW⟩, ⟨W', by omega, hNW'⟩⟩

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
