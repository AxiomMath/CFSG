module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule Subgroup SymplecticFlag CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem flagStabilizer_singleton (d : ℕ) :
    flagStabilizer r K {d} = stabilizer r K (flag r K d) := by
  ext g
  rw [mem_flagStabilizer]
  simp

theorem projStabilizer_map_spAct (g : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    projStabilizer r K (W.map (spAct g)) =
      (projStabilizer r K W).map (MulAut.conj (proj r K g)).toMonoidHom := by
  rw [projStabilizer, projStabilizer, stabilizer_map_spAct, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem weylRep_notMem_stabilizer (k : Fin r) :
    weylRep K k ∉ stabilizer r K (flag r K ((k : ℕ) + 1)) := by
  rw [← flagStabilizer_singleton]
  exact fun h => ((subflag_generation (K := K) {(k : ℕ) + 1}
    (fun i hi => by rw [Set.mem_singleton_iff.mp hi]; exact k.2)).2.1 k).mp h rfl

theorem stabilizer_flag_ne_top {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    stabilizer r K (flag r K d) ≠ ⊤ := fun h => by
  have := weylRep_notMem_stabilizer (K := K) (r := r) ⟨d - 1, by omega⟩
  rw [show ((⟨d - 1, by omega⟩ : Fin r) : ℕ) + 1 = d by simp; omega, h] at this
  exact this (mem_top _)

theorem borelSubgroup_le_stabilizer_flag {d : ℕ} (hdr : d ≤ r) :
    borelSubgroup r K ≤ stabilizer r K (flag r K d) := by
  rw [← flagStabilizer_singleton]
  exact borelSubgroup_le_flagStabilizer fun i hi => by rw [Set.mem_singleton_iff.mp hi]; exact hdr

theorem eq_of_stabilizer_flag_le {d : ℕ} (hdr : d ≤ r) (A : Subgroup (StatedSp r K))
    (hA : stabilizer r K (flag r K d) ≤ A) : A = stabilizer r K (flag r K d) ∨ A = ⊤ := by
  obtain ⟨hAI, -⟩ := borel_overgroups A ((borelSubgroup_le_stabilizer_flag hdr).trans hA)
  have hsub : borelCuts K A ⊆ {d} := by
    rintro e ⟨k, rfl, hnot⟩
    by_contra hed
    refine hnot (hA ?_)
    rw [← flagStabilizer_singleton]
    exact ((subflag_generation (K := K) {d} fun i hi => by
      rw [Set.mem_singleton_iff.mp hi]; exact hdr).2.1 k).mpr hed
  rcases Set.subset_singleton_iff_eq.mp hsub with h | h
  · right
    rw [hAI, h, flagStabilizer_empty]
  · left
    rw [hAI, h, flagStabilizer_singleton]

theorem isCoatom_projStabilizer_flag {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    IsCoatom (projStabilizer r K (flag r K d)) := by
  refine ⟨fun h => stabilizer_flag_ne_top (K := K) hd hdr ?_, fun M hM => ?_⟩
  · rw [← comap_projStabilizer, h, Subgroup.comap_top]
  · have hle : stabilizer r K (flag r K d) ≤ M.comap (proj r K) := by
      rw [← comap_projStabilizer]
      exact comap_mono hM.le
    rcases eq_of_stabilizer_flag_le hdr _ hle with h | h
    · refine absurd ?_ hM.ne'
      rw [projStabilizer, ← h, map_comap_eq_self_of_surjective proj_surjective]
    · rw [← map_comap_eq_self_of_surjective proj_surjective M, h,
        map_top_of_surjective _ proj_surjective]

theorem exists_map_flag_eq_of_isTotallyIsotropic {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW0 : W ≠ ⊥) (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    ∃ (d : ℕ) (g : StatedSp r K), 1 ≤ d ∧ d ≤ r ∧ (flag r K d).map (spAct g) = W := by
  set d := finrank K W
  have hdr : d ≤ r := finrank_le_of_isTotallyIsotropic SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate finrank_standard hW
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq (isCompleteIsotropicFlag_flag.2.2 d hdr) hW
    (by rw [finrank_flag (by omega)])
  exact ⟨d, g, hd, hdr, hg⟩

theorem isCoatom_projStabilizer {W : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) : IsCoatom (projStabilizer r K W) := by
  obtain ⟨d, g, hd, hdr, hg⟩ := exists_map_flag_eq_of_isTotallyIsotropic hW0 hW
  rw [← hg, projStabilizer_map_spAct]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj (proj r K g))) _).mpr
    (isCoatom_projStabilizer_flag hd hdr)

theorem eq_projStabilizer_of_isCoatom {M : Subgroup (StatedProj (StatedSp r K))} (hM : IsCoatom M)
    (hBM : projBorel r K ≤ M) : ∃ d, 1 ≤ d ∧ d ≤ r ∧ M = projStabilizer r K (flag r K d) := by
  set A := M.comap (proj r K) with hAdef
  have hBA : borelSubgroup r K ≤ A := by
    rw [hAdef, ← Subgroup.map_le_iff_le_comap]
    exact hBM
  have hMA : M = A.map (proj r K) := (map_comap_eq_self_of_surjective proj_surjective M).symm
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  obtain ⟨d, hdmem⟩ : (borelCuts K A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hM.1
    rw [hMA, hAI, h, flagStabilizer_empty, map_top_of_surjective _ proj_surjective]
  obtain ⟨hd, hdr⟩ := borelCuts_le A d hdmem
  refine ⟨d, hd, hdr, ?_⟩
  have hle : M ≤ projStabilizer r K (flag r K d) := by
    rw [hMA, projStabilizer]
    refine map_mono ?_
    rw [hAI, ← flagStabilizer_singleton]
    exact fun g hg => mem_flagStabilizer.mpr fun i hi =>
      mem_flagStabilizer.mp hg i ((Set.mem_singleton_iff.mp hi) ▸ hdmem)
  rcases hM.le_iff.mp hle with h | h
  · exact absurd h (isCoatom_projStabilizer_flag hd hdr).1
  · exact h.symm

theorem spSylowNormalizers_eq [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hr : 1 ≤ r) :
    spSylowNormalizers r K p = {B₀ | ∃ x : StatedProj (StatedSp r K),
      B₀ = (projBorel r K).map (MulAut.conj x).toMonoidHom} := by
  rw [spSylowNormalizers, (sylow_normalizers (K := K) p hr).2.2.1]
  ext B₀
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨g, hg⟩ := exists_map_flag_eq hF
    exact ⟨proj r K g, projIsoFlagStabilizer_eq_map_conj hg⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨fun i => (flag r K i).map (spAct g), ⟨fun i hi => ?_, fun i _ => map_mono
      (flag_mono (Nat.le_succ i)), fun i hi => ?_⟩,
      (projIsoFlagStabilizer_eq_map_conj fun i _ _ => rfl).symm⟩
    · rw [finrank_map_spAct, finrank_flag (by omega)]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
      exact isCompleteIsotropicFlag_flag.2.2 i hi x hx y hy

theorem eq_of_stabilizer_le {W W' : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) (hW0' : W' ≠ ⊥)
    (hW' : IsTotallyIsotropic (pairedSympForm K r) W')
    (hle : stabilizer r K W ≤ stabilizer r K W') : W' = W := by
  obtain ⟨d, g, hd, hdr, rfl⟩ := exists_map_flag_eq_of_isTotallyIsotropic hW0 hW
  have hle' : flagStabilizer r K {d} ≤ stabilizer r K (W'.map (spAct g⁻¹)) := by
    intro h hh
    rw [flagStabilizer_singleton] at hh
    have : g * h * g⁻¹ ∈ stabilizer r K W' := hle (by
      rw [stabilizer_map_spAct]
      exact ⟨h, hh, rfl⟩)
    rw [stabilizer_map_spAct]
    refine ⟨g * h * g⁻¹, this, ?_⟩
    change g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h
    group
  have hiso : IsTotallyIsotropic (pairedSympForm K r) (W'.map (spAct g⁻¹)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
    exact hW' x hx y hy
  rcases ((subflag_generation (K := K) {d} fun i hi => by
      rw [Set.mem_singleton_iff.mp hi]; exact hdr).2.2 _ hiso).mp hle' with h | ⟨i, hi, h⟩
  · exfalso
    rw [flag_zero] at h
    apply hW0'
    have := congrArg (Submodule.map (spAct g)) h
    rwa [← map_spAct_mul, mul_inv_cancel, map_spAct_one, Submodule.map_bot] at this
  · rw [Set.mem_singleton_iff.mp hi] at h
    rw [← h, ← map_spAct_mul, mul_inv_cancel, map_spAct_one]

theorem maximal_parabolics [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hr : 1 ≤ r) :
    spMaximalParabolics r K p = {M | ∃ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ ∧
      IsTotallyIsotropic (pairedSympForm K r) W ∧ M = projStabilizer r K W} ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K r) W → IsCoatom (projStabilizer r K W)) ∧
    (∀ W W' : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K r) W → W' ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K r) W' →
      projStabilizer r K W = projStabilizer r K W' → W = W') := by
  classical
  have hsyl : LinearFlag.sylowNormalizers (StatedProj (StatedSp r K)) p = _ :=
    spSylowNormalizers_eq (K := K) p hr
  refine ⟨?_, fun W h0 hW => isCoatom_projStabilizer h0 hW,
    fun W W' h0 hW h0' hW' hWW' => ?_⟩
  · ext M
    constructor
    · rintro ⟨hM, B₀, hB₀, hle⟩
      rw [hsyl] at hB₀
      obtain ⟨x, rfl⟩ := hB₀
      obtain ⟨g, rfl⟩ := proj_surjective x
      set e := MulEquiv.mapSubgroup (MulAut.conj (proj r K g)) with he
      have hM' : IsCoatom (e.symm M) := by
        rw [← OrderIso.isCoatom_iff e, OrderIso.apply_symm_apply]
        exact hM
      have hBM' : projBorel r K ≤ e.symm M := by
        rw [← e.le_iff_le, OrderIso.apply_symm_apply]
        exact hle
      obtain ⟨d, hd, hdr, hMd⟩ := eq_projStabilizer_of_isCoatom hM' hBM'
      refine ⟨(flag r K d).map (spAct g), ?_, ?_, ?_⟩
      · intro h0
        have := finrank_map_spAct g (flag r K d)
        rw [h0, finrank_bot, finrank_flag (by omega)] at this
        omega
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
        exact isCompleteIsotropicFlag_flag.2.2 d hdr x hx y hy
      · rw [projStabilizer_map_spAct, ← hMd]
        change M = e (e.symm M)
        rw [OrderIso.apply_symm_apply]
    · rintro ⟨W, h0, hW, rfl⟩
      refine ⟨isCoatom_projStabilizer h0 hW, ?_⟩
      obtain ⟨d, g, hd, hdr, hg⟩ := exists_map_flag_eq_of_isTotallyIsotropic h0 hW
      refine ⟨(projBorel r K).map (MulAut.conj (proj r K g)).toMonoidHom, ?_, ?_⟩
      · rw [hsyl]
        exact ⟨proj r K g, rfl⟩
      · rw [← hg, projStabilizer_map_spAct]
        exact map_mono (map_mono (borelSubgroup_le_stabilizer_flag hdr))
  · have hS : stabilizer r K W = stabilizer r K W' := by
      rw [← comap_projStabilizer, hWW', comap_projStabilizer]
    exact (eq_of_stabilizer_le h0 hW h0' hW' hS.le).symm

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
