module

public import CFSG.LieType.ChevTwo.OppCl.SLInduces
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section UnitaryAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem lineNormalizer_eq_semilinearPointGroup' (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f ∨ 2 ≤ r) (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) :
    lineNormalizer h r ε = semilinearPointGroup h r ε := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | hr3
  · obtain rfl : ε = 1 := by omega
    exact (unitary_rank_one_permutation_normalizer h (hq.resolve_right (by omega))).1
  · exact (unitary_rank_two_permutation_normalizer h hε).1
  · exact (unitary_higher_permutation_normalizer h hr3 hε).1

theorem semilinearAutHom_surjective' (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hq : 2 < p ^ f ∨ 2 ≤ r) (hn : 3 ≤ 2 * r + ε) :
    Function.Surjective (semilinearAutHom h hr hε) := by
  intro α
  have hmem : linePerm h hr hε α ∈ semilinearPointGroup h r ε := by
    rw [← lineNormalizer_eq_semilinearPointGroup' h hq hr hε hn, ← range_linePerm h hr hε]
    exact ⟨α, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, linePerm_injective h hr hε ?_⟩
  rw [linePerm_semilinearAutHom, hx]

theorem exists_isometry_hypPSU' (h : UnitaryFieldData p f K) (hq : 2 < p ^ f ∨ 2 ≤ r)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (hypPSU h r ε)) :
    ∃ (σ : K ≃+* K) (B : GL (HypIndex r ε) K),
      ((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
          (B : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K ∧
        ∀ g : hypSU h r ε, ∃ hg : B * glAut σ (g : GL (HypIndex r ε) K) * B⁻¹ ∈ hypSU h r ε,
          β (hypProj h r ε g) = hypProj h r ε ⟨_, hg⟩ := by
  obtain ⟨x₀, rfl⟩ := semilinearAutHom_surjective' h hr hε hq hn β
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h hr hε hn x₀
  refine ⟨(x : SemiGL (HypIndex r ε) K).right, (x : SemiGL (HypIndex r ε) K).left, hxU,
    fun g => ⟨conj_mem_hypSU x.2 g, ?_⟩⟩
  rw [← hxΦ]
  exact semilinearAutHom_apply h hr hε x g

theorem exists_unitary_semilinear_psu' (h : UnitaryFieldData p f K) (hq : 2 < p ^ f ∨ 2 ≤ r)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (unitaryPSU h (2 * r + ε))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin (2 * r + ε)) K),
      ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map h.bar)ᵀ *
          (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = 1 ∧
        ∀ g : unitarySU p f K (2 * r + ε),
          ∃ hg : A * glAut σ (g : GL (Fin (2 * r + ε)) K) * A⁻¹ ∈ unitarySU p f K (2 * r + ε),
            β (unitaryProj h (2 * r + ε) g) = unitaryProj h (2 * r + ε) ⟨_, hg⟩ := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set e := hypProjTransport h hR
  obtain ⟨σ, B, hB, hBg⟩ := exists_isometry_hypPSU' h hq hr hε hn ((e.trans β).trans e.symm)
  refine ⟨σ, semiTransportGL hR B σ, semiTransportGL_unitary hR hB σ, fun g' => ?_⟩
  set g := (hypTransport h hR).symm g'
  have hg' : hypTransport h hR g = g' := MulEquiv.apply_symm_apply _ _
  obtain ⟨hg, hα⟩ := hBg g
  have hconj : transportGL hR (B * glAut σ (g : GL (HypIndex r ε) K) * B⁻¹) =
      semiTransportGL hR B σ * glAut σ (g' : GL (Fin (2 * r + ε)) K) *
        (semiTransportGL hR B σ)⁻¹ := by
    rw [transportGL_conj, ← hg']
    rfl
  have hmem := transportGL_mem hR ⟨_, hg⟩
  rw [hconj] at hmem
  refine ⟨hmem, ?_⟩
  have h1 : unitaryProj h (2 * r + ε) g' = e (hypProj h r ε g) := by
    rw [hypProjTransport_hypProj, hg']
  have h2 : e.symm (β (e (hypProj h r ε g))) = hypProj h r ε ⟨_, hg⟩ := hα
  rw [h1, ← e.apply_symm_apply (β (e (hypProj h r ε g))), h2, hypProjTransport_hypProj]
  congr 1
  exact Subtype.ext hconj

end UnitaryAut

section Form

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem ringEquiv_unitaryInvolution_comm (σ : F ≃+* F) (c : F) :
    σ (unitaryInvolution F p f c) = unitaryInvolution F p f (σ c) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

theorem unitaryForm_β_ringEquiv (hK : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F) {n : ℕ}
    (u v : Fin n → F) :
    (unitaryForm p f hK n).β (fun i => σ (u i)) (fun i => σ (v i)) =
      σ ((unitaryForm p f hK n).β u v) := by
  simp only [unitaryForm_β, map_sum, map_mul, ringEquiv_unitaryInvolution_comm]

end Form

section Main

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem induced_PSU_aux (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ)
    (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n) (hq : 2 < 2 ^ f ∨ 4 ≤ n)
    (α : MulAut (StatedProj (StatedSU n (2 ^ f) F))) :
    ∃ s : Equiv.Perm (Fin n → F), s ∈ semilinGroup F (Fin n → F) ∧
      SemiIso (unitaryForm 2 f hK n) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ f) F)))
        (natRep (StatedSU n (2 ^ f) F)) s α := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := F)
      rw [hK] at this
      simp at this
    · exact hf
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 1 ≤ r := by omega
  have hq' : 2 < 2 ^ f ∨ 2 ≤ r := by
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (by omega)
  have hn1 : 1 ≤ 2 * r + ε := by omega
  obtain ⟨σ, A, hAu, hA⟩ := exists_unitary_semilinear_psu' h hq' hr hε hn
    (MulAut.congr (unitaryPSUEquiv h hn1).symm α)
  have hAu' : ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) F).map
      (unitaryInvolution F 2 f))ᵀ * (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) F) = 1 := by
    have hfun : (⇑(unitaryInvolution F 2 f) : F → F) = ⇑h.bar :=
      funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
    rw [hfun]
    exact hAu
  refine ⟨semilinMap A σ, semilinMap_mem A σ, ⟨σ, fun u v => ?_⟩,
    induces_of_conj _ A σ α fun g => ?_⟩
  · rw [semilinMap_apply, semilinMap_apply,
      (unitaryForm_preserves_iff hK _).mpr hAu' (fun i => σ (u i)) (fun i => σ (v i)),
      unitaryForm_β_ringEquiv]
  · obtain ⟨hg, hβ⟩ := hA g
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · rw [Subgroup.coe_mk, Units.val_mul, Units.val_mul, coe_glAut]
    · have h3 := congrArg (unitaryPSUEquiv h hn1) hβ
      simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply, unitaryPSUEquiv_unitaryProj] at h3
      exact h3

end Main

end CFSG.LieType.ChevTwo.OppCl
