module

public import CFSG.GH74.Generic.BProg.B3.S3T5Obs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

namespace W

open Equiv Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Th2.Bal

theorem a7_outer_oddCore_eq_bot {K : Type} [Group K] [Finite K] (φ : K ≃* alternatingGroup (Fin 7))
    {H : Subgroup (MulAut K)} (hH : (MulAut.conj : K →* MulAut K).range ≤ H) {g : H}
    (hg2 : g * g = 1) (hout : (g : MulAut K) ∉ (MulAut.conj : K →* MulAut K).range) :
    CFSG.Assembly.Dichotomy.involutionOddCore g = ⊥ := by
  classical
  have hinj := a7Theta_conj_injective φ
  set σ : Perm (Fin 7) := (a7Theta φ).symm (g : MulAut K) with hσ
  have hg : (g : MulAut K) = a7Theta φ σ := by rw [hσ, MulEquiv.apply_symm_apply]
  have hσ2 : σ * σ = 1 := by
    apply (a7Theta φ).injective
    rw [map_mul, ← hg, map_one]
    exact congrArg Subtype.val hg2
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hout
    rw [hg, h1, map_one]
    exact one_mem _
  have hσA : σ ∉ alternatingGroup (Fin 7) := by
    intro hA
    apply hout
    rw [hg]
    have := a7Theta_even φ ⟨σ, hA⟩
    rw [show ((⟨σ, hA⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ from rfl] at this
    rw [this]
    exact ⟨_, rfl⟩
  have hsign : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hσA
    · exact h
  by_contra hne
  have hW : pPrimeCoreOf 2 (H ⊓ centralizer ({(g : MulAut K)} : Set (MulAut K))) ≠ ⊥ :=
    fun h => hne (involutionOddCore_eq_bot_of_pPrimeCoreOf H g h)
  rw [show (g : MulAut K) = a7Theta φ σ from hg] at hW
  obtain ⟨W', hW'ne, hle, hodd, hnorm⟩ :=
    exists_normal_odd_fixed hinj (fun w hw => a7_odd_orderOf_mem_innAut φ hw) hH hW
  obtain ⟨ρ0⟩ := a7_fixed_equiv φ σ
  apply hW'ne
  rcases A7.involution_cycleType σ (by rw [pow_two]; exact hσ2) hσ1 with h | h | h
  · obtain ⟨ρ1⟩ := A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr h)
    refine eq_bot_of_odd_normal_fixed hle hodd hnorm ?_
    intro W hWn hWodd
    exact eq_bot_of_normal_odd_of_equiv_perm5 (ρ0.trans ρ1) W hWodd
  · exfalso
    have := Equiv.Perm.sign_of_cycleType σ
    rw [h, hsign] at this
    have h6 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2} : Multiset ℕ) +
        Multiset.card ({2, 2} : Multiset ℕ)) = 1 := Even.neg_one_pow (by decide)
    rw [h6] at this
    exact absurd this (by decide)
  · obtain ⟨ρ1⟩ := A7.centralizer_A7_two_two_two_equiv h
    refine eq_bot_of_odd_normal_fixed hle hodd hnorm ?_
    intro W hWn hWodd
    exact eq_bot_of_normal_odd_of_equiv_perm4 (ρ0.trans ρ1) W hWodd

theorem exists_inner_of_twoA7 {G : Type} [Group G] [Finite G] {B : Subgroup G} {b : G}
    {D J : Subgroup G} (h : Obs52 B b D J) (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hcov : IsDoubleCoverOfAlt (kBar J) 7) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    ∃ q : kBar J, Th2.Obs.barAct J ⟨d, h.D_norm hdD⟩ = MulAut.conj q := by
  classical
  obtain ⟨-, hDel, -⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  obtain ⟨c, hc, hcs⟩ := exists_move h hBel
  have hcM : c ∈ normalizer (J : Set G) := AG_inf_le_normalizer h hc
  have hdM : d ∈ normalizer (J : Set G) := h.D_norm hdD
  set X : Type := kBar J with hX
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ρ : ↥M →* MulAut X := Th2.Obs.barAct J with hρ
  set Z : Subgroup (MulAut X) := ρ.range with hZ
  set F : Subgroup ↥Z := (D.subgroupOf M).map ρ.rangeRestrict with hF
  have hmem : ρ.rangeRestrict ⟨c, hcM⟩ ∈ CFSG.ClassicalInvolution.Balance.deltaCore F :=
    barAct_mem_deltaCore h hc hcM
  have hdF : ρ.rangeRestrict ⟨d, hdM⟩ ∈ F := Subgroup.mem_map_of_mem _ (show (⟨d, hdM⟩ : ↥M) ∈
    D.subgroupOf M from hdD)
  have hf1 : ρ.rangeRestrict ⟨d, hdM⟩ ≠ 1 := by
    intro h1
    have h2 : ρ ⟨d, hdM⟩ = 1 := congrArg Subtype.val h1
    exact h.D_faith d hdD hd1 ((Th2.Obs.barAct_eq_one_iff ⟨d, hdM⟩).1 h2)
  have hco := (CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hmem) _ hdF hf1
  have : Group.IsPerfect X := hcov.1.1
  set ψ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X with hψ
  have hψinj : Function.Injective ψ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X
  obtain ⟨e⟩ := hcov.2.2
  set H' : Subgroup (MulAut (X ⧸ center X)) := Z.map ψ with hH'
  have hInn : (MulAut.conj : (X ⧸ center X) →* MulAut (X ⧸ center X)).range ≤ H' := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective k
    exact ⟨MulAut.conj q, Th2.Obs.innAut_le_range_barAct J ⟨q, rfl⟩, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj (G := X) q⟩
  set θ : ↥Z →* ↥H' := ψ.subgroupMap Z with hθ
  have hθs : Function.Surjective θ := ψ.subgroupMap_surjective Z
  have hf2 : ρ.rangeRestrict ⟨d, hdM⟩ * ρ.rangeRestrict ⟨d, hdM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, hdM⟩ : ↥M) * ⟨d, hdM⟩ = 1 := Subtype.ext (hDsq d hdD)
    rw [this, map_one]
  have hθco := CFSG.ClassicalInvolution.Balance.map_involutionOddCore_le θ hθs
    (CFSG.ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one hf2)
    (Subgroup.mem_map_of_mem θ hco)
  by_contra hno
  push Not at hno
  have hout : ((θ (ρ.rangeRestrict ⟨d, hdM⟩) : ↥H') : MulAut (X ⧸ center X)) ∉
      (MulAut.conj : (X ⧸ center X) →* MulAut (X ⧸ center X)).range := by
    rintro ⟨k, hk⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective k
    apply hno q
    apply hψinj
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj (G := X) q]
    exact hk.symm
  have hθ2 : θ (ρ.rangeRestrict ⟨d, hdM⟩) * θ (ρ.rangeRestrict ⟨d, hdM⟩) = 1 := by
    rw [← map_mul, hf2, map_one]
  have hbot := a7_outer_oddCore_eq_bot e hInn hθ2 hout
  rw [hbot, Subgroup.mem_bot] at hθco
  have h1 : ψ (ρ ⟨c, hcM⟩) = 1 := congrArg Subtype.val hθco
  have h2 : ρ ⟨c, hcM⟩ = 1 := hψinj (h1.trans (map_one ψ).symm)
  exact hcs ((Th2.Obs.barAct_eq_one_iff ⟨c, hcM⟩).1 h2)

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3
