module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorGlue
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorTransport
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainIso
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfectCentralizerBigQ
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfectCentralizerFixed
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CensusOpenNodes

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

theorem cube_scalar_data {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 1 ≤ n)
    (x : StatedSU n (2 ^ f) K) (hx : ((x : GL (Fin n) K)) ^ 3 ∈ StatedScalars (Fin n) K) :
    ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = (x : GL (Fin n) K) ^ 3 ∧ c ^ n = 1 ∧
      c ^ (2 ^ f + 1) = 1 := by
  obtain ⟨c, hc⟩ := hx
  have hsc : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ f) K := by
    rw [hc]; exact Subgroup.pow_mem _ x.2 3
  exact ⟨c, hc, (scalar_mem_statedSU_iff Nat.prime_two hK hn c).mp hsc⟩

theorem survivor_core [Finite K] [CharP K 2] {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hε : ε ≤ 1)
    (hn : 4 ≤ 2 * r + ε) {I : Set ℕ} (hIne : I.Nonempty) (hIsub : I ⊆ Set.Icc 1 r)
    (hshort : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ I → j₂ ∉ I → False)
    (htail : 2 ≤ r → r ∉ I → r - 1 ∉ I → False)
    {W : ℕ → Submodule K (Fin (2 * r + ε) → K)}
    (hWd : ∀ i ∈ I, Module.finrank K (W i) = i ∧ IsTotallyIsotropicSU (2 ^ 1) (W i))
    (hWm : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ 1) K))
    (hDtW : ∀ y ∈ Dt, ∀ i ∈ I, ∀ w ∈ W i,
      ((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w ∈ W i)
    (hDt : ⁅Dt, Dt⁆ = Dt) {d : StatedSU (2 * r + ε) (2 ^ 1) K} (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K)
    (hd3 : (d : GL (Fin (2 * r + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r + ε)) K)
    (hfree : ∀ H : Subgroup (StatedSU (2 * r + ε) (2 ^ 1) K), ⁅H, H⁆ = H →
      (∀ w ∈ H, Commute w d) → H = ⊥) :
    (r = 2 ∧ ε = 0 ∧ I = {2}) ∨ (r = 2 ∧ ε = 1 ∧ I = {2}) ∨
    (r = 3 ∧ ε = 0 ∧ I = {2}) ∨ (r = 3 ∧ ε = 0 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 0 ∧ I = {2, 3}) ∨
    (r = 3 ∧ ε = 1 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2}) := by
  classical
  have := h.charP
  have hK : Nat.card K = (2 ^ 1) ^ 2 := card_unitary h
  have hr2 : 2 ≤ r := by omega
  set S : Finset ℕ := (Finset.Icc 1 r).filter (· ∈ I) with hSdef
  have hSI : ∀ i, i ∈ S ↔ i ∈ I := fun i =>
    ⟨fun hi => (Finset.mem_filter.mp hi).2, fun hi => Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr (by simpa using hIsub hi), hi⟩⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hIne
    exact ⟨i, (hSI i).mpr hi⟩
  have hS'' : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r := fun i hi => by
    simpa using hIsub ((hSI i).mp hi)
  have hS' : ∀ i ∈ S, i ≤ r := fun i hi => (hS'' i hi).2
  obtain ⟨a, ha⟩ := exists_enumeration S (fun i hi => (hS'' i hi).1)
  have hshortS : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ S → j₂ ∉ S → False :=
    fun j₁ j₂ h1 h2 h3 h4 h5 => hshort j₁ j₂ h1 h2 h3 (fun hh => h4 ((hSI j₁).mpr hh))
      (fun hh => h5 ((hSI j₂).mpr hh))
  have htailS : 2 ≤ r → r ∉ S → r - 1 ∉ S → False :=
    fun h1 h2 h3 => htail h1 (fun hh => h2 ((hSI r).mpr hh)) (fun hh => h3 ((hSI (r - 1)).mpr hh))
  have hc : SUChain h (2 * r + ε) Dt S a W :=
    { enum := ha
      ne := hSne
      mono := fun i hi j hj hij => hWm i ((hSI i).mp hi) j ((hSI j).mp hj) hij
      dim := fun i hi => (hWd i ((hSI i).mp hi)).1
      iso := fun i hi v hv w hw =>
        (ToralCensus.isTotallyIsotropicSU_iff h (W i)).mp (hWd i ((hSI i).mp hi)).2 v hv w hw
      stab := fun y hy i hi w hw => hDtW y hy i ((hSI i).mp hi) w hw
      perf := hDt }
  have hlast := le_last_of_tail ha hSne hS' htailS hr2
  have htailb : 2 * r + ε - 2 * a S.card ≤ 3 := by omega
  by_cases hopen : ∃ j, 1 ≤ j ∧ j < r ∧ j ∉ I
  swap
  · exfalso
    push Not at hopen
    have hall : ∀ j, 1 ≤ j → j < r → j ∈ S := fun j h1 h2 => (hSI j).mpr (hopen j h1 h2)
    have hone := hc.eq_one_of_gaps_one
      (fun k hk1 hk2 => gap_eq_one_of_no_short_open ha hS' hall hk1 hk2) htailb d hd
    exact hds (by rw [hone, Subgroup.coe_one]; exact Subgroup.one_mem _)
  obtain ⟨j₀, hj1, hjr, hj₀⟩ := hopen
  obtain ⟨k₀, hk1, hk2, hplane, hother⟩ := exists_unique_plane_piece ha hSne hS'' hshortS htailS
    hj1 hjr (fun hh => hj₀ ((hSI j₀).mp hh))
  obtain ⟨c, hcd, hcn, hc3⟩ := cube_scalar_data hK (by omega) d hd3
  have hM : ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) ^ 3 =
      Matrix.scalar (Fin (2 * r + ε)) (c : K) := by
    have := congrArg (fun g : GL (Fin (2 * r + ε)) K =>
      (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) hcd
    simpa [GeneralLinearGroup.coe_scalar] using this.symm
  have hcx : ∀ v, ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ
      (((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ
        (((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v)) =
      (c : K) • v := by
    intro v
    have e : ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
        ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
        ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        ((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) ^ 3 := by
      simp [pow_succ]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, hM]
    simp [Matrix.scalar_apply]
  have hc1 : c = 1 := by
    by_cases hbig : 2 ≤ S.card ∨ 0 < 2 * r + ε - 2 * a S.card
    · exact Units.ext (hc.cube_scalar_eq_one hother htailb hbig hd hcx)
    · push Not at hbig
      have hs1 : S.card = 1 := by have := Finset.card_pos.mpr hSne; omega
      have hk01 : k₀ = 1 := by omega
      subst hk01
      have ha1 : a 1 = 2 := by simpa [ha.zero] using hplane
      have h4 : 2 * r + ε = 4 := by rw [hs1, ha1] at hbig; omega
      rw [h4] at hcn
      have hc3' : c ^ 3 = 1 := by simpa using hc3
      calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
        _ = 1 := by rw [hc3', hcn]; simp
  have hd3one : (d : GL (Fin (2 * r + ε)) K) ^ 3 = 1 := by
    rw [← hcd, hc1, map_one]
  have hfix := hc.fixed_space_dim_of_plane_piece hk1 hk2 hplane hother htailb hd hd3one
  have hlt : ¬ 4 ≤ finrank K (LinearMap.ker (Matrix.mulVecLin
      (((d : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) - 1))) := by
    intro h4
    obtain ⟨H, hH0, hHp, hHc⟩ := exists_perfect_centralizer_of_fixed_space hK le_rfl d hd3one h4
    exact hH0 (hfree H hHp hHc)
  have h7 : 2 * r + ε ≤ 7 := by omega
  exact survivors_of_dim_le_seven hε hn h7 hIsub hIne hshort htail ⟨j₀, hj1, hjr, hj₀⟩

theorem survivor_analysis [Finite K] [CharP K 2] {r ε f : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 4 ≤ 2 * r + ε) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) (hDtJ : Dt ≤ J) (hDt : ⁅Dt, Dt⁆ = Dt)
    (d : StatedSU (2 * r + ε) (2 ^ f) K) (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K)
    (hd3 : (d : GL (Fin (2 * r + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r + ε)) K)
    (hfree : ∀ H : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), ⁅H, H⁆ = H →
      (∀ w ∈ H, Commute w d) → H = ⊥)
    (hcyc : ∀ V : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), V ≤ J → ⁅V, V⁆ = V →
      ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center (StatedSU (2 * r + ε) (2 ^ f) K)))))
    :
    f = 1 ∧
    ∃ (I : Set ℕ) (ψ : hypSU (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε ≃*
        StatedSU (2 * r + ε) (2 ^ f) K),
      I.Nonempty ∧ I ⊆ Set.Icc 1 r ∧
      J = (flagStabilizer (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε I).map
        ψ.toMonoidHom ∧
      (hypScalars (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε).map ψ.toMonoidHom =
        (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) ∧
      (∃ W : ℕ → Submodule K (Fin (2 * r + ε) → K),
        (∀ i ∈ I, Module.finrank K (W i) = i ∧ IsTotallyIsotropicSU (2 ^ f) (W i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j) ∧
        ∀ y : StatedSU (2 * r + ε) (2 ^ f) K, y ∈ J ↔
          ∀ i ∈ I, ∀ w ∈ W i, ((y : GL (Fin (2 * r + ε)) K) : Matrix _ _ K) *ᵥ w ∈ W i) ∧
      ((r = 2 ∧ ε = 0 ∧ I = {2}) ∨ (r = 2 ∧ ε = 1 ∧ I = {2}) ∨
        (r = 3 ∧ ε = 0 ∧ I = {2}) ∨ (r = 3 ∧ ε = 0 ∧ I = {1, 3}) ∨
        (r = 3 ∧ ε = 0 ∧ I = {2, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {1, 3}) ∨
        (r = 3 ∧ ε = 1 ∧ I = {2, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2})) := by
  classical
  have hf1 : f = 1 := by
    by_contra hne
    obtain ⟨H, hH0, hHp, hHc⟩ := exists_perfect_centralizer_of_cube_scalar hK (by omega) hn d hd3 hds
    exact hH0 (hfree H hHp hHc)
  refine ⟨hf1, ?_⟩
  subst hf1
  obtain ⟨I, ψ, hIne, hIsub, hJI, hZψ, W, hWd, hWm, hWJ⟩ := exists_chain_iso hr hε hK hf J S₀ hNJ hJ
  refine ⟨I, ψ, hIne, hIsub, hJI, hZψ, ⟨W, hWd, hWm, hWJ⟩, ?_⟩
  have hcyc' := cyclic_hypProj_of_cyclic_centralQuot
    (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) ψ hZψ
    (center_statedSU_eq_scalars hK (by omega)) I hJI hcyc
  obtain ⟨hshort, htail⟩ := census_open_nodes (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf)
    hε hn I hIsub hcyc'
  exact survivor_core (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) hε hn hIne hIsub hshort
    htail hWd hWm Dt (fun y hy i hi w hw => (hWJ y).mp (hDtJ hy) i hi w hw) hDt hd hds hd3 hfree

end CFSG.HardMathSupport.Curtis.UnitaryLevi
