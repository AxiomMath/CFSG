module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (d4Nodes)
open scoped Matrix

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L]

theorem excTri_exists_pinned_of_pos {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0)
    {K : KacData τ} (hK : K.Facts) {a : Fin τ.rank → Lˣ}
    (hTN : rootDiagUnit τ a ^ N = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ),
      (∀ j : KernelComponent (rootCharHom a), ∃ y, K.IsZ N μ y ∧
        componentRoots (rootCharHom a) j = (fun α => v • α) '' K.rootsOf (K.comp N μ y)) ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ (x : Option (Fin τ.rank))
        (C : Finset (Option (Fin τ.rank))), K.comp N μ x = C ∧ (∃ y, y ∉ C) ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf C ∧
        compRank (componentRoots (rootCharHom a) i) = C.card ∧
        (componentRoots (rootCharHom a) i).ncard = kacCount τ K.θ C := by
  haveI : NeZero (N : L) := ⟨hNL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  obtain ⟨v, μ, -, hall⟩ := K.exists_smul_rootsOf hK hN (ζ := hu.unit) (by simpa using hζ) a
    (pow_eq_one_of_rootDiagUnit_pow hTN)
  refine ⟨v, μ, hall, fun i => ?_⟩
  obtain ⟨x, -, hi⟩ := hall i
  set hfin := Set.toFinite (K.comp N μ x)
  have hC : K.comp N μ x = (hfin.toFinset : Set (Option (Fin τ.rank))) :=
    hfin.coe_toFinset.symm
  have hCp : ∃ y, y ∉ hfin.toFinset := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K hN μ x
    exact ⟨y, fun h => hy (hfin.mem_toFinset.1 h)⟩
  rw [hC] at hi
  refine ⟨x, hfin.toFinset, hC, hCp, hi, ?_, ?_⟩
  · rw [hi, compRank_image, compRank_rootsOf K hK hCp]
  · rw [hi, ncard_image_smul, ncard_rootsOf K hK hCp]

theorem excTri_d4_pinned_of_pos {p₀ N : ℕ} (S : LangSetup τ L p₀) (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {D4C F : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 4 → kacCount τ K.θ C = 24 → C = D4C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ D4C ↔ 1 ≤ j.val ∧ j.val ≤ 4) (hnone : none ∉ D4C)
    (hF : ∀ y, (∀ z ∈ D4C, y ≠ z ∧ ¬ K.Adj y z) → y ∈ F) (hFp : ∃ y, y ∉ F)
    (hFc : kacCount τ K.θ F < 24)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus) (hTN : rootDiagUnit τ a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨v, μ, hall, hpinned⟩ :=
    excTri_exists_pinned_of_pos (N := N) (K := K) hN hNL hK hTN
  obtain ⟨x, C, hxC, -, hi, hr, hc⟩ := hpinned i
  have hC : C = D4C := hpin C (hr ▸ hrank) (hc ▸ hcard)
  subst hC
  refine ⟨v, ?_, S.rho_mem_of_farT_of_prime (p := N) hK haT hall i hxC hi hF hFp (by omega)⟩
  rw [hi, K.rootsOf_eq_parabolicRoots (by exact_mod_cast hnone)]
  congr 2
  exact Set.ext fun j => hJ j

theorem excTri_exists_order [CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) :
    ∃ N : ℕ, 0 < N ∧ (N : L) ≠ 0 ∧ rootDiagUnit τ a ^ N = 1 := by
  haveI : Finite S.D.model := S.finite
  let y : S.D.model := ⟨rootDiagUnit τ a, S.D.torus_le_model haT⟩
  have hN : orderOf y = orderOf (rootDiagUnit τ a) := Subgroup.orderOf_mk _ _
  have hpos : 0 < orderOf y := orderOf_pos y
  refine ⟨orderOf (rootDiagUnit τ a), ?_, ?_, pow_orderOf_eq_one _⟩
  · rw [← hN]
    exact hpos
  · intro h0
    have h0' : (orderOf y : L) = 0 := by
      rw [hN]
      exact h0
    have h2dvd : 2 ∣ orderOf y := (CharP.cast_eq_zero_iff L 2 (orderOf y)).1 h0'
    obtain ⟨m, hm⟩ := h2dvd
    have hmpos : 0 < m := by
      have := hpos
      omega
    have hmN : m < orderOf (rootDiagUnit τ a) := by
      rw [← hN]
      omega
    have hmne : m ≠ 0 := by omega
    have hm' : orderOf (rootDiagUnit τ a) = 2 * m := by
      rw [← hN]
      exact hm
    have h2m : rootDiagUnit τ a ^ (2 * m) = 1 := by
      rw [← hm']
      exact pow_orderOf_eq_one _
    have hai : ∀ i, a i ^ m = 1 := by
      intro i
      have h1 : a i ^ (2 * m) = 1 := pow_eq_one_of_rootDiagUnit_pow h2m i
      have h1' : (a i : L) ^ (2 * m) = 1 := by
        have := congrArg (fun u : Lˣ => (u : L)) h1
        simpa using this
      have hsq : ((a i : L) ^ m) ^ 2 = 1 ^ 2 := by
        rw [one_pow, ← pow_mul, mul_comm m 2]
        exact h1'
      exact Units.ext (CharTwo.sq_inj.mp hsq)
    have hb : a ^ m = 1 := funext fun i => by simpa using hai i
    have hpow : rootDiagUnit τ a ^ m = 1 := by
      have e : rootDiagUnit τ (a ^ m) = rootDiagUnit τ a ^ m :=
        map_pow (rootDiagUnitHom τ L) a m
      rw [← e, hb, rootDiagUnit_one]
    exact (pow_ne_one_of_lt_orderOf hmne hmN) hpow


theorem excTri_d4_pinned_E6 {p : ℕ} (S : LangSetup .E6 L p) {N : ℕ} (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (haT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hTN : rootDiagUnit .E6 a ^ N = 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup .E6, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  exact excTri_d4_pinned_of_pos S hN hNL facts_E6 kacCount_E6_four (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) haT hTN i hrank hcard

theorem excTri_d4_pinned_E7 {p : ℕ} (S : LangSetup .E7 L p) {N : ℕ} (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ} (haT : rootDiagUnit .E7 a ∈ S.D.torus)
    (hTN : rootDiagUnit .E7 a ^ N = 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup .E7, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E7 (d4Nodes .E7) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  exact excTri_d4_pinned_of_pos S hN hNL facts_E7 kacCount_E7_four (by decide) (by decide)
    (fun y hy => far_d4_E7 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) haT hTN i hrank hcard

theorem excTri_d4_pinned_E8 {p : ℕ} (S : LangSetup .E8 L p) {N : ℕ} (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ} (haT : rootDiagUnit .E8 a ∈ S.D.torus)
    (hTN : rootDiagUnit .E8 a ^ N = 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup .E8, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E8 (d4Nodes .E8) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  exact excTri_d4_pinned_of_pos S hN hNL facts_E8 kacCount_E8_four (by decide) (by decide)
    (fun y hy => far_d4_E8 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) haT hTN i hrank hcard

theorem excTri_F4_absurd {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTN : rootDiagUnit .F4 a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) : False := by
  obtain ⟨v, μ, -, hpinned⟩ :=
    excTri_exists_pinned_of_pos (N := N) (K := kacF4) hN hNL facts_F4 hTN
  obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
  exact absurd (hc' ▸ hcard) (kacCount_F4_four C (hr' ▸ hrank))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
