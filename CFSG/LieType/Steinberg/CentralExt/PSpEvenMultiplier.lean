module

public import CFSG.LieType.Steinberg.CentralExt.CoverAssembly
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCatalogCover
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.CentralExt

namespace CFSG.LieType.Steinberg.CentralExt.SpClosed

variable {K : Type} [Field K] [Finite K] {n f : ℕ}

omit [Finite K] in
theorem isPerfect_statedSp' (hK : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    Group.IsPerfect (StatedSp n K) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin K n
      (hK.elim (fun h => Or.inl (Or.inr h)) fun h => Or.inr (Or.inr h))
  let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := n) (K := K)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem sp_exists_section_of_coprime
    {p : ℕ} [Fact p.Prime] [CharP K p] (E : Type) [Group E]
    [Finite E] (π : E →* StatedSp n K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : StatedSp n K →* E, ∀ g, π (σ g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  exact (CFSG.LieType.Steinberg.sp_existsUnique_section_of_sl2_lift n hπ hcen hC' fun ρ => by
    obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem lieModel_statedProj_sp (hK : Nat.card K = 2 ^ f) (hadm : StatedLieAdmissible .PSp n 2 f) :
    CFSG.Blueprint.LieModel (StatedProj (StatedSp n K)) .PSp n 2 f :=
  Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem psp_two_cover_trivial (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hnf : n ≤ 3 → 2 ≤ f) (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* StatedProj (StatedSp n K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hadm : StatedLieAdmissible .PSp n 2 f := by
    refine ⟨Nat.prime_two, hf, hn, fun h => ?_⟩
    have h1 : n = 2 := congrArg Prod.fst h
    have h2' : 2 ^ f = 2 := congrArg Prod.snd h
    have hf2 := hnf (by omega)
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hJ := lieModel_statedProj_sp hK hadm
  have := Nat.card_pos (α := K)
  have : Finite (StatedProj (StatedSp n K)) := inferInstance
  rcases (show n = 2 ∨ (3 ≤ n ∧ 2 ≤ f) ∨ (4 ≤ n ∧ f = 1) by
    rcases Nat.lt_or_ge f 2 with h | h
    · have := hnf
      right; right; constructor
      · by_contra hlt
        exact absurd (hnf (by omega)) (by omega)
      · omega
    · omega) with rfl | ⟨hn3, hf2⟩ | ⟨hn4, rfl⟩
  · exact (SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial η hη hC
      h2 (hnf (by omega)) hJ).1
  · exact (even_higher_symplectic_catalog_perfect_central_two_cover_trivial η hη hC h2 hn3 hf2
      hJ).1
  · exact (SymplecticCoverHigher.even_higher_symplectic_prime_field_central_two_cover_trivial η hη
      hC h2 hn4 hJ).1

theorem psp_even_hopfMultiplier
    [CharP K 2] (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hnf : n ≤ 3 → 2 ≤ f) :
    commutator (StatedProj (StatedSp n K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp n K)) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := SymplecticHigher.spScalars n K
  have hZc : Z ≤ Subgroup.center (StatedSp n K) := SymplecticHigher.spScalars_le_center
  have : Group.IsPerfect (StatedSp n K) := isPerfect_statedSp' (by
    rcases Nat.lt_or_ge f 2 with h | h
    · right
      refine ⟨by rw [hK]; interval_cases f; rfl, ?_⟩
      by_contra hlt
      exact absurd (hnf (by omega)) (by omega)
    · left
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h)
  have hsplit := CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc) (psp_two_cover_trivial hK hf hn hnf)
    (fun E _ _ π hπ hcen hc => sp_exists_section_of_coprime E π hπ hcen hc)
  obtain ⟨hperf, ⟨e⟩⟩ := CoverAssembly.hopfMultiplier_quotient Z hZc hsplit
  have hcard : Nat.card Z = Nat.gcd 2 (Nat.card K - 1) :=
    card_spScalars_eq_gcd K (by omega)
  have hcyc : IsCyclic Z := by
    have h1 : Nat.gcd 2 (Nat.card K - 1) = 1 := by
      rw [hK]
      have : Odd (2 ^ f - 1) := by
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        exact Nat.Even.sub_odd this (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
      exact (Nat.coprime_two_left.2 this)
    have : Subsingleton Z := by
      have := (Nat.card_eq_one_iff_unique (α := Z)).1 (hcard.trans h1)
      exact this.1
    exact isCyclic_of_subsingleton
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end CFSG.LieType.Steinberg.CentralExt.SpClosed
