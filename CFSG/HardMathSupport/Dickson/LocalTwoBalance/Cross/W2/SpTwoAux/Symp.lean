module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section Small

theorem le_center_of_card_two {G : Type*} [Group G] {N : Subgroup G} (hN : Nat.card N = 2)
    (hn : ∀ y : G, ∀ x ∈ N, y * x * y⁻¹ ∈ N) : N ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).1 hN
  have hz' : (⟨z, hz⟩ : N) = u := huniq _ fun h => hz1 (congrArg Subtype.val h)
  have hw : (⟨g * z * g⁻¹, hn g z hz⟩ : N) = u := huniq _ fun h => by
    have h2 : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    apply hz1
    have := congrArg (fun t => g⁻¹ * t * g) h2
    simpa [mul_assoc] using this
  have h3 : g * z * g⁻¹ = z := congrArg Subtype.val (hw.trans hz'.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h3]

theorem noNormalPPrime_three_perm_six : NoNormalPPrime 3 (⊤ : Subgroup (Equiv.Perm (Fin 6))) := by
  intro M _ hMn hMc
  haveI : M.Normal := ⟨fun x hx g => by simpa using hMn g (Subgroup.mem_top g) x hx⟩
  by_contra hne
  have h1 : 1 < Nat.card M := by
    have := Nat.card_pos (α := M)
    have h2 : Nat.card M ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    omega
  have hnt : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp h1
  have hle : alternatingGroup (Fin 6) ≤ M :=
    Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
  have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card M := Subgroup.card_dvd_of_le hle
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hA] at hdvd
  have hpM : 3 ∣ Nat.card M := (by norm_num : 3 ∣ 360).trans hdvd
  exact absurd (Nat.Coprime.eq_one_of_dvd hMc hpM) (by norm_num)

end Small

section Statement

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_two (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK]; simp)

theorem center_statedSp_eq_bot (hK : Nat.card K = 2) (n : ℕ) :
    Subgroup.center (StatedSp n K) = ⊥ := by
  have : CharP K 2 := charP_two_of_card_two hK
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

theorem three_dvd_card_statedSp (hK : Nat.card K = 2) {s : ℕ} (hs : 1 ≤ s) :
    3 ∣ Nat.card (StatedSp s K) := by
  rw [SymplecticFlag.card_statedSp, hK]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.2 ⟨le_rfl, hs⟩
  exact (by norm_num : 3 ∣ 2 ^ (2 * 1) - 1).trans
    (Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1) h1)

theorem noNormalPPrime_three_statedSp (hK : Nat.card K = 2) (s : ℕ) :
    NoNormalPPrime 3 (⊤ : Subgroup (StatedSp s K)) := by
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ 3 ≤ s by omega) with rfl | rfl | rfl | hs
  ·
    intro N _ _ _
    haveI : Subsingleton (StatedSp 0 K) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => by
        rcases i with i | i <;> exact i.elim0))⟩
    exact Subgroup.eq_bot_of_subsingleton N
  ·
    intro N _ hNn hNc
    have hcard : Nat.card (StatedSp 1 K) = 2 * 3 := by
      rw [SymplecticFlag.card_statedSp, hK]
      simp
    have hdvd : Nat.card N ∣ 2 * 3 := hcard ▸ Subgroup.card_subgroup_dvd_card N
    have h2 : Nat.card N ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hNc.symm hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact Subgroup.card_eq_one.1 h
    · have hc := le_center_of_card_two h (fun y x hx => hNn y (Subgroup.mem_top y) x hx)
      rw [center_statedSp_eq_bot hK 1] at hc
      exact le_bot_iff.1 hc
  ·
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K)
      (by rw [← Nat.card_eq_fintype_card, hK])
    exact noNormalPPrime_top_of_mulEquiv e noNormalPPrime_three_perm_six
  ·
    have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple s K (by omega)
      (Or.inr (Or.inr ⟨hK, hs⟩))
    intro N _ hNn hNc
    haveI hNnorm : N.Normal := ⟨fun x hx g => by simpa using hNn g (Subgroup.mem_top g) x hx⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnorm with htop | hcen
    · exfalso
      have h3 : 3 ∣ Nat.card N := by
        rw [htop, Subgroup.card_top]
        exact three_dvd_card_statedSp hK (by omega)
      exact absurd (Nat.Coprime.eq_one_of_dvd hNc h3) (by norm_num)
    · rw [center_statedSp_eq_bot hK s] at hcen
      exact le_bot_iff.1 hcen

theorem noNormalPPrime_three_sesqUnitaryGroup_alt (hK : Nat.card K = 2) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W}
    (hB : B.IsAlt) (hn : B.Nondegenerate) :
    NoNormalPPrime 3 (⊤ : Subgroup (sesqUnitaryGroup B)) := by
  obtain ⟨s, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  exact noNormalPPrime_top_of_mulEquiv e (noNormalPPrime_three_statedSp hK s)

end Statement

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
