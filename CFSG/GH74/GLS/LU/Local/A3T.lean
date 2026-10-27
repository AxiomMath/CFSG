module

public import CFSG.GH74.GLS.LU.Local.A3Model
public import CFSG.GH74.GLS.LU.Local.A3Rec
public import CFSG.GH74.GLS.LU.Local.Gen

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.GH74.L5U5 CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem iSup_vec_three {G : Type} [Group G] (K₁ L K₂ : Subgroup G) :
    (⨆ i : Fin 3, ![K₁, L, K₂] i) = K₁ ⊔ L ⊔ K₂ := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup (fun i : Fin 3 => ![K₁, L, K₂] i) 0)
      (le_iSup (fun i : Fin 3 => ![K₁, L, K₂] i) 1)) (le_iSup (fun i : Fin 3 => ![K₁, L, K₂] i) 2)

theorem card_S_eq {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
    {t u : G} [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) :
    Nat.card ↥(S : Subgroup G) = 2 ^ (1 + 2 * (Nat.card ↥K₁).factorization 2) := by
  have hg := hs.toGen
  have hQ := card_Q hc hg
  have hK2 := card_K_mul_two hc hg
  rw [← hs.card_eq] at hK2
  have h1 : Nat.card ↥(K₁ ⊔ K₂) ≠ 0 := Nat.card_pos.ne'
  have h2 : Nat.card ↥K₁ ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 + 1 = 2 * (Nat.card ↥K₁).factorization 2 := by
    have h := congrArg (fun n => n.factorization 2) hK2
    rw [Nat.factorization_mul h1 (by norm_num), Nat.factorization_mul h2 h2] at h
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h
    omega
  rw [hs.card_S, hQ]
  have : 4 * 2 ^ (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 =
      2 ^ (2 + (Nat.card ↥(K₁ ⊔ K₂)).factorization 2) := by
    rw [pow_add]; norm_num
  rw [this]
  congr 1
  omega

theorem hom_central_eq {X G : Type} [Group X] [Group G] {K₁ : Subgroup G} {z : G} (ι : X →* G)
    (hinj : Function.Injective ι) (hrange : ι.range = K₁)
    (hz : (Subgroup.center ↥K₁).map K₁.subtype = zpowers z) (hz2 : orderOf z = 2) {m : X}
    (hm : m ∈ Subgroup.center X) (hm1 : m ≠ 1) : ι m = z := by
  have hmK : ι m ∈ K₁ := hrange ▸ ⟨m, rfl⟩
  have hcen : (⟨ι m, hmK⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, ha⟩ : (g : G) ∈ ι.range := hrange.symm ▸ g.2
    apply Subtype.ext
    show (g : G) * ι m = ι m * (g : G)
    rw [← ha, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hm a]
  have hmem : ι m ∈ zpowers z := by
    rw [← hz]
    exact ⟨⟨ι m, hmK⟩, hcen, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz2' : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · exfalso
    have h1 : ι m = 1 := by
      rw [← hk, zpow_mul]; simp [hz2']
    exact hm1 (hinj (by rw [h1, map_one]))
  · rw [← hk, zpow_add_one, zpow_mul]
    simp [hz2']

theorem negOneSL2_mem_center {K : Type} [Field K] : negOneSL2 K ∈ Subgroup.center SL(2, K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  show Matrix.scalar (Fin 2) (-1 : K) = -1
  rw [map_neg, map_one]

theorem negOneSL2_ne_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) : negOneSL2 K ≠ 1 := by
  intro h
  have h' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have h'' : (-1 : K) = 1 := by simpa [negOneSL2] using h'
  exact h2 (by linear_combination (-1 : K) * h'')

theorem negOneSu_mem_center {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) : negOneSu K p f hK ∈ Subgroup.center (Su K p f 2) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : GL (Fin 2) K) * (-1) = (-1) * (g : GL (Fin 2) K)
  simp

theorem negOneSu_ne_one {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) : negOneSu K p f hK ≠ 1 := by
  intro h
  have h' := congrArg (fun A : Su K p f 2 => ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have h'' : (-1 : K) = 1 := by simpa [negOneSu] using h'
  exact h2 (by linear_combination (-1 : K) * h'')

theorem exists_T_of_nbhd_lin {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    {z : G} {S : Sylow 2 G} {K₁ K₂ L : Subgroup G} {t u u' : G} [IsCyclic ↥(A0 z)]
    (hc : LUComps G (p ^ f) z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    (hN : IsLinearA3Neighborhood K z u' ![K₁, L, K₂]) :
    ∃ T : Subgroup G, T ≤ (K₁ ⊔ L ⊔ K₂) ⊓ Cz z ∧ IsPGroup 2 T ∧
      Nat.card ↥(S : Subgroup G) ≤ Nat.card ↥T := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  obtain ⟨hcomm, hpair⟩ := hN.comm_pairs hK4 h2
  have hz0 := hN.2.1
  have hz2 := hN.2.2.1
  obtain ⟨ψ, ι, hrange, hker, hι, hψι⟩ := exists_surjection_pos_lin p f hp hK (by omega)
    ![K₁, L, K₂] hcomm hpair ⟨z, hz0.1, hs.z_ne_one⟩
  have hr0 : (ι 0).range = K₁ := (hι 0).1
  have hr2 : (ι 2).range = K₂ := (hι 2).1
  have hι0 : ι 0 (negOneSL2 K) = z :=
    hom_central_eq (ι 0) (hι 0).2 hr0 hc.cen₁ hs.z_inv negOneSL2_mem_center (negOneSL2_ne_one h2)
  have hι2 : ι 2 (negOneSL2 K) = z :=
    hom_central_eq (ι 2) (hι 2).2 hr2 hc.cen₂ hs.z_inv negOneSL2_mem_center (negOneSL2_ne_one h2)
  have hψ0 : ψ (blockSL2 K 3 0 (negOneSL2 K)) = z := by rw [hψι, hι0]
  have hψ2 : ψ (blockSL2 K 3 2 (negOneSL2 K)) = z := by rw [hψι, hι2]
  obtain ⟨T, hTr, hTc, hTp, hTcard⟩ := exists_two_subgroup_lin h2 ψ hker (by rw [hψ0, hψ2])
  refine ⟨T, ?_, hTp, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · have := hrange ▸ hTr hx
      rwa [iSup_vec_three] at this
    · rw [hψ0] at hTc
      exact mem_centralizer_singleton_iff.mpr (hTc x hx)
  · rw [card_S_eq hc hs]
    have hK1 : Nat.card ↥K₁ = Nat.card ↥(StatedSL 2 K) := by
      rw [← hr0]
      rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
      exact Nat.card_congr (MonoidHom.ofInjective (hι 0).2).toEquiv.symm
    rw [hK1]
    exact hTcard

theorem exists_T_of_nbhd_uni {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K F : Type} [Field K] [Finite K] [CharP K p] [Field F]
    [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f)
    {z : G} {S : Sylow 2 G} {K₁ K₂ L : Subgroup G} {t u u' : G} [IsCyclic ↥(A0 z)]
    (hc : LUComps G (p ^ f) z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    (hN : IsUnitaryA3Neighborhood (p ^ f) K F z u' ![K₁, L, K₂]) :
    ∃ T : Subgroup G, T ≤ (K₁ ⊔ L ⊔ K₂) ⊓ Cz z ∧ IsPGroup 2 T ∧
      Nat.card ↥(S : Subgroup G) ≤ Nat.card ↥T := by
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (by rw [hK]; exact hodd.pow)
  obtain ⟨hcomm, hpair⟩ := hN.comm_pairs hK hF hp2 hq
  have hz0 := hN.2.1
  obtain ⟨ψ, ι, hrange, hker, hι, hψι⟩ := exists_surjection_pos_uni p f hK hq
    ![K₁, L, K₂] hcomm hpair ⟨z, hz0.1, hs.z_ne_one⟩
  have hr0 : (ι 0).range = K₁ := (hι 0).1
  have hr2 : (ι 2).range = K₂ := (hι 2).1
  have hι0 : ι 0 (negOneSu K p f hK) = z :=
    hom_central_eq (ι 0) (hι 0).2 hr0 hc.cen₁ hs.z_inv (negOneSu_mem_center hK)
      (negOneSu_ne_one hK h2)
  have hι2 : ι 2 (negOneSu K p f hK) = z :=
    hom_central_eq (ι 2) (hι 2).2 hr2 hc.cen₂ hs.z_inv (negOneSu_mem_center hK)
      (negOneSu_ne_one hK h2)
  have hψ0 : ψ (blockEmb2 K p f 3 0 (negOneSu K p f hK)) = z := by rw [hψι, hι0]
  have hψ2 : ψ (blockEmb2 K p f 3 2 (negOneSu K p f hK)) = z := by rw [hψι, hι2]
  obtain ⟨T, hTr, hTc, hTp, hTcard⟩ := exists_two_subgroup_uni hK hp2 ψ hker (by rw [hψ0, hψ2])
  refine ⟨T, ?_, hTp, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · have := hrange ▸ hTr hx
      rwa [iSup_vec_three] at this
    · rw [hψ0] at hTc
      exact mem_centralizer_singleton_iff.mpr (hTc x hx)
  · rw [card_S_eq hc hs]
    have hK1 : Nat.card ↥K₁ = Nat.card ↥(StatedSU 2 (p ^ f) K) := by
      rw [← hr0]
      rw [← Nat.card_congr (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 2)).toEquiv]
      exact Nat.card_congr (MonoidHom.ofInjective (hι 0).2).toEquiv.symm
    rw [hK1]
    exact hTcard

end CFSG.GH74.GLS.LU.Local
