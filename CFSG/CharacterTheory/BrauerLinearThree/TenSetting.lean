module

public import CFSG.CharacterTheory.BrauerLinearThree.LayerOrder

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage (N NZ Gamma barKappa nu)

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem centerSub_le_centralizer :
    centerSub φ ≤ Subgroup.centralizer ({J} : Set G) := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_centerSub φ).mp hx
  exact linearCentralizerHom_mem φ _

include hZ in
theorem card_centerSub_of_u_eq_one (hu : Nat.card F - 1 = 2 * Nat.card Z) :
    Nat.card (centerSub φ) = 2 := by
  have hm : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  rw [hu] at hm
  exact Nat.eq_of_mul_eq_mul_right hZ0 hm

include φ hZ hZodd h2 hJ in
theorem oddCore_eq_bot_of_u_eq_one (hq : Nat.card F % 4 = 3) (hq3 : 3 ≤ Nat.card F)
    (hu : Nat.card F - 1 = 2 * Nat.card Z) : N J = ⊥ := by
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hle : N J ≤ (centerSub φ).subgroupOf (Subgroup.centralizer ({J} : Set G)) := by
    rw [← NZ_eq_centerSub φ hZ hZodd h2 hJ hq hq3]
    exact le_sup_left
  have hcard2 : Nat.card ((centerSub φ).subgroupOf (Subgroup.centralizer ({J} : Set G))) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centerSub_le_centralizer φ)).toEquiv]
    exact card_centerSub_of_u_eq_one φ hZ hu
  have hdvd : Nat.card (N J) ∣ 2 := by
    rw [← hcard2]
    exact Subgroup.card_dvd_of_le hle
  have hodd : Odd (Nat.card (N J)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have h1 : Nat.card (N J) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.card_eq_one.mp h1

include φ hZ hZodd h2 hJ in
theorem layer_preimage_index_two (hq : Nat.card F % 4 = 3) (p f : ℕ) (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq5 : 5 ≤ Nat.card F) :
    (((CFSG.generalizedFitting (Gamma J)).comap (barKappa J)).comap (nu J)).index = 2 := by
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  have hq3 : 3 ≤ Nat.card F := by omega
  set θ := (gammaEquiv φ hZ hZodd h2 hJ hq hq3).trans (pglTopEquiv (F := F)) with hθ
  obtain ⟨hs, hnab, hcen, hidx, -⟩ :=
    CFSG.Wreathed.DegreeThreeModelFullCenter.matrix_overgroup_generalizedFitting_full_conclusions
      (F := F) (E := F) p f hp hpodd hf (hF ▸ hq5) hF (RingHom.id F) 1 ⊤ le_top
      (card_top_GL (F := F))
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have := hs
  have hmap := CFSG.Semidihedral.Local.OddKernel.generalizedFitting_map_of_mulEquiv θ.symm hnab hcen
  have hLidx : (CFSG.generalizedFitting (Gamma J)).index = 2 := by
    rw [← hmap, Subgroup.index_map_of_bijective θ.symm.bijective]
    exact hidx
  have hsurj : Function.Surjective ((barKappa J).comp (nu J)) :=
    (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.barKappa_surjective J).comp
      (QuotientGroup.mk'_surjective _)
  rw [Subgroup.comap_comap]
  exact (Subgroup.index_comap_of_surjective _ hsurj).trans hLidx

theorem two_pow_sub_two_eq_modulus_div_two {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 2) = CFSG.Semidihedral.modulus n / 2 := by
  rw [CFSG.Semidihedral.modulus, show n - 1 = (n - 2) + 1 by omega, pow_succ,
    Nat.mul_div_cancel _ (by norm_num)]

include φ hZ hZodd h2 hJ in
theorem exists_centered_semidihedral_sylow [Finite G] (hq : Nat.card F % 4 = 3) :
    4 ≤ (Nat.card F + 1).factorization 2 + 2 ∧
      ∃ (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup
          ((Nat.card F + 1).factorization 2 + 2) ≃* (S : Subgroup G)),
        J = (fS (CFSG.Semidihedral.r _) : G) ^ 2 ^ ((Nat.card F + 1).factorization 2 + 2 - 2) ∧
          (fS (CFSG.Semidihedral.s _) : G) = invJ₁ φ := by
  obtain ⟨hn4, S, e', he'r, he's⟩ := exists_semidihedral_sylow_of_G φ hZ hZodd h2 hJ hq
  refine ⟨hn4, S, e', ?_, he's⟩
  rw [two_pow_sub_two_eq_modulus_div_two (by omega), he'r]

end CFSG.BrauerLinearThree
