module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutL2Count

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

private theorem ffOutFFRankAutL2_isPGroup_two {G : Type} [Group G] {A : Subgroup G}
    (hel : ∀ x ∈ A, x * x = 1) : IsPGroup 2 A :=
  fun x => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, pow_two]
    exact hel (x : G) x.2⟩

private theorem ffOutFFRankAutL2_card_le_eight_S0 (hH : HarrisHyp F)
    (hF : Nat.card F = 3 ^ 4) {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F)
    (hel : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 8 := by
  have hmul := Subgroup.card_ker_mul_card_range (AutL2.projHom A)
  have hrange : Nat.card (AutL2.projHom A).range ≤ 2 := by
    haveI := isCyclic_ringAut F
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (AutL2.projHom A).range)
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      obtain ⟨x, hx⟩ := g.2
      have hx2 : x * x = 1 := Subtype.ext (hel (x : PGammaL2 F) x.2)
      rw [Subgroup.coe_pow, pow_two, ← hx, ← map_mul, hx2]
      exact map_one (AutL2.projHom A)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
    have hcard : orderOf g = Nat.card (AutL2.projHom A).range :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    rw [← hcard]
    exact Nat.le_of_dvd (by norm_num) hdvd
  rw [← hmul]
  by_cases hR : ∃ c : Fˣ, nm F c true 1 ∈ A
  · obtain ⟨c, ht⟩ := hR
    have hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      intro x hx y hy
      have hx2 : x * x = 1 := hel x hx
      have hy2 : y * y = 1 := hel y hy
      have hxy : x * y * (x * y) = 1 := hel (x * y) (mul_mem hx hy)
      calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_left hxy).symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
        _ = y * x := by rw [inv_eq_of_mul_eq_one_left hx2, inv_eq_of_mul_eq_one_left hy2]
    calc Nat.card (AutL2.projHom A).ker * Nat.card (AutL2.projHom A).range ≤ 4 * 2 :=
          Nat.mul_le_mul (AutL2.card_ker_le_four hA hc ht) hrange
      _ = 8 := by norm_num
  · push Not at hR
    have hker : Nat.card (AutL2.projHom A).ker ≤ 2 := by
      refine AutL2.card_ker_le_pow hA hR (n := 2) ?_
      intro a ha
      have h1 : nm F (a ^ 2) false 1 = nm F 1 false 1 := by
        rw [← nm_false_pow, pow_two, hel _ ha, nm_one]
      exact (nm_injective h1).1
    calc Nat.card (AutL2.projHom A).ker * Nat.card (AutL2.projHom A).range ≤ 2 * 2 :=
          Nat.mul_le_mul hker hrange
      _ ≤ 8 := by norm_num

private theorem ffOutFFRankAutL2_card_le_eight_of_isPGroup (hH : HarrisHyp F)
    (hF : Nat.card F = 3 ^ 4) {A : Subgroup (PGammaL2 F)} (hp : IsPGroup 2 A)
    (hel : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 8 := by
  have hS := hH.isSylowIn_stdTS (K := ⊤) le_top
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQS : IsSylowIn (Q : Subgroup (PGammaL2 F)) ⊤ :=
    ⟨le_top, Q.isPGroup', fun Q' _ h1 h2 => Q.is_maximal' h1 h2⟩
  obtain ⟨g, -, hg⟩ := hS.exists_conj hQS
  have hBS : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ sylS0 F := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (stdTS F ⊤).map (MulAut.conj g).toMonoidHom := hg ▸ hQ hx
    obtain ⟨s, hs, hsx⟩ := hxQ
    have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
      rw [← hsx]
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hs.1
  have hBel : ∀ x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hel x hx, map_one]
  have h := ffOutFFRankAutL2_card_le_eight_S0 hH hF hBS hBel
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h

theorem ffRA_aut_psl281_elemAb_le_eight {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 2 3 4) (X : Subgroup (MulAut Y))
    (hX : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 8 := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F :=
    harrisHyp_of Nat.prime_three (by norm_num) hF (by decide) (by norm_num)
  let Φ : MulAut Y ≃* PGammaL2 F := autEquiv e
  have hmap : ∀ x ∈ X.map Φ.toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hX x hx, map_one]
  have hp : IsPGroup 2 (X.map Φ.toMonoidHom) := ffOutFFRankAutL2_isPGroup_two hmap
  have h := ffOutFFRankAutL2_card_le_eight_of_isPGroup hH hF hp hmap
  rwa [Subgroup.card_map_of_injective Φ.injective] at h

end CFSG.OddStandard.SmallF3.Omega
