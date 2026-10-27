module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenT
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenC
public import CFSG.Sporadic.HeldB.OuterFixedCore
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

theorem signalizerFixedSubgroup_eq_fixedSubgroup {G : Type*} [Group G] (s : MulAut G) :
    Open.signalizerFixedSubgroup s = FixedCommutingProduct.fixedSubgroup s :=
  Subgroup.ext fun _ => Iff.rfl

theorem map_layerOfFixed_heConjR
    (x : heAutGroup) :
    (Sol78.layerOfFixed (heConjR x)).map heP.subtype =
      layerIn (heP ⊓ centralizer {(x : Equiv.Perm (Fin 8330))}) := by
  rw [layerOfFixed_eq_layerIn]
  apply map_layerIn_eq heP.subtype_injective
  rw [signalizerFixedSubgroup_eq_fixedSubgroup]
  exact map_fixedSubgroup_heConjR x

theorem not_isPerfect_alternating_four : ¬ Group.IsPerfect (alternatingGroup (Fin 4)) := by
  intro h
  have h1 := alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)
  rw [Group.isPerfect_def.1 h] at h1
  have h2 := alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  rw [h1, Subgroup.card_top, alternatingGroup.card_of_card_eq_four (by simp)] at h2
  norm_num at h2

theorem card_layer_cases {X : Type*} [Group X] {L : Subgroup X} {m : ℕ} (hm : 4 ≤ m)
    (hperf : ⁅L, L⁆ = L)
    (hL : Nonempty (L ≃* alternatingGroup (Fin m)) ∨ Sol78.IsTripleCoverAltSeven L) :
    (5 ≤ m ∧ Nat.card L = m.factorial / 2) ∨ Nat.card L = 7560 := by
  rcases hL with he | hT
  · left
    have e := he.some
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card L = m.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    refine ⟨?_, hc⟩
    by_contra h4
    have hm4 : m = 4 := by omega
    subst hm4
    have : Group.IsPerfect L := Subgroup.isPerfect_iff.2 hperf
    exact not_isPerfect_alternating_four
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  · right
    unfold Sol78.IsTripleCoverAltSeven at hT
    obtain ⟨-, h3, ⟨q⟩⟩ := hT
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Nat.card_congr q.toEquiv, h3, h7] at h1
    rw [h1]

theorem five_dvd_factorial_div_two {m : ℕ} (hm : 5 ≤ m) : 5 ∣ m.factorial / 2 :=
  Nat.dvd_div_of_mul_dvd ((show 5 * 2 ∣ Nat.factorial 5 by decide).trans
    (Nat.factorial_dvd_factorial hm))

theorem four_le_of_card {m : ℕ} (D : Finset (Fin m)) (hD : D.card = 4) : 4 ≤ m := by
  simpa [hD] using D.card_le_univ

theorem genAt_t1
    (hy : heT1P ∈ heAutGroup) : GenAt heP (heConjR ⟨heT1P, hy⟩) := by
  intro m hL e F hFL hF hD
  exfalso
  have hK := map_layerOfFixed_heConjR (⟨heT1P, hy⟩ : heAutGroup)
  obtain ⟨D, hD4, -⟩ := hD
  have hperf : ⁅Sol78.layerOfFixed (heConjR ⟨heT1P, hy⟩),
      Sol78.layerOfFixed (heConjR ⟨heT1P, hy⟩)⁆ = Sol78.layerOfFixed (heConjR ⟨heT1P, hy⟩) := by
    rw [layerOfFixed_eq_layerIn]
    exact layerIn_perfect _
  have hdvd : Nat.card (Sol78.layerOfFixed (heConjR ⟨heT1P, hy⟩)) ∣ 21504 := by
    rw [← card_heP_cent1, ← Subgroup.card_map_of_injective heP.subtype_injective, hK]
    exact card_dvd_of_le (layerIn_le _)
  rcases card_layer_cases (four_le_of_card D hD4) hperf hL with ⟨h5, hc⟩ | hc
  · rw [hc] at hdvd
    have := (five_dvd_factorial_div_two h5).trans hdvd
    norm_num at this
  · rw [hc] at hdvd
    norm_num at hdvd

theorem genAt_t0
    (hy : heGenPerm 0 ∈ heAutGroup) : GenAt heP (heConjR ⟨heGenPerm 0, hy⟩) := by
  intro m hL e F hFL hF hD
  exfalso
  have hK := map_layerOfFixed_heConjR (⟨heGenPerm 0, hy⟩ : heAutGroup)
  obtain ⟨D, hD4, -⟩ := hD
  set L := Sol78.layerOfFixed (heConjR ⟨heGenPerm 0, hy⟩) with hLdef
  obtain ⟨K, hKdef⟩ : ∃ K, K = layerIn (heP ⊓ centralizer {heGenPerm 0}) := ⟨_, rfl⟩
  have hK' : L.map heP.subtype = K := by rw [hK, hKdef]
  have hperf : ⁅L, L⁆ = L := by
    rw [hLdef, layerOfFixed_eq_layerIn]
    exact layerIn_perfect _
  have hLK : Nat.card L = Nat.card K := by
    rw [← Subgroup.card_map_of_injective heP.subtype_injective, hK']
  obtain ⟨hC, -⟩ := oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])
  have hcard0 : Nat.card heInnerGrp0 = 161280 := by
    rw [hC]
    exact card_heP_cent0
  have hKC : K ≤ heInnerGrp0 := by
    rw [hC, hKdef]
    exact layerIn_le _
  have hdvd : Nat.card L ∣ 161280 := by
    rw [← hcard0, hLK]
    exact card_dvd_of_le hKC
  have hL5 : 5 ∣ Nat.card L ∧ Nat.card L ≤ 20160 := by
    rcases card_layer_cases (four_le_of_card D hD4) hperf hL with ⟨h5, hc⟩ | hc
    · have hm8 : m ≤ 8 := by
        by_contra h9
        have h2 : Nat.factorial 9 / 2 ≤ m.factorial / 2 :=
          Nat.div_le_div_right (Nat.factorial_le (show 9 ≤ m by omega))
        have h3 := Nat.le_of_dvd (by norm_num) hdvd
        rw [hc] at h3
        have : Nat.factorial 9 / 2 = 181440 := by decide
        omega
      refine ⟨hc ▸ five_dvd_factorial_div_two h5, ?_⟩
      rw [hc]
      have h1 : m.factorial / 2 ≤ Nat.factorial 8 / 2 :=
        Nat.div_le_div_right (Nat.factorial_le hm8)
      have : Nat.factorial 8 / 2 = 20160 := by decide
      omega
    · rw [hc] at hdvd
      norm_num at hdvd
  obtain ⟨ψ, hψ⟩ : ∃ ψ : heInnerGrp0 →* Equiv.Perm (Fin 240),
      ψ = restrictHom heDelta0_injective heInnerGrp0 heInnerGrp0_stab := ⟨_, rfl⟩
  have hψr : ψ.range = heX0.originalSubgroup := by
    rw [hψ]
    exact heInnerRes0_range
  have hker : Nat.card ψ.ker = 2 := by
    have h := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hψr, card_heX0, hcard0] at h
    omega
  have hK₀c : Nat.card (K.subgroupOf heInnerGrp0) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv
  have hK₀n : ∀ h : heInnerGrp0, ∀ k ∈ K.subgroupOf heInnerGrp0,
      h * k * h⁻¹ ∈ K.subgroupOf heInnerGrp0 := by
    intro h k hk
    rw [mem_subgroupOf] at hk ⊢
    have hh : (h : Equiv.Perm (Fin 8330)) ∈ centralizerIn heP (heGenPerm 0) := hC ▸ h.2
    rw [hKdef] at hk ⊢
    exact conj_mem_layerIn _ hh hk
  generalize K.subgroupOf heInnerGrp0 = K₀ at hK₀c hK₀n
  have hN : K₀.map ψ = (ψ.comp K₀.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hK₀N : Nat.card K₀ = Nat.card (ψ.comp K₀.subtype).ker * Nat.card (K₀.map ψ) := by
    rw [hN, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker' : Nat.card (ψ.comp K₀.subtype).ker ∣ 2 := by
    rw [← hker, ← Subgroup.card_map_of_injective K₀.subtype_injective]
    refine card_dvd_of_le fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact hy
  have hpos : 0 < Nat.card (ψ.comp K₀.subtype).ker := Nat.card_pos
  have h5N : 5 ∣ Nat.card (K₀.map ψ) := by
    have h1 : 5 ∣ Nat.card (ψ.comp K₀.subtype).ker * Nat.card (K₀.map ψ) := by
      rw [← hK₀N, hK₀c, ← hLK]
      exact hL5.1
    exact (Nat.Coprime.coprime_dvd_right hker' (by norm_num)).dvd_of_dvd_mul_left h1
  have hltN : Nat.card (K₀.map ψ) < 40320 := by
    have h1 : Nat.card (K₀.map ψ) ≤ Nat.card K₀ := by
      rw [hK₀N]
      exact Nat.le_mul_of_pos_left _ hpos
    rw [hK₀c, ← hLK] at h1
    have := hL5.2
    omega
  refine false_of_normal_heX0 (N := K₀.map ψ) ?_ ?_ h5N hltN
  · rw [← hψr]
    exact map_le_range ψ K₀
  · intro g hg n hn
    rw [← hψr] at hg
    obtain ⟨h, rfl⟩ := hg
    obtain ⟨k, hk, rfl⟩ := mem_map.1 hn
    rw [← map_mul, ← map_inv, ← map_mul]
    exact mem_map_of_mem ψ (hK₀n h k hk)

end CFSG.ComponentClassification.SolMax.HeGen
