module

import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem eq_bot_of_isPGroup_of_coprime [Finite G] {N : Subgroup G} (h2 : IsPGroup 2 ↥N)
    (hodd : Nat.Coprime 2 (Nat.card ↥N)) : N = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  · rw [hn, pow_succ] at hodd
    exact absurd (Nat.Coprime.coprime_dvd_right (dvd_mul_left 2 _) hodd) (by norm_num)

theorem isPGroup_center_of_pPrimeCore_eq_bot [Finite G] (hO : pPrimeCore 2 G = ⊥) :
    IsPGroup 2 ↥(center G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPGroup_of_nilpotent_normal (center G) inferInstance CommGroup.isNilpotent hO

theorem pPrimeCore_eq_bot_of_surjective_of_isQuasisimple {Q R : Type*} [Group Q] [Group R]
    [Finite Q] [Finite R] (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 ↥(center Q)) (ψ : Q →* R)
    (hψ : Function.Surjective ψ) : pPrimeCore 2 R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 R)) := pPrimeCore_coprime_card
  have hmap := Subgroup.map_comap_eq_self_of_surjective hψ (pPrimeCore 2 R)
  rcases LocalCores.quasisimple_normal_subgroups hQ (N := (pPrimeCore 2 R).comap ψ)
      inferInstance with htop | hcen
  · have hR : pPrimeCore 2 R = ⊤ := by
      rw [← hmap, htop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ hψ]
    have : Group.IsPerfect Q := hQ.1
    have hperf : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := ψ) hψ
    have hRodd : Odd (Nat.card R) := by
      rw [← card_top (G := R), ← hR]
      exact Nat.coprime_two_left.mp hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
    have : Subsingleton R := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable R hsolv
    exact Subgroup.eq_bot_of_subsingleton _
  · have hle : pPrimeCore 2 R ≤ (center Q).map ψ := by
      rw [← hmap]
      exact map_mono hcen
    exact eq_bot_of_isPGroup_of_coprime ((hZ.map ψ).to_le hle) hodd

theorem map_center_layer_le_pCore [Finite G] (hO : pPrimeCore 2 G = ⊥) :
    (center ↥(layer G)).map (layer G).subtype ≤ pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 2 hO

theorem le_centralizer_map_conj_of_isComponent [Finite G] {K : Subgroup G} (hK : IsComponent K)
    {g : G} (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    K ≤ centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hKg := LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  rcases LocalCores.component_subnormal_subgroup hKg hK.2 with h | h
  · exfalso
    apply hne
    refine eq_of_le_of_card_ge h ?_
    rw [card_map_of_injective (MulAut.conj g).injective]
  · rw [le_centralizer_iff]
    exact commutator_eq_bot_iff_le_centralizer.mp h

end CFSG.ComponentClassification.HarrisLit
