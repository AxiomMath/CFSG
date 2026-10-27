module

public import CFSG.GH74.Defs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup

theorem nb_pPrimeCore_eq_bot_of_center {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (hne : center K ≠ ⊥) : pPrimeCore 2 K = ⊥ := by
  have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (pPrimeCore_normal (p := 2) (G := K)) with h | h
  ·
    exfalso
    rw [h, Subgroup.card_top] at hodd
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [pow_zero] at hn
      exact (Subgroup.card_eq_one).1 hn
    have h2 : 2 ∣ Nat.card K :=
      (dvd_pow_self 2 hn0).trans (hn ▸ Subgroup.card_subgroup_dvd_card (center K))
    exact absurd (Nat.Coprime.eq_one_of_dvd hodd h2) (by norm_num)
  ·
    have h2 : IsPGroup 2 (pPrimeCore 2 K) := hZ.to_le h
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    have hn0 : n = 0 := by
      by_contra hn0
      have h3 : 2 ∣ Nat.card (pPrimeCore 2 K) := hn ▸ dvd_pow_self 2 hn0
      exact absurd (Nat.Coprime.eq_one_of_dvd hodd h3) (by norm_num)
    rw [hn0, pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn

theorem nb_center_eq_pCore {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) : center K = pCore 2 K := by
  refine le_antisymm (le_sSup ⟨inferInstance, hZ⟩) ?_
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (pCore_normal (p := 2) (G := K))
      with h | h
  ·
    exfalso
    have hP : IsPGroup 2 K := fun g => by
      obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := K) ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect K := hq.1
    exact Group.IsPerfect.not_isNilpotent (G := K) hP.isNilpotent
  · exact h

theorem nb_nonempty_mulEquiv_centralizerBar {K : Type} [Group K] [Finite K] {w : K}
    (hw : w ∈ center K) (hO : pPrimeCore 2 K = ⊥) : Nonempty (K ≃* CentralizerBar w) := by
  have hC : centralizer ({w} : Set K) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.2 (Set.singleton_subset_iff.2 hw)
  let e : ↥(centralizer ({w} : Set K)) ≃* K :=
    MulEquiv.ofBijective (centralizer ({w} : Set K)).subtype
      ⟨Subgroup.subtype_injective _, fun x => ⟨⟨x, by rw [hC]; exact mem_top x⟩, rfl⟩⟩
  have hbot : pPrimeCore 2 ↥(centralizer ({w} : Set K)) = ⊥ := by
    have h := pPrimeCore_map_iso 2 e
    rw [hO] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  exact ⟨e.symm.trans (MulEquiv.ofBijective (QuotientGroup.mk' _)
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot],
      QuotientGroup.mk'_surjective _⟩)⟩

end CFSG.GH74.Generic.S1.Exo
