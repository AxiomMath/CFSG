module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BA5
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure A5Quot {Y : Type} [Group Y] (J : Subgroup Y) where
  q : ↥J →* A5
  surj : Function.Surjective q
  ker_central : ∀ a : ↥J, q a = 1 → ∀ b : ↥J, a * b = b * a
  central_ker : ∀ a : ↥J, (∀ b : ↥J, a * b = b * a) → q a = 1
  ker_coprime : ∀ a : ↥J, q a = 1 → Nat.Coprime (orderOf a) 5

theorem a5Quot_of_component {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (hJ : IsComponentOf J ⊤)
    (hA : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    Nonempty (A5Quot J) := by
  obtain ⟨e⟩ := hA
  obtain ⟨q, hqdef⟩ : ∃ q : ↥J →* A5, ∀ a : ↥J, q a = e (QuotientGroup.mk a) :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (primeComplementCore (G := ↥J) 5)), fun a => rfl⟩
  have hq : ∀ a : ↥J, q a = 1 ↔ a ∈ primeComplementCore (G := ↥J) 5 := fun a => by
    rw [hqdef]
    exact (e.map_eq_one_iff).trans (QuotientGroup.eq_one_iff a)
  have hsurj : Function.Surjective q := by
    intro g
    obtain ⟨x, hx⟩ := e.surjective g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a, (hqdef a).trans hx⟩
  have hQ : CFSG.IsQuasisimple ↥J := ((CFSG.isComponent_iff_open J).2 hJ).1
  have hnorm : primeComplementCore (G := ↥J) 5 = ⊤ ∨
      primeComplementCore (G := ↥J) 5 ≤ Subgroup.center ↥J :=
    CFSG.LocalCores.quasisimple_normal_subgroups hQ inferInstance
  have hne : primeComplementCore (G := ↥J) 5 ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := a5_exists_ne_one
    obtain ⟨a, ha⟩ := hsurj g
    have hapc : a ∈ primeComplementCore (G := ↥J) 5 := by
      rw [htop]
      exact Subgroup.mem_top a
    exact hg (by rw [← ha]; exact (hq a).2 hapc)
  have hcent : primeComplementCore (G := ↥J) 5 ≤ Subgroup.center ↥J := hnorm.resolve_left hne
  refine ⟨⟨q, hsurj, ?_, ?_, ?_⟩⟩
  · intro a ha b
    have hapc : a ∈ primeComplementCore (G := ↥J) 5 := (hq a).1 ha
    exact ((Subgroup.mem_center_iff.mp (hcent hapc)) b).symm
  · intro a ha
    apply a5_center
    intro g
    obtain ⟨b, rfl⟩ := hsurj g
    calc q b * q a = q (b * a) := (map_mul q b a).symm
      _ = q (a * b) := by rw [ha b]
      _ = q a * q b := map_mul q a b
  · intro a ha
    have hapc : a ∈ primeComplementCore (G := ↥J) 5 := (hq a).1 ha
    have hdvd : orderOf a ∣ Nat.card (primeComplementCore (G := ↥J) 5) := by
      have h := orderOf_dvd_natCard (⟨a, hapc⟩ : primeComplementCore (G := ↥J) 5)
      rwa [Subgroup.orderOf_mk] at h
    exact Nat.Coprime.coprime_dvd_left hdvd (primeComplementCore_coprime 5).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123
