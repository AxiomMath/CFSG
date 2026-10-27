module

public import CFSG.GH74.GLS.Basic
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GroupTheory

theorem not_isSolvable_oPrimeResidual_of_quasisimple_image {p : ℕ} (hp : p.Prime)
    {K X R : Type*} [Group K] [Finite K] [Group X] [Group R] (α : K →* R) (β : K →* X)
    (hQ : CFSG.IsQuasisimple ↥α.range)
    (hpQ : p ∣ Nat.card (↥α.range ⧸ Subgroup.center ↥α.range))
    (hker : ¬ p ∣ Nat.card β.ker) :
    ¬ Group.IsSolvable ↥(CFSG.GH74.GLS.oPrimeResidual p X) := by
  classical
  intro hsolv
  have : Fact p.Prime := ⟨hp⟩
  let Q : Subgroup R := α.range
  let Z : Subgroup ↥Q := Subgroup.center ↥Q
  have : IsSimpleGroup (↥Q ⧸ Z) := hQ.2.1
  let α' : K →* ↥Q := α.rangeRestrict
  have hα' : Function.Surjective α' := α.rangeRestrict_surjective
  have : Finite ↥Q := Finite.of_surjective α' hα'
  let σ : K →* (↥Q ⧸ Z) := (QuotientGroup.mk' Z).comp α'
  have hσ : Function.Surjective σ := (QuotientGroup.mk'_surjective Z).comp hα'
  have hkerσ : β.ker ≤ σ.ker := by
    let N' : Subgroup ↥Q := β.ker.map α'
    have : N'.Normal := Subgroup.Normal.map inferInstance α' hα'
    let N'' : Subgroup (↥Q ⧸ Z) := N'.map (QuotientGroup.mk' Z)
    have : N''.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N'' with hbot | htop
    · intro k hk
      have hmem : σ k ∈ N'' := Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem α' hk)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      have h1 : Nat.card N'' ∣ Nat.card β.ker :=
        (Subgroup.card_map_dvd N' (QuotientGroup.mk' Z)).trans (Subgroup.card_map_dvd β.ker α')
      rw [htop, Subgroup.card_top] at h1
      exact hker (hpQ.trans h1)
  have hnotsolv : ¬ Group.IsSolvable (↥Q ⧸ Z) := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hQ.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  let T : Subgroup K := CFSG.GH74.GLS.oPrimeResidual p K
  have hσT : T.map σ = CFSG.GH74.GLS.oPrimeResidual p (↥Q ⧸ Z) :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oPrimeResidual σ hσ hp
  have hσT_top : T.map σ = ⊤ := by
    rw [hσT]
    have : (CFSG.GH74.GLS.oPrimeResidual p (↥Q ⧸ Z)).Normal :=
      CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal p _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (CFSG.GH74.GLS.oPrimeResidual p (↥Q ⧸ Z)) with hbot | htop
    · exfalso
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hpQ
      have hsmem : s ∈ CFSG.GH74.GLS.oPrimeResidual p (↥Q ⧸ Z) :=
        Subgroup.subset_closure ⟨1, by rw [pow_one, ← hs]; exact pow_orderOf_eq_one s⟩
      rw [hbot, Subgroup.mem_bot] at hsmem
      rw [hsmem, orderOf_one] at hs
      exact hp.one_lt.ne hs
    · exact htop
  have hβT : ∀ x ∈ T, β x ∈ CFSG.GH74.GLS.oPrimeResidual p X := by
    intro x hx
    have hle : T ≤ (CFSG.GH74.GLS.oPrimeResidual p X).comap β := by
      apply (Subgroup.closure_le _).mpr
      rintro y ⟨k, hk⟩
      show β y ∈ CFSG.GH74.GLS.oPrimeResidual p X
      exact Subgroup.subset_closure ⟨k, by rw [← map_pow, hk, map_one]⟩
    exact hle hx
  let βT : ↥T →* ↥(CFSG.GH74.GLS.oPrimeResidual p X) :=
    (β.comp T.subtype).codRestrict _ (fun x => hβT x x.2)
  obtain ⟨d, hd⟩ := hsolv.solvable
  let σT : ↥T →* (↥Q ⧸ Z) := σ.comp T.subtype
  have hσT_surj : Function.Surjective σT := by
    intro s
    have : s ∈ T.map σ := by
      rw [hσT_top]
      exact Subgroup.mem_top s
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨t, ht⟩, hts⟩
  have hD : derivedSeries ↥T d ≤ σT.ker := by
    intro x hx
    have h1 : βT x ∈ derivedSeries ↥(CFSG.GH74.GLS.oPrimeResidual p X) d :=
      map_derivedSeries_le_derivedSeries βT d (Subgroup.mem_map_of_mem βT hx)
    rw [hd, Subgroup.mem_bot] at h1
    have h2 : β (x : K) = 1 := congrArg Subtype.val h1
    exact hkerσ h2
  have hS : derivedSeries (↥Q ⧸ Z) d = ⊥ := by
    rw [← map_derivedSeries_eq hσT_surj d, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hD hx
  exact hnotsolv ⟨⟨d, hS⟩⟩

end CFSG.GroupTheory
