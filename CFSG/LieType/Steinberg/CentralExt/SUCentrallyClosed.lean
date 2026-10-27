module

public import CFSG.LieType.Steinberg.CentralExt.SUPosLift
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

namespace CFSG.LieType.Steinberg.CentralExt.SUClosed

theorem exists_section_of_mulEquiv_sl2
    {p : ℕ} [Fact p.Prime]
    {k : Type} [Field k] [Finite k] [CharP k p] {G : Type*} [Group G] {E : Type*} [Group E]
    [Finite E] {π : E →* G} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) {L : Subgroup G} (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) k) :
    ∃ φ : L →* E, ∀ g, π (φ g) = g := by
  obtain ⟨ρ, hρ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := p) hπ hcen hC
    (L.subtype.comp e.symm.toMonoidHom)
  refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
  have h := DFunLike.congr_fun hρ (e g)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    Subgroup.coe_subtype] at h
  exact h

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

include hF in
theorem exists_rankOne_section_coprime
    (he : Even n) (hn : 2 ≤ n)
    {E : Type*} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F p f) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n) k) →* E,
      ∀ g, π (φ g) = g := by
  by_cases hk : k.val + 1 < n / 2
  · exact exists_section_of_mulEquiv_sl2 hπ hcen hC (rankOneShortEquiv hk)
  · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he hn hk
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    exact exists_section_of_mulEquiv_sl2 hπ hcen hC (e.trans (hypEquiv hζ0 hζ).symm)

include hF in
theorem su_exists_section_of_coprime
    (he : Even n) (hn : 2 ≤ n)
    {E : Type*} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F p f) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : p.Coprime (Nat.card π.ker)) :
    ∃ s : SU (unitaryInvolution F p f) n →* E, ∀ g, π (s g) = g := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd hp.out).1 hC
  obtain ⟨s, hs, -⟩ := existsUnique_section_of_rankOne_lift (D := rootDatum hF n)
    (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC'
    (exists_rankOne_section_coprime hF he hn hπ hcen hC')
  exact ⟨s, hs⟩

include hF in
theorem su_exists_section_of_central
    (he : Even n) (hn : 4 ≤ n)
    (hq : 4 ≤ p ^ f) {E : Type} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F p f) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : SU (unitaryInvolution F p f) n →* E, ∀ g, π (s g) = g :=
  CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => su_exists_section_of_pKernel hF he hn hq hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => su_exists_section_of_coprime hF he (by omega) hπ' hcen' hc')

end CFSG.LieType.Steinberg.CentralExt.SUClosed
