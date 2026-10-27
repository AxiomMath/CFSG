module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutN0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_claim1 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {Qs : Subgroup (ProjSim Q)}
    (hPQ : ffPS hQ fr ≤ Qs) (hQN : Qs ≤ normalizer (ffPS hQ fr : Set (ProjSim Q)))
    (hi : ∀ q ∈ Qs, ∀ α : ℤˣ, ¬ SimHasType q 1 α ∧ ¬ SimHasType q 3 α)
    (hii : ∀ q ∈ Qs, q ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) →
      ∃ w ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)), SimInOmegaStar hQ w ∧
        ∀ β ∈ ffBS hQ fr, q * β * q⁻¹ = w * β * w⁻¹) :
    ∀ q ∈ Qs, SimInGStar q → q ∈ ffPS hQ fr := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  intro q hq hqG
  have hqN : q ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) := hQN hq
  obtain ⟨σ, K, hqeq, hσ⟩ := ff_N0_monomial hQ hdim hsgn fr hqN hqG
  have hqBS : q ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) := by
    rw [hqeq]; exact ffM_mem_normalizer_ffBS hQ fr σ K
  obtain ⟨w, hwN, hwΩ, hact⟩ := hii q hq hqBS
  obtain ⟨σ', K', hweq⟩ := ff_normalizer_ffBS_monomial hQ h2 fr hwN
  have hwΩ' : SimInOmegaStar hQ (ffM fr σ' K') := hweq ▸ hwΩ
  have hsign' : Equiv.Perm.sign σ' = 1 ∧ Even K'.card :=
    (ffM_simInOmegaStar_iff hQ hdim hsgn fr σ' K').mp hwΩ'
  have hperm : σ'⁻¹ * σ = 1 := by
    apply ff_perm_eq_one_of_even
    intro J hJ
    have hJBS : ffM fr 1 J ∈ ffBS hQ fr :=
      (ffM_mem_ffBS_iff hQ fr 1 J).mpr ⟨rfl, hJ⟩
    have hconj := hact (ffM fr 1 J) hJBS
    rw [hqeq, hweq, ffM_conj_signChange fr σ K J,
      ffM_conj_signChange fr σ' K' J] at hconj
    rcases ((ffM_eq_iff fr).mp hconj).2 with h | h
    · left
      calc J.map (σ'⁻¹ * σ).toEmbedding
          = (J.map σ.toEmbedding).map σ'⁻¹.toEmbedding :=
            ffOutClass_map_perm_mul J σ'⁻¹ σ
        _ = (J.map σ'.toEmbedding).map σ'⁻¹.toEmbedding := by rw [h]
        _ = J.map (σ'⁻¹ * σ').toEmbedding :=
            (ffOutClass_map_perm_mul J σ'⁻¹ σ').symm
        _ = J.map (1 : Equiv.Perm (Fin 6)).toEmbedding := by rw [inv_mul_cancel σ']
        _ = J := ffOutClass_map_one J
    · right
      calc J.map (σ'⁻¹ * σ).toEmbedding
          = (J.map σ.toEmbedding).map σ'⁻¹.toEmbedding :=
            ffOutClass_map_perm_mul J σ'⁻¹ σ
        _ = ((J.map σ'.toEmbedding)ᶜ).map σ'⁻¹.toEmbedding := by rw [h]
        _ = ((J.map σ'.toEmbedding).map σ'⁻¹.toEmbedding)ᶜ :=
            (ffOutClass_map_compl σ'⁻¹ (J.map σ'.toEmbedding)).symm
        _ = (J.map (σ'⁻¹ * σ').toEmbedding)ᶜ := by
            rw [(ffOutClass_map_perm_mul J σ'⁻¹ σ').symm]
        _ = (J.map (1 : Equiv.Perm (Fin 6)).toEmbedding)ᶜ := by rw [inv_mul_cancel σ']
        _ = Jᶜ := by rw [ffOutClass_map_one]
  have hσσ' : σ = σ' := (eq_of_inv_mul_eq_one hperm).symm
  have hsignσ : Equiv.Perm.sign σ = 1 := by rw [hσσ', hsign'.1]
  have hD : σ ∈ monoD := ff_normalizer_even hσ hsignσ
  by_cases hKeven : Even K.card
  · rw [hqeq]; exact (ffM_mem_ffPS_iff hQ fr σ K).mpr ⟨hD, hKeven⟩
  · exfalso
    have hq1mem : (ffM fr σ ∅)⁻¹ * q ∈ Qs :=
      Qs.mul_mem (Qs.inv_mem (hPQ ((ffM_mem_ffPS_iff hQ fr σ ∅).mpr ⟨hD, ⟨0, rfl⟩⟩))) hq
    have hq1eq : (ffM fr σ ∅)⁻¹ * q = ffM fr 1 K := by
      rw [hqeq]; exact ffOutClass_ffM_inv_mul fr σ K
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hKeven
    have hKle : K.card ≤ 6 := by simpa using Finset.card_le_univ K
    by_cases h5 : K.card = 5
    · have hcardc : Kᶜ.card = 1 := by
        simp [Finset.card_compl, h5]
      have hq1eqc : (ffM fr σ ∅)⁻¹ * q = ffM fr 1 Kᶜ := by
        rw [hq1eq, ffM_compl]
      obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := Kᶜ) (Or.inl hcardc)
      have htype : SimHasType ((ffM fr σ ∅)⁻¹ * q) 1 α := by
        rw [hq1eqc]
        have he : ffM fr 1 Kᶜ = projOrthToProjSim Q (toProj Q (fr.signChange Kᶜ)) := by
          unfold ffM; rw [fr.permOrth_one, one_mul]
        rw [he, ← hcardc]; exact hα
      exact (hi _ hq1mem α).1 htype
    · have hcard13 : K.card = 1 ∨ K.card = 3 := by omega
      obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := K) hcard13
      have htype : SimHasType ((ffM fr σ ∅)⁻¹ * q) K.card α := by
        rw [hq1eq]
        have he : ffM fr 1 K = projOrthToProjSim Q (toProj Q (fr.signChange K)) := by
          unfold ffM; rw [fr.permOrth_one, one_mul]
        rw [he]; exact hα
      rcases hcard13 with h1 | h3
      · exact (hi _ hq1mem α).1 (by rw [h1] at htype; exact htype)
      · exact (hi _ hq1mem α).2 (by rw [h3] at htype; exact htype)

theorem ff_out_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {Qs : Subgroup (ProjSim Q)}
    (hPQ : ffPS hQ fr ≤ Qs) (hQN : Qs ≤ normalizer (ffPS hQ fr : Set (ProjSim Q)))
    (hi : ∀ q ∈ Qs, ∀ α : ℤˣ, ¬ SimHasType q 1 α ∧ ¬ SimHasType q 3 α)
    (hii : ∀ q ∈ Qs, q ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) →
      ∃ w ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)), SimInOmegaStar hQ w ∧
        ∀ β ∈ ffBS hQ fr, q * β * q⁻¹ = w * β * w⁻¹) :
    (∀ q ∈ Qs, SimInOmegaStar hQ q) ∨
      ∃ x ∈ Qs, ¬ SimInGStar x ∧ x * x = 1 ∧
        ∀ q ∈ Qs, ∃ (n : ℤ) (p : ProjSim Q), p ∈ ffPS hQ fr ∧ q = x ^ n * p := by
  by_cases hΩ : ∀ q ∈ Qs, SimInOmegaStar hQ q
  · exact Or.inl hΩ
  · push_neg at hΩ
    obtain ⟨q₀, hq₀, hq₀Ω⟩ := hΩ
    have hex : ∃ x ∈ Qs, ¬ SimInGStar x := by
      by_contra h
      push_neg at h
      have hq₀PS : q₀ ∈ ffPS hQ fr :=
        ff_claim1 hQ hdim hsgn fr hPQ hQN hi hii q₀ hq₀ (h q₀ hq₀)
      change q₀ ∈ (ffP1 hQ fr).map (ffOmegaToSim hQ) at hq₀PS
      obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.mp hq₀PS
      exact hq₀Ω ⟨(p : ProjOrth Q), p.2, (ffOmegaToSim_apply hQ p).symm.trans hpq⟩
    obtain ⟨x, hxQ, hxG⟩ := hex
    have hxN : x ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) := hQN hxQ
    have hhN : (ffX0 fr)⁻¹ * x ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
      (normalizer (ffPS hQ fr : Set (ProjSim Q))).mul_mem
        ((normalizer (ffPS hQ fr : Set (ProjSim Q))).inv_mem
          (ffX0_mem_normalizer_ffPS hQ fr)) hxN
    have hhG : SimInGStar ((ffX0 fr)⁻¹ * x) :=
      ffSimInGStar_inv_mul_of_not (ffX0_not_simInGStar fr) hxG
    obtain ⟨σ, K, hhEq, hσ⟩ := ff_N0_monomial hQ hdim hsgn fr hhN hhG
    have hxinvG : ¬ SimInGStar x⁻¹ := fun h => hxG (by simpa using ffSimInGStar_inv h)
    have key : ∀ x₁ ∈ Qs, ¬ SimInGStar x₁ → x₁ * x₁ = 1 →
        ∀ q ∈ Qs, ∃ (n : ℤ) (p : ProjSim Q), p ∈ ffPS hQ fr ∧ q = x₁ ^ n * p := by
      intro x₁ hx₁Q hx₁G _ q hq
      by_cases hqG : SimInGStar q
      · exact ⟨0, q, ff_claim1 hQ hdim hsgn fr hPQ hQN hi hii q hq hqG,
          by rw [zpow_zero, one_mul]⟩
      · have hq'G : SimInGStar (x₁⁻¹ * q) := ffSimInGStar_inv_mul_of_not hx₁G hqG
        have hq'Q : x₁⁻¹ * q ∈ Qs := Qs.mul_mem (Qs.inv_mem hx₁Q) hq
        exact ⟨1, x₁⁻¹ * q, ff_claim1 hQ hdim hsgn fr hPQ hQN hi hii _ hq'Q hq'G,
          by rw [zpow_one, mul_inv_cancel_left]⟩
    rcases ff_N0_class hQ fr hσ K with hPS | haPS | hbPS | hrPS
    · have hmem : (ffX0 fr)⁻¹ * x ∈ ffPS hQ fr := by rwa [hhEq]
      have hξQ : ffX0 fr ∈ Qs := by
        have hξeq : ffX0 fr = x * ((ffX0 fr)⁻¹ * x)⁻¹ := by group
        rw [hξeq]
        exact Qs.mul_mem hxQ (Qs.inv_mem (hPQ hmem))
      exact Or.inr ⟨ffX0 fr, hξQ, ffX0_not_simInGStar fr, ffX0_mul_self fr,
        key (ffX0 fr) hξQ (ffX0_not_simInGStar fr) (ffX0_mul_self fr)⟩
    · exfalso
      set g : ProjSim Q := (ffM fr 1 {0})⁻¹ * ffM fr σ K with hgdef
      have hgPS : g ∈ ffPS hQ fr := by rw [hgdef]; exact haPS
      have hxg : x = ffX0 fr * ((ffM fr 1 {0}) * g) := by
        rw [hgdef, ← hhEq]; group
      have hxxQ : x * x ∈ Qs := Qs.mul_mem hxQ hxQ
      have hxxG : SimInGStar (x * x) := by
        have hh := ffSimInGStar_inv_mul_of_not hxinvG hxG
        simpa using hh
      have hxxPS : x * x ∈ ffPS hQ fr :=
        ff_claim1 hQ hdim hsgn fr hPQ hQN hi hii _ hxxQ hxxG
      have hsq : (ffX0 fr * ((ffM fr 1 {0}) * g)) *
          (ffX0 fr * ((ffM fr 1 {0}) * g)) ∈ ffPS hQ fr := by rw [← hxg]; exact hxxPS
      have hnorm : (ffM fr 1 {0}) ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
        ffM_mem_normalizer_ffPS hQ fr (fun τ hτ => by simpa using hτ) {0}
      have hres := ffOut_sq_aux (H := ProjSim Q) (P := ffPS hQ fr)
        (x := ffX0 fr) (c := ffM fr 1 {0}) (g := g)
        (ffX0_mul_self fr) (ffX0_mem_normalizer_ffPS hQ fr) hnorm hgPS hsq
      have hnotPS : ffM fr ffBeta {2} ∉ ffPS hQ fr := fun hmem =>
        ff_beta_not_mem ((ffM_mem_ffPS_iff hQ fr ffBeta {2}).mp hmem).1
      rw [ffOutClass_conj_a fr, ffOutClass_a_mul fr] at hres
      exact hnotPS hres
    · exfalso
      set g : ProjSim Q := (ffM fr ffBeta ∅)⁻¹ * ffM fr σ K with hgdef
      have hgPS : g ∈ ffPS hQ fr := by rw [hgdef]; exact hbPS
      have hxg : x = ffX0 fr * ((ffM fr ffBeta ∅) * g) := by
        rw [hgdef, ← hhEq]; group
      have hxxQ : x * x ∈ Qs := Qs.mul_mem hxQ hxQ
      have hxxG : SimInGStar (x * x) := by
        have hh := ffSimInGStar_inv_mul_of_not hxinvG hxG
        simpa using hh
      have hxxPS : x * x ∈ ffPS hQ fr :=
        ff_claim1 hQ hdim hsgn fr hPQ hQN hi hii _ hxxQ hxxG
      have hsq : (ffX0 fr * ((ffM fr ffBeta ∅) * g)) *
          (ffX0 fr * ((ffM fr ffBeta ∅) * g)) ∈ ffPS hQ fr := by rw [← hxg]; exact hxxPS
      have hnorm : (ffM fr ffBeta ∅) ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
        ffM_mem_normalizer_ffPS hQ fr (fun τ hτ => ff_beta_conj_mem hτ) ∅
      have hres := ffOut_sq_aux (H := ProjSim Q) (P := ffPS hQ fr)
        (x := ffX0 fr) (c := ffM fr ffBeta ∅) (g := g)
        (ffX0_mul_self fr) (ffX0_mem_normalizer_ffPS hQ fr) hnorm hgPS hsq
      have hnotPS : ffM fr ffBeta {0} ∉ ffPS hQ fr := fun hmem =>
        ff_beta_not_mem ((ffM_mem_ffPS_iff hQ fr ffBeta {0}).mp hmem).1
      rw [ffOutClass_conj_b fr, ffOutClass_b_mul fr] at hres
      exact hnotPS hres
    · set ρ : ProjSim Q := ffM fr ffRhoPerm ffRhoSet with hρdef
      have hρh : ρ⁻¹ * ((ffX0 fr)⁻¹ * x) ∈ ffPS hQ fr := by
        rw [hρdef]; rwa [hhEq]
      have hx₁Q : ffX0 fr * ρ ∈ Qs := by
        have hxx : x = ffX0 fr * ((ffX0 fr)⁻¹ * x) := by group
        have heq : ffX0 fr * ρ = x * (ρ⁻¹ * ((ffX0 fr)⁻¹ * x))⁻¹ := by
          rw [hxx]; group
        rw [heq]
        exact Qs.mul_mem hxQ (Qs.inv_mem (hPQ hρh))
      have hx₁G : ¬ SimInGStar (ffX0 fr * ρ) := by
        intro h
        have hρG : SimInGStar ρ := by rw [hρdef]; exact ffM_simInGStar fr _ _
        have hξG : SimInGStar (ffX0 fr) := by
          have hh := ffSimInGStar_mul h (ffSimInGStar_inv hρG)
          simpa [mul_assoc] using hh
        exact ffX0_not_simInGStar fr hξG
      have hx₁sq : (ffX0 fr * ρ) * (ffX0 fr * ρ) = 1 := by
        have hξρ : ffX0 fr * ρ = ρ * ffX0 fr := by rw [hρdef]; exact ffX0_conj_rho fr
        calc (ffX0 fr * ρ) * (ffX0 fr * ρ)
            = ffX0 fr * (ρ * ffX0 fr) * ρ := by group
          _ = ffX0 fr * (ffX0 fr * ρ) * ρ := by rw [← hξρ]
          _ = (ffX0 fr * ffX0 fr) * (ρ * ρ) := by group
          _ = 1 := by simp [ffX0_mul_self fr, hρdef, ffRho_mul_self fr]
      exact Or.inr ⟨ffX0 fr * ρ, hx₁Q, hx₁G, hx₁sq, key _ hx₁Q hx₁G hx₁sq⟩

end CFSG.OddStandard.SmallF3.Omega
