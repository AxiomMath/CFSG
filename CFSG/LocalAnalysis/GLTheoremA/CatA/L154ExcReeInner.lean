module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcRestAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenLabel LargeEvenInnSet)
open CFSG.StandardType (GGOutdiagPrime markTag markRank)

theorem l154_notCfg_of_markTag {p : ℕ} {lab : LargeEvenLabel} {t : CFSG.Open.StatedLieTag}
    (h : markTag lab = t) (ht : t = .twistedF4 ∨ t = .twistedB2) : ¬ L154OutdiagCfg p lab := by
  obtain ⟨tag, l, n⟩ := lab
  intro hc
  rcases ht with rfl | rfl <;>
    cases tag <;> simp [L154OutdiagCfg, markTag] at h hc <;> split_ifs at h

theorem l154_notCfg_of_markTag_markRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : markTag lab = .PSL) (hr : markRank lab = 2) :
    ¬ L154OutdiagCfg p lab := by
  obtain ⟨tag, l, n⟩ := lab
  intro hc
  have hp2' : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  cases tag <;> simp [L154OutdiagCfg, markTag, markRank] at h hr hc
  case A => subst hr; exact hp2' hc.1
  case twD => obtain ⟨rfl, -⟩ := hc; simp at hr

section Inner


theorem l154_inner_of_innDiagOn_nonCfg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ : Type} [Group Γ]
    {K : Subgroup Γ} {x : Γ} (hxN : x ∈ Subgroup.normalizer (K : Set Γ)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) K)
    (hM : LargeEvenMarking (PQuot p K) fun lab _ _ _ _ _ => ¬ L154OutdiagCfg p lab) :
    MI.indAut p K x hxN ∈ OuterAutomorphisms.inner (PSimple p K) := by
  have hdiag : LargeEvenMarking (PQuot p K)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p K x) φ :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  have h2 := MI.marking_transport (indRel p K x) hdiag hM
  have h3 := FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I _ => ¬ L154OutdiagCfg p lab → GGOutdiagPrime p R I)
    (fun lab hlab => ?_) h2
  · obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨hcfg, φ, hφ, hind⟩, hI⟩⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists h3
    have e1 : φ = MulAut.congr θ (MI.indAut p K x hxN) := (MI.induces_indRel_iff hxN θ).1 hind
    have hφp : φ ^ p = 1 := by
      rw [e1, ← map_pow, l154_indAut_pow_eq_one hxN hxp, map_one]
    obtain ⟨g, hg⟩ := hI hcfg φ hφ hφp
    have e2 : MulAut.congr θ.symm (MulAut.conj g) = MulAut.conj (θ.symm g) :=
      OuterAutomorphisms.congr_conj θ.symm g
    have e3 : MulAut.congr θ.symm (MulAut.congr θ (MI.indAut p K x hxN)) =
        MI.indAut p K x hxN := by
      ext y
      simp [MulAut.congr_apply]
    refine ⟨θ.symm g, ?_⟩
    rw [← e2, hg, e1, e3]
  · by_cases hc : L154OutdiagCfg p lab
    · intro Q hQ
      exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F hq => ⟨hq, fun _ _ h => absurd hc h⟩) hQ
    · intro Q hQ
      exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F ⟨hq, hg⟩ => ⟨hq, fun hs hna _ => hg hs hna⟩)
        (l154_outdiagPrime hp hp2 hlab hc Q hQ)

end Inner

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
