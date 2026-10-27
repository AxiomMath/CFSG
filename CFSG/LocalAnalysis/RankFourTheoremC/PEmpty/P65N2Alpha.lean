module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Key
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Perfect
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem card_le_of_cyclic {A : Type} [Group A] [Finite A] {p : ℕ} (hp : 0 < p) {H T : Subgroup A}
    (hH : IsCyclic H) (hTH : T ≤ H) (hT : ∀ t ∈ T, t ^ p = 1) : Nat.card T ≤ p := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI := hH
  have h := IsCyclic.card_pow_eq_one_le (α := ↥H) hp
  have h2 : (Finset.univ : Finset ↥T).card ≤
      (Finset.univ.filter (fun a : ↥H => a ^ p = 1)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (⟨t.1, hTH t.2⟩ : ↥H)) ?_ ?_
    · intro t _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact Subtype.ext (by simpa using hT t t.2)
    · intro a _ b _ hab
      have := congrArg (fun x : ↥H => (x : A)) hab
      exact Subtype.ext this
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact h2.trans h

theorem card_le_of_pRank_le {A : Type} [Group A] [Finite A] {f : ℕ} (hf : f.Prime)
    {X Fs : Subgroup A} (hFX : Fs ≤ X) (hX : Open.pRank f X ≤ 3) :
    ∀ E : Subgroup A, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ f = 1) →
      Nat.card E ≤ f ^ 3 := by
  intro E hEF hEc hEp
  haveI : Fact f.Prime := ⟨hf⟩
  have hEf : IsPGroup f E := fun g => ⟨1, Subtype.ext (by simpa using hEp g g.2)⟩
  obtain ⟨k, hk⟩ := hEf.exists_card_eq
  have hEab : IsElemAbelian f E := ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, hEp⟩
  have := CFSG.SectionRank.le_pRank hf.one_lt (hEF.trans hFX) hEab hk
  rw [hk]
  exact Nat.pow_le_pow_right hf.pos (this.trans hX)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}

@[expose] def coreA (p : ℕ) (X : Subgroup A) : Subgroup A :=
  (primeComplementCore (G := ↥X) p).map X.subtype

theorem coreA_le : coreA p X ≤ X := Subgroup.map_subtype_le _

theorem coreA_card (hp : p.Prime) : ¬ p ∣ Nat.card (coreA p X) := by
  have h1 : Nat.card (coreA p X) = Nat.card (primeComplementCore (G := ↥X) p) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h1]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)

theorem coreA_conj : ∀ g ∈ X, ∀ d ∈ coreA p X, g * d * g⁻¹ ∈ coreA p X := by
  rintro g hg _ ⟨d, hd, rfl⟩
  exact ⟨⟨g, hg⟩ * d * ⟨g, hg⟩⁻¹, (primeComplementCore_normal (G := ↥X) p).conj_mem d hd _, rfl⟩

theorem coreA_normalizer : X ≤ normalizer (coreA p X : Set A) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro d
  refine ⟨fun hd => coreA_conj g hg d hd, fun hd => ?_⟩
  have := coreA_conj g⁻¹ (X.inv_mem hg) _ hd
  simpa [mul_assoc] using this

theorem p65N2_sylow_of_le_core (hpl : Plane65 p P X x z) {f : ℕ} (hf : f.Prime)
    {Fs : Subgroup A} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs)
    (hFD : Fs ≤ coreA p X) : fusionIsSylowIn f Fs (coreA p X) := by
  have hprime := hpl.prime
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup A := zpowers x ⊔ zpowers z with hBdef
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hBP : B ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hBX : B ≤ X := hBP.trans hpl.sylow_le
  obtain ⟨⟨_, hF2, hBF⟩, hmax⟩ := hF
  have hBD : B ≤ normalizer (coreA p X : Set A) := hBX.trans coreA_normalizer
  obtain ⟨S, hSsyl, hFS, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hprime hf hB3 (coreA_card hprime) hBD hFD hF2 hBF
  have hSF : S = Fs := hmax S ⟨hSsyl.1.trans coreA_le, hSsyl.2.1, hBS⟩ hFS
  rwa [← hSF]

theorem p65N2_le_core (hpl : Plane65 p P X x z) (hcon : HasPrimeConstraint (G := ↥X) p)
    {f : ℕ} (hf : f.Prime) (hfp : f ≠ p) {Fs : Subgroup A}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs) :
    fusionIsSylowIn f Fs (coreA p X) := by
  have hprime := hpl.prime
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup A := zpowers x ⊔ zpowers z with hBdef
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hBP : B ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hBX : B ≤ X := hBP.trans hpl.sylow_le
  have hFX := hF.1.1
  have hF2 := hF.1.2.1
  have hBF := hF.1.2.2
  have hF3 : Nat.Coprime p (Nat.card Fs) := by
    obtain ⟨k, hk⟩ := hF2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime hf).mpr hfp.symm)
  have hFD : Fs ≤ coreA p X := ambient_prime_constraint_signalizer_le_core p hprime
    (by have := hpl.five_le; omega) X B Fs hcon hB3 hBX hF3 hFX hBF
    (fun y _ hyB hord => hpl.plane.mem_of_mem_centralizer y hyB (by
      rw [← hord]
      exact pow_orderOf_eq_one y))
  exact p65N2_sylow_of_le_core hpl hf hF hFD

theorem p65N2_frattini (hp : p.Prime) {f : ℕ} (hf : f.Prime) {Fs : Subgroup A}
    (hsyl : fusionIsSylowIn f Fs (coreA p X)) :
    ∀ g ∈ X, ∃ d ∈ coreA p X, ∃ n ∈ X ⊓ normalizer (Fs : Set A), g = d * n := by
  intro g hg
  have hFm := p65_fusionIsSylowIn_conj hsyl (coreA_normalizer hg)
  have hbotp : IsPGroup p (⊥ : Subgroup A) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨c, hc, hFc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    hp hf hbotp (coreA_card hp) bot_le hsyl hFm bot_le bot_le
  have hcD : c ∈ coreA p X := (mem_inf.mp hc).1
  have hn := p65_mem_normalizer_of_map_eq hFc
  exact ⟨c, hcD, c⁻¹ * g, mem_inf.mpr ⟨X.mul_mem (X.inv_mem (coreA_le hcD)) hg, hn⟩,
    (mul_inv_cancel_left c g).symm⟩

theorem p65N2_of_sylow (hpl : Plane65 p P X x z) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (hfp : f ≠ p) {Fs R : Subgroup A} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs)
    (hFsyl : fusionIsSylowIn f Fs (coreA p X)) (hRN : R ≤ X ⊓ normalizer (Fs : Set A))
    (hR4 : 4 ≤ Open.pRank p R) (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A)) :
    4 ≤ Open.pRank f X := by
  by_contra hlt
  push Not at hlt
  have hX3 : Open.pRank f X ≤ 3 := by omega
  haveI : Fact f.Prime := ⟨hf⟩
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : NeZero f := ⟨hf.ne_zero⟩
  have hFsf : IsPGroup f Fs := hF.1.2.1
  obtain ⟨χ, hχ⟩ := exists_rank_bound hf2 hprime hfp.symm hFsf (N := X ⊓ normalizer (Fs : Set A))
    inf_le_right (card_le_of_pRank_le hf hF.1.1 hX3)
  obtain ⟨E, hER, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hprime hR4
  have hEN : E ≤ X ⊓ normalizer (Fs : Set A) := hER.trans hRN
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hχE : ∀ (a : A) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1 := fun a ha =>
    trivial_of_perfect hprime (fun M _ h => hpl.perfect M h) coreA_le coreA_conj
      (coreA_card hprime) inf_le_left (p65N2_frattini hprime hf hFsyl) χ a (hEN ha) 1
      (by simpa using hEab.2 a ha)
  have h1 := hχ E hEN hEc hEab.2 hχE
  have h2 : Nat.card (E ⊓ centralizer (Fs : Set A) : Subgroup A) ≤ p :=
    card_le_of_cyclic hprime.pos hcyc (inf_le_inf_right _ hER) (fun t ht => hEab.2 t ht.1)
  rw [hEcard] at h1
  have h3 : p ^ 4 ≤ p ^ 2 * p := h1.trans (Nat.mul_le_mul_left _ h2)
  have h4 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hprime.one_lt (by norm_num)
  have h5 : p ^ 2 * p = p ^ 3 := by ring
  omega

theorem p65N2_alpha (hpl : Plane65 p P X x z) (hcon : HasPrimeConstraint (G := ↥X) p)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {Fs R : Subgroup A}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hR4 : 4 ≤ Open.pRank p R)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A)) :
    4 ≤ Open.pRank f X :=
  p65N2_of_sylow hpl hf hf2 hfp hF (p65N2_le_core hpl hcon hf hfp hF) hRN hR4 hcyc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
