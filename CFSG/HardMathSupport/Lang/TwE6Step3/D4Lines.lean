module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Assembly

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Malle.SeitzCube
open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)


section IsoLieNeg



theorem planeGen_graphFixed_neg
    {ℓ f p : ℕ} (hphi : PhiPlaneGenAt (-1) p) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {X : Type} [Field X] [Finite X] (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    PlaneGen (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) p :=
  fun E hE hcard => hphi ℓ f hℓ hℓ2 hf X hX σ hσ hp hpℓ hd E hE hcard

theorem planeGen_of_isoLie_neg {Y : Type} [Group Y] {q : PrimePower}
    (hiso : IsoLie Y (.trialityD4 q)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (hdvd : (p : ℤ) ∣ (q.card : ℤ) ^ 2 + (-1) * (q.card : ℤ) + 1)
    (hphi : q.p ≠ 2 → PhiPlaneGenAt (-1) p)
    (hext : q.p = 2 → ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True)
    (hfs : q.p = 2 → Finite Y ∧ IsSimpleGroup Y) :
    PlaneGen Y p := by
  by_cases hq : q.p = 2
  · obtain ⟨hfin, hsimp⟩ := hfs hq
    exact planeGen_even hq (hext hq) hiso hp5
  · obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_trialityD4_model_of_isoLie hiso
    have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    rw [hqc] at hX hσ hdvd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    exact planeGen_of_mulEquiv e
      (planeGen_graphFixed_neg (hphi hq) q.prime_p hq q.exponent_pos hX σ hσ (Fact.out) hpq hdvd)

end IsoLieNeg

theorem mem_hyperClosure_of_split {G : Type} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {E Y E' : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hYy : ∀ g ∈ Y, g * y = y * g)
    (hdisj : Disjoint (Subgroup.zpowers y) Y) (hE'E : E' ≤ E) (hE'Y : E' ≤ Y)
    (hE'c : Nat.card E' = p ^ 2) (hgen : PlaneGen ↥Y p) {t g : G}
    (ht : ∀ e ∈ E, t * e = e * t) (hg : g ∈ Y) : t * g ∈ hyperClosure p ⊤ E := by
  have hord : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hYE : Y ≤ hyperClosure p ⊤ E := by
    refine le_hyperClosure_of_planeGen hE hEc (B := Subgroup.zpowers y) ?_ ?_ hdisj ?_ hE'E hE'Y
      hE'c hgen
    · exact Subgroup.zpowers_le.2 hy
    · rw [Nat.card_zpowers, hord]
    · intro g hg b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (show Commute g y from hYy g hg).zpow_right n
  obtain ⟨e, he, hey⟩ := exists_mem_not_mem_zpowers hE hEc hy
  have htE : t ∈ hyperClosure p ⊤ E :=
    mem_hyperClosure_of_commute_pair hE hEc hy he hy1 hey (ht y hy) (ht e he)
  exact mul_mem htE (hYE hg)

end CFSG.HardMathSupport.Lang.TwE6Step3
