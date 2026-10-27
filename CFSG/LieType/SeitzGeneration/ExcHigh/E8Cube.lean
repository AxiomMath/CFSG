module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Rank4
public import CFSG.LieType.SeitzGeneration.ExcHigh.FrameGlue
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
public import CFSG.LieType.SeitzGeneration.ExcHigh.FrameLayer

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.AnisoE6 TauCeti
  CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def E8FrameData (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ) : Prop :=
  ∃ V₁ V₂ X₁ X₂ : Subgroup (Cat ⟨.E8 q, hv⟩),
    IsElemAbelian p V₁ ∧ IsElemAbelian p V₂ ∧ Nat.card V₁ = p ^ 2 ∧ Nat.card V₂ = p ^ 2 ∧
    Disjoint V₁ V₂ ∧ (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧
    V₁ ≤ X₁ ∧ V₂ ≤ X₂ ∧
    (∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) ∧
    (∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g) ∧ (∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g) ∧
    X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g} ∧
    X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g} ∧
    Nat.card X₁ ≤ ordTrialityD4 q.card ∧ Nat.card X₂ ≤ ordTrialityD4 q.card ∧
    (∀ H : Subgroup (Cat ⟨.E8 q, hv⟩), X₁ ⊔ X₂ ≤ H →
      ¬ H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup (Cat ⟨.E8 q, hv⟩)) : Set (Cat ⟨.E8 q, hv⟩))
        → H = ⊤) ∧
    (∀ H : Subgroup (Cat ⟨.E8 q, hv⟩),
      H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup (Cat ⟨.E8 q, hv⟩)) : Set (Cat ⟨.E8 q, hv⟩)) →
      Group.IsSolvable ↥(H ⊓ (X₁ ⊔ X₂)) → Group.IsSolvable ↥H)

@[expose] def E8FrameFactors (e : ℕ) : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p → p ≠ q.p →
    orderOf ((q.card : ℕ) : ZMod p) = e → E8FrameData q hv p

@[expose] def E8LeviPiece (e : ℕ) : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p → p ≠ q.p →
    orderOf ((q.card : ℕ) : ZMod p) = e →
    ∀ V : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V → Nat.card V = p ^ 4 →
      ∃ P : Subgroup (Cat ⟨.E8 q, hv⟩), LeviLayer _ p V P ∧ CFSG.Open.IsQuasisimple ↥P ∧
        ordTrialityD4 q.card ^ 2 < Nat.card ↥P

theorem planeGen_of_frame_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hS : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4)
    (hinj : Function.Injective (MulAut.conj : Cat ⟨.E8 q, hv⟩ →* MulAut (Cat ⟨.E8 q, hv⟩)))
    (hfr : E8FrameData q hv p)
    (hlay : ∀ V : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V → Nat.card V = p ^ 4 →
      ∃ P : Subgroup (Cat ⟨.E8 q, hv⟩), LeviLayer _ p V P ∧ CFSG.Open.IsQuasisimple ↥P ∧
        ordTrialityD4 q.card ^ 2 < Nat.card ↥P)
    {E : Subgroup (MulAut (Cat ⟨.E8 q, hv⟩))} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hin : InnerPlane ⟨.E8 q, hv⟩ p E) : PlaneGen E := by
  obtain ⟨V₁, V₂, X₁, X₂, hV₁, hV₂, hV₁c, hV₂c, hdisj, hcomm, -, -, hXc, hX₁V₂, hX₂V₁,
    hPG₁, hPG₂, hXb₁, hXb₂, hclose, hsolv⟩ := hfr
  have hVel : IsElemAbelian p (V₁ ⊔ V₂) := isElemAbelian_sup_of_commute hV₁ hV₂ hcomm
  have hVc : Nat.card ↥(V₁ ⊔ V₂) = p ^ 4 := by
    rw [card_sup_eq_mul_of_commute_disjoint hcomm hdisj, hV₁c, hV₂c]
    ring
  obtain ⟨P, hlayer, hQS, hPbig⟩ := hlay (V₁ ⊔ V₂) hVel hVc
  haveI : Finite (Cat ⟨.E8 q, hv⟩) :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_E8 hv).1
  have hXlt : Nat.card ↥(X₁ ⊔ X₂) < Nat.card ↥P := by
    have h1 := natCard_sup_le_mul_of_commute hXc
    have h2 : Nat.card ↥X₁ * Nat.card ↥X₂ ≤ ordTrialityD4 q.card ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hXb₁ hXb₂
    exact lt_of_le_of_lt (h1.trans h2) hPbig
  have hPX : ¬ P ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup (Cat ⟨.E8 q, hv⟩)) :
      Set (Cat ⟨.E8 q, hv⟩)) :=
    not_le_normalizer_of_isQuasisimple hQS hsolv hXlt
  have hall := planes_of_frame_layer hp hVc (le_sup_left : V₁ ≤ V₁ ⊔ V₂)
    (le_sup_right : V₂ ≤ V₁ ⊔ V₂) hV₁c hV₂c hdisj hcomm (fun x hx => hVel.2 x hx) hX₁V₂ hX₂V₁
    hPG₁ hPG₂ hclose hlayer hPX
  exact planeGen_of_oneV hp hinj hS ⟨V₁ ⊔ V₂, hVel, hVc, fun E hEV _ hEc' => hall E hEV hEc'⟩
    hE hEc hin

theorem seitzExcHighE8Three_of_leaves (h₁ : E8FrameFactors 3) (h₂ : E8LeviPiece 3) :
    SeitzExcHighE8Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hQ, hr, hn⟩
  obtain ⟨hp5, q, hdq, -, hord⟩ := hQ
  have hdq' : d = LieTypeIndex.E8 q := hdq
  subst hdq'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E8 q).symm)
  have h7 := seven_le_of_orderOf_three hp hp5 hord
  exact planeGen_of_frame_E8 hv hp (sylowTorus_cat_E8_three hv hp h7 hpq hord)
    (conj_injective_cat_E8 q hv) (h₁ q hv p hp h7 hpq hord)
    (fun V hV hVc => h₂ q hv p hp h7 hpq hord V hV hVc) hE hc hin

theorem seitzExcHighE8Six_of_leaves (h₁ : E8FrameFactors 6) (h₂ : E8LeviPiece 6) :
    SeitzExcHighE8Six := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hQ, hr, hn⟩
  obtain ⟨hp5, q, hdq, -, hord⟩ := hQ
  have hdq' : d = LieTypeIndex.E8 q := hdq
  subst hdq'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E8 q).symm)
  have h7 := seven_le_of_orderOf_six hp hord
  exact planeGen_of_frame_E8 hv hp (sylowTorus_cat_E8_six hv hp h7 hpq hord)
    (conj_injective_cat_E8 q hv) (h₁ q hv p hp h7 hpq hord)
    (fun V hV hVc => h₂ q hv p hp h7 hpq hord V hV hVc) hE hc hin

end CFSG.LieType.SeitzGeneration.ExcHigh
