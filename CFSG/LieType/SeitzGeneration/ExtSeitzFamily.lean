module

public import CFSG.LieType.SeitzGeneration.ExtSeitzBridge
public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP

theorem extSeitzAtInnerFor_union {d : TauCeti.LieTypeIndex} {P P₁ P₂ : ℕ → Prop}
    (hP : ∀ p, p.Prime → 5 ≤ p → P p → P₁ p ∨ P₂ p) (h₁ : ExtSeitzAtInnerFor d P₁)
    (h₂ : ExtSeitzAtInnerFor d P₂) : ExtSeitzAtInnerFor d P :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hPp E hE hcard hin =>
    (hP p hp hp5 hPp).elim
      (fun h => h₁ K hnab hiso p hp hp5 hpd h E hE hcard hin)
      (fun h => h₂ K hnab hiso p hp hp5 hpd h E hE hcard hin)

theorem extSeitzAtOuterFor_union {d : TauCeti.LieTypeIndex} {P P₁ P₂ : ℕ → Prop}
    (hP : ∀ p, p.Prime → 5 ≤ p → P p → P₁ p ∨ P₂ p) (h₁ : ExtSeitzAtOuterFor d P₁)
    (h₂ : ExtSeitzAtOuterFor d P₂) : ExtSeitzAtOuterFor d P :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hPp E hE hcard hout =>
    (hP p hp hp5 hPp).elim
      (fun h => h₁ K hnab hiso p hp hp5 hpd h E hE hcard hout)
      (fun h => h₂ K hnab hiso p hp hp5 hpd h E hE hcard hout)

theorem ExtSeitzAtInnerFor.of_cond {d : TauCeti.LieTypeIndex} {C : Prop} {P : ℕ → Prop}
    (h : C → ExtSeitzAtInnerFor d P) : ExtSeitzAtInnerFor d fun p => C ∧ P p :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hPp E hE hcard hin =>
    h hPp.1 K hnab hiso p hp hp5 hpd hPp.2 E hE hcard hin

theorem ExtSeitzAtOuterFor.of_cond {d : TauCeti.LieTypeIndex} {C : Prop} {P : ℕ → Prop}
    (h : C → ExtSeitzAtOuterFor d P) : ExtSeitzAtOuterFor d fun p => C ∧ P p :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hPp E hE hcard hout =>
    h hPp.1 K hnab hiso p hp hp5 hpd hPp.2 E hE hcard hout

theorem seitzPlanes_inner_family {α : Type*} {c : α → TauCeti.LieTypeIndex} {P : α → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtInnerFor (c a) (P a)) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ ∃ a, d.1 = c a ∧ 5 ≤ p ∧ P a p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, a, rfl, hp5, hP⟩
  obtain ⟨hfin, hsimple⟩ := hfs a hv
  exact planeGen_of_extSeitzAtInnerFor (h a) hp hp5 hpd hex hP hE hc hin

theorem seitzPlanes_outer_family {α : Type*} {c : α → TauCeti.LieTypeIndex} {P : α → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtOuterFor (c a) (P a)) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ∃ a, d.1 = c a ∧ 5 ≤ p ∧ P a p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, a, rfl, hp5, hP⟩
  obtain ⟨hfin, hsimple⟩ := hfs a hv
  exact planeGen_of_extSeitzAtOuterFor (h a) hp hp5 hpd hex hP hE hc hout

theorem seitzExcAnisotropicForAt_family {α : Type*} {c : α → TauCeti.LieTypeIndex}
    {P : α → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtInnerFor (c a) (P a)) :
    SeitzExcAnisotropicForAt (fun d => ∃ a, d = c a) (fun d p => ∃ a, d = c a ∧ 5 ≤ p ∧ P a p) :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.2.1⟩) (seitzPlanes_inner_family hfs h)

theorem seitzExcOuterNarrowForAt_family {α : Type*} {c : α → TauCeti.LieTypeIndex}
    {P : α → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtOuterFor (c a) (P a)) :
    SeitzExcOuterNarrowForAt (fun d => ∃ a, d = c a) (fun d p => ∃ a, d = c a ∧ 5 ≤ p ∧ P a p) :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.2.2⟩) (seitzPlanes_outer_family hfs h)

theorem seitzExcAnisotropicForAt_of_family {α : Type*} {c : α → TauCeti.LieTypeIndex}
    {P : α → ℕ → Prop} {F : TauCeti.LieTypeIndex → Prop} {Q : TauCeti.LieTypeIndex → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtInnerFor (c a) (P a))
    (hQ : ∀ d p, F d → Q d p → ∃ a, d = c a ∧ 5 ≤ p ∧ P a p) :
    SeitzExcAnisotropicForAt F Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hQ _ _ hE.2.1 hE.2.2.1⟩)
    (seitzPlanes_inner_family hfs h)

theorem seitzExcOuterNarrowForAt_of_family {α : Type*} {c : α → TauCeti.LieTypeIndex}
    {P : α → ℕ → Prop} {F : TauCeti.LieTypeIndex → Prop} {Q : TauCeti.LieTypeIndex → ℕ → Prop}
    (hfs : ∀ (a : α) (hv : (c a).Valid), Finite (Cat ⟨c a, hv⟩) ∧ IsSimpleGroup (Cat ⟨c a, hv⟩))
    (h : ∀ a, ExtSeitzAtOuterFor (c a) (P a))
    (hQ : ∀ d p, F d → Q d p → ∃ a, d = c a ∧ 5 ≤ p ∧ P a p) :
    SeitzExcOuterNarrowForAt F Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hQ _ _ hE.2.2.1 hE.2.2.2⟩)
    (seitzPlanes_outer_family hfs h)

theorem SeitzExcAnisotropicForAt.of_cover {P : TauCeti.LieTypeIndex → Prop}
    {Q Q₁ Q₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → P d → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcAnisotropicForAt P Q₁) (h₂ : SeitzExcAnisotropicForAt P Q₂) :
    SeitzExcAnisotropicForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hP, hQ, hr, hn⟩ := hE
    exact (hcov d.1 p hp hp2 hP hQ).imp (fun h => ⟨hi, hP, h, hr, hn⟩)
      (fun h => ⟨hi, hP, h, hr, hn⟩)) h₁ h₂

theorem SeitzExcOuterNarrowForAt.of_cover {P : TauCeti.LieTypeIndex → Prop}
    {Q Q₁ Q₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → P d → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcOuterNarrowForAt P Q₁) (h₂ : SeitzExcOuterNarrowForAt P Q₂) :
    SeitzExcOuterNarrowForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hs, hP, hQ⟩ := hE
    exact (hcov d.1 p hp hp2 hP hQ).imp (fun h => ⟨hi, hs, hP, h⟩)
      (fun h => ⟨hi, hs, hP, h⟩)) h₁ h₂

end CFSG.LieType.SeitzGeneration
