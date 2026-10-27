module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictExtraAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeKAux

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem cSide_cent_isExtraspecial [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ))
    (hfix : Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn ρ v = v} = 16)
    (hnd : cSideFixedNondeg (extraspecialQuadForm hE) (conjLinEquiv hQn ρ)) :
    CFSG.IsExtraspecial 2 ↥(Q ⊓ Subgroup.centralizer ({ρ} : Set C)) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({ρ} : Set C)) = 2 ^ 5 := by
  classical
  set R : Subgroup C := Q ⊓ Subgroup.centralizer ({ρ} : Set C) with hRdef
  have hZle : centerOf Q ≤ R := cSide_centerOf_le_cent hE ρ
  have hcardZ : Nat.card ↥(centerOf Q) = 2 := cSide_card_centerOf hE
  have hcardR : Nat.card ↥R = 2 ^ 5 := by
    have h := cSide_card_cent_of_odd hE hρ
    rw [← hRdef] at h
    rw [h, hfix]
    norm_num
  obtain ⟨c0, hc0ne, hc0uniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(centerOf Q))).1 hcardZ
  let c : ↥R := ⟨(c0 : C), hZle c0.2⟩
  have hc0Q : (c0 : C) ∈ Q := (Subgroup.mem_inf.mp c0.2).1
  have hcsq : c * c = 1 := by
    apply Subtype.ext
    have hmem : (⟨(c0 : C), hc0Q⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
      (mem_centerOf_iff ⟨(c0 : C), hc0Q⟩).mp c0.2
    have h := sq_eq_one_of_mem_center hE hmem
    simpa [c, pow_two] using congrArg Subtype.val h
  have hcen : ∀ g : ↥R, g * c = c * g := by
    intro g
    apply Subtype.ext
    have hgc : (g : C) * (c0 : C) = (c0 : C) * (g : C) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c0.2).2 (g : C) g.2.1
    simpa [c] using hgc
  have hcen' : ∀ q : ↥R, (∀ r : ↥R, q * r = r * q) → q = 1 ∨ q = c := by
    intro q hq
    have hqZ : (q : C) ∈ centerOf Q :=
      cSide_mem_centerOf_of_mem_center hE hρ hnd q.2
        (fun y hy => congrArg Subtype.val (hq ⟨y, hy⟩))
    have hqmem : (⟨(q : C), hqZ⟩ : ↥(centerOf Q)) = 1 ∨
        (⟨(q : C), hqZ⟩ : ↥(centerOf Q)) = c0 := by
      by_cases h : (⟨(q : C), hqZ⟩ : ↥(centerOf Q)) = 1
      · exact Or.inl h
      · exact Or.inr (hc0uniq _ h)
    rcases hqmem with h | h
    · left; exact Subtype.ext (by simpa using congrArg Subtype.val h)
    · right; exact Subtype.ext (by simpa [c] using congrArg Subtype.val h)
  have hcomm : ∀ q r : ↥R, q * r * (r * q)⁻¹ = 1 ∨ q * r * (r * q)⁻¹ = c := by
    intro q r
    have hZ : ((q * r * (r * q)⁻¹ : ↥R) : C) ∈ centerOf Q := by
      have heq : ((q * r * (r * q)⁻¹ : ↥R) : C) = ⁅(q : C), (r : C)⁆ := by
        show (q : C) * (r : C) * ((r : C) * (q : C))⁻¹ = ⁅(q : C), (r : C)⁆
        rw [commutatorElement_def]; group
      have hZc : ⁅(q : C), (r : C)⁆ ∈ centerOf Q := by
        have hmem := commutatorElement_mem_center hE (⟨(q : C), q.2.1⟩ : ↥Q)
          (⟨(r : C), r.2.1⟩ : ↥Q)
        have hcoe : ((⁅(⟨(q : C), q.2.1⟩ : ↥Q), (⟨(r : C), r.2.1⟩ : ↥Q)⁆ : ↥Q) : C) =
            ⁅(q : C), (r : C)⁆ := rfl
        rw [← hcoe]
        exact (mem_centerOf_iff _).mpr hmem
      rw [heq]
      exact hZc
    by_cases h1 : ((q * r * (r * q)⁻¹ : ↥R) : C) = 1
    · left; exact Subtype.ext h1
    · right
      have := hc0uniq (⟨_, hZ⟩ : ↥(centerOf Q)) (fun hh => h1 (congrArg Subtype.val hh))
      exact Subtype.ext (by simpa [c] using congrArg Subtype.val this)
  have hsq : ∀ q : ↥R, q * q = 1 ∨ q * q = c := by
    intro q
    have hZ : ((q * q : ↥R) : C) ∈ centerOf Q := by
      have hmemQ : ((⟨(q : C), q.2.1⟩ : ↥Q) ^ 2) ∈ Subgroup.center ↥Q :=
        sq_mem_center hE ⟨(q : C), q.2.1⟩
      have hcoe : (((⟨(q : C), q.2.1⟩ : ↥Q) ^ 2 : ↥Q) : C) = ((q * q : ↥R) : C) := by
        simp [Subgroup.coe_pow, pow_two]
      rw [← hcoe]
      exact (mem_centerOf_iff _).mpr hmemQ
    by_cases h1 : ((q * q : ↥R) : C) = 1
    · left; exact Subtype.ext h1
    · right
      have := hc0uniq (⟨_, hZ⟩ : ↥(centerOf Q)) (fun hh => h1 (congrArg Subtype.val hh))
      exact Subtype.ext (by simpa [c] using congrArg Subtype.val this)
  have hnt : ∃ q : ↥R, q ≠ 1 ∧ q ≠ c := by
    have hlt : centerOf Q < R := by
      refine lt_of_le_of_ne hZle ?_
      intro h
      have hh : Nat.card ↥(centerOf Q) = Nat.card ↥R :=
        congrArg (fun S : Subgroup C => Nat.card ↥S) h
      rw [hcardZ, hcardR] at hh
      norm_num at hh
    obtain ⟨-, q, hqR, hqZ⟩ := SetLike.lt_iff_le_and_exists.mp hlt
    refine ⟨⟨q, hqR⟩, ?_, ?_⟩
    · intro h
      apply hqZ
      rw [show q = 1 from congrArg (fun t : ↥R => (t : C)) h]
      exact (centerOf Q).one_mem
    · intro h
      apply hqZ
      rw [show q = (c : C) from congrArg (fun t : ↥R => (t : C)) h]
      exact c0.2
  have hc1 : c ≠ 1 := fun h =>
    hc0ne (Subtype.ext (by simpa [c] using congrArg (fun t : ↥R => (t : C)) h))
  exact ⟨CFSG.EvenSporadicStandard.HNRecog.TwoHSData.isExtraspecial_two_of_elements c hc1 hcsq
    hcen hcen' hcomm hsq hnt, hcardR⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
