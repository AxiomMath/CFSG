module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameVertex
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.Q3CH
open scoped commutatorElement

namespace TwinFrame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Vertex

theorem autOddFreeOn_of_mem_of_inner {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hrow : Q3NM.AutOddFreeInner ↥L) {x : Q} (hx : x ∈ L) :
    Q3NM.AutOddFreeOn ↥L (IsInducedAut L x) := by
  intro 𝒳 hinn f hf hf2
  refine hrow 𝒳 hinn f ⟨⟨_, hx⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩ hf2
  exact (hf y).symm

theorem hyp51At_of_classicalOrQuiet_inner (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) (hD4 : D4OddAutInnerNC3) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) {a b c : G} (hgen : B = Subgroup.closure {a, b, c}) (hc1 : c ≠ 1)
    (ha1 : a ≠ 1) (hac : a ≠ c) (haC : a ∈ Subgroup.centralizer ({c} : Set G))
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) (ha : ClassicalOrQuiet c a haC)
    (hb : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      oddQuotMk c ⟨b, hbC⟩ ∈ L) :
    Hyp51At B c := by
  have haB : a ∈ B := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hcB : c ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  refine hyp51At_of_moved (fun x hx => (sq x).symm.trans (hB.2 x hx))
    (fun x hx x' hx' => congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨x', hx'⟩))
    ⟨oddQuotMk c ⟨a, haC⟩, oddQuotMk_mem_modOdd haB haC,
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC,
      atMostOne_of_classicalOrQuiet hBelow hZ hc1 ha⟩ ?_
  intro L hL hm x hx hxN hxmv
  obtain ⟨d, hd, hdC, e, he, rfl⟩ := exists_mul_central_of_mem_modOdd hB hgen hx
  have heN' : e⁻¹ ∈ Subgroup.normalizer (L : Set (OddQuot c)) :=
    mem_normalizer_of_mem_center (Subgroup.inv_mem _ he)
  have hdN : oddQuotMk c ⟨d, hdC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)) := by
    have h1 := Subgroup.mul_mem _ hxN heN'
    rwa [mul_inv_cancel_right] at h1
  have hdmv : ∃ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y ≠ y * oddQuotMk c ⟨d, hdC⟩ := by
    obtain ⟨y, hy, hne⟩ := hxmv
    refine ⟨y, hy, fun h => hne ?_⟩
    have hey : e * y = y * e := (Subgroup.mem_center_iff.mp he y).symm
    calc oddQuotMk c ⟨d, hdC⟩ * e * y = oddQuotMk c ⟨d, hdC⟩ * (e * y) := mul_assoc _ _ _
      _ = oddQuotMk c ⟨d, hdC⟩ * (y * e) := by rw [hey]
      _ = (oddQuotMk c ⟨d, hdC⟩ * y) * e := (mul_assoc _ _ _).symm
      _ = (y * oddQuotMk c ⟨d, hdC⟩) * e := by rw [h]
      _ = y * (oddQuotMk c ⟨d, hdC⟩ * e) := mul_assoc _ _ _
  suffices hsuff : Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨d, hdC⟩)) by
    refine hsuff.mono fun σ hσ => ?_
    have h1 := isInducedAut_mul_central (Subgroup.inv_mem _ he) hσ
    rwa [mul_inv_cancel_right] at h1
  have hma : ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩ :=
    hm _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC)
  obtain ⟨haL, hrow⟩ := mem_inner_of_classicalOrQuiet hBelow hZ hc1 ha hD4 hL hma
  have hbL := hb L hL hm
  rcases hd with rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨y, hy, hne⟩ := hdmv
    apply hne
    have h1 : oddQuotMk c ⟨1, hdC⟩ = 1 := map_one _
    rw [h1, one_mul, mul_one]
  · exact autOddFreeOn_of_classicalOrQuiet hBelow hZ hc1 ha L hL hdN hdmv
  · exact autOddFreeOn_of_mem_of_inner hrow hbL
  · refine autOddFreeOn_of_mem_of_inner hrow ?_
    have e : oddQuotMk c ⟨a * b, hdC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact L.mul_mem haL hbL

theorem hyp51At_of_classicalOrQuiet_model (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a c : G}
    (haB : a ∈ B) (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha : ClassicalOrQuiet c a haC)
    (hM : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      alphaOf (inducedImage L (modOdd c B)) = ⊥) :
    Hyp51At B c := by
  have hmv : ∀ L : Subgroup (OddQuot c), MovedByAll B c L →
      ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩ := fun L hL =>
    hL _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC)
  exact ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ =>
    atMostOne_of_classicalOrQuiet hBelow hZ hc1 ha L₁ L₂ h₁ h₂ (hmv L₁ m₁) (hmv L₂ m₂), hM⟩

end Vertex

section Frame

variable {K K' J : Subgroup G} {z u t : G}

theorem zt_ne_one (h : TwinFrameData Ω K K' z u J t) : z * t ≠ 1 := by
  intro e
  have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_right e
  rw [inv_eq_of_mul_eq_one_right h.hz.sq] at h1
  exact h.t_ne_z h1

theorem closure_three_eq {a b c : G} (h₁ : a ∈ Subgroup.closure ({z, u, t} : Set G))
    (h₂ : b ∈ Subgroup.closure ({z, u, t} : Set G)) (h₃ : c ∈ Subgroup.closure ({z, u, t} : Set G))
    (h₄ : z ∈ Subgroup.closure ({a, b, c} : Set G)) (h₅ : u ∈ Subgroup.closure ({a, b, c} : Set G))
    (h₆ : t ∈ Subgroup.closure ({a, b, c} : Set G)) :
    Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({a, b, c} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact h₄
    · exact h₅
    · exact h₆
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact h₁
    · exact h₂
    · exact h₃

theorem hyp51At_nbr (hBelow : CIT3Below (Nat.card G)) (hZ : Subgroup.center G = ⊥)
    (hD4 : D4OddAutInnerNC3) (hΩ : HypOmegaGen Ω) (h : TwinFrameData Ω K K' z u J t) {c : G}
    (hc : c = t ∨ c = z * t)
    (hcq : ∀ hzc : z ∈ Subgroup.centralizer ({c} : Set G), ClassicalOrQuiet c z hzc)
    (hmem : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      MovedByAll (Subgroup.closure ({z, u, t} : Set G)) c L →
        ∀ huc : u ∈ Subgroup.centralizer ({c} : Set G), oddQuotMk c ⟨u, huc⟩ ∈ L) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hB := isElemAbelian_of_frameData hΩ h
  have hzB := z_mem z u t
  have huB := u_mem z u t
  have htB := t_mem z u t
  have hz2 := h.hz.sq
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
    rcases hc with rfl | rfl
    · exact htB
    · exact Subgroup.mul_mem _ hzB htB
  have haC := Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have hbC := Lemma52Proof.le_centralizer_of_mem hB hcB huB
  have hgen : Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({z, u, c} : Set G) := by
    rcases hc with rfl | rfl
    · rfl
    · refine closure_three_eq hzB huB hcB (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) ?_
      have e : t = z * (z * t) := by rw [← mul_assoc, hz2, one_mul]
      have h1 : z * (z * t) ∈ Subgroup.closure ({z, u, z * t} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      rwa [← e] at h1
  have hc1 : c ≠ 1 := by
    rcases hc with rfl | rfl
    · exact h.ht.ne_one
    · exact zt_ne_one h
  have hac : z ≠ c := by
    rcases hc with rfl | rfl
    · exact h.t_ne_z.symm
    · intro e
      have : t = 1 := by
        have h1 : z * t = z * 1 := by rw [mul_one]; exact e.symm
        exact mul_left_cancel h1
      exact h.ht.ne_one this
  exact hyp51At_of_classicalOrQuiet_inner hBelow hZ hD4 hB hgen hc1 h.hz.ne_one hac haC hbC
    (hcq haC) (fun L hL hm => hmem L hL hm hbC)

end Frame

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
