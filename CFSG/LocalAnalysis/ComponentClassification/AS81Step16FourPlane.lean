module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Radical
public import CFSG.LocalAnalysis.ComponentClassification.AS81PlaneTrans
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Line

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

section Torus

theorem eq_commutator_of_mem_normalizer (hF : Frame G A A R g E F) {j : G}
    (hjR : ∀ r ∈ R, j * r = r * j) (hCV : ∀ v ∈ E ⊓ F, j * v = v * j → v ∈ R)
    {Q : Subgroup G} (hQ : Q ∈ pointsIn R (E ⊓ F)) (hQR : Q ≠ R)
    (hjQ : j ∈ normalizer (Q : Set G)) : Q = ⁅E ⊓ F, zpowers j⁆ := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVab : ∀ a ∈ E ⊓ F, ∀ b ∈ E ⊓ F, a * b = b * a := fun a ha b hb =>
    hcommE a ha.1 b hb.1
  have hRV : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  have hR : R ∈ pointsIn R (E ⊓ F) := self_mem_pointsIn hRV
  have hRQ : R ⊓ Q = ⊥ := inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hVab hR hQ hQR.symm
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨-, x, rfl⟩ := hQ
    rw [rightConjugate_card, hF.cardR]
  have hN : R ≤ normalizer (Q : Set G) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun q hq =>
      hVab q (hQ.1 hq) r (hRV hr))
  have hsup : R ⊔ Q = E ⊓ F := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hRV hQ.1) ?_
    have h := card_sup_mul_card_inf hN
    rw [inf_comm, hRQ, Subgroup.card_bot, mul_one, hQ4, hF.cardR, sup_comm] at h
    rw [card_inf_of_frame hF, h]
  have hdec : ∀ v ∈ E ⊓ F, ∃ r ∈ R, ∃ q ∈ Q, v = r * q := by
    intro v hv
    have hv' : v ∈ ((R ⊔ Q : Subgroup G) : Set G) := by rw [hsup]; exact hv
    rw [coe_mul_of_left_le_normalizer_right R Q hN] at hv'
    obtain ⟨r, hr, q, hq, rfl⟩ := hv'
    exact ⟨r, hr, q, hq, rfl⟩
  refine le_antisymm ?_ (commutator_zpowers_le_of_complement hVab hRV hQ.1 hjR hjQ hdec)
  refine le_commutator_zpowers_of_fixedPointFree hQ.1 hjQ fun q hq hjq => ?_
  have h1 : q ∈ R ⊓ Q := ⟨hCV q (hQ.1 hq) hjq, hq⟩
  rwa [hRQ, mem_bot] at h1

theorem exists_torus_of_card_four (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) :
    ∃ j ∈ A, (∃ n : ℕ, j ^ 3 ^ n = 1) ∧ j ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ∧
      ∀ Q ∈ pointsIn R (E ⊓ F), Q ≠ R →
        ∃ k : ℕ, Q = rightConjugate (rightConjugate R g) (j ^ k) := by
  classical
  obtain ⟨j, hjA, ⟨n, hn⟩, hjEF, hCV, -⟩ := exists_torus_frame h11 hF hL
  refine ⟨j, hjA, ⟨n, hn⟩, hjEF, ?_⟩
  set V := E ⊓ F with hVdef
  have hjR : ∀ r ∈ R, j * r = r * j := fun r hr =>
    (mem_centralizer_iff.mp (hF.sylowR.le hr) j hjA)
  have hjV : j ∈ normalizer (V : Set G) := by
    rw [hVdef, hF.inf_eq_center]
    exact mem_normalizer_centerIn hjEF
  have hRV : R ≤ V := le_inf hF.R_le_E hF.R_le_F
  have hR : R ∈ pointsIn R V := self_mem_pointsIn hRV
  have hjRN : j ∈ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => (hjR r hr).symm)
  have hperm : ∀ m : ℕ, ∀ Q ∈ pointsIn R V, rightConjugate Q (j ^ m) ∈ pointsIn R V := by
    rintro m Q ⟨hQV, y, rfl⟩
    refine ⟨?_, y * j ^ m, rightConjugate_mul R y (j ^ m)⟩
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hQV (j ^ m)
    rwa [(rightConjugate_eq_self_iff V (j ^ m)).mpr (pow_mem hjV m)] at h1
  have hperm1 : ∀ Q ∈ pointsIn R V, rightConjugate Q j ∈ pointsIn R V := fun Q hQ => by
    have := hperm 1 Q hQ
    rwa [pow_one] at this
  have hfix : ∀ Q ∈ pointsIn R V, j ∈ normalizer (Q : Set G) → Q = R := by
    intro Q hQ hjQ
    by_contra hQR
    have hQζ := eq_commutator_of_mem_normalizer hF hjR hCV hQ hQR hjQ
    have hmod := card_modEq_card_normalized hn hperm1
    set S := {X : ↥(pointsIn R V) // j ∈ normalizer ((X : Subgroup G) : Set G)}
    have hS2 : Nat.card S = 2 := by
      let f : S → Fin 2 := fun X => if (X : ↥(pointsIn R V)).1 = R then 0 else 1
      have hfb : Function.Bijective f := by
        refine ⟨fun X₁ X₂ h => ?_, fun i => ?_⟩
        · have key : ∀ X : S, (X : ↥(pointsIn R V)).1 = R ∨ (X : ↥(pointsIn R V)).1 = Q :=
            fun X => by
              by_cases hX : (X : ↥(pointsIn R V)).1 = R
              · exact Or.inl hX
              · right
                rw [hQζ]
                exact eq_commutator_of_mem_normalizer hF hjR hCV X.1.2 hX X.2
          apply Subtype.ext
          apply Subtype.ext
          rcases key X₁ with h₁ | h₁ <;> rcases key X₂ with h₂ | h₂
          · rw [h₁, h₂]
          · have : (X₂ : ↥(pointsIn R V)).1 ≠ R := by rw [h₂]; exact hQR
            simp [f, h₁, this] at h
          · have : (X₁ : ↥(pointsIn R V)).1 ≠ R := by rw [h₁]; exact hQR
            simp [f, h₂, this] at h
          · rw [h₁, h₂]
        · fin_cases i
          · exact ⟨⟨⟨R, hR⟩, hjRN⟩, by simp [f]⟩
          · exact ⟨⟨⟨Q, hQ⟩, hjQ⟩, by simp [f, hQR]⟩
      rw [Nat.card_eq_of_bijective f hfb, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h4, hS2] at hmod
    exact absurd hmod (by decide)
  set P₁ := rightConjugate R g with hP₁
  have hP₁V : P₁ ∈ pointsIn R V := ⟨by rw [hVdef, hF.inf_eq]; exact le_sup_right, g, rfl⟩
  have hP₁R : P₁ ≠ R := by
    intro h
    have h1 : V = R := by rw [hVdef, hF.inf_eq, ← hP₁, h, sup_idem]
    have := card_inf_of_frame hF
    rw [← hVdef, h1, hF.cardR] at this
    omega
  have hconjR : ∀ m : ℕ, rightConjugate R (j ^ m) = R := fun m =>
    (rightConjugate_eq_self_iff R _).mpr (pow_mem hjRN m)
  have hcancel : ∀ (X Y : Subgroup G) (m : ℕ), rightConjugate X (j ^ m) = rightConjugate Y (j ^ m) →
      X = Y := by
    intro X Y m h
    have h1 := congrArg (fun Z => rightConjugate Z (j ^ m)⁻¹) h
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    exact h1
  have hpow : (j ^ 2) ^ ((3 ^ n + 1) / 2) = j := by
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
    rw [h1, ← pow_mul]
    have h2 : 2 * (m + 1) = 3 ^ n + 1 := by omega
    rw [h2, pow_succ, hn, one_mul]
  have hne₁ : rightConjugate P₁ j ≠ P₁ := fun h =>
    hP₁R (hfix P₁ hP₁V ((rightConjugate_eq_self_iff P₁ _).mp h))
  have hne₂ : rightConjugate P₁ (j ^ 2) ≠ P₁ := fun h => by
    have hj2 : j ^ 2 ∈ normalizer (P₁ : Set G) := (rightConjugate_eq_self_iff P₁ _).mp h
    exact hP₁R (hfix P₁ hP₁V (hpow ▸ pow_mem hj2 _))
  have hne₁₂ : rightConjugate P₁ j ≠ rightConjugate P₁ (j ^ 2) := fun h => by
    apply hne₁
    have e : rightConjugate (rightConjugate P₁ j) (j ^ 1) = rightConjugate P₁ (j ^ 2) := by
      rw [rightConjugate_mul, pow_one, ← sq]
    have e' : rightConjugate (rightConjugate P₁ j) (j ^ 1) = rightConjugate P₁ (j ^ 1) := by
      rw [e, ← h, pow_one]
    exact hcancel _ _ 1 e'
  have hR₁ : rightConjugate P₁ j ≠ R := fun h =>
    hP₁R (hcancel _ _ 1 (by rw [pow_one, h, ← pow_one j, hconjR 1]))
  have hR₂ : rightConjugate P₁ (j ^ 2) ≠ R := fun h =>
    hP₁R (hcancel _ _ 2 (h.trans (hconjR 2).symm))
  intro Q hQ hQR
  by_contra hQ'
  push Not at hQ'
  have hsub : ({R, P₁, rightConjugate P₁ j, rightConjugate P₁ (j ^ 2), Q} :
      Set (Subgroup G)) ⊆ pointsIn R V := by
    rintro X (rfl | rfl | rfl | rfl | rfl)
    · exact hR
    · exact hP₁V
    · exact hperm1 _ hP₁V
    · exact hperm 2 _ hP₁V
    · exact hQ
  have hQ0 := hQ' 0
  have hQ1 := hQ' 1
  have hQ2 := hQ' 2
  rw [pow_zero, rightConjugate_one] at hQ0
  rw [pow_one] at hQ1
  have h5 : ({R, P₁, rightConjugate P₁ j, rightConjugate P₁ (j ^ 2), Q} :
      Set (Subgroup G)).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hP₁R.symm, hR₁.symm, hR₂.symm, hQR.symm]),
      Set.ncard_insert_of_notMem (by simp [hne₁.symm, hne₂.symm, hQ0.symm]),
      Set.ncard_insert_of_notMem (by simp [hne₁₂, hQ1.symm]), Set.ncard_pair hQ2.symm]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h5, ← Nat.card_coe_set_eq, h4] at h1
  omega

end Torus

section Transitive

omit [Finite G] in
theorem mem_normalizer_of_pow_three {X Y : Subgroup G} {j : G} {n : ℕ} (hn : j ^ 3 ^ n = 1)
    (hne : X ≠ Y) (hX : rightConjugate X j = X ∨ rightConjugate X j = Y)
    (hY : rightConjugate Y j = X ∨ rightConjugate Y j = Y) : j ∈ normalizer (X : Set G) := by
  rcases hX with h | h
  · exact (rightConjugate_eq_self_iff X j).mp h
  · exfalso
    have hYj : rightConjugate Y j = X := by
      rcases hY with h' | h'
      · exact h'
      · exfalso
        apply hne
        have h3 := congrArg (fun Z => rightConjugate Z j⁻¹) (h.trans h'.symm)
        simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h3
        exact h3
    have hj2 : j ^ 2 ∈ normalizer (X : Set G) := by
      rw [← rightConjugate_eq_self_iff, sq, ← rightConjugate_mul, h, hYj]
    have hpow : (j ^ 2) ^ ((3 ^ n + 1) / 2) = j := by
      have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨m, hm⟩ := hodd
      have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
      rw [h1, ← pow_mul]
      have h2 : 2 * (m + 1) = 3 ^ n + 1 := by omega
      rw [h2, pow_succ, hn, one_mul]
    have hjX : j ∈ normalizer (X : Set G) := hpow ▸ pow_mem hj2 _
    rw [(rightConjugate_eq_self_iff X j).mpr hjX] at h
    exact hne h

theorem card_inf_eq_of_le_sup (c : L34Cover ↥A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    {D : Subgroup G} (hRD : R ≤ D) (hDAR : D ≤ A ⊔ R) (hD64 : Nat.card D = 64)
    (hR4 : Nat.card R = 4) : Nat.card ↥(D ⊓ A) = 16 * Nat.card c.π.ker := by
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hN : R ≤ normalizer ((D ⊓ A : Subgroup G) : Set G) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_iff.mp (hRA hr) x hx.2)
  have h1 := card_sup_mul_card_inf hN
  have h2 : D ⊓ A ⊓ R = R ⊓ A :=
    le_antisymm (fun x hx => ⟨hx.2, hx.1.2⟩) (fun x hx => ⟨⟨hRD hx.1, hx.2⟩, hx.1⟩)
  rw [← eq_inf_sup_of_le_sup hRA hRD hDAR, hD64, hR4, h2] at h1
  rw [card_ker_eq_card_inf c hR]
  omega

theorem exists_mem_eq_of_card_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) :
    ∀ Q ∈ pointsIn R E, Q ≠ R → ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      Q = rightConjugate (rightConjugate R g) n⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  have hNZ := oddCore_le_center hstd.1.1 hstd.1.2
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcommF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hT, -⟩ := isSylowOf_inf_and_inf_eq hF
  set T := (E ⊔ F) ⊓ A with hTdef
  set B := A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) with hBdef
  have hEAe : IsElemAbelian 2 (E ⊓ A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE a a.2.1 b b.2.1)⟩⟩, fun x hx => hF.elemE.2 x hx.1⟩
  have hFAe : IsElemAbelian 2 (F ⊓ A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommF a a.2.1 b b.2.1)⟩⟩, fun x hx => hF.elemF.2 x hx.1⟩
  have hcardEA := card_inf_eq_of_le_sup c hF.sylowR hF.R_le_E hF.E_le hF.cardE hF.cardR
  have hcardFA := card_inf_eq_of_le_sup c hF.sylowR hF.R_le_F hF.F_le hF.cardF hF.cardR
  have hEAT : E ⊓ A ≤ T := inf_le_inf_right A le_sup_left
  have hFAT : F ⊓ A ≤ T := inf_le_inf_right A le_sup_right
  have hTB : T ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    (radical_of_le c hNZ hT hEAT hEAe hcardEA).1
  have hTsylB : IsSylowOf 2 T B := hT.of_le (le_inf hT.le hTB) inf_le_left
  obtain ⟨j, hjA, ⟨n, hn⟩, hjEF, hjorb⟩ := exists_torus_of_card_four h11 hF hL h4
  have hjT : rightConjugate T j = T := by
    rw [hTdef, AschbacherTheorem3.rightConjugate_inf,
      (rightConjugate_eq_self_iff _ j).mpr hjEF, AschbacherTheorem3.rightConjugate_eq_of_mem hjA]
  have hEAF : E ⊓ A ≠ F ⊓ A := by
    intro h
    apply hF.ne
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le, eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le, h]
  have hcls : ∀ X : Subgroup G, X ≤ T → IsElemAbelian 2 X →
      Nat.card X = 16 * Nat.card c.π.ker → rightConjugate X j = E ⊓ A ∨
        rightConjugate X j = F ⊓ A := by
    intro X hXT hXe hXc
    have hXjT : rightConjugate X j ≤ T := by
      rw [← hjT]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hXT j
    rcases eq_or_eq_of_isElemAbelian c hNZ hT hEAT hFAT hXjT hEAe hFAe
      (AS76b.isElemAbelian_rightConjugate hXe j) hcardEA hcardFA
      (by rw [rightConjugate_card, hXc]) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hEAF
  have hjB : j ∈ B := ⟨hjA, mem_normalizer_of_pow_three hn hEAF (hcls _ hEAT hEAe hcardEA)
    (hcls _ hFAT hFAe hcardFA)⟩
  intro Q hQ hQR
  obtain ⟨a, ha, haQ⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hQ hQR
  have hS := isSylowOf_rightConjugate_of_mem hT ha
  have hline := rightConjugate_inf_eq hF ha
  have hZE : centerIn (rightConjugate T a) ≤ E := by
    have h1 : centerIn (rightConjugate T a) ≤ R ⊔ Q := haQ ▸ hline ▸ le_sup_left
    exact h1.trans (sup_le hF.R_le_E hQ.1)
  obtain ⟨h, hhS, hhK⟩ : ∃ h ∈ centerIn (rightConjugate T a), h ∉ centralizer (A : Set G) := by
    by_contra hall
    push Not at hall
    have hle : centerIn (rightConjugate T a) ≤ R := fun z hz =>
      mem_of_mem_centralizer_of_isPGroup hF.sylowR (hS.le hz.1) (hall z hz)
        (hS.isPGroup.to_le (zpowers_le.mpr hz.1))
    have h1 : rightConjugate (E ⊓ F) a ≤ R := hline ▸ sup_le hle le_rfl
    have h2 := Subgroup.card_le_of_le h1
    rw [rightConjugate_card, card_inf_of_frame hF, hF.cardR] at h2
    omega
  have hEAS : E ⊓ A ≤ rightConjugate T a :=
    le_of_le_sup_centralizer hS inf_le_right
      ((isPGroup_two_of_isElemAbelian hF.elemE).to_le inf_le_left) fun y hy =>
        mem_sup_centralizer_of_commute c hNZ hS hhS hhK hy.2 (hcommE y hy.1 h (hZE hhS))
  have hSB : rightConjugate T a ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    (radical_of_le c hNZ hS hEAS hEAe hcardEA).1
  have hSsylB : IsSylowOf 2 (rightConjugate T a) B := hS.of_le (le_inf hS.le hSB) inf_le_left
  obtain ⟨b, hb, hTb⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hSsylB hTsylB
  have hVb : rightConjugate (E ⊓ F) b = R ⊔ Q := by
    rw [rightConjugate_inf_eq hF hb.1, hTb, ← hline, haQ]
  have hbR : rightConjugate R b = R := (rightConjugate_eq_self_iff R b).mpr
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hRA hr) b hb.1).symm))
  have hQ'V : rightConjugate Q b⁻¹ ∈ pointsIn R (E ⊓ F) := by
    refine ⟨?_, ?_⟩
    · have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate
        (le_sup_right : Q ≤ R ⊔ Q) b⁻¹
      rwa [← hVb, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    · obtain ⟨x, hx⟩ := hQ.2
      exact ⟨x * b⁻¹, by rw [hx, rightConjugate_mul]⟩
  have hQ'R : rightConjugate Q b⁻¹ ≠ R := fun h' => hQR (by
    have h1 := congrArg (fun Z => rightConjugate Z b) h'
    simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h1
    rw [h1, hbR])
  obtain ⟨k, hk⟩ := hjorb _ hQ'V hQ'R
  refine ⟨(j ^ k * b)⁻¹, B.inv_mem (B.mul_mem (B.pow_mem hjB k) hb), ?_⟩
  rw [inv_inv, ← rightConjugate_mul, ← hk, rightConjugate_mul, inv_mul_cancel,
    rightConjugate_one]

end Transitive

section Plane

theorem exists_pointsAction_eq_pair_of_card_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) {p₁ p₂ q₁ q₂ : ↥(pointsIn R E)} (hp : p₁ ≠ p₂)
    (hq : q₁ ≠ q₂) :
    ∃ n : ↥(normalizer (E : Set G)), pointsAction R E n p₁ = q₁ ∧ pointsAction R E n p₂ = q₂ := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRgV : rightConjugate R g ≤ E ⊓ F := by rw [hF.inf_eq]; exact le_sup_right
  have hRgE : rightConjugate R g ≤ E := hRgV.trans inf_le_left
  have hRgR := rightConjugate_ne_of_frame hF
  set pR : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hF.R_le_E⟩
  set pRg : ↥(pointsIn R E) := ⟨rightConjugate R g, hRgE, g, rfl⟩
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRgA : rightConjugate R g ≤ centralizer (rightConjugate A g : Set G) :=
    hKg ▸ AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g
  have htA := exists_mem_eq_of_card_four hE16 h11 hF hL h4
  have hF' := frame_at_point hE16 hF hL hRgV hRgR
  have h4' : Nat.card (pointsIn (rightConjugate R g) (E ⊓ F)) = 4 := by
    rw [pointsIn_rightConjugate]
    exact h4
  have htAg : ∀ Q ∈ pointsIn R E, Q ≠ rightConjugate R g →
      ∃ n ∈ rightConjugate A g ⊓ normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G),
        Q = rightConjugate R n⁻¹ := by
    intro Q hQ hQR
    obtain ⟨n, hn, hQn⟩ := exists_mem_eq_of_card_four hE16 h11 hF'
      (typeL34_rightConjugate g hL) h4' Q (by rw [pointsIn_rightConjugate]; exact hQ) hQR
    refine ⟨n, hn, ?_⟩
    rw [hQn, rightConjugate_mul R g g⁻¹, mul_inv_cancel, rightConjugate_one]
  have hfixR : ∀ a, ∀ ha : a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      pointsAction R E ⟨a, mem_normalizer_of_mem_inf hF ha⟩ pR = pR := fun a ha => by
    apply Subtype.ext
    rw [coe_pointsAction_apply]
    exact (rightConjugate_eq_self_iff R _).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr =>
        (mem_centralizer_iff.mp (hRA hr) _ (A.inv_mem ha.1)).symm))
  have hpA : ∀ p : ↥(pointsIn R E), p ≠ pR → ∃ a, ∃ ha : a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) :
      Set G), pointsAction R E ⟨a, mem_normalizer_of_mem_inf hF ha⟩ pRg = p := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := htA p p.2 (fun h => hp (Subtype.ext h))
    exact ⟨a, ha, Subtype.ext (by rw [coe_pointsAction_apply]; exact hpa.symm)⟩
  have hpAg : ∀ p : ↥(pointsIn R E), p ≠ pRg → ∃ b, ∃ hb : b ∈ rightConjugate A g ⊓
      normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G),
      pointsAction R E ⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ pR = p := fun p hp => by
    obtain ⟨b, hb, hpb⟩ := htAg p p.2 (fun h => hp (Subtype.ext h))
    exact ⟨b, hb, Subtype.ext (by rw [coe_pointsAction_apply]; exact hpb.symm)⟩
  have hpRpRg : pR ≠ pRg := fun h => hRgR (congrArg Subtype.val h).symm
  have h16 : Nat.card (pointsIn R E) = 16 := by rw [card_pointsIn_eq hE16 h11 hF hL, h4]
  obtain ⟨p₃, hp₃R, hp₃Rg⟩ : ∃ p₃ : ↥(pointsIn R E), p₃ ≠ pR ∧ p₃ ≠ pRg := by
    classical
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set ↥(pointsIn R E)) ⊆ {pR, pRg} := fun p _ => by
      by_cases hpR : p = pR
      · exact Or.inl hpR
      · exact Or.inr (h p hpR)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, h16] at h1
    have h2 := Set.ncard_insert_le pR ({pRg} : Set ↥(pointsIn R E))
    rw [Set.ncard_singleton] at h2
    omega
  have htoR : ∀ p : ↥(pointsIn R E), ∃ n : ↥(normalizer (E : Set G)),
      pointsAction R E n p = pR := by
    intro p
    by_cases hp1 : p = pR
    · exact ⟨1, by rw [hp1, map_one]; rfl⟩
    by_cases hp2 : p = pRg
    · obtain ⟨a, ha, hpa⟩ := hpA p₃ hp₃R
      obtain ⟨b, hb, hpb⟩ := hpAg p₃ hp₃Rg
      refine ⟨(⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ :
        ↥(normalizer (E : Set G)))⁻¹ * ⟨a, mem_normalizer_of_mem_inf hF ha⟩, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hp2, hpa, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpb.symm
    · obtain ⟨b, hb, hpb⟩ := hpAg p hp2
      refine ⟨(⟨b, mem_normalizer_of_mem_inf_conj hE16 hF hL hb⟩ :
        ↥(normalizer (E : Set G)))⁻¹, ?_⟩
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpb.symm
  have hpair : ∀ p₁ p₂ : ↥(pointsIn R E), p₁ ≠ p₂ → ∃ n : ↥(normalizer (E : Set G)),
      pointsAction R E n p₁ = pR ∧ pointsAction R E n p₂ = pRg := by
    intro p₁ p₂ hp
    obtain ⟨n₁, hn₁⟩ := htoR p₁
    have hne : pointsAction R E n₁ p₂ ≠ pR := fun h =>
      hp ((pointsAction R E n₁).injective (hn₁.trans h.symm))
    obtain ⟨a, ha, hpa⟩ := hpA _ hne
    refine ⟨(⟨a, mem_normalizer_of_mem_inf hF ha⟩ : ↥(normalizer (E : Set G)))⁻¹ * n₁, ?_, ?_⟩
    · rw [map_mul, Equiv.Perm.mul_apply, hn₁, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact (hfixR a ha).symm
    · rw [map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hpa.symm
  obtain ⟨np, hnp₁, hnp₂⟩ := hpair p₁ p₂ hp
  obtain ⟨nq, hnq₁, hnq₂⟩ := hpair q₁ q₂ hq
  refine ⟨nq⁻¹ * np, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hnp₁, map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hnq₁.symm
  · rw [map_mul, Equiv.Perm.mul_apply, hnp₂, map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hnq₂.symm

theorem ncard_pointLine_of_card_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) {p q : ↥(pointsIn R E)} (hpq : p ≠ q) :
    (pointLine R E p q).ncard = 4 := by
  have hRgE : rightConjugate R g ≤ E := (hF.inf_eq ▸ le_sup_right).trans inf_le_left
  set pR : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hF.R_le_E⟩
  set pRg : ↥(pointsIn R E) := ⟨rightConjugate R g, hRgE, g, rfl⟩
  have hpRpRg : pR ≠ pRg := fun h => rightConjugate_ne_of_frame hF (congrArg Subtype.val h).symm
  obtain ⟨n, hn₁, hn₂⟩ := exists_pointsAction_eq_pair_of_card_four hE16 h11 hF hL h4 hpq hpRpRg
  have himg := image_pointLine n p q
  rw [hn₁, hn₂] at himg
  have h1 : (pointLine R E p q).ncard = (pointLine R E pR pRg).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (pointsAction R E n).injective]
  rw [h1, ← h4, Nat.card_coe_set_eq (pointsIn R (E ⊓ F)),
    ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext X
  simp only [Set.mem_image, pointLine, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨hF.inf_eq ▸ hQ, Q.2.2⟩
  · rintro ⟨hXV, hX⟩
    exact ⟨⟨X, hXV.trans inf_le_left, hX⟩, hF.inf_eq ▸ hXV, rfl⟩

theorem isAffinePlane_points_of_card_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) :
    IsAffinePlane ↥(pointsIn R E) (linesOf (pointLine R E)) := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hne : ∀ {a b : ↥(pointsIn R E)}, a ≠ b → (a : Subgroup G) ≠ b := fun h e =>
    h (Subtype.ext e)
  refine isAffinePlane_of_line (fun p q _ =>
    ⟨(le_sup_left : (p : Subgroup G) ≤ _ ⊔ (q : Subgroup G)),
      (le_sup_right : (q : Subgroup G) ≤ (p : Subgroup G) ⊔ _)⟩) ?_
    (fun p q hpq => ncard_pointLine_of_card_four hE16 h11 hF hL h4 hpq) ?_
  · intro p q r s hpq hrs hr hs
    have hle : (r : Subgroup G) ⊔ s ≤ (p : Subgroup G) ⊔ q := sup_le hr hs
    have heq : (r : Subgroup G) ⊔ s = (p : Subgroup G) ⊔ q := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_sup_of_mem_pointsIn hKte hF.sylowR hcomm p.2 q.2 (hne hpq),
        card_sup_of_mem_pointsIn hKte hF.sylowR hcomm r.2 s.2 (hne hrs)]
    ext x
    simp only [pointLine, Set.mem_ofPred_eq]
    rw [heq]
  · rw [card_pointsIn_eq hE16 h11 hF hL, h4]

end Plane

end CFSG.ComponentClassification.AS81
