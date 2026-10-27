module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Frame

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (SylowFrame)

variable {G : Type} [Group G] [Finite G]

theorem exists_y_le_normalizer {J T S : Subgroup G} (hS : SylowFrame J T S)
    (h : ∃ y ∈ J, rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≤ S ∧
      rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≠
        S ⊓ Subgroup.normalizer (T : Set G)) :
    ∃ y ∈ J, rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≤
        S ⊓ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) ∧
      rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≠
        S ⊓ Subgroup.normalizer (T : Set G) := by
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = S ⊓ Subgroup.normalizer (T : Set G) := ⟨_, rfl⟩
  rw [← hWdef] at h ⊢
  have hTW : T ≤ W := by
    rw [hWdef]
    exact le_inf hS.le Subgroup.le_normalizer
  have hWS : W ≤ S := by
    rw [hWdef]
    exact inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  by_cases hN : S ≤ Subgroup.normalizer (W : Set G)
  · obtain ⟨y, hy, hle, hne⟩ := h
    exact ⟨y, hy, le_inf hle (fun x hx => hN (hle hx)), hne⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥S := hS.sylow.isPGroup.isNilpotent
    set H : Subgroup ↥S := (S ⊓ Subgroup.normalizer (W : Set G)).subgroupOf S with hH
    have hHtop : H < ⊤ := by
      refine lt_top_iff_ne_top.2 fun hT' => hN ?_
      intro x hx
      have : (⟨x, hx⟩ : ↥S) ∈ H := by
        rw [hT']
        trivial
      exact (Subgroup.mem_inf.1 this).2
    have hlt : H < Subgroup.normalizer (H : Set ↥S) :=
      Group.normalizerCondition_of_isNilpotent H hHtop
    obtain ⟨n, hnN, hnH⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt).2
    have hnN' : ∀ h : ↥S, h ∈ H ↔ n * h * n⁻¹ ∈ H := Subgroup.mem_normalizer_iff.1 hnN
    have hnG : (n : G) ∈ T ⊔ J := by
      rw [sup_comm]
      exact hS.sylow.le n.2
    obtain ⟨t, ht, d, hd, htd⟩ := exists_mul_of_mem_sup hTN hnG
    have hdeq : d = t⁻¹ * (n : G) := by
      rw [← htd]
      group
    have hdS : d ∈ S := by
      rw [hdeq]
      exact S.mul_mem (S.inv_mem (hS.le ht)) n.2
    have htW : t ∈ W := hTW ht
    have key : ∀ x : G, d * x * d⁻¹ ∈ W ↔ (n : G) * x * (n : G)⁻¹ ∈ W := by
      intro x
      have e : (n : G) * x * (n : G)⁻¹ = t * (d * x * d⁻¹) * t⁻¹ := by
        rw [← htd]
        group
      rw [e]
      constructor
      · intro hx
        exact W.mul_mem (W.mul_mem htW hx) (W.inv_mem htW)
      · intro hx
        have := W.mul_mem (W.mul_mem (W.inv_mem htW) hx) htW
        have e2 : t⁻¹ * (t * (d * x * d⁻¹) * t⁻¹) * t = d * x * d⁻¹ := by group
        rwa [e2] at this
    refine ⟨d, hd, ?_, ?_⟩
    · intro x hx
      rw [mem_rightConjugate_iff] at hx
      have hxS : x ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem hdS) (hWS hx)) hdS
        have e : d⁻¹ * (d * x * d⁻¹) * d = x := by group
        rwa [e] at this
      refine Subgroup.mem_inf.2 ⟨hxS, ?_⟩
      have hx' : (n : G) * x * (n : G)⁻¹ ∈ W := (key x).1 hx
      have hmem : (⟨(n : G) * x * (n : G)⁻¹, S.mul_mem (S.mul_mem n.2 hxS) (S.inv_mem n.2)⟩ : ↥S)
          ∈ H := ⟨hWS hx', Subgroup.le_normalizer hx'⟩
      have h1 : (⟨x, hxS⟩ : ↥S) ∈ H := by
        rw [hnN']
        exact hmem
      exact (Subgroup.mem_inf.1 h1).2
    · intro heq
      apply hnH
      have hW' : ∀ x : G, x ∈ W ↔ d * x * d⁻¹ ∈ W := by
        intro x
        have h1 : x ∈ rightConjugate W d ↔ x ∈ W := by rw [heq]
        rw [← h1, mem_rightConjugate_iff]
      have hnN2 : (n : G) ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.mem_normalizer_iff.2 fun x => (hW' x).trans (key x)
      exact ⟨n.2, hnN2⟩

omit [Finite G] in
theorem rightConjugate_inf_eq_bot {J T : Subgroup G} (hTJ : T ⊓ J = ⊥) {y : G} (hy : y ∈ J) :
    rightConjugate T y ⊓ J = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxT, hxJ⟩
  have hxT' : y * x * y⁻¹ ∈ T := (mem_rightConjugate_iff T y x).1 hxT
  have hxJ' : y * x * y⁻¹ ∈ J := J.mul_mem (J.mul_mem hy hxJ) (J.inv_mem hy)
  have : y * x * y⁻¹ ∈ T ⊓ J := ⟨hxT', hxJ'⟩
  rw [hTJ, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have h2 : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [h2, this]
  group

theorem not_conj_le_of_ne {J T S V : Subgroup G} (hS : SylowFrame J T S)
    (hVJ : V ≤ J) (hVn : ∀ y ∈ J, ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hVS : V ≤ S)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hQV : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤ V) {y : G} (hy : y ∈ J)
    (hne : rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≠
      S ⊓ Subgroup.normalizer (T : Set G)) :
    ¬ rightConjugate T y ≤ S ⊓ Subgroup.normalizer (T : Set G) := by
  intro hTy
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = S ⊓ Subgroup.normalizer (T : Set G) ⊓ J := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = S ⊓ Subgroup.normalizer (T : Set G) := ⟨_, rfl⟩
  rw [← hQdef] at hQV
  rw [← hWdef] at hne hTy
  have hTJ : T ⊓ J = ⊥ := hS.inf_eq_bot
  have hTW : T ≤ W := by
    rw [hWdef]
    exact le_inf hS.le Subgroup.le_normalizer
  have hQW : Q ≤ W := by
    rw [hQdef, hWdef]
    exact inf_le_left
  have hQc : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q := by
    rw [hQdef]
    exact inf_comm_T hS
  have hWTQ : W = T ⊔ Q := by
    apply le_antisymm
    · intro x hx
      rw [hWdef] at hx
      obtain ⟨t, ht, q, hq, rfl⟩ := X_decomp hS hx
      rw [← hQdef] at hq
      exact Subgroup.mul_mem_sup ht hq
    · exact sup_le hTW hQW
  have hQJ : Q ≤ J := by
    rw [hQdef]
    exact inf_le_right
  have hTQ : T ⊓ Q = ⊥ := by
    rw [eq_bot_iff, ← hTJ]
    exact inf_le_inf_left T hQJ
  have hcom : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q := fun t ht q hq => by
    rw [← hQc q hq t ht]
    group
  have hTnQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [hcom t ht q hq]
      exact hq
    · intro hq
      have h3 := hcom t⁻¹ (T.inv_mem ht) _ hq
      have e : t⁻¹ * (t * q * t⁻¹) * t⁻¹⁻¹ = q := by group
      rw [e] at h3
      rw [h3]
      exact hq
  have hQnQ : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hWnQ : W ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hWTQ]
    exact sup_le hTnQ hQnQ
  have hTyQ : rightConjugate T y ⊓ Q = ⊥ := by
    rw [eq_bot_iff, ← rightConjugate_inf_eq_bot hTJ hy]
    exact inf_le_inf_left _ hQJ
  have hcardTy : Nat.card ↥(rightConjugate T y) = Nat.card T := rightConjugate_card T y
  have hQnT : Q ≤ Subgroup.normalizer (T : Set G) := by
    rw [hQdef]
    exact inf_le_left.trans inf_le_right
  have hcardW : Nat.card W = Nat.card T * Nat.card Q := by
    rw [hWTQ]
    exact CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer hQnT hTQ
  have hQTy : Q ⊔ rightConjugate T y = W := by
    have hle : Q ⊔ rightConjugate T y ≤ W := sup_le hQW hTy
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hc := CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
      (A := Q) (B := rightConjugate T y) (hTy.trans hWnQ) (by rw [inf_comm]; exact hTyQ)
    rw [hc, hcardTy, hcardW]
    exact le_of_eq (mul_comm _ _)
  have hcentral : ∀ q ∈ Q, ∀ x ∈ W, x * (y⁻¹ * q * y) = (y⁻¹ * q * y) * x := by
    intro q hq
    have haV : y⁻¹ * q * y ∈ V := by
      have := hVn y⁻¹ (J.inv_mem hy) q (hQV hq)
      simpa using this
    have hcen : W ≤ Subgroup.centralizer (({y⁻¹ * q * y} : Set G)) := by
      rw [← hQTy]
      refine sup_le (fun x hx => ?_) (fun s hs => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hVc x (hQV hx) _ haV
      · rw [Subgroup.mem_centralizer_singleton_iff]
        rw [mem_rightConjugate_iff] at hs
        have hc := hQc q hq _ hs
        have e1 : s * (y⁻¹ * q * y) = y⁻¹ * ((y * s * y⁻¹) * q) * y := by group
        have e2 : (y⁻¹ * q * y) * s = y⁻¹ * (q * (y * s * y⁻¹)) * y := by group
        rw [e1, e2, hc]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcen hx)
  have hQy : rightConjugate Q y ≤ Q := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hxV : x ∈ V := by
      have := hVn y⁻¹ (J.inv_mem hy) _ (hQV hx)
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [e] at this
    have hcT : ∀ t ∈ T, t * x = x * t := by
      intro t ht
      have h := hcentral _ hx t (hTW ht)
      have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
      rwa [e] at h
    have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hcT)
    rw [hQdef]
    exact ⟨⟨hVS hxV, hxN⟩, hVJ hxV⟩
  have hWy : rightConjugate W y ≤ W := by
    have h1 : rightConjugate W y = rightConjugate T y ⊔ rightConjugate Q y := by
      rw [hWTQ]
      exact Subgroup.map_sup _ _ _
    rw [h1]
    exact sup_le hTy (hQy.trans hQW)
  exact hne (Subgroup.eq_of_le_of_card_ge hWy (le_of_eq (rightConjugate_card W y).symm))

end CFSG.CGT.PushingUpLit.LIT.Foote
