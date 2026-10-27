module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Mirror

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
  (Theorem3Statement Frame SylowFrame exists_isSylowOf_le rightConjugate_le_rightConjugate
    exists_rightConjugate_le_of_isSylowOf conj_mem_rightConjugate)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_conj_mem_of_mem_S {J T S : Subgroup G} (hS : SylowFrame J T S)
    (hTc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (hTs : ∀ t ∈ T, t * t = 1) {u : G} (huS : u ∈ S)
    {t : G} (ht : t ∈ T) : t * (u⁻¹ * t * u) ∈ J := by
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have huTJ : u ∈ T ⊔ J := by
    rw [sup_comm]
    exact hS.sylow.le huS
  obtain ⟨t₁, ht₁, d, hd, htd⟩ := exists_mul_of_mem_sup hTN huTJ
  have hc1 : t₁⁻¹ * t * t₁ = t := by
    have := hTc t ht t₁ ht₁
    calc t₁⁻¹ * t * t₁ = t₁⁻¹ * (t * t₁) := by group
      _ = t₁⁻¹ * (t₁ * t) := by rw [this]
      _ = t := by group
  have e : t * (u⁻¹ * t * u) = (t * d⁻¹ * t⁻¹) * (t * t) * d := by
    rw [← htd]
    calc t * ((t₁ * d)⁻¹ * t * (t₁ * d)) = t * (d⁻¹ * (t₁⁻¹ * t * t₁) * d) := by group
      _ = t * (d⁻¹ * t * d) := by rw [hc1]
      _ = (t * d⁻¹ * t⁻¹) * (t * t) * d := by group
  rw [e, hTs t ht, mul_one]
  exact J.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTN ht) d⁻¹).1 (J.inv_mem hd)) hd

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem le_normalizer_of_le_M (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {h : G}
    (hh : h ∉ M) {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hAs : ∀ a ∈ A, a * a = 1) (h4 : 4 ≤ Nat.card A) (hAJ : A ≤ J)
    (hAM : A ≤ rightConjugate M h) :
    A ≤ Subgroup.normalizer ((rightConjugate J h : Subgroup G) : Set G) := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  obtain ⟨W, hWA, haW, hW2, hW4⟩ := exists_fourGroup_of_card hAc hAs h4 ha ha1
  have hc' := c.transport h
  have hz' := hz.transport h
  have e : rightConjugate (rightConjugate J h) h⁻¹ = J := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hWle : W ≤ rightConjugate (rightConjugate J h) h⁻¹ ⊓ rightConjugate M h := by
    rw [e]
    exact le_inf (hWA.trans hAJ) (hWA.trans hAM)
  have hgM : h⁻¹ ∉ rightConjugate M h := by
    intro hm
    apply hh
    rw [mem_rightConjugate_iff] at hm
    have h' : h⁻¹ ∈ M := by simpa using hm
    simpa using M.inv_mem h'
  exact hc'.normalizes_of_le_conj hA hz' hgM hWle hW2 hW4 haW

theorem exists_swap (h3 : Theorem3Statement) (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀)
    {g : G} {T S : Subgroup G} (hgood : Good56 M J g)
    (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t) :
    ∃ x ∈ J, x ∈ rightConjugate M g ∧
      x ∉ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTc, hTs, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hncent
  have hTB : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hTU : T ≤ blockU (rightConjugate J g) := c.le_blockU_conj hA hz hgood hT hmax hS hncent
  obtain ⟨x, hxJ, hxN, u, huT, hu1, hxu⟩ := c.exists_x h3 hA hz hgood hT hmax hS
  have hu2 : ∃ n : ℕ, u ^ 2 ^ n = 1 := ⟨1, by rw [pow_one, pow_two]; exact hTs u huT⟩
  have hC := c.centralizer_le_conj (hTB huT) hu2 hu1
  have hxM : x ∈ rightConjugate M g := hC (Subgroup.mem_centralizer_singleton_iff.2 hxu)
  refine ⟨x, hxJ, hxM, fun hxB => hxN ?_⟩
  have hAE : blockU (rightConjugate J g) ⊓ Subgroup.normalizer (J : Set G) ≤ eSub J g :=
    inf_le_inf_right _ (blockU_le _)
  have hA2 : IsPGroup 2 ↥(blockU (rightConjugate J g) ⊓ Subgroup.normalizer (J : Set G)) :=
    (c.block.conj g).isPGroup_blockU.to_inf_left
  have hAeq := hT.eq_of_le (le_inf hTU hTN) hAE hA2
  have hxle : rightConjugate T x ≤ T := by
    intro s hs
    have hs' : x * s * x⁻¹ ∈ T := (mem_rightConjugate_iff T x s).1 hs
    have hsU : s ∈ blockU (rightConjugate J g) := by
      have h1 := conj_mem_blockU ((Subgroup.normalizer _).inv_mem hxB) (hTU hs')
      have e : x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s := by group
      rwa [e] at h1
    have hsN : s ∈ Subgroup.normalizer (J : Set G) := by
      have h1 := (Subgroup.normalizer (J : Set G)).mul_mem
        ((Subgroup.normalizer (J : Set G)).mul_mem
          ((Subgroup.normalizer (J : Set G)).inv_mem (Subgroup.le_normalizer hxJ)) (hTN hs'))
        (Subgroup.le_normalizer hxJ)
      have e : x⁻¹ * (x * s * x⁻¹) * x = s := by group
      rwa [e] at h1
    rw [← hAeq]
    exact ⟨hsU, hsN⟩
  have heq : rightConjugate T x = T :=
    Subgroup.eq_of_le_of_card_ge hxle (le_of_eq (rightConjugate_card T x).symm)
  exact (rightConjugate_eq_self_iff T x).1 heq

theorem exists_swap_le (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G} {T S : Subgroup G}
    (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hS : SylowFrame J T S) {x₁ : G} (hx₁J : x₁ ∈ J) (hx₁M : x₁ ∈ rightConjugate M g)
    (hx₁B : x₁ ∉ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G)) :
    ∃ x ∈ J, x ∈ rightConjugate M g ∧
      x ∉ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) ∧
      rightConjugate T x ≤ S ⊓ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : g ∉ M := hgood.1
  have hT1 : T ≠ ⊥ := sylow_ne_bot56 hgood hT
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTB : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hTJ : T ⊓ J = ⊥ := hS.inf_eq_bot
  have hc₁ := c.transport g
  have hnc := c.exists_noncentral hA hz hg hT hT1
  obtain ⟨t₀, ht₀T, ht₀1, ht₀2⟩ := exists_involution_of_isPGroup hT2 hT1
  have hCt₀ := c.centralizer_le_conj (hTB ht₀T) ⟨1, by rw [pow_one, pow_two]; exact ht₀2⟩ ht₀1
  have hne : rightConjugate (rightConjugate J g) x₁ ≠ rightConjugate J g := fun h =>
    hx₁B ((rightConjugate_eq_self_iff _ x₁).1 h)
  have hBB : ∀ b ∈ rightConjugate J g, ∀ b' ∈ rightConjugate (rightConjugate J g) x₁,
      b * b' = b' * b := by
    intro b hb b' hb'
    have hcomm := hc₁.commutator_conj_eq_bot hx₁M hne
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hb
    exact (Subgroup.mem_centralizer_iff.1 this b' hb').symm
  have hTx : rightConjugate T x₁ ≤ (J ⊔ T) ⊓ Subgroup.normalizer (T : Set G) := by
    intro s hs
    have hs' : x₁ * s * x₁⁻¹ ∈ T := (mem_rightConjugate_iff T x₁ s).1 hs
    refine ⟨?_, ?_⟩
    · have hj : (x₁ * s * x₁⁻¹)⁻¹ * x₁⁻¹ * (x₁ * s * x₁⁻¹) * x₁ ∈ J := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hTN (T.inv_mem hs')) x₁⁻¹).1 (J.inv_mem hx₁J)
        have h2 := J.mul_mem h1 hx₁J
        have e : (x₁ * s * x₁⁻¹)⁻¹ * x₁⁻¹ * (x₁ * s * x₁⁻¹)⁻¹⁻¹ * x₁ =
            (x₁ * s * x₁⁻¹)⁻¹ * x₁⁻¹ * (x₁ * s * x₁⁻¹) * x₁ := by group
        rwa [e] at h2
      have hmem : (x₁ * s * x₁⁻¹) * ((x₁ * s * x₁⁻¹)⁻¹ * x₁⁻¹ * (x₁ * s * x₁⁻¹) * x₁) ∈ T ⊔ J :=
        Subgroup.mul_mem_sup hs' hj
      have e2 : (x₁ * s * x₁⁻¹) * ((x₁ * s * x₁⁻¹)⁻¹ * x₁⁻¹ * (x₁ * s * x₁⁻¹) * x₁) = s := by
        group
      rw [e2, sup_comm] at hmem
      exact hmem
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht => ?_)
      have hsB' : s ∈ rightConjugate (rightConjugate J g) x₁ := by
        rw [mem_rightConjugate_iff]
        exact hTB hs'
      exact hBB t (hTB ht) s hsB'
  obtain ⟨c', hc'L, hc'le⟩ := exists_rightConjugate_le_of_isSylowOf (R := rightConjugate T x₁)
    hS.sylow_normalizer (hT2.map _) hTx
  have hc'inv : c'⁻¹ ∈ T ⊔ J := by
    rw [sup_comm]
    exact (J ⊔ T).inv_mem (Subgroup.mem_inf.1 hc'L).1
  obtain ⟨t₂, ht₂, j₂, hj₂, hc'eq⟩ := exists_mul_of_mem_sup hTN hc'inv
  set j' : G := j₂⁻¹ with hj'
  set t' : G := t₂⁻¹ with ht'
  have hc'e : c' = j' * t' := by
    rw [hj', ht', ← mul_inv_rev, hc'eq]
    group
  have hj'J : j' ∈ J := J.inv_mem hj₂
  have ht'T : t' ∈ T := T.inv_mem ht₂
  have hj'N : j' ∈ Subgroup.normalizer (T : Set G) := by
    have h1 := (Subgroup.mem_inf.1 hc'L).2
    have e : j' = c' * t'⁻¹ := by rw [hc'e]; group
    rw [e]
    exact (Subgroup.normalizer (T : Set G)).mul_mem h1
      ((Subgroup.normalizer (T : Set G)).inv_mem (Subgroup.le_normalizer ht'T))
  have hj'C : ∀ t ∈ T, j' * t = t * j' := by
    intro t ht
    have h1 : j' * t * j'⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hj'N t).1 ht
    have h2 : j' * t * j'⁻¹ * t⁻¹ ∈ T ⊓ J := by
      refine ⟨T.mul_mem h1 (T.inv_mem ht), ?_⟩
      have h3 := (Subgroup.mem_normalizer_iff.1 (hTN ht) j'⁻¹).1 (J.inv_mem hj'J)
      have e : j' * t * j'⁻¹ * t⁻¹ = j' * (t * j'⁻¹ * t⁻¹) := by group
      rw [e]
      exact J.mul_mem hj'J h3
    rw [hTJ, Subgroup.mem_bot] at h2
    calc j' * t = (j' * t * j'⁻¹ * t⁻¹) * (t * j') := by group
      _ = t * j' := by rw [h2, one_mul]
  have hj'M : j' ∈ rightConjugate M g := hCt₀ (Subgroup.mem_centralizer_singleton_iff.2
    (hj'C t₀ ht₀T))
  have hj'B : j' ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
    by_contra hjB
    have hne' : rightConjugate (rightConjugate J g) j' ≠ rightConjugate J g := fun h =>
      hjB ((rightConjugate_eq_self_iff _ j').1 h)
    have hcomm := hc₁.commutator_conj_eq_bot hj'M hne'
    obtain ⟨t, ht, k, hk, htk⟩ := hnc
    apply htk
    have htB' : t ∈ rightConjugate (rightConjugate J g) j' := by
      rw [mem_rightConjugate_iff]
      have e : j' * t * j'⁻¹ = t := by rw [hj'C t ht]; group
      rw [e]
      exact hTB ht
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hk
    exact Subgroup.mem_centralizer_iff.1 this t htB'
  refine ⟨x₁ * j', J.mul_mem hx₁J hj'J, (rightConjugate M g).mul_mem hx₁M hj'M, ?_, ?_⟩
  · intro hx
    apply hx₁B
    have := (Subgroup.normalizer _).mul_mem hx ((Subgroup.normalizer _).inv_mem hj'B)
    simpa using this
  · intro s hs
    have hs₂ : t'⁻¹ * s * t' ∈ rightConjugate (rightConjugate T (x₁ * j')) t' :=
      conj_mem_rightConjugate hs t'
    rw [rightConjugate_mul, mul_assoc, ← hc'e] at hs₂
    rw [rightConjugate_mul] at hc'le
    have h1 := hc'le hs₂
    have h2 : t' * (t'⁻¹ * s * t') * t'⁻¹ ∈ S ⊓ Subgroup.normalizer (T : Set G) := by
      have hW : t' ∈ S ⊓ Subgroup.normalizer (T : Set G) :=
        le_inf hS.le Subgroup.le_normalizer ht'T
      exact (S ⊓ Subgroup.normalizer (T : Set G)).mul_mem
        ((S ⊓ Subgroup.normalizer (T : Set G)).mul_mem hW h1)
        ((S ⊓ Subgroup.normalizer (T : Set G)).inv_mem hW)
    have e : t' * (t'⁻¹ * s * t') * t'⁻¹ = s := by group
    rwa [e] at h2

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
