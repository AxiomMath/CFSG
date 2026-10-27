module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LargeExtraspecialAll

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll

open CFSG.Open CFSG.HardMathSupport.MathTwE6

variable {G : Type*} [Group G]

structure Setup (G : Type*) [Group G] (p : ℕ) (w : G) (Q L X : Subgroup G)
    (a b k m : ℕ) : Prop where
  prime : p.Prime
  order_w : orderOf w = p
  hLQ : L ≤ Subgroup.normalizer (Q : Set G)
  hLX : L ≤ Subgroup.normalizer (X : Set G)
  hQX : Q ≤ X
  hwQ : w ∈ Q
  hwX : ∀ x ∈ X, x * w = w * x
  hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup p P →
    Nat.card P ≤ p
  hdich : ∀ N : Subgroup G, N ≤ Q → (∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G)) →
    N ≤ Subgroup.zpowers w ∨ N = Q
  hrel : (Subgroup.zpowers w).relIndex Q = p ^ a
  hk : k < p ^ a
  hm : k.factorial ∣ m
  hr : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ^ (k + 1) ∣ Nat.card G
  hb : b < 2 * a
  hG : ¬ p ^ (b + 1) ∣ Nat.card G

section Counting

variable [Finite G]

theorem card_eq_pow_mul_of_relIndex {p a : ℕ} {w : G} (hw : orderOf w = p) {Q : Subgroup G}
    (hwQ : w ∈ Q) (hrel : (Subgroup.zpowers w).relIndex Q = p ^ a) :
    Nat.card Q = p ^ a * p := by
  have h := Subgroup.relIndex_mul_card (Subgroup.zpowers w) Q
  rw [inf_of_le_left (Subgroup.zpowers_le.2 hwQ), Nat.card_zpowers, hw, hrel] at h
  exact h.symm

theorem mul_pow_dvd_card_sup {p a : ℕ} {w : G} (hw : orderOf w = p) {Q J A : Subgroup G}
    (hwQ : w ∈ Q) (hrel : (Subgroup.zpowers w).relIndex Q = p ^ a)
    (hQJ : Q ≤ Subgroup.normalizer (J : Set G)) (hQA : Q ≤ A) (hJA : J ≤ A)
    (hinf : Q ⊓ J ≤ Subgroup.zpowers w) : Nat.card J * p ^ a ∣ Nat.card A := by
  have hQc := card_eq_pow_mul_of_relIndex hw hwQ hrel
  have h1 := card_sup_mul_card_inf_of_le_normalizer hQJ
  have hdvd : Nat.card ↥(J ⊓ Q) ∣ p := by
    have := Subgroup.card_dvd_of_le ((inf_comm J Q).le.trans hinf)
    rwa [Nat.card_zpowers, hw] at this
  obtain ⟨s, hs⟩ := hdvd
  have hpos : 0 < Nat.card ↥(J ⊓ Q) := Nat.card_pos
  have h2 : Nat.card ↥(J ⊔ Q) = Nat.card J * p ^ a * s := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(J ⊔ Q) * Nat.card ↥(J ⊓ Q) = Nat.card J * Nat.card Q := h1
      _ = Nat.card J * (p ^ a * p) := by rw [hQc]
      _ = Nat.card J * p ^ a * s * Nat.card ↥(J ⊓ Q) := by
        rw [mul_assoc (Nat.card J * p ^ a) s, mul_comm s, ← hs]
        ring
  have h3 : Nat.card ↥(J ⊔ Q) ∣ Nat.card A := Subgroup.card_dvd_of_le (sup_le hJA hQA)
  exact (Dvd.intro s h2.symm).trans h3

theorem pow_two_mul_dvd_card_sup {p a : ℕ} {w : G} (hw : orderOf w = p) {Q J C : Subgroup G}
    (hwQ : w ∈ Q) (hrel : (Subgroup.zpowers w).relIndex Q = p ^ a)
    (hJC : ∀ j ∈ J, ∀ c ∈ C, j * c = c * j) (hQA : Q ≤ J ⊔ C)
    (hQJ : Q ⊓ J ≤ Subgroup.zpowers w) (hQC : Q ⊓ C ≤ Subgroup.zpowers w) :
    p ^ (2 * a) ∣ Nat.card ↥(J ⊔ C) := by
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact hJC j hj c hc
  have hJC' : J ≤ Subgroup.normalizer (C : Set G) := by
    intro j hj
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hJC j hj c hc).symm
  have hAJ : J ⊔ C ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hCJ
  have hAC : J ⊔ C ≤ Subgroup.normalizer (C : Set G) := sup_le hJC' Subgroup.le_normalizer
  have hA1 := mul_pow_dvd_card_sup hw hwQ hrel (hQA.trans hAJ) hQA le_sup_left hQJ
  have hA2 := mul_pow_dvd_card_sup hw hwQ hrel (hQA.trans hAC) hQA le_sup_right hQC
  have h3 := card_sup_mul_card_inf_of_le_normalizer hCJ
  obtain ⟨u, hu⟩ := hA1
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hC : Nat.card C = p ^ a * u * Nat.card ↥(J ⊓ C) := by
    apply Nat.eq_of_mul_eq_mul_left hJpos
    calc Nat.card J * Nat.card C = Nat.card ↥(J ⊔ C) * Nat.card ↥(J ⊓ C) := h3.symm
      _ = Nat.card J * (p ^ a * u * Nat.card ↥(J ⊓ C)) := by rw [hu]; ring
  have h4 : p ^ (2 * a) ∣ Nat.card C * p ^ a := by
    rw [hC]
    exact ⟨u * Nat.card ↥(J ⊓ C), by ring⟩
  exact h4.trans hA2

end Counting

section Cases

variable [Finite G] {p : ℕ} {w : G} {Q L X : Subgroup G} {a b k m : ℕ}

theorem component_cases (S : Setup G p w Q L X a b k m) {J : Subgroup G}
    (hJ : IsComponentOf J X) (hpJ : p ∣ Nat.card J) :
    Q ≤ Subgroup.normalizer (J : Set G) ∧
      ((Q ⊓ (J ⊔ (X ⊓ Subgroup.centralizer (J : Set G))) ≤ Subgroup.zpowers w ∧
        p ^ a * Nat.card ↥(J ⊔ (X ⊓ Subgroup.centralizer (J : Set G))) ∣ Nat.card G) ∨
        Q ≤ J) := by
  classical
  obtain ⟨r, hr, hr5, hrd⟩ := exists_prime_ge_five_dvd_index_center hJ.2.2
  have hrk := S.hr r hr hr5
  have hfix : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (J : Set G) := by
    intro g hg
    have h1 := pow_factorial_mem_normalizer (S.hLX hg) hJ hrd hrk
    obtain ⟨t, ht⟩ := S.hm
    rw [ht, pow_mul]
    exact (Subgroup.normalizer (J : Set G)).pow_mem h1 t
  have hLQm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (Q : Set G) := fun g hg =>
    (Subgroup.normalizer (Q : Set G)).pow_mem (S.hLQ hg) m
  have hLXm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (X : Set G) := fun g hg =>
    (Subgroup.normalizer (X : Set G)).pow_mem (S.hLX hg) m
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := by
    set N : Subgroup G := Q ⊓ Subgroup.normalizer (J : Set G) with hN
    have hNnorm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G) := fun g hg =>
      mem_normalizer_inf (hLQm g hg) (Subgroup.le_normalizer (hfix g hg))
    rcases S.hdich N inf_le_left hNnorm with hNw | hNQ
    · exfalso
      have hcount := index_normalizer_le (S.hQX.trans Subgroup.le_normalizer) hJ hrd hrk
      have hsub : N.subgroupOf Q = (Subgroup.normalizer (J : Set G)).subgroupOf Q := by
        ext x
        simp only [Subgroup.mem_subgroupOf, hN, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      have hdvd : (Subgroup.zpowers w).relIndex Q ∣ N.relIndex Q :=
        Subgroup.relIndex_dvd_of_le_left Q hNw
      rw [S.hrel, Subgroup.relIndex, hsub] at hdvd
      have hne : ((Subgroup.normalizer (J : Set G)).subgroupOf Q).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      have h2 := S.hk
      omega
    · intro q hq
      have : q ∈ N := by rw [hNQ]; exact hq
      exact (Subgroup.mem_inf.1 this).2
  refine ⟨hQN, ?_⟩
  have hJX : J ≤ X := hJ.1
  have hwJ : ∀ j ∈ J, j * w = w * j := fun j hj => S.hwX j (hJX hj)
  have hwQ' : w ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact S.hwX q (S.hQX hq)
  have hnotC : ¬ J ≤ Subgroup.centralizer (Q : Set G) := fun hJQ =>
    not_dvd_card_of_perfect_le_centralizer S.prime S.order_w hwQ' hwJ hJQ S.hCQ hJ.2.2.1 hpJ
  have hQCJ : Q ⊓ Subgroup.centralizer (J : Set G) ≤ Subgroup.zpowers w := by
    rcases S.hdich (Q ⊓ Subgroup.centralizer (J : Set G)) inf_le_left
      (fun g hg => mem_normalizer_inf (hLQm g hg) (mem_normalizer_centralizer (hfix g hg)))
      with h | h
    · exact h
    · exfalso
      apply hnotC
      have hQC : Q ≤ Subgroup.centralizer (J : Set G) := h.symm.le.trans inf_le_right
      rw [← Subgroup.le_centralizer_iff]
      exact hQC
  have hD2 := S.hdich (Q ⊓ J) inf_le_left
    (fun g hg => mem_normalizer_inf (hLQm g hg) (hfix g hg))
  set C : Subgroup G := X ⊓ Subgroup.centralizer (J : Set G) with hCdef
  set A : Subgroup G := J ⊔ C with hAdef
  have hCnorm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_inf (hLXm g hg) (mem_normalizer_centralizer (hfix g hg))
  have hAnorm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (A : Set G) := fun g hg =>
    mem_normalizer_sup (hfix g hg) (hCnorm g hg)
  have hD3 := S.hdich (Q ⊓ A) inf_le_left
    (fun g hg => mem_normalizer_inf (hLQm g hg) (hAnorm g hg))
  by_cases hQJ : Q ≤ J
  · exact Or.inr hQJ
  left
  have hQJw : Q ⊓ J ≤ Subgroup.zpowers w := by
    rcases hD2 with h | h
    · exact h
    · exact absurd (h.symm.le.trans inf_le_right) hQJ
  have hQCw : Q ⊓ C ≤ Subgroup.zpowers w :=
    (inf_le_inf_left Q (inf_le_right : C ≤ Subgroup.centralizer (J : Set G))).trans hQCJ
  rcases hD3 with hQAw | hQA
  ·
    refine ⟨hQAw, ?_⟩
    have hwC : w ∈ C := Subgroup.mem_inf.2 ⟨S.hQX S.hwQ, by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact hwJ j hj⟩
    have hwA : w ∈ A := (le_sup_right : C ≤ A) hwC
    have hQAeq : Q ⊓ A = Subgroup.zpowers w :=
      le_antisymm hQAw (le_inf (Subgroup.zpowers_le.2 S.hwQ) (Subgroup.zpowers_le.2 hwA))
    have hQNA : Q ≤ Subgroup.normalizer (A : Set G) := by
      intro q hq
      refine mem_normalizer_sup (hQN hq) ?_
      exact mem_normalizer_inf (Subgroup.le_normalizer (S.hQX hq))
        (mem_normalizer_centralizer (hQN hq))
    have hprod := card_sup_mul_card_inf_of_le_normalizer hQNA
    have hQc := card_eq_pow_mul_of_relIndex S.order_w S.hwQ S.hrel
    have hAQ : A ⊓ Q = Subgroup.zpowers w := by rw [inf_comm]; exact hQAeq
    rw [hAQ, Nat.card_zpowers, S.order_w, hQc] at hprod
    have hpp : 0 < p := S.prime.pos
    have h2 : Nat.card ↥(A ⊔ Q) = Nat.card A * p ^ a := by
      apply Nat.eq_of_mul_eq_mul_right hpp
      rw [hprod]
      ring
    have h3 : Nat.card ↥(A ⊔ Q) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [h2] at h3
    simpa [mul_comm] using h3
  ·
    exfalso
    have hJC : ∀ j ∈ J, ∀ c ∈ C, j * c = c * j := by
      intro j hj c hc
      have : c ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.1 hc).2
      exact Subgroup.mem_centralizer_iff.1 this j hj
    have hQA' : Q ≤ J ⊔ C := hQA.symm.le.trans inf_le_right
    have h2a := pow_two_mul_dvd_card_sup S.order_w S.hwQ S.hrel hJC hQA' hQJw hQCw
    apply S.hG
    have hb := S.hb
    exact (pow_dvd_pow p (by omega)).trans (h2a.trans (Subgroup.card_subgroup_dvd_card _))

theorem beta2a_structure (S : Setup G p w Q L X a b k m) {J : Subgroup G}
    (hJ : IsComponentOf J X) (hQJ : Q ≤ J)
    (hpd : ∀ K : Subgroup G, IsComponentOf K X → p ∣ Nat.card K)
    (hO : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      Nat.Coprime p (Nat.card N) → N = ⊥) :
    (∀ K : Subgroup G, IsComponentOf K X → K = J) ∧ X ≤ Subgroup.normalizer (J : Set G) ∧
      X ⊓ Subgroup.centralizer (J : Set G) = Subgroup.zpowers w ∧
      Nat.card (Subgroup.center J) = p := by
  classical
  have hwQ' : w ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact S.hwX q (S.hQX hq)
  have huniq : ∀ K : Subgroup G, IsComponentOf K X → K = J := by
    intro K hK
    by_contra hne
    have hKQ : K ≤ Subgroup.centralizer (Q : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hJ hne hx (hQJ hq)).symm
    exact not_dvd_card_of_perfect_le_centralizer S.prime S.order_w hwQ'
      (fun j hj => S.hwX j (hK.1 hj)) hKQ S.hCQ hK.2.2.1 (hpd K hK)
  have hXN : X ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    have hc := isComponentOf_map_conj_of_mem_normalizer hJ (Subgroup.le_normalizer hx)
    exact (map_conj_eq_iff_mem_normalizer J x).1 (huniq _ hc)
  set C : Subgroup G := X ⊓ Subgroup.centralizer (J : Set G) with hCdef
  have hCX : C ≤ X := inf_le_left
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (mem_normalizer_centralizer (hXN hx))
  have hwC : w ∈ C := Subgroup.mem_inf.2 ⟨S.hQX S.hwQ, by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact S.hwX j (hJ.1 hj)⟩
  have hCQ' : C ≤ Subgroup.centralizer (Q : Set G) := fun c hc =>
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQJ) (Subgroup.mem_inf.1 hc).2
  have hC2 := not_sq_dvd_card_of_le_centralizer S.prime S.hCQ hCQ'
  have hCeq : C = Subgroup.zpowers w :=
    eq_zpowers_of_central_sylow S.prime S.order_w hCX hXC hwC S.hwX hC2 hO
  have hwJ : w ∈ J := hQJ S.hwQ
  have hZ : (Subgroup.center J).map J.subtype = Subgroup.zpowers w := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzc : (z : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨j, hj⟩)
      have : (z : G) ∈ C := Subgroup.mem_inf.2 ⟨hJ.1 z.2, hzc⟩
      rwa [hCeq] at this
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨w, hwJ⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (S.hwX g (hJ.1 g.2))
  refine ⟨huniq, hXN, hCeq, ?_⟩
  rw [← Subgroup.card_map_of_injective J.subtype_injective, hZ, Nat.card_zpowers, S.order_w]

end Cases

end CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll
