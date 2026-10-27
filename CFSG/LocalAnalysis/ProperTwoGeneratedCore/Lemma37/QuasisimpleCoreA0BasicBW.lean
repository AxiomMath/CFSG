module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem exists_mul_of_index_eq_relIndex {G : Type*} [Group G] [Finite G] {Y C : Subgroup G}
    (h : Y.index = Y.relIndex C) (g : G) : ∃ c ∈ C, ∃ y ∈ Y, g = c * y := by
  let f := Subgroup.quotientSubgroupOfEmbeddingOfLE Y (le_top : C ≤ ⊤)
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨f.injective, ?_⟩
    change Y.relIndex C = Y.relIndex ⊤
    rw [Subgroup.relIndex_top_right, h]
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq] at hq
  refine ⟨c, c.2, (c : G)⁻¹ * g, ?_, by group⟩
  simpa [Subgroup.mem_subgroupOf] using hq

theorem odd_orderOf_of_mem {G : Type*} [Group G] {O : Subgroup G} (hO : Odd (Nat.card O))
    {o : G} (ho : o ∈ O) : Odd (orderOf o) := by
  have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  exact Odd.of_dvd_nat hO hdvd

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

namespace Setting

theorem inv_eq_central_mul (h : Setting J Q B) {c : J} (hc : c * c = centralElt J) :
    c⁻¹ = centralElt J * c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← mul_assoc, (h.commute_centralElt c).eq, mul_assoc, hc, h.centralElt_mul_self]

theorem eq_centralElt_of_conj_mem (h : Setting J Q B) {o t : J} (ho : o ∉ B) (htB : t ∈ B)
    (hot : o * t * o⁻¹ ∈ B) (ht : orderOf t = 2) : t = centralElt J := by
  refine h.eq_centralElt_of_mem_inf_conj ho ⟨htB, Subgroup.mem_map.mpr ⟨_, hot, ?_⟩⟩ ht
  change o⁻¹ * (o * t * o⁻¹) * o⁻¹⁻¹ = t
  group

theorem exists_mul_eq_of_centralizer_le (h : Setting J Q B) {O : Subgroup J}
    (hodd : Odd (Nat.card O)) {a b : J} (haB : a ∈ B) (hbB : b ∈ B)
    (haa : a * a ∈ Subgroup.center J) (hbb : b * b ∈ Subgroup.center J)
    (ha : a ∉ Subgroup.center J) (hb : b ∉ Subgroup.center J)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J) (hne : a * b ∉ Subgroup.center J)
    (haO : a ∈ Subgroup.normalizer (O : Set J)) (hbO : b ∈ Subgroup.normalizer (O : Set J))
    (haC : ∀ n ∈ O, n * a = a * n → n ∈ B) (hbC : ∀ n ∈ O, n * b = b * n → n ∈ B)
    {o : J} (ho : o ∈ O) : ∃ y ∈ O, y ∈ B ∧ ∃ c ∈ O, c * (a * b) = a * b * c ∧ o = y * c := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center J) with hπ
  have hπZ : ∀ x : J, π x = 1 ↔ x ∈ Subgroup.center J := fun x => QuotientGroup.eq_one_iff x
  have haa' : π a * π a = 1 := by rw [← map_mul, hπZ]; exact haa
  have hbb' : π b * π b = 1 := by rw [← map_mul, hπZ]; exact hbb
  have hcomm : Commute (π a) (π b) := (commute_mk_iff a b).mpr hab
  have ha1 : π a ≠ 1 := fun h1 => ha ((hπZ a).mp h1)
  have hb1 : π b ≠ 1 := fun h1 => hb ((hπZ b).mp h1)
  have hab1 : π a ≠ π b := fun h1 => hne ((hπZ _).mp (by rw [map_mul, h1, hbb']))
  set A := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (π a) (π b) haa' hbb' hcomm
    with hA
  have hAK : IsKleinFour A := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ haa' hbb' ha1 hb1 hab1 hcomm
  have hAmem : ∀ x, x ∈ A ↔ x = π a * π b ∨ x = π a ∨ x = π b ∨ x = 1 := fun x => by
    change x ∈ ({π a * π b, π a, π b, 1} : Set (J ⧸ Subgroup.center J)) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  set X := O.map π with hX
  have hnorm : ∀ m ∈ Subgroup.normalizer (O : Set J), π m ∈ Subgroup.normalizer (X : Set _) :=
    fun m hm => Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hm)
  have hAX : A ≤ Subgroup.normalizer (X : Set _) := by
    intro x hx
    rcases (hAmem x).mp hx with rfl | rfl | rfl | rfl
    · rw [← map_mul]
      exact hnorm _ ((Subgroup.normalizer _).mul_mem haO hbO)
    · exact hnorm _ haO
    · exact hnorm _ hbO
    · exact Subgroup.one_mem _
  have hAB : A ≤ B.map π := by
    intro x hx
    rcases (hAmem x).mp hx with rfl | rfl | rfl | rfl
    · rw [← map_mul]
      exact Subgroup.mem_map_of_mem π (B.mul_mem haB hbB)
    · exact Subgroup.mem_map_of_mem π haB
    · exact Subgroup.mem_map_of_mem π hbB
    · exact Subgroup.one_mem _
  have hXodd : Odd (Nat.card X) := Odd.of_dvd_nat hodd (Subgroup.card_map_dvd O π)
  let _ : MulDistribMulAction A X :=
    MulDistribMulAction.compHom X (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))
  have hsmul : ∀ (x : A) (y : X), ((x • y : X) : J ⧸ Subgroup.center J) =
      (x : J ⧸ Subgroup.center J) * y * (x : J ⧸ Subgroup.center J)⁻¹ := fun _ _ => rfl
  set Y : Subgroup X := (B.map π).subgroupOf X with hY
  have hYinv : ∀ x : A, ∀ y ∈ Y, x • y ∈ Y := by
    intro x y hy
    rw [hY, Subgroup.mem_subgroupOf, hsmul]
    exact (B.map π).mul_mem ((B.map π).mul_mem (hAB x.2) hy) ((B.map π).inv_mem (hAB x.2))
  have hfix : ∀ g : J, (∀ n ∈ O, n * g = g * n → n ∈ B) → ∀ x : A,
      (x : J ⧸ Subgroup.center J) = π g → ∀ y : X, x • y = y → y ∈ Y := by
    intro g hgC x hx y hxy
    obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp y.2
    have h1 := congrArg Subtype.val hxy
    rw [hsmul, hx, ← hny] at h1
    have h2 : Commute (π n) (π g) := by
      change π n * π g = π g * π n
      calc π n * π g = π g * π n * (π g)⁻¹ * π g := by rw [h1]
        _ = π g * π n := by group
    rw [hY, Subgroup.mem_subgroupOf, ← hny]
    exact Subgroup.mem_map_of_mem π (hgC n hn
      (h.mul_comm_of_odd (odd_orderOf_of_mem hodd hn) ((commute_mk_iff n g).mp h2)))
  let _ : Fintype A := Fintype.ofFinite A
  set x₀ : A := ⟨π a * π b, (hAmem _).mpr (Or.inl rfl)⟩ with hx₀
  have hx₀1 : x₀ ≠ 1 := fun h1 => hab1 (by
    have h2 : π a * π b = 1 := congrArg Subtype.val h1
    calc π a = π a * π b * π b := by rw [mul_assoc, hbb', mul_one]
      _ = π b := by rw [h2, one_mul])
  have hrel := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity (A := A)
    (X := X) hXodd).2 Y hYinv
  have hAle : CFSG.fixedPointSubgroup A X ≤ Y := fun y hy =>
    hfix a haC ⟨π a, (hAmem _).mpr (Or.inr (Or.inl rfl))⟩ rfl y
      ((FixedPoints.mem_subgroup A X y).mp hy _)
  rw [Subgroup.relIndex_eq_one.mpr hAle, one_pow, mul_one,
    Finset.prod_eq_single_of_mem x₀ (Finset.mem_erase.mpr ⟨hx₀1, Finset.mem_univ _⟩)] at hrel
  swap
  · intro x hx hxx₀
    rw [Subgroup.relIndex_eq_one]
    intro y hy
    have hxy : x • y = y := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff x y).mp hy
    rcases (hAmem x).mp x.2 with h1 | h1 | h1 | h1
    · exact absurd (Subtype.ext h1) hxx₀
    · exact hfix a haC x h1 y hxy
    · exact hfix b hbC x h1 y hxy
    · exact absurd (Subtype.ext h1) (Finset.mem_erase.mp hx).1
  obtain ⟨cb, hcb, yb, hyb, hdec⟩ := exists_mul_of_index_eq_relIndex hrel
    (⟨π o⁻¹, Subgroup.mem_map_of_mem π (O.inv_mem ho)⟩ : X)
  obtain ⟨c, hcO, hc⟩ := Subgroup.mem_map.mp cb.2
  obtain ⟨y, hyO, hy⟩ := Subgroup.mem_map.mp yb.2
  have hcab : c * (a * b) = a * b * c := by
    have h1 := congrArg Subtype.val
      ((CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff x₀ cb).mp hcb)
    rw [hsmul, ← hc] at h1
    have h2 : Commute (π c) (π (a * b)) := by
      change π c * π (a * b) = π (a * b) * π c
      rw [map_mul]
      calc π c * (π a * π b) = π a * π b * π c * (π a * π b)⁻¹ * (π a * π b) := by
            rw [show (x₀ : J ⧸ Subgroup.center J) = π a * π b from rfl] at h1
            rw [h1]
        _ = π a * π b * π c := by group
    exact h.mul_comm_of_odd (odd_orderOf_of_mem hodd hcO) ((commute_mk_iff c (a * b)).mp h2)
  have hyB : y ∈ B := by
    have h1 := hyb
    rw [hY, Subgroup.mem_subgroupOf, ← hy] at h1
    exact (h.mk_mem_map_iff y).mp h1
  have hdec' : π o⁻¹ = π c * π y := by
    have h1 := congrArg Subtype.val hdec
    rwa [Subgroup.coe_mul, ← hc, ← hy] at h1
  have hζ : (c * y)⁻¹ * o⁻¹ ∈ Subgroup.center J := by
    rw [← hπZ, map_mul, map_inv, map_mul, ← hdec', inv_mul_cancel]
  have hζO : (c * y)⁻¹ * o⁻¹ ∈ O := O.mul_mem (O.inv_mem (O.mul_mem hcO hyO)) (O.inv_mem ho)
  have hζ1 : (c * y)⁻¹ * o⁻¹ = 1 := by
    rcases h.mem_center_iff.mp hζ with h1 | h1
    · exact h1
    · exfalso
      have h2 := odd_orderOf_of_mem hodd hζO
      rw [h1, h.orderOf_centralElt] at h2
      exact absurd h2 (by decide)
  have hoinv : o⁻¹ = c * y := by
    calc o⁻¹ = (c * y) * ((c * y)⁻¹ * o⁻¹) := by group
      _ = c * y := by rw [hζ1, mul_one]
  refine ⟨y⁻¹, O.inv_mem hyO, B.inv_mem hyB, c⁻¹, O.inv_mem hcO, ?_, ?_⟩
  · calc c⁻¹ * (a * b) = c⁻¹ * (a * b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (a * b)) * c⁻¹ := by rw [hcab]
      _ = a * b * c⁻¹ := by group
  · calc o = (o⁻¹)⁻¹ := by group
      _ = y⁻¹ * c⁻¹ := by rw [hoinv]; group

theorem exists_mul_eq_of_odd (h : Setting J Q B) {O : Subgroup J} (hodd : Odd (Nat.card O))
    {a b : J} (haB : a ∈ B) (hbB : b ∈ B) (haa : a * a = 1) (hbb : b * b = 1)
    (ha : a ∉ Subgroup.center J) (hb : b ∉ Subgroup.center J)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J) (hne : a * b ∉ Subgroup.center J)
    (haO : a ∈ Subgroup.normalizer (O : Set J)) (hbO : b ∈ Subgroup.normalizer (O : Set J))
    {o : J} (ho : o ∈ O) : ∃ y ∈ O, y ∈ B ∧ ∃ c ∈ O, c * (a * b) = a * b * c ∧ o = y * c := by
  have hC : ∀ g : J, g ∈ B → g * g = 1 → g ∉ Subgroup.center J →
      ∀ n ∈ O, n * g = g * n → n ∈ B := fun g hgB hgg hgZ n _ hng => by
    have hg1 : g ≠ 1 := fun h1 => hgZ (h1 ▸ (Subgroup.center J).one_mem)
    exact h.centralizer_le hgB (orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1) hgZ
      (Subgroup.mem_centralizer_singleton_iff.mpr hng)
  exact h.exists_mul_eq_of_centralizer_le hodd haB hbB (haa ▸ (Subgroup.center J).one_mem)
    (hbb ▸ (Subgroup.center J).one_mem) ha hb hab hne haO hbO (hC a haB haa ha)
    (hC b hbB hbb hb) ho

theorem exists_mem_not_mem_commute (h : Setting J Q B) {O : Subgroup J}
    (hodd : Odd (Nat.card O)) (hOB : ¬ O ≤ B) {a b : J} (haB : a ∈ B) (hbB : b ∈ B)
    (haa : a * a = 1) (hbb : b * b = 1) (ha : a ∉ Subgroup.center J)
    (hb : b ∉ Subgroup.center J) (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J)
    (hne : a * b ∉ Subgroup.center J) (haO : a ∈ Subgroup.normalizer (O : Set J))
    (hbO : b ∈ Subgroup.normalizer (O : Set J)) :
    ∃ o ∈ O, o ∉ B ∧ o * (a * b) = a * b * o := by
  obtain ⟨o, hoO, hoB⟩ := Set.not_subset.mp hOB
  obtain ⟨y, -, hyB, c, hcO, hc, rfl⟩ :=
    h.exists_mul_eq_of_odd hodd haB hbB haa hbb ha hb hab hne haO hbO hoO
  exact ⟨c, hcO, fun hcB => hoB (B.mul_mem hyB hcB), hc⟩

theorem mul_eq_central_mul_of_odd (h : Setting J Q B) {O : Subgroup J}
    (hodd : Odd (Nat.card O)) (hOB : ¬ O ≤ B) {a b : J} (haB : a ∈ B) (hbB : b ∈ B)
    (haa : a * a = 1) (hbb : b * b = 1) (ha : a ∉ Subgroup.center J)
    (hb : b ∉ Subgroup.center J) (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J)
    (hne : a * b ∉ Subgroup.center J) (haO : a ∈ Subgroup.normalizer (O : Set J))
    (hbO : b ∈ Subgroup.normalizer (O : Set J)) : a * b = centralElt J * (b * a) := by
  obtain ⟨o, -, hoB, hoab⟩ :=
    h.exists_mem_not_mem_commute hodd hOB haB hbB haa hbb ha hb hab hne haO hbO
  have hsplit : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
  rcases h.mem_center_iff.mp hab with h1 | h1
  · exfalso
    have hba : a * b = b * a := by rw [hsplit, h1, one_mul]
    have hww : a * b * (a * b) = 1 := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = (a * a) * (b * b) := by rw [← hba]; group
        _ = 1 := by rw [haa, hbb, mul_one]
    have hw1 : a * b ≠ 1 := fun h2 => hne (h2 ▸ (Subgroup.center J).one_mem)
    have hw2 : orderOf (a * b) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
    have hwB : a * b ∈ B := B.mul_mem haB hbB
    have hconj : o * (a * b) * o⁻¹ ∈ B := by rw [hoab, mul_inv_cancel_right]; exact hwB
    exact hne (h.eq_centralElt_of_conj_mem hoB hwB hconj hw2 ▸ h.centralElt_mem_center)
  · rw [hsplit, h1]

theorem eq_of_commute_of_odd (h : Setting J Q B) {c : J} (hcB : c ∈ B)
    (hcc : c * c = centralElt J) {O : Subgroup J} (hOX : O ≤ quasiNormalizer c)
    (hXO : quasiNormalizer c ≤ Subgroup.normalizer (O : Set J)) (hodd : Odd (Nat.card O))
    (hOB : ¬ O ≤ B) {a b : J} (haB : a ∈ B) (hbB : b ∈ B) (haX : a ∈ quasiNormalizer c)
    (hbX : b ∈ quasiNormalizer c) (haa : a * a = 1) (hbb : b * b = 1)
    (ha : a ∉ Subgroup.center J) (hb : b ∉ Subgroup.center J)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J) (hne : a * b ∉ Subgroup.center J)
    (hcomm : a * b * c = c * (a * b)) : a * b = c ∨ a * b = centralElt J * c := by
  obtain ⟨o, hoO, hoB, hoab⟩ :=
    h.exists_mem_not_mem_commute hodd hOB haB hbB haa hbb ha hb hab hne (hXO haX) (hXO hbX)
  have hanti :=
    h.mul_eq_central_mul_of_odd hodd hOB haB hbB haa hbb ha hb hab hne (hXO haX) (hXO hbX)
  have hoc : o * c = c * o := h.mul_comm_of_odd (odd_orderOf_of_mem hodd hoO)
    ((h.mem_normalizer_zpowers_iff hcc).mp (hOX hoO))
  have hww : a * b * (a * b) = centralElt J := by
    calc a * b * (a * b) = a * b * a * b := by group
      _ = centralElt J * (b * a) * a * b := by rw [hanti]
      _ = centralElt J * (b * (a * a) * b) := by group
      _ = centralElt J := by rw [haa, mul_one, hbb, mul_one]
  have hxx : c * (a * b) * (c * (a * b)) = 1 := by
    calc c * (a * b) * (c * (a * b)) = c * (a * b * c) * (a * b) := by group
      _ = (c * c) * (a * b * (a * b)) := by rw [hcomm]; group
      _ = 1 := by rw [hcc, hww, h.centralElt_mul_self]
  have hxB : c * (a * b) ∈ B := B.mul_mem hcB (B.mul_mem haB hbB)
  have hox : o * (c * (a * b)) * o⁻¹ ∈ B := by
    have h1 : o * (c * (a * b)) * o⁻¹ = c * (a * b) := by
      calc o * (c * (a * b)) * o⁻¹ = (o * c) * (a * b) * o⁻¹ := by group
        _ = c * (o * (a * b)) * o⁻¹ := by rw [hoc]; group
        _ = c * (a * b) := by rw [hoab]; group
    rw [h1]
    exact hxB
  have hcinv := h.inv_eq_central_mul hcc
  by_cases hx1 : c * (a * b) = 1
  · right
    rw [← hcinv]
    calc a * b = c⁻¹ * (c * (a * b)) := by group
      _ = c⁻¹ := by rw [hx1, mul_one]
  · left
    have hx2 : orderOf (c * (a * b)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
    have hxe := h.eq_centralElt_of_conj_mem hoB hxB hox hx2
    calc a * b = c⁻¹ * (c * (a * b)) := by group
      _ = c := by
        rw [hxe, hcinv, mul_assoc, (h.commute_centralElt c).eq, ← mul_assoc,
          h.centralElt_mul_self, one_mul]

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
