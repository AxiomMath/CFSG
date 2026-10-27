module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionTwoGroup

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

section Pair

variable {Q : Type*} [Group Q]

@[expose] def fourGroupOfPair (a b : Q) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup Q where
  carrier := {1, a, b, a * b}
  one_mem' := by simp
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h3 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, ← hab, Set.mem_insert_iff,
        Set.mem_singleton_iff, true_or, or_true]
  inv_mem' := by
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · simp [ha']
    · simp [hb']
    · simp [ha', hb', hab]

theorem mem_fourGroupOfPair {a b : Q} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    {x : Q} : x ∈ fourGroupOfPair a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem isFourGroup_fourGroupOfPair [Finite Q] {a b : Q} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) :
    AschbacherKnownGroup.IsFourGroup
      (fourGroupOfPair a b (by rw [← pow_two, ← ha, pow_orderOf_eq_one])
        (by rw [← pow_two, ← hb, pow_orderOf_eq_one]) hab) := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left hb2]
  have habA : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habB : a * b ≠ b := fun h => ha1 (by simpa using h)
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    change x * y = y * x
    have hcomm : ∀ u ∈ ({1, a, b, a * b} : Set Q), u * a = a * u ∧ u * b = b * u := by
      rintro u (rfl | rfl | rfl | rfl)
      · simp
      · exact ⟨rfl, hab⟩
      · exact ⟨hab.symm, rfl⟩
      · refine ⟨?_, ?_⟩
        · calc a * b * a = b := by rw [hab, mul_assoc, ha2, mul_one]
            _ = a * (a * b) := by rw [← mul_assoc, ha2, one_mul]
        · calc a * b * b = a := by rw [mul_assoc, hb2, mul_one]
            _ = b * (a * b) := by rw [← mul_assoc, ← hab, mul_assoc, hb2, mul_one]
    rcases hy with rfl | rfl | rfl | rfl
    · simp
    · exact (hcomm x hx).1
    · exact (hcomm x hx).2
    · rw [← mul_assoc, (hcomm x hx).1, mul_assoc, (hcomm x hx).2, mul_assoc]
  · rcases hx with rfl | rfl | rfl | rfl
    · simp
    · rw [pow_two, ha2]
    · rw [pow_two, hb2]
    · rw [pow_two, mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb2, mul_one, ha2]
  · classical
    have hcard : (({1, a, b, a * b} : Finset Q) : Set Q) = (fourGroupOfPair a b ha2 hb2 hab) := by
      ext x
      simp [mem_fourGroupOfPair]
    have hc : Nat.card (fourGroupOfPair a b ha2 hb2 hab) = ({1, a, b, a * b} : Finset Q).card :=
      (Nat.card_congr (Set.equivOfEq hcard.symm)).trans (Nat.card_eq_finsetCard _)
    rw [hc]
    have h1a : (1 : Q) ≠ a := Ne.symm ha1
    have h1b : (1 : Q) ≠ b := Ne.symm hb1
    have h1ab : (1 : Q) ≠ a * b := Ne.symm hab1
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1b, h1ab]),
      Finset.card_insert_of_notMem (by simp [hne, habA.symm]),
      Finset.card_insert_of_notMem (by simp [habB.symm]), Finset.card_singleton]

end Pair

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem no_commuting_pair (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {a b : D ⧸ aschbacherThm5OddCore D} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b)
    (hfa : onQuotient D ⟨t, h.mem⟩ a = a) (hfb : onQuotient D ⟨t, h.mem⟩ b = b) (k : Fin r)
    (hak : a ∈ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D)))
    (hbk : b ∈ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D))) : False := by
  apply no_four_group_quotient hin hC h (isFourGroup_fourGroupOfPair ha hb hab hne)
  · rintro v (rfl | rfl | rfl | rfl)
    · exact map_one _
    · exact hfa
    · exact hfb
    · rw [map_mul, hfa, hfb]
  · rintro v (rfl | rfl | rfl | rfl) _
    · exact ⟨k, Subgroup.one_mem _⟩
    · exact ⟨k, hak⟩
    · exact ⟨k, hbk⟩
    · exact ⟨k, Subgroup.mul_mem _ hak hbk⟩

structure RankOneFactors (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (c : Fin r → D ⧸ aschbacherThm5OddCore D) : Prop where
  mem : ∀ k, c k ∈ Abar k
  orderOf_eq : ∀ k, orderOf (c k) = 2
  unique : ∀ k, ∀ x ∈ Abar k, orderOf x = 2 → x = c k

theorem mem_centralizer_factor (hyp : Hyp61 G D r Abar) {k l : Fin r} (hkl : k ≠ l)
    {x : D ⧸ aschbacherThm5OddCore D} (hx : x ∈ Abar l) :
    x ∈ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact hyp.hcomm k l hkl y hy x hx

theorem c_mem_centralizer (hyp : Hyp61 G D r Abar) {c : Fin r → D ⧸ aschbacherThm5OddCore D}
    (hc : RankOneFactors Abar c) (k l : Fin r) :
    c k ∈ Subgroup.centralizer (Abar l : Set (D ⧸ aschbacherThm5OddCore D)) := by
  by_cases hkl : l = k
  · subst hkl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (unique_involution_central (hc.mem l) (hc.orderOf_eq l) (hc.unique l) hy)
  · exact mem_centralizer_factor hyp hkl (hc.mem k)

omit [Finite G] in
theorem map_c {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c)
    (σ : MulAut (D ⧸ aschbacherThm5OddCore D)) {k l : Fin r}
    (hkl : (Abar k).map σ.toMonoidHom = Abar l) : σ (c k) = c l := by
  apply hc.unique l
  · rw [← hkl]
    exact Subgroup.mem_map_of_mem _ (hc.mem k)
  · rw [MulEquiv.orderOf_eq]
    exact hc.orderOf_eq k

omit [Finite G] in
theorem onQuotient_c {c : Fin r → D ⧸ aschbacherThm5OddCore D} (hc : RankOneFactors Abar c)
    (h : Subgroup.normalizer (D : Set G)) {k l : Fin r}
    (hkl : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar l)) :
    onQuotient D h (c k) = c l :=
  map_c hc (onQuotient D h) (map_onQuotient_factor h hkl)

theorem rankOneFactors_of_one (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {i : Fin r} {c₀ : D ⧸ aschbacherThm5OddCore D} (hc₀ : c₀ ∈ Abar i)
    (hc₀2 : orderOf c₀ = 2) (huniq : ∀ x ∈ Abar i, orderOf x = 2 → x = c₀) :
    ∃ c : Fin r → D ⧸ aschbacherThm5OddCore D, RankOneFactors Abar c ∧ c i = c₀ := by
  classical
  have hconj : ∀ k, ∃ h ∈ Subgroup.normalizer (D : Set G),
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar k) := fun k => hin.lemma_6_3 hC i k
  choose h hh hk using hconj
  let c : Fin r → D ⧸ aschbacherThm5OddCore D := fun k =>
    if k = i then c₀ else onQuotient D ⟨h k, hh k⟩ c₀
  have hmap : ∀ k, (Abar i).map (onQuotient D ⟨h k, hh k⟩).toMonoidHom = Abar k :=
    fun k => map_onQuotient_factor ⟨h k, hh k⟩ (hk k)
  refine ⟨c, ⟨fun k => ?_, fun k => ?_, fun k x hx hx2 => ?_⟩, by simp [c]⟩
  · by_cases hki : k = i
    · subst hki
      simpa [c] using hc₀
    · have : c k = onQuotient D ⟨h k, hh k⟩ c₀ := by simp [c, hki]
      rw [this, ← hmap k]
      exact Subgroup.mem_map_of_mem _ hc₀
  · by_cases hki : k = i
    · subst hki
      simpa [c] using hc₀2
    · have : c k = onQuotient D ⟨h k, hh k⟩ c₀ := by simp [c, hki]
      rw [this, MulEquiv.orderOf_eq]
      exact hc₀2
  · by_cases hki : k = i
    · subst hki
      have : c k = c₀ := by simp [c]
      rw [this]
      exact huniq x hx hx2
    · have hx' : (onQuotient D ⟨h k, hh k⟩).symm x ∈ Abar i := by
        rw [← hmap k] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa using hy
      have hy := huniq _ hx' (by rw [MulEquiv.orderOf_eq]; exact hx2)
      have : c k = onQuotient D ⟨h k, hh k⟩ c₀ := by simp [c, hki]
      rw [this, ← hy, MulEquiv.apply_symm_apply]

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
