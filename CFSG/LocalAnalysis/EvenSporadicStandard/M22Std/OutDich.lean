module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutKSq

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

omit [Finite G] in
theorem sq_mul_mul_F (h : OutOne L z F) {k k' u u' : G} (hk : k ∈ Ksub z F) (hk' : k' ∈ Ksub z F)
    (hu : u ∈ F) (hu' : u' ∈ F) :
    (k * u * (k' * u')) * (k * u * (k' * u')) = (k * k') * (k * k') := by
  have hu_k : u * k = k * u := (mem_Ksub.1 hk).2 u hu
  have hu_k' : u * k' = k' * u := (mem_Ksub.1 hk').2 u hu
  have hu'_k : u' * k = k * u' := (mem_Ksub.1 hk).2 u' hu'
  have hu'_k' : u' * k' = k' * u' := (mem_Ksub.1 hk').2 u' hu'
  have huu' : u * u' = u' * u := h.F_comm u hu u' hu'
  have hc2 : (u * u') * (u * u') = 1 := by
    calc u * u' * (u * u') = u * (u' * u) * u' := by simp only [mul_assoc]
      _ = u * (u * u') * u' := by rw [← huu']
      _ = (u * u) * (u' * u') := by simp only [mul_assoc]
      _ = 1 := by rw [h.F_sq u hu, h.F_sq u' hu', mul_one]
  have hmm : k * u * (k' * u') = (k * k') * (u * u') := by
    calc k * u * (k' * u') = k * (u * k') * u' := by simp only [mul_assoc]
      _ = k * (k' * u) * u' := by rw [hu_k']
      _ = (k * k') * (u * u') := by simp only [mul_assoc]
  have hA : ∀ w : G, w * k = k * w → w * k' = k' * w → w * (k * k') = (k * k') * w := by
    intro w h1 h2
    calc w * (k * k') = (w * k) * k' := by simp only [mul_assoc]
      _ = (k * w) * k' := by rw [h1]
      _ = k * (w * k') := by simp only [mul_assoc]
      _ = k * (k' * w) := by rw [h2]
      _ = (k * k') * w := by simp only [mul_assoc]
  have hcomm : (u * u') * (k * k') = (k * k') * (u * u') := by
    have h1 := hA u hu_k hu_k'
    have h2 := hA u' hu'_k hu'_k'
    calc (u * u') * (k * k') = u * (u' * (k * k')) := by simp only [mul_assoc]
      _ = u * ((k * k') * u') := by rw [h2]
      _ = (u * (k * k')) * u' := by simp only [mul_assoc]
      _ = ((k * k') * u) * u' := by rw [h1]
      _ = (k * k') * (u * u') := by simp only [mul_assoc]
  calc (k * u * (k' * u')) * (k * u * (k' * u'))
      = ((k * k') * (u * u')) * ((k * k') * (u * u')) := by rw [hmm]
    _ = (k * k') * ((u * u') * (k * k')) * (u * u') := by simp only [mul_assoc]
    _ = (k * k') * ((k * k') * (u * u')) * (u * u') := by rw [hcomm]
    _ = ((k * k') * (k * k')) * ((u * u') * (u * u')) := by simp only [mul_assoc]
    _ = (k * k') * (k * k') := by rw [hc2, mul_one]

omit [Finite G] in
theorem pairProp_of_sq (h : OutOne L z F) {a b : G}
    (ha : a ∈ Ksub z F) (hb : b ∈ Ksub z F) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : phiv z a ≠ 1) (hb1 : phiv z b ≠ 1) (hab : (a * b) * (a * b) = 1) :
    PairProp z F (phiv z a) (phiv z b) := by
  intro m hm m' hm' hm2 hm'2 hmf hm'f'
  obtain ⟨u, hu, hmu⟩ := (involutions_eq h ha ha2 ha1).1 ⟨hm, hmf, hm2⟩
  obtain ⟨u', hu', hm'u'⟩ := (involutions_eq h hb hb2 hb1).1 ⟨hm', hm'f', hm'2⟩
  rw [hmu, hm'u', sq_mul_mul_F h ha hb hu hu']
  exact hab

omit [Finite G] in
theorem pairProp_iff_sq (h : OutOne L z F) {a b f f' : G}
    (ha : a ∈ Ksub z F) (hb : b ∈ Ksub z F) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (haf : phiv z a = f) (hbf : phiv z b = f') (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) :
    PairProp z F f f' ↔ (a * b) * (a * b) = 1 := by
  subst haf hbf
  exact ⟨fun hP => sq_of_pairProp ha hb ha2 hb2 hP,
    fun hab => pairProp_of_sq h ha hb ha2 hb2 hf1 hf'1 hab⟩

theorem pairProp_iff_triple (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f f' g : G} (hf : f ∈ F) (hf' : f' ∈ F) (hg : g ∈ F)
    (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hff : f ≠ f') (hfg : f ≠ g) (hf'g : f' ≠ g)
    (hfff : f * f' ≠ g) :
    (PairProp z F f f' ↔ PairProp z F f g) ∧ (PairProp z F f f' ↔ PairProp z F f' g) := by
  obtain ⟨a, ha, haf, ha2⟩ := exists_involution h hsq X htr hf hf1
  obtain ⟨b, hb, hbf, hb2⟩ := exists_involution h hsq X htr hf' hf'1
  obtain ⟨c, hc, hcg, hc2⟩ := exists_involution h hsq X htr hg hg1
  have hab : a * b ∈ Ksub z F := Subgroup.mul_mem _ ha hb
  have hac : a * c ∈ Ksub z F := Subgroup.mul_mem _ ha hc
  have hbc : b * c ∈ Ksub z F := Subgroup.mul_mem _ hb hc
  have habc : a * b * c ∈ Ksub z F := Subgroup.mul_mem _ hab hc
  have pab : phiv z (a * b) = f * f' := by rw [phiv_mul h ha hb, haf, hbf]
  have pac : phiv z (a * c) = f * g := by rw [phiv_mul h ha hc, haf, hcg]
  have pbc : phiv z (b * c) = f' * g := by rw [phiv_mul h hb hc, hbf, hcg]
  have pabc : phiv z (a * b * c) = f * f' * g := by rw [phiv_mul h hab hc, pab, hcg]
  have n_ab : phiv z (a * b) ≠ 1 := by
    rw [pab]
    exact fun h1 => hff (eq_of_mul_eq_one_of_sq (h.F_sq f' hf') h1)
  have n_ac : phiv z (a * c) ≠ 1 := by
    rw [pac]
    exact fun h1 => hfg (eq_of_mul_eq_one_of_sq (h.F_sq g hg) h1)
  have n_bc : phiv z (b * c) ≠ 1 := by
    rw [pbc]
    exact fun h1 => hf'g (eq_of_mul_eq_one_of_sq (h.F_sq g hg) h1)
  have n_abc : phiv z (a * b * c) ≠ 1 := by
    rw [pabc]
    exact fun h1 => hfff (eq_of_mul_eq_one_of_sq (h.F_sq g hg) h1)
  have hu : (a * b) * (a * b) = 1 ∨ (a * b) * (a * b) = f * f' := by
    rcases sq_mem_pair h hsq X hab n_ab with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pab)
  have hv : (a * c) * (a * c) = 1 ∨ (a * c) * (a * c) = f * g := by
    rcases sq_mem_pair h hsq X hac n_ac with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pac)
  have hw : (b * c) * (b * c) = 1 ∨ (b * c) * (b * c) = f' * g := by
    rcases sq_mem_pair h hsq X hbc n_bc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pbc)
  have hF1 : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F := fun x hx y hy => Subgroup.mul_mem _ hx hy
  have huF : (a * b) * (a * b) ∈ F :=
    hu.elim (fun h1 => h1 ▸ F.one_mem) (fun h1 => h1 ▸ hF1 f hf f' hf')
  have hvF : (a * c) * (a * c) ∈ F :=
    hv.elim (fun h1 => h1 ▸ F.one_mem) (fun h1 => h1 ▸ hF1 f hf g hg)
  have hwF : (b * c) * (b * c) ∈ F :=
    hw.elim (fun h1 => h1 ▸ F.one_mem) (fun h1 => h1 ▸ hF1 f' hf' g hg)
  have hs : (a * b * c) * (a * b * c) = 1 ∨ (a * b * c) * (a * b * c) = f * f' * g := by
    rcases sq_mem_pair h hsq X habc n_abc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pabc)
  have hvb : (a * c) * (a * c) * b = b * ((a * c) * (a * c)) := (mem_Ksub.1 hb).2 _ hvF
  have hprod := sq_mul_three ha2 hb2 hc2 hvb
  rw [hprod] at hs
  obtain ⟨e1, e2⟩ := tri_alg_sub h.F_comm h.F_sq hf hf' hg huF hvF hwF hf1 hf'1 hg1 hff hfg hf'g
    hu hv hw hs
  have q1 := pairProp_iff_sq h ha hb ha2 hb2 haf hbf hf1 hf'1
  have q2 := pairProp_iff_sq h ha hc ha2 hc2 haf hcg hf1 hg1
  have q3 := pairProp_iff_sq h hb hc hb2 hc2 hbf hcg hf'1 hg1
  exact ⟨q1.trans (e1.trans q2.symm), q1.trans (e2.trans q3.symm)⟩

theorem pairProp_right (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f x y : G} (hf : f ∈ F) (hx : x ∈ F) (hy : y ∈ F) (hf1 : f ≠ 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hfx : f ≠ x) (hfy : f ≠ y) (hP : PairProp z F f x) : PairProp z F f y := by
  by_cases hxy : x = y
  · rwa [← hxy]
  by_cases hy' : f * x = y
  · obtain ⟨w, hwF, hw⟩ := exists_not_mem_of_length_lt F [1, f, x, f * x]
      (by rw [h.F_card]; simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw1, hwf, hwx, hwfx⟩ := hw
    have hfy2 : f * y = x := by rw [← hy', ← mul_assoc, h.F_sq f hf, one_mul]
    have h1 := (pairProp_iff_triple h hsq X htr hf hx hwF hf1 hx1 hw1 hfx
      (fun e => hwf e.symm) (fun e => hwx e.symm) (fun e => hwfx e.symm)).1
    have h2 := (pairProp_iff_triple h hsq X htr hf hy hwF hf1 hy1 hw1 hfy
      (fun e => hwf e.symm) (fun e => hwfx (e.symm.trans hy'.symm))
      (by rw [hfy2]; exact fun e => hwx e.symm)).1
    exact h2.mpr (h1.mp hP)
  · exact (pairProp_iff_triple h hsq X htr hf hx hy hf1 hx1 hy1 hfx hfy hxy hy').1.mp hP

theorem pairProp_const (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f f' g g' : G} (hf : f ∈ F) (hf' : f' ∈ F) (hg : g ∈ F) (hg' : g' ∈ F)
    (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hg'1 : g' ≠ 1) (hff : f ≠ f') (hgg : g ≠ g')
    (hP : PairProp z F f f') : PairProp z F g g' := by
  by_cases hfg : f = g
  · subst hfg
    exact pairProp_right h hsq X htr hf hf' hg' hf1 hf'1 hg'1 hff hgg hP
  · have h1 : PairProp z F f g :=
      pairProp_right h hsq X htr hf hf' hg hf1 hf'1 hg1 hff hfg hP
    exact pairProp_right h hsq X htr hg hf hg' hg1 hf1 hg'1 (Ne.symm hfg) hgg
      (pairProp_symm h1)

theorem goodK_or_badK_of_fixed (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) : GoodK z F ∨ BadK z F := by
  by_cases hgood : GoodK z F
  · exact Or.inl hgood
  · right
    have hex : ∃ k ∈ Ksub z F, ∃ k' ∈ Ksub z F, k * k = 1 ∧ k' * k' = 1 ∧ phiv z k ≠ 1 ∧
        phiv z k' ≠ 1 ∧ phiv z k ≠ phiv z k' ∧ (k * k') * (k * k') ≠ 1 := by
      by_contra hcon
      apply hgood
      intro k hk k' hk' h1 h2 h3 h4 h5
      by_contra h6
      exact hcon ⟨k, hk, k', hk', h1, h2, h3, h4, h5, h6⟩
    obtain ⟨k₁, hk₁, k₁', hk₁', hk₁2, hk₁'2, hf₁, hf₁', hff₁, hbad⟩ := hex
    intro k hk k' hk' hk2 hk'2 hf hf' hff hgood2
    have hP : PairProp z F (phiv z k) (phiv z k') :=
      pairProp_of_sq h hk hk' hk2 hk'2 hf hf' hgood2
    have := pairProp_const h hsq X htr (phiv_mem h hk) (phiv_mem h hk')
      (phiv_mem h hk₁) (phiv_mem h hk₁') hf hf' hf₁ hf₁' hff hff₁ hP
    exact hbad (sq_of_pairProp hk₁ hk₁' hk₁2 hk₁'2 this)

end OutOne

end CFSG.EvenSporadicStandard.M22Std
