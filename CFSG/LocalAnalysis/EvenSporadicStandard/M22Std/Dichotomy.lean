module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KDichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabElem

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

omit [Finite G] in
theorem sq_mul_three {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hv : (a * c) * (a * c) * b = b * ((a * c) * (a * c))) :
    (a * b * c) * (a * b * c) =
      ((a * b) * (a * b)) * ((a * c) * (a * c)) * ((b * c) * (b * c)) := by
  have h1 : c * a * c = a * ((a * c) * (a * c)) := by
    calc c * a * c = (a * a) * (c * a * c) := by rw [ha, one_mul]
      _ = a * ((a * c) * (a * c)) := by group
  have h2 : c * b * c = b * ((b * c) * (b * c)) := by
    calc c * b * c = (b * b) * (c * b * c) := by rw [hb, one_mul]
      _ = b * ((b * c) * (b * c)) := by group
  have h3 : (c * a * c) * (c * b * c) = c * a * b * c := by
    calc (c * a * c) * (c * b * c) = c * a * (c * c) * b * c := by group
      _ = c * a * b * c := by rw [hc]; group
  calc (a * b * c) * (a * b * c) = a * b * (c * a * b * c) := by group
    _ = a * b * ((c * a * c) * (c * b * c)) := by rw [h3]
    _ = a * b * ((a * ((a * c) * (a * c))) * (b * ((b * c) * (b * c)))) := by rw [h1, h2]
    _ = a * b * a * (((a * c) * (a * c)) * b) * ((b * c) * (b * c)) := by group
    _ = a * b * a * (b * ((a * c) * (a * c))) * ((b * c) * (b * c)) := by rw [hv]
    _ = ((a * b) * (a * b)) * ((a * c) * (a * c)) * ((b * c) * (b * c)) := by group

omit [Finite G] in
theorem pairProp_symm {f f' : G} (hP : PairProp z F f f') : PairProp z F f' f := by
  intro k hk k' hk' hk2 hk'2 hkf hk'f
  have h1 := hP k' hk' k hk hk'2 hk2 hk'f hkf
  have e : k * k' = (k' * k)⁻¹ := by
    rw [mul_inv_rev]
    rw [inv_eq_of_mul_eq_one_right hk2, inv_eq_of_mul_eq_one_right hk'2]
  have h2 : (k * k') * (k * k') = ((k' * k) * (k' * k))⁻¹ := by
    rw [e, ← mul_inv_rev]
  rw [h2, h1]
  simp

omit [Finite G] in
theorem pairProp_of_sq (h : OneClassData L z t) (D : NData L F) {a b : G}
    (ha : a ∈ Ksub z F) (hb : b ∈ Ksub z F) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : phiv z a ≠ 1) (hb1 : phiv z b ≠ 1) (hab : (a * b) * (a * b) = 1) :
    PairProp z F (phiv z a) (phiv z b) := by
  intro m hm m' hm' hm2 hm'2 hmf hm'f'
  obtain ⟨u, hu, hmu⟩ := (involutions_eq h D ha ha2 ha1).1 ⟨hm, hmf, hm2⟩
  obtain ⟨u', hu', hm'u'⟩ := (involutions_eq h D hb hb2 hb1).1 ⟨hm', hm'f', hm'2⟩
  rw [hmu, hm'u', sq_mul_mul_F D ha hb hu hu']
  exact hab

omit [Finite G] in
theorem sq_of_pairProp {a b : G} (ha : a ∈ Ksub z F) (hb : b ∈ Ksub z F) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hP : PairProp z F (phiv z a) (phiv z b)) : (a * b) * (a * b) = 1 :=
  hP a ha b hb ha2 hb2 rfl rfl

theorem tri_alg {V : Type*} [CommGroup V] (hsq : ∀ x : V, x * x = 1) {f f' g u v w : V}
    (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hff : f ≠ f') (hfg : f ≠ g) (hf'g : f' ≠ g)
    (hu : u = 1 ∨ u = f * f') (hv : v = 1 ∨ v = f * g) (hw : w = 1 ∨ w = f' * g)
    (hs : u * v * w = 1 ∨ u * v * w = f * f' * g) : (u = 1 ↔ v = 1) ∧ (u = 1 ↔ w = 1) := by
  have h1 : ∀ x y : V, x * y = 1 → x = y := fun x y h => by
    rw [mul_eq_one_iff_eq_inv.1 h, inv_eq_of_mul_eq_one_right (hsq y)]
  have h2 : ∀ x y : V, x * (x * y) = y := fun x y => by rw [← mul_assoc, hsq x, one_mul]
  have b1a : f * f' ≠ 1 := fun h => hff (h1 _ _ h)
  have b1b : f * f' ≠ f * f' * g := fun h => hg1 (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have b2a : f * g ≠ 1 := fun h => hfg (h1 _ _ h)
  have b2b : f * g ≠ f * f' * g := fun h => hf'1 (by
    have : f * g = f * (f' * g) := by rw [h, mul_assoc]
    have h3 : g = f' * g := mul_left_cancel this
    exact (mul_right_cancel (show 1 * g = f' * g by rw [one_mul]; exact h3)).symm)
  have b3a : f' * g ≠ 1 := fun h => hf'g (h1 _ _ h)
  have b3b : f' * g ≠ f * f' * g := fun h => hf1 (by
    have h3 : f' = f * f' := mul_right_cancel h
    have h4 : f * f' = 1 * f' := by rw [← h3, one_mul]
    exact mul_right_cancel h4)
  have P1 : f * f' * (f * g) = f' * g := by
    calc f * f' * (f * g) = f' * (f * (f * g)) := by rw [mul_comm f f', mul_assoc]
      _ = f' * g := by rw [h2]
  have P2 : f * f' * (f' * g) = f * g := by
    calc f * f' * (f' * g) = f * (f' * (f' * g)) := mul_assoc _ _ _
      _ = f * g := by rw [h2]
  have P3 : f * g * (f' * g) = f * f' := by
    calc f * g * (f' * g) = f * (g * (f' * g)) := mul_assoc _ _ _
      _ = f * (g * (g * f')) := by rw [mul_comm f' g]
      _ = f * f' := by rw [h2]
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · rw [one_mul, one_mul] at hs
    exact absurd hs (by push Not; exact ⟨b3a, b3b⟩)
  · rw [one_mul, mul_one] at hs
    exact absurd hs (by push Not; exact ⟨b2a, b2b⟩)
  · rw [one_mul, P3] at hs
    exact absurd hs (by push Not; exact ⟨b1a, b1b⟩)
  · rw [mul_one, mul_one] at hs
    exact absurd hs (by push Not; exact ⟨b1a, b1b⟩)
  · rw [mul_one, P2] at hs
    exact absurd hs (by push Not; exact ⟨b2a, b2b⟩)
  · rw [P1, mul_one] at hs
    exact absurd hs (by push Not; exact ⟨b3a, b3b⟩)
  · exact ⟨⟨fun h => absurd h b1a, fun h => absurd h b2a⟩,
      ⟨fun h => absurd h b1a, fun h => absurd h b3a⟩⟩

omit [Finite G] in
theorem tri_alg_sub (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hsq : ∀ x ∈ F, x * x = 1)
    {f f' g u v w : G} (hf : f ∈ F) (hf' : f' ∈ F) (hg : g ∈ F) (hu' : u ∈ F) (hv' : v ∈ F)
    (hw' : w ∈ F) (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hff : f ≠ f') (hfg : f ≠ g)
    (hf'g : f' ≠ g) (hu : u = 1 ∨ u = f * f') (hv : v = 1 ∨ v = f * g)
    (hw : w = 1 ∨ w = f' * g) (hs : u * v * w = 1 ∨ u * v * w = f * f' * g) :
    (u = 1 ↔ v = 1) ∧ (u = 1 ↔ w = 1) := by
  let _ : CommGroup F :=
    { (inferInstance : Group F) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  have key := tri_alg (V := F) (fun x => Subtype.ext (hsq x x.2)) (f := ⟨f, hf⟩) (f' := ⟨f', hf'⟩)
    (g := ⟨g, hg⟩) (u := ⟨u, hu'⟩) (v := ⟨v, hv'⟩) (w := ⟨w, hw'⟩)
    (fun h => hf1 (congrArg Subtype.val h)) (fun h => hf'1 (congrArg Subtype.val h))
    (fun h => hg1 (congrArg Subtype.val h)) (fun h => hff (congrArg Subtype.val h))
    (fun h => hfg (congrArg Subtype.val h)) (fun h => hf'g (congrArg Subtype.val h))
    (hu.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h))
    (hv.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h))
    (hw.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h))
    (hs.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h))
  have e : ∀ x : G, ∀ hx : x ∈ F, ((⟨x, hx⟩ : F) = 1 ↔ x = 1) := fun x hx =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [e, e] at key
  rw [e] at key
  exact key

omit [Finite G] in
theorem pairProp_iff_sq (h : OneClassData L z t) (D : NData L F) {a b f f' : G}
    (ha : a ∈ Ksub z F) (hb : b ∈ Ksub z F) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (haf : phiv z a = f) (hbf : phiv z b = f') (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) :
    PairProp z F f f' ↔ (a * b) * (a * b) = 1 := by
  subst haf hbf
  exact ⟨fun hP => sq_of_pairProp ha hb ha2 hb2 hP,
    fun hab => pairProp_of_sq h D ha hb ha2 hb2 hf1 hf'1 hab⟩

omit [Finite G] in
theorem eq_of_mul_eq_one_of_sq {x y : G} (hy : y * y = 1) (hxy : x * y = 1) : x = y := by
  calc x = x * (y * y) := by rw [hy, mul_one]
    _ = (x * y) * y := by rw [mul_assoc]
    _ = y := by rw [hxy, one_mul]

theorem pairProp_iff_triple (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f f' g : G} (hf : f ∈ F) (hf' : f' ∈ F) (hg : g ∈ F)
    (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hff : f ≠ f') (hfg : f ≠ g) (hf'g : f' ≠ g)
    (hfff : f * f' ≠ g) :
    (PairProp z F f f' ↔ PairProp z F f g) ∧ (PairProp z F f f' ↔ PairProp z F f' g) := by
  obtain ⟨a, ha, haf, ha2⟩ := exists_involution h hZ D X htr hf hf1
  obtain ⟨b, hb, hbf, hb2⟩ := exists_involution h hZ D X htr hf' hf'1
  obtain ⟨c, hc, hcg, hc2⟩ := exists_involution h hZ D X htr hg hg1
  have hab : a * b ∈ Ksub z F := Subgroup.mul_mem _ ha hb
  have hac : a * c ∈ Ksub z F := Subgroup.mul_mem _ ha hc
  have hbc : b * c ∈ Ksub z F := Subgroup.mul_mem _ hb hc
  have habc : a * b * c ∈ Ksub z F := Subgroup.mul_mem _ hab hc
  have pab : phiv z (a * b) = f * f' := by rw [phiv_mul h D ha hb, haf, hbf]
  have pac : phiv z (a * c) = f * g := by rw [phiv_mul h D ha hc, haf, hcg]
  have pbc : phiv z (b * c) = f' * g := by rw [phiv_mul h D hb hc, hbf, hcg]
  have pabc : phiv z (a * b * c) = f * f' * g := by rw [phiv_mul h D hab hc, pab, hcg]
  have n_ab : phiv z (a * b) ≠ 1 := by
    rw [pab]
    exact fun h1 => hff (eq_of_mul_eq_one_of_sq (D.F_sq f' hf') h1)
  have n_ac : phiv z (a * c) ≠ 1 := by
    rw [pac]
    exact fun h1 => hfg (eq_of_mul_eq_one_of_sq (D.F_sq g hg) h1)
  have n_bc : phiv z (b * c) ≠ 1 := by
    rw [pbc]
    exact fun h1 => hf'g (eq_of_mul_eq_one_of_sq (D.F_sq g hg) h1)
  have n_abc : phiv z (a * b * c) ≠ 1 := by
    rw [pabc]
    exact fun h1 => hfff (eq_of_mul_eq_one_of_sq (D.F_sq g hg) h1)
  have hu : (a * b) * (a * b) = 1 ∨ (a * b) * (a * b) = f * f' := by
    rcases sq_mem_pair h hZ D X hab n_ab with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pab)
  have hv : (a * c) * (a * c) = 1 ∨ (a * c) * (a * c) = f * g := by
    rcases sq_mem_pair h hZ D X hac n_ac with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pac)
  have hw : (b * c) * (b * c) = 1 ∨ (b * c) * (b * c) = f' * g := by
    rcases sq_mem_pair h hZ D X hbc n_bc with h1 | h1
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
    rcases sq_mem_pair h hZ D X habc n_abc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans pabc)
  have hvb : (a * c) * (a * c) * b = b * ((a * c) * (a * c)) := (mem_Ksub.1 hb).2 _ hvF
  have hprod := sq_mul_three ha2 hb2 hc2 hvb
  rw [hprod] at hs
  obtain ⟨e1, e2⟩ := tri_alg_sub D.F_comm D.F_sq hf hf' hg huF hvF hwF hf1 hf'1 hg1 hff hfg hf'g
    hu hv hw hs
  have q1 := pairProp_iff_sq h D ha hb ha2 hb2 haf hbf hf1 hf'1
  have q2 := pairProp_iff_sq h D ha hc ha2 hc2 haf hcg hf1 hg1
  have q3 := pairProp_iff_sq h D hb hc hb2 hc2 hbf hcg hf'1 hg1
  exact ⟨q1.trans (e1.trans q2.symm), q1.trans (e2.trans q3.symm)⟩

theorem pairProp_right (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f x y : G} (hf : f ∈ F) (hx : x ∈ F) (hy : y ∈ F) (hf1 : f ≠ 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hfx : f ≠ x) (hfy : f ≠ y) (hP : PairProp z F f x) : PairProp z F f y := by
  by_cases hxy : x = y
  · rwa [← hxy]
  by_cases hy' : f * x = y
  · obtain ⟨w, hwF, hw⟩ := exists_not_mem_of_length_lt F [1, f, x, f * x]
      (by rw [D.F_card]; simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw1, hwf, hwx, hwfx⟩ := hw
    have hfy2 : f * y = x := by rw [← hy', ← mul_assoc, D.F_sq f hf, one_mul]
    have h1 := (pairProp_iff_triple h hZ D X htr hf hx hwF hf1 hx1 hw1 hfx
      (fun e => hwf e.symm) (fun e => hwx e.symm) (fun e => hwfx e.symm)).1
    have h2 := (pairProp_iff_triple h hZ D X htr hf hy hwF hf1 hy1 hw1 hfy
      (fun e => hwf e.symm) (fun e => hwfx (e.symm.trans hy'.symm))
      (by rw [hfy2]; exact fun e => hwx e.symm)).1
    exact h2.mpr (h1.mp hP)
  · exact (pairProp_iff_triple h hZ D X htr hf hx hy hf1 hx1 hy1 hfx hfy hxy hy').1.mp hP

theorem pairProp_const (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htr : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {f f' g g' : G} (hf : f ∈ F) (hf' : f' ∈ F) (hg : g ∈ F) (hg' : g' ∈ F)
    (hf1 : f ≠ 1) (hf'1 : f' ≠ 1) (hg1 : g ≠ 1) (hg'1 : g' ≠ 1) (hff : f ≠ f') (hgg : g ≠ g')
    (hP : PairProp z F f f') : PairProp z F g g' := by
  by_cases hfg : f = g
  · subst hfg
    exact pairProp_right h hZ D X htr hf hf' hg' hf1 hf'1 hg'1 hff hgg hP
  · have h1 : PairProp z F f g :=
      pairProp_right h hZ D X htr hf hf' hg hf1 hf'1 hg1 hff hfg hP
    exact pairProp_right h hZ D X htr hg hf hg' hg1 hf1 hg'1 (Ne.symm hfg) hgg
      (pairProp_symm h1)

theorem goodK_or_badK_of_fixed (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
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
      pairProp_of_sq h D hk hk' hk2 hk'2 hf hf' hgood2
    have := pairProp_const h hZ D X htr (phiv_mem h D hk) (phiv_mem h D hk')
      (phiv_mem h D hk₁) (phiv_mem h D hk₁') hf hf' hf₁ hf₁' hff hff₁ hP
    exact hbad (sq_of_pairProp hk₁ hk₁' hk₁2 hk₁'2 this)

end CFSG.EvenSporadicStandard.M22Std
