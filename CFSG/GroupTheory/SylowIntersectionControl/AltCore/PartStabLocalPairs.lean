module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {n : ℕ} {s : Setoid (Fin n)}

private theorem exists_partner {x : Fin n} (h : Nat.card {y // s.r x y} = 2) :
    ∃ x', x' ≠ x ∧ s.r x x' ∧ ∀ y, s.r x y → y = x ∨ y = x' := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (⟨x, s.iseqv.refl x⟩ : {y // s.r x y})).1 h
  refine ⟨y.1, fun h => hy (Subtype.ext h), y.2, fun w hw => ?_⟩
  by_cases hwx : w = x
  · exact Or.inl hwx
  · exact Or.inr (congrArg Subtype.val (huniq ⟨w, hw⟩ fun h => hwx (congrArg Subtype.val h)))

private theorem rel_swap {a a' : Fin n} (h : s.r a a') (w : Fin n) : s.r (swap a a' w) w := by
  by_cases h1 : w = a
  · rw [h1, swap_apply_left]; exact s.iseqv.symm h
  · by_cases h2 : w = a'
    · rw [h2, swap_apply_right]; exact h
    · rw [swap_apply_of_ne_of_ne h1 h2]

private theorem rel_congr {a a' b b' : Fin n} (ha : s.r a a') (hb : s.r b b') :
    s.r a b ↔ s.r a' b' :=
  ⟨fun h => s.iseqv.trans (s.iseqv.trans (s.iseqv.symm ha) h) hb,
    fun h => s.iseqv.trans (s.iseqv.trans ha h) (s.iseqv.symm hb)⟩

private structure Good (s : Setoid (Fin n)) (F : Fin n → Prop) : Prop where
  union : ∀ x y, s.r x y → F x → F y
  pair : ∀ x, ¬ F x → Nat.card {y // s.r x y} = 2
  inv : ∀ h ∈ partStab s, ∀ x, F (h x) ↔ F x
  card : Nat.card {y // F y} + 5 ≤ n

private def Qs (s : Setoid (Fin n)) (F : Fin n → Prop) : Subgroup (Perm (Fin n)) where
  carrier := {g | g ∈ alternatingGroup (Fin n) ∧ ∀ x, s.r (g x) x ∧ (F x → g x = x)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x => ⟨?_, fun hx => ?_⟩⟩
    · exact s.iseqv.trans (ha' (b x)).1 (hb' x).1
    · rw [Perm.mul_apply, (hb' x).2 hx, (ha' x).2 hx]
  one_mem' := ⟨one_mem _, fun x => ⟨s.iseqv.refl x, fun _ => rfl⟩⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x => ⟨?_, fun hx => ?_⟩⟩
    · have := (ha' (a⁻¹ x)).1
      rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
      exact s.iseqv.symm this
    · rw [Perm.inv_eq_iff_eq]
      exact ((ha' x).2 hx).symm

private theorem apply_apply_of_rel {F : Fin n → Prop} (G : Good s F) {g : Perm (Fin n)}
    (hg : ∀ z, ¬ F z → s.r (g z) z) {z : Fin n} (hz : ¬ F z) : g (g z) = z := by
  obtain ⟨z', hne, hzz', hcl⟩ := exists_partner (G.pair z hz)
  have hz' : ¬ F z' := fun h => hz (G.union _ _ (s.iseqv.symm hzz') h)
  rcases hcl _ (s.iseqv.symm (hg z hz)) with h | h
  · rw [h, h]
  · rcases hcl (g z') (s.iseqv.trans hzz' (s.iseqv.symm (hg z' hz'))) with h' | h'
    · rw [h, h']
    · exact absurd (g.injective (h.trans h'.symm)) hne.symm

private theorem Qs_sq {F : Fin n → Prop} (G : Good s F) {g : Perm (Fin n)} (hg : g ∈ Qs s F) :
    g * g = 1 := by
  refine Perm.ext fun w => ?_
  by_cases hw : F w
  · simp [(hg.2 w).2 hw]
  · exact apply_apply_of_rel G (fun z _ => (hg.2 z).1) hw

private theorem isPGroup_Qs {F : Fin n → Prop} (G : Good s F) : IsPGroup 2 (Qs s F) := by
  intro g
  refine ⟨1, ?_⟩
  ext1
  simpa [pow_two] using Qs_sq G g.2

private theorem Qs_le {F : Fin n → Prop} : Qs s F ≤ partStab s ⊓ alternatingGroup (Fin n) := by
  rintro g ⟨hA, hg⟩
  exact ⟨fun x y => rel_congr (hg x).1 (hg y).1, hA⟩

private theorem conj_mem_Qs {F : Fin n → Prop} (G : Good s F) {h q : Perm (Fin n)}
    (hh : h ∈ partStab s ⊓ alternatingGroup (Fin n)) (hq : q ∈ Qs s F) :
    h * q * h⁻¹ ∈ Qs s F := by
  obtain ⟨hY, hA⟩ := hh
  obtain ⟨hqA, hq⟩ := hq
  refine ⟨mul_mem (mul_mem hA hqA) (inv_mem hA), fun w => ⟨?_, fun hw => ?_⟩⟩
  · simpa using (hY (q (h⁻¹ w)) (h⁻¹ w)).2 (hq (h⁻¹ w)).1
  · have hF : F (h⁻¹ w) := (G.inv h⁻¹ (inv_mem hY) w).2 hw
    show h (q (h⁻¹ w)) = w
    rw [(hq _).2 hF]
    exact h.apply_symm_apply w

private theorem Qs_le_pCoreOf {F : Fin n → Prop} (G : Good s F) :
    Qs s F ≤ pCoreOf 2 (partStab s ⊓ alternatingGroup (Fin n)) :=
  CFSG.ClassicalGroups.PCoreSection.le_pCoreOf Qs_le (fun _ hx _ hy => conj_mem_Qs G hx hy)
    (isPGroup_Qs G)

private theorem swap_mul_swap_mem {F : Fin n → Prop} (G : Good s F) {z z' l l' : Fin n}
    (hz : s.r z z') (hl : s.r l l') (hFz : ¬ F z) (hFl : ¬ F l) (hzz : z ≠ z') (hll : l ≠ l') :
    swap z z' * swap l l' ∈ Qs s F := by
  refine ⟨?_, fun w => ⟨s.iseqv.trans (rel_swap hz _) (rel_swap hl w), fun hw => ?_⟩⟩
  · rw [mem_alternatingGroup, map_mul, sign_swap hzz, sign_swap hll]
    decide
  · have hz' : ¬ F z' := fun h => hFz (G.union _ _ (s.iseqv.symm hz) h)
    have hl' : ¬ F l' := fun h => hFl (G.union _ _ (s.iseqv.symm hl) h)
    have h1 : w ≠ l := fun h => hFl (h ▸ hw)
    have h2 : w ≠ l' := fun h => hl' (h ▸ hw)
    have h3 : w ≠ z := fun h => hFz (h ▸ hw)
    have h4 : w ≠ z' := fun h => hz' (h ▸ hw)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h3 h4]

private theorem mem_of_comm_swap {x : Perm (Fin n)} {z z' l l' : Fin n} (hzz : z ≠ z')
    (hzl : z ≠ l) (hzl' : z ≠ l')
    (hx : (swap z z' * swap l l') * x = x * (swap z z' * swap l l')) :
    x z = z ∨ x z = z' ∨ x z = l ∨ x z = l' := by
  have h2 := Perm.congr_fun hx z
  simp only [Perm.mul_apply] at h2
  rw [swap_apply_of_ne_of_ne hzl hzl', swap_apply_left] at h2
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨c1, c2, c3, c4⟩ := hcon
  rw [swap_apply_of_ne_of_ne c3 c4, swap_apply_of_ne_of_ne c1 c2] at h2
  exact hzz (x.injective h2)

private theorem exists_fresh {F : Fin n → Prop} (G : Good s F) (T : Finset (Fin n))
    (hT : ∀ t ∈ T, ¬ F t) (h : Nat.card {y // F y} + 2 * T.card < n) :
    ∃ w, ¬ F w ∧ ∀ t ∈ T, ¬ s.r t w := by
  classical
  by_contra hcon
  have hcon' : ∀ w, ¬ F w → ∃ t ∈ T, s.r t w := by
    intro w hw
    by_contra hex
    exact hcon ⟨w, hw, fun t ht htw => hex ⟨t, ht, htw⟩⟩
  have hcov : (Finset.univ : Finset (Fin n)) ⊆
      Finset.univ.filter F ∪ T.biUnion (fun t => Finset.univ.filter (s.r t)) := by
    intro w _
    by_cases hw : F w
    · exact Finset.mem_union_left _ (by simpa using hw)
    · obtain ⟨t, ht, htw⟩ := hcon' w hw
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨t, ht, by simpa using htw⟩)
  have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have h3 := (Finset.card_biUnion_le (s := T) (t := fun t => Finset.univ.filter (s.r t)))
  have h4 : ∑ t ∈ T, (Finset.univ.filter (s.r t)).card = T.card * 2 :=
    Finset.sum_const_nat fun t ht => by
      rw [← G.pair t (hT t ht), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h5 : (Finset.univ.filter F).card = Nat.card {y // F y} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

private theorem exists_two_fresh {F : Fin n → Prop} (G : Good s F) {z : Fin n} (hz : ¬ F z) :
    ∃ l m, ¬ F l ∧ ¬ F m ∧ ¬ s.r z l ∧ ¬ s.r z m ∧ ¬ s.r l m := by
  have hc := G.card
  obtain ⟨l, hl, hzl⟩ := exists_fresh G {z} (by simpa using hz)
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨m, hm, hm'⟩ := exists_fresh G {z, l} (by simp [hz, hl])
    (by have := Finset.card_le_two (a := z) (b := l); omega)
  exact ⟨l, m, hl, hm, hzl z (by simp), hm' z (by simp), hm' l (by simp)⟩

private theorem rel_of_comm_aux {F : Fin n → Prop} (G : Good s F) {x : Perm (Fin n)}
    (hx : ∀ q ∈ Qs s F, q * x = x * q) {z l : Fin n} (hz : ¬ F z) (hl : ¬ F l)
    (hzl : ¬ s.r z l) : s.r (x z) z ∨ s.r (x z) l := by
  obtain ⟨z', hzz', hz', -⟩ := exists_partner (G.pair z hz)
  obtain ⟨l', hll', hl', -⟩ := exists_partner (G.pair l hl)
  have h1 : z ≠ l := by rintro rfl; exact hzl (s.iseqv.refl _)
  have h2 : z ≠ l' := by
    rintro rfl; exact hzl (s.iseqv.symm hl')
  rcases mem_of_comm_swap hzz'.symm h1 h2
    (hx _ (swap_mul_swap_mem G hz' hl' hz hl hzz'.symm hll'.symm)) with h | h | h | h
  · rw [h]; exact Or.inl (s.iseqv.refl _)
  · rw [h]; exact Or.inl (s.iseqv.symm hz')
  · rw [h]; exact Or.inr (s.iseqv.refl _)
  · rw [h]; exact Or.inr (s.iseqv.symm hl')

private theorem rel_of_comm {F : Fin n → Prop} (G : Good s F) {x : Perm (Fin n)}
    (hx : ∀ q ∈ Qs s F, q * x = x * q) {z : Fin n} (hz : ¬ F z) : s.r (x z) z := by
  obtain ⟨l, m, hl, hm, hzl, hzm, hlm⟩ := exists_two_fresh G hz
  rcases rel_of_comm_aux G hx hz hl hzl with h | h
  · exact h
  · rcases rel_of_comm_aux G hx hz hm hzm with h' | h'
    · exact h'
    · exact absurd (s.iseqv.trans (s.iseqv.symm h) h') hlm

private abbrev Cc (s : Setoid (Fin n)) : Subgroup (Perm (Fin n)) :=
  (partStab s ⊓ alternatingGroup (Fin n)) ⊓
    centralizer (pCoreOf 2 (partStab s ⊓ alternatingGroup (Fin n)) : Set (Perm (Fin n)))

private theorem mem_Cc {F : Fin n → Prop} (G : Good s F) {x : Perm (Fin n)} (hx : x ∈ Cc s) :
    x ∈ partStab s ∧ x ∈ alternatingGroup (Fin n) ∧ ∀ z, ¬ F z → s.r (x z) z :=
  ⟨hx.1.1, hx.1.2, fun _ hz => rel_of_comm G (fun _ hq =>
    Subgroup.mem_centralizer_iff.1 hx.2 _ (Qs_le_pCoreOf G hq)) hz⟩

private theorem good_class {b : Fin n} {k : ℕ} (hk : k ≠ 2) (hb : Nat.card {y // s.r b y} = k)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 2) (hn : k + 5 ≤ n) :
    Good s (s.r b) where
  union _ _ hxy hbx := s.iseqv.trans hbx hxy
  pair := hs
  inv h hh x := by
    have hbh : s.r b (h b) := by
      by_contra hc
      exact hk (hb.symm.trans
        ((Nat.card_congr (Equiv.subtypeEquiv h fun y => (hh b y).symm)).trans (hs _ hc)))
    rw [← hh b x]
    exact ⟨fun hx => s.iseqv.trans (s.iseqv.symm hbh) hx, fun hx => s.iseqv.trans hbh hx⟩
  card := by rw [hb]; exact hn

private theorem eq_one_of_fix {g : Perm (Fin n)} {u v : Fin n} (hs : sign g = 1)
    (hfix : ∀ w, w ≠ u → w ≠ v → g w = w) : g = 1 := by
  have hsub : g.support ⊆ {u, v} := fun w hw => by
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    exact Perm.mem_support.1 hw (hfix w hcon.1 hcon.2)
  have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
  rcases (by omega : g.support.card = 0 ∨ g.support.card = 1 ∨ g.support.card = 2) with h | h | h
  · exact Perm.card_support_eq_zero.1 h
  · exact absurd h (Perm.card_support_ne_one g)
  · have := (Perm.card_support_eq_two.1 h).sign_eq
    rw [hs] at this
    exact absurd this (by decide)

private theorem eq_one_of_fix3 {u v t : Fin n} {g : Perm (Fin n)} (hs : sign g = 1)
    (hu : g u = u) (hfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → g w = w) : g = 1 :=
  eq_one_of_fix (u := v) (v := t) hs fun w hv ht => by
    by_cases hw : w = u
    · rw [hw]; exact hu
    · exact hfix w hw hv ht

private theorem swap_mul_swap_apply {u v t w : Fin n} (h1 : w ≠ u) (h2 : w ≠ v) (h3 : w ≠ t) :
    (swap u v * swap u t) w = w := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]

private theorem mem_zpowers_of_fix {u v t : Fin n} (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t)
    {g : Perm (Fin n)} (hs : sign g = 1) (hfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → g w = w) :
    g ∈ zpowers (swap u v * swap u t) := by
  set z := swap u v * swap u t with hz
  have hzs : sign z = 1 := by rw [hz, map_mul, sign_swap huv, sign_swap hut]; decide
  have hzfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → z w = w := fun w h1 h2 h3 =>
    swap_mul_swap_apply h1 h2 h3
  have hzu : z u = t := by
    rw [hz, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hut.symm hvt.symm]
  have hzv : z v = u := by
    rw [hz, Perm.mul_apply, swap_apply_of_ne_of_ne huv.symm hvt, swap_apply_right]
  have hgu : g u = u ∨ g u = v ∨ g u = t := by
    by_contra hcon
    simp only [not_or] at hcon
    exact hcon.1 (g.injective (hfix _ hcon.1 hcon.2.1 hcon.2.2 : g (g u) = g u))
  rcases hgu with h | h | h
  · rw [eq_one_of_fix3 hs h hfix]; exact one_mem _
  · have h1 : z * g = 1 := eq_one_of_fix3 (u := u) (v := v) (t := t)
      (by rw [map_mul, hs, hzs, mul_one]) (by rw [Perm.mul_apply, h, hzv])
      fun w a b c => by rw [Perm.mul_apply, hfix w a b c, hzfix w a b c]
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (mem_zpowers z)
  · have h1 : z⁻¹ * g = 1 := eq_one_of_fix3 (u := u) (v := v) (t := t)
      (by rw [map_mul, hs, sign_inv, hzs, mul_one])
      (by rw [Perm.mul_apply, h, Perm.inv_eq_iff_eq, hzu])
      fun w a b c => by
        rw [Perm.mul_apply, hfix w a b c, Perm.inv_eq_iff_eq, hzfix w a b c]
    rw [← inv_mul_eq_one.1 h1]
    exact mem_zpowers z

private theorem le_normalizer_inf {G : Type*} [Group G] {C A : Subgroup G}
    (h : ∀ c ∈ C, ∀ y ∈ A, c * y * c⁻¹ ∈ A) : C ≤ normalizer ((C ⊓ A : Subgroup G) : Set G) := by
  have key : ∀ c ∈ C, ∀ y ∈ C ⊓ A, c * y * c⁻¹ ∈ C ⊓ A := fun c hc y hy =>
    ⟨C.mul_mem (C.mul_mem hc hy.1) (C.inv_mem hc), h c hc y hy.2⟩
  intro c hc
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => key c hc y hy, fun hy => ?_⟩
  simpa [mul_assoc] using key c⁻¹ (inv_mem hc) _ hy

theorem charTwo_partStab_inf_pairs (hn : 6 ≤ n) (hs : ∀ x, Nat.card {y // s.r x y} = 2) :
    CharTwo (partStab s ⊓ alternatingGroup (Fin n)) := by
  have G : Good s (fun _ => False) :=
    ⟨fun _ _ _ h => h, fun x _ => hs x, fun _ _ _ => Iff.rfl, by simp; omega⟩
  intro x hx
  obtain ⟨hxY, hxA, hxr⟩ := mem_Cc G hx
  exact Qs_le_pCoreOf G ⟨hxA, fun w => ⟨hxr w not_false, fun h => h.elim⟩⟩

theorem twoResidual_le_partStab_inf_pairsPoint (hn : 7 ≤ n) {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 1) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 2) :
    ∃ z : Perm (Fin n), z.IsThreeCycle ∧
      twoResidual ((partStab s ⊓ alternatingGroup (Fin n)) ⊓
        centralizer (pCoreOf 2 (partStab s ⊓ alternatingGroup (Fin n)) : Set (Perm (Fin n)))) ≤
        zpowers z := by
  have G := good_class (by omega) hb hs (by omega : 1 + 5 ≤ n)
  have hsing : ∀ y, s.r b y → y = b := by
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 hb
    exact fun y hy => congrArg Subtype.val (hsub.allEq ⟨y, hy⟩ ⟨b, s.iseqv.refl b⟩)
  have hsq : ∀ x ∈ Cc s, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨hxY, -, hxr⟩ := mem_Cc G hx
    refine (pow_two x).trans (Perm.ext fun w => ?_)
    by_cases hw : s.r b w
    · obtain rfl := hsing w hw
      have := hsing _ ((G.inv x hxY w).2 hw)
      simp [this]
    · exact apply_apply_of_rel G hxr hw
  refine ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨0, by omega⟩ ⟨2, by omega⟩,
    isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]), ?_⟩
  refine (twoResidual_le_of_isTwoQuotient (N := ⊥) bot_le Subgroup.le_normalizer_of_normal
    fun x hx => ⟨1, by simpa using hsq x hx⟩).trans bot_le

end CFSG.GroupTheory.AltCore
