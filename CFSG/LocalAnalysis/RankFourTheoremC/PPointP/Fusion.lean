module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Lines

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup CFSG.Open

@[expose] def ConjLine {G : Type} [Group G] (x y : G) : Prop :=
  ∃ g : G, zpowers y = (zpowers x).map (MulAut.conj g).toMonoidHom

theorem conjLine_self {G : Type} [Group G] (x : G) : ConjLine x x :=
  ⟨1, by rw [map_conj_zpowers']; simp⟩

theorem ConjLine.conj {G : Type} [Group G] {x y : G} (hy : ConjLine x y) (m : G) :
    ConjLine x (m * y * m⁻¹) := by
  obtain ⟨g, hg⟩ := hy
  refine ⟨m * g, ?_⟩
  have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (m * g)).toMonoidHom := MonoidHom.ext fun z => by simp [mul_assoc]
  rw [← map_conj_zpowers', hg, Subgroup.map_map, hcomp]

theorem natCast_inj_of_lt {F : Type*} [Field F] {p : ℕ} [CharP F p] {a b : ℕ} (ha : a < p)
    (hb : b < p) (hab : (a : F) = b) : a = b :=
  Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast F p).mp hab) ha hb

theorem natCast_ne_zero_of_lt {F : Type*} [Field F] {p : ℕ} [CharP F p] {a : ℕ} (ha : 0 < a)
    (hp : a < p) : (a : F) ≠ 0 := fun h0 =>
  absurd (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff F p a).mp h0)) (by omega)

theorem eq_of_affine_proportional {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    {c t : F} (ht : t ≠ 0) (hc : ∀ m : ℕ, c ≠ (m : F)) {m m' j : ℕ} (hm : m < p) (hm' : m' < p)
    (hj0 : 0 < j) (hjp : j < p)
    (h : t * ((m : F) + c) = (j : F) * (t * ((m' : F) + c))) : m = m' := by
  have h1 : (m : F) + c = (j : F) * ((m' : F) + c) := by
    apply mul_left_cancel₀ ht
    rw [h]; ring
  by_cases hj1 : j = 1
  · subst hj1
    rw [Nat.cast_one, one_mul] at h1
    exact natCast_inj_of_lt hm hm' (add_right_cancel h1)
  · exfalso
    have hne : (1 : F) - j ≠ 0 := by
      intro h0
      have : ((j : ℕ) : F) = ((1 : ℕ) : F) := by rw [Nat.cast_one]; linear_combination -h0
      have := natCast_inj_of_lt hjp hp.out.one_lt this
      exact hj1 this
    have hcm : c = ((j : F) * m' - m) / (1 - j) := by
      rw [eq_div_iff hne]; linear_combination h1
    apply hc (((j : ZMod p) * m' - m) / (1 - j)).val
    rw [hcm]
    have hι := ZMod.castHom (dvd_refl p) F
    have : ((((j : ZMod p) * m' - m) / (1 - j) : ZMod p).val : F) =
        ZMod.castHom (dvd_refl p) F (((j : ZMod p) * m' - m) / (1 - j)) := by
      rw [← map_natCast (ZMod.castHom (dvd_refl p) F), ZMod.natCast_zmod_val]
    rw [this, map_div₀]
    simp

theorem natCast_add_ne_zero {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p] {c : F}
    (hc : ∀ m : ℕ, c ≠ (m : F)) (m : ℕ) : (m : F) + c ≠ 0 := by
  intro hm0
  apply hc (p * m - m)
  rw [Nat.cast_sub (Nat.le_mul_of_pos_left m hp.out.pos), Nat.cast_mul, CharP.cast_eq_zero F p,
    zero_mul, zero_sub]
  linear_combination hm0

namespace FusionData

variable {G : Type} [Group G] [Finite G] {p n : ℕ} {F : Type} [Field F] {f : F → G} {x : G}
  {W : Subgroup G} (h : FusionData G p n F f x W)

include h

omit [Finite G] in
@[expose] def V : Subgroup G where
  carrier := Set.range f
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, h.f_add a b⟩
  one_mem' := ⟨0, h.f_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, h.f_neg a⟩

omit [Finite G] in
theorem card_V : Nat.card h.V = p ^ n := by
  rw [← h.card_F]
  exact (Nat.card_range_of_injective h.f_inj)

theorem zpowers_eq_of_mem [hp : Fact p.Prime] {y y' : G} (hy : ConjLine x y)
    (hmem : y' ∈ zpowers y) (hne : y' ≠ 1) : zpowers y' = zpowers y := by
  obtain ⟨g, hg⟩ := hy
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom :=
    fun a b hab => (MulAut.conj g).injective hab
  have hcy : Nat.card (zpowers y) = p := by
    rw [hg, Subgroup.card_map_of_injective hinj, h.card_zpowers_x]
  have hle : zpowers y' ≤ zpowers y := zpowers_le.mpr hmem
  have hd : orderOf y' ∣ p := by
    rw [← hcy, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hop : orderOf y' = p := by
    rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcy, Nat.card_zpowers, hop])

theorem conjLine_of_mem [hp : Fact p.Prime] {y y' : G} (hy : ConjLine x y)
    (hmem : y' ∈ zpowers y) (hne : y' ≠ 1) : ConjLine x y' := by
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, (h.zpowers_eq_of_mem ⟨g, hg⟩ hmem hne).trans hg⟩

omit [Finite G] in
theorem conjLine_B_torus {k a : F} (hk : ConjLine x (f k)) (ha : a ≠ 0) :
    ConjLine x (f (a ^ 2 * k)) := by
  have h0 : ∃ g : G, zpowers (f k * x ^ 0) = (zpowers x).map (MulAut.conj g).toMonoidHom := by
    rw [pow_zero, mul_one]; exact hk
  have := h.conj_torus (e := 0) h0 ha
  rw [pow_zero, mul_one] at this
  exact this

omit [Finite G] in
theorem conjLine_A_torus {k a : F} (hk : ConjLine x (f k * x)) (ha : a ≠ 0) :
    ConjLine x (f (a ^ 2 * k) * x) := by
  have h0 : ∃ g : G, zpowers (f k * x ^ 1) = (zpowers x).map (MulAut.conj g).toMonoidHom := by
    rw [pow_one]; exact hk
  have := h.conj_torus (e := 1) h0 ha
  rw [pow_one] at this
  exact this

theorem f_mul_x_ne_one [hp : Fact p.Prime] (s : F) : f s * x ≠ 1 := by
  intro h1
  have h2 : f s = x ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    exact eq_inv_of_mul_eq_one_left h1
  exact h.f_ne_zpow_x _ _ (by rw [zpow_neg_one]; exact inv_ne_one.mpr h.x_ne_one) h2

theorem exists_type [hp : Fact p.Prime] [CharP F p] {y : G} (hyW : y ∈ W) (hy : ConjLine x y)
    (hyx : y ∉ zpowers x) :
    (∃ t : F, t ≠ 0 ∧ zpowers y = zpowers (f t)) ∨
      (∃ t : F, t ≠ 0 ∧ zpowers y = zpowers (f t * x)) := by
  obtain ⟨t, i, hi, rfl⟩ := h.mem_iff y hyW
  by_cases ht : t = 0
  · exfalso
    apply hyx
    rw [ht, h.f_zero, one_mul]
    exact Subgroup.pow_mem _ (mem_zpowers x) i
  by_cases hi0 : i = 0
  · left
    exact ⟨t, ht, by rw [hi0, pow_zero, mul_one]⟩
  right
  have hcop : Nat.Coprime i p := by
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) hi
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have hxij : x ^ (i * j) = x := by
    rw [← Nat.mod_add_div (i * j) p, hj, pow_add, pow_mul, h.x_pow, one_pow, mul_one, pow_one]
  have hyj : (f t * x ^ i) ^ j = f ((j : F) * t) * x := by
    rw [Commute.mul_pow (h.f_mul_x_pow_comm t i), ← h.f_natCast_mul, ← pow_mul, hxij]
  have hmem : f ((j : F) * t) * x ∈ zpowers (f t * x ^ i) :=
    hyj ▸ Subgroup.pow_mem _ (mem_zpowers _) j
  have heq := h.zpowers_eq_of_mem hy hmem (h.f_mul_x_ne_one _)
  refine ⟨(j : F) * t, fun hz => ?_, heq.symm⟩
  apply hyx
  rw [hz, h.f_zero, one_mul] at heq
  rw [heq]
  exact mem_zpowers _

theorem card_W [hp : Fact p.Prime] : Nat.card W = p ^ (n + 1) := by
  have hdisj : Disjoint h.V (zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro a haV haX
    obtain ⟨t, rfl⟩ := haV
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp haX
    by_contra hne
    exact h.f_ne_zpow_x t j (by rw [hj]; exact hne) hj.symm
  have hnormal : zpowers x ≤ normalizer (h.V : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨t, rfl⟩ := ha
    exact h.f_comm t
  have hWeq : W = h.V ⊔ zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨t, i, -, rfl⟩ := h.mem_iff y hy
      exact Subgroup.mul_mem_sup ⟨t, rfl⟩ (Subgroup.pow_mem _ (mem_zpowers x) i)
    · exact sup_le (by rintro _ ⟨t, rfl⟩; exact h.f_mem t) ((zpowers_le).mpr h.x_mem)
  rw [hWeq, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
    h.card_V, h.card_zpowers_x, pow_succ]

omit [Finite G] in
theorem false_of_B_plane [hp : Fact p.Prime] [CharP F p] {t c : F} (ht : t ≠ 0)
    (hc : ∀ m : ℕ, c ≠ (m : F))
    (hB : ∀ m : ℕ, m < p → ConjLine x (f (t * ((m : F) + c)))) : False := by
  have hcm : ∀ m : ℕ, (m : F) + c ≠ 0 := natCast_add_ne_zero hc
  have hft1 : f t ≠ 1 := fun h1 => ht (h.f_inj (h1.trans h.f_zero.symm))
  have hvu : f (t * c) ∉ zpowers (f t) := by
    intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    rw [← h.f_intCast_mul] at hj
    have h2 : (j : F) * t = t * c := h.f_inj hj
    apply hc ((j % p).toNat)
    rw [← intCast_eq_natCast_emod (F := F) (p := p) j]
    apply mul_left_cancel₀ ht
    rw [← h2]
    ring
  refine h.false_of_lines (u := f t) (v := f (t * c)) (h.f_mem t) (h.f_mem _) (h.f_comm' t _)
    hft1 (h.f_pow_p t) (h.f_pow_p _) hvu (fun m => f (t * ((m : F) + c))) ?_ ?_ ?_ ?_
  · intro i _
    have : f (t * ((i : F) + c)) = f t ^ i * f (t * c) := by
      rw [show t * ((i : F) + c) = (i : F) * t + t * c by ring, h.f_add, h.f_natCast_mul]
    rw [this]
    exact mul_mem (pow_mem (subset_closure (Set.mem_insert _ _)) i)
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · exact fun i _ h1 => mul_ne_zero ht (hcm i) (h.f_inj (h1.trans h.f_zero.symm))
  · exact fun i hi => hB i hi
  · intro i hi j hj hij
    obtain ⟨m, hm0, hmp, hm⟩ := h.exists_natCast_of_zpowers_eq (mul_ne_zero ht (hcm i)) hij
    exact eq_of_affine_proportional ht hc hi hj hm0 hmp hm

theorem false_of_A_plane [hp : Fact p.Prime] [CharP F p] {k : F} (hk : k ≠ 0)
    (hA : ∀ m : ℕ, m < p → ConjLine x (f ((m : F) * k) * x)) : False := by
  have hvu : f k ∉ zpowers x := by
    intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    by_cases hxj : x ^ j = 1
    · rw [hxj] at hj
      exact hk (h.f_inj (hj.symm.trans h.f_zero.symm))
    · exact h.f_ne_zpow_x k j hxj hj.symm
  refine h.false_of_lines (u := x) (v := f k) h.x_mem (h.f_mem k) (h.f_comm k).symm h.x_ne_one
    h.x_pow (h.f_pow_p k) hvu (fun m => f ((m : F) * k) * x) ?_ ?_ ?_ ?_
  · intro i _
    rw [h.f_natCast_mul]
    exact mul_mem (pow_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) i)
      (subset_closure (Set.mem_insert _ _))
  · exact fun i _ => h.f_mul_x_ne_one _
  · exact fun i hi => hA i hi
  · intro i hi j hj hij
    exact natCast_inj_of_lt hi hj (mul_right_cancel₀ hk (h.eq_of_zpowers_mul_eq hij))

end FusionData

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
