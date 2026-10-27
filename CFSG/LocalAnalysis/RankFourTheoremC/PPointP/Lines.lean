module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup CFSG.Open

structure FusionData (G : Type) [Group G] (p n : ℕ) (F : Type) [Field F] (f : F → G) (x : G)
    (W : Subgroup G) : Prop where
  two_le : 2 ≤ n
  p_n : 5 ≤ p ∨ 3 ≤ n
  card_F : Nat.card F = p ^ n
  x_pow : x ^ p = 1
  f_add : ∀ s t, f (s + t) = f s * f t
  f_inj : Function.Injective f
  f_comm : ∀ t, f t * x = x * f t
  f_ne : ∀ t, f t ≠ x
  f_mem : ∀ t, f t ∈ W
  x_mem : x ∈ W
  mem_iff : ∀ y ∈ W, ∃ (t : F) (i : ℕ), i < p ∧ y = f t * x ^ i
  torus : ∀ a : Fˣ, ∃ g : G, g * x * g⁻¹ = x ∧ ∀ t, g * f t * g⁻¹ = f ((a : F) ^ 2 * t)
  no_plane : ∀ D : Subgroup G, D ≤ W → IsElemAbelian p D → Nat.card D = p ^ 2 →
    ¬ ∃ S : Finset (Subgroup G), S.card = p ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = p ∧
      ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom
  trans : ∀ g : G, g * x * g⁻¹ ∈ W →
    ∃ m ∈ normalizer (W : Set G), m * x * m⁻¹ = g * x * g⁻¹

theorem map_conj_zpowers' {G : Type*} [Group G] (y g : G) :
    (zpowers y).map (MulAut.conj g).toMonoidHom = zpowers (g * y * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem intCast_eq_natCast_emod {F : Type*} [Field F] {p : ℕ} [CharP F p] [hp : Fact p.Prime]
    (j : ℤ) : (j : F) = (((j % p).toNat : ℕ) : F) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnn : 0 ≤ j % (p : ℤ) := Int.emod_nonneg _ hp0
  have h1 : (((j % p).toNat : ℕ) : ℤ) = j % p := Int.toNat_of_nonneg hnn
  have h2 : (((((j % p).toNat : ℕ) : ℤ)) : F) = (j : F) := by
    rw [h1]
    exact (CharP.intCast_eq_intCast F p).mpr (Int.mod_modEq j p)
  rw [← h2]
  exact Int.cast_natCast _

theorem card_closure_pair {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {u v : G}
    (huv : u * v = v * u) (hu1 : u ≠ 1) (hup : u ^ p = 1) (hvp : v ^ p = 1)
    (hvu : v ∉ zpowers u) : Nat.card (closure ({u, v} : Set G)) = p ^ 2 := by
  have hv1 : v ≠ 1 := fun h1 => hvu (h1 ▸ one_mem _)
  have hou : orderOf u = p := orderOf_eq_prime hup hu1
  have hov : orderOf v = p := orderOf_eq_prime hvp hv1
  have hDeq : closure ({u, v} : Set G) = zpowers u ⊔ zpowers v := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hfin : Finite (zpowers v) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hov]; exact hp.out.ne_zero)
  have hdisj : Disjoint (zpowers u) (zpowers v) := by
    rw [Subgroup.disjoint_def]
    intro a hau hav
    by_contra hne
    apply hvu
    have hap : a ^ p = 1 := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hav
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hvp, one_zpow]
    have hoa : orderOf a = p := orderOf_eq_prime hap hne
    have hsub : zpowers a ≤ zpowers v := (zpowers_le).mpr hav
    have heq : zpowers a = zpowers v :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hov])
    have hvmem : v ∈ zpowers a := heq ▸ mem_zpowers v
    exact (zpowers_le.mpr hau) hvmem
  have hnormal : zpowers v ≤ normalizer (zpowers u : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left huv j).eq
  rw [hDeq, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hou, hov, sq]

namespace FusionData

variable {G : Type} [Group G] {p n : ℕ} {F : Type} [Field F] {f : F → G} {x : G}
  {W : Subgroup G} (h : FusionData G p n F f x W)

include h

theorem f_zero : f 0 = 1 := by
  have h1 := h.f_add 0 0
  rw [add_zero] at h1
  exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)

theorem f_neg (t : F) : f (-t) = (f t)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← h.f_add, add_neg_cancel, h.f_zero])

theorem f_comm' (s t : F) : f s * f t = f t * f s := by
  rw [← h.f_add, ← h.f_add, add_comm]

theorem f_natCast_mul (m : ℕ) (t : F) : f ((m : F) * t) = f t ^ m := by
  induction m with
  | zero => simp [h.f_zero]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, h.f_add, ih, pow_succ]

theorem f_intCast_mul (j : ℤ) (t : F) : f ((j : F) * t) = f t ^ j := by
  rcases j with m | m
  · simpa using h.f_natCast_mul m t
  · have : ((Int.negSucc m : ℤ) : F) * t = -(((m + 1 : ℕ) : F) * t) := by
      push_cast
      ring
    rw [this, h.f_neg, h.f_natCast_mul, zpow_negSucc]

theorem f_pow_p [CharP F p] (t : F) : f t ^ p = 1 := by
  have h1 := h.f_natCast_mul p t
  rw [CharP.cast_eq_zero, zero_mul, h.f_zero] at h1
  exact h1.symm

theorem f_mul_x_pow_comm (t : F) (i : ℕ) : f t * x ^ i = x ^ i * f t :=
  (Commute.pow_right (show Commute (f t) x from h.f_comm t) i).eq

theorem x_zpow_comm (t : F) (i : ℤ) : f t * x ^ i = x ^ i * f t :=
  (Commute.zpow_right (show Commute (f t) x from h.f_comm t) i).eq

theorem x_ne_one : x ≠ 1 := by
  intro h1
  exact h.f_ne 0 (by rw [h.f_zero, h1])

theorem orderOf_x [hp : Fact p.Prime] : orderOf x = p :=
  orderOf_eq_prime h.x_pow h.x_ne_one

variable [Finite G]

theorem f_ne_zpow_x [hp : Fact p.Prime] (u : F) (i : ℤ) (hi : x ^ i ≠ 1) : f u ≠ x ^ i := by
  intro hfu
  have hsub : zpowers (x ^ i) ≤ zpowers x := by
    rw [zpowers_le]
    exact zpow_mem (mem_zpowers x) i
  have hcard : Nat.card (zpowers (x ^ i)) = p := by
    have hxp : (x ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.x_pow, one_zpow]
    have hdvd : orderOf (x ^ i) ∣ p := orderOf_dvd_of_pow_eq_one hxp
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hi
    · rw [Nat.card_zpowers, h1]
  have heq : zpowers (x ^ i) = zpowers x :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, Nat.card_zpowers, h.orderOf_x])
  have hxmem : x ∈ zpowers (f u) := by
    rw [hfu, heq]
    exact mem_zpowers x
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxmem
  apply h.f_ne ((j : F) * u)
  rw [h.f_intCast_mul]
  exact hj

omit [Finite G] in
theorem exists_natCast_of_zpowers_eq [hp : Fact p.Prime] [CharP F p] {s t : F} (hs : s ≠ 0)
    (hst : zpowers (f s) = zpowers (f t)) :
    ∃ m : ℕ, 0 < m ∧ m < p ∧ s = (m : F) * t := by
  have hmem : f s ∈ zpowers (f t) := hst ▸ mem_zpowers (f s)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have h1 : f ((j : F) * t) = f s := by rw [h.f_intCast_mul, hj]
  have h2 : (j : F) * t = s := h.f_inj h1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnn : 0 ≤ j % (p : ℤ) := Int.emod_nonneg _ hp0
  have hlt : j % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp.out.pos)
  have hjm := intCast_eq_natCast_emod (F := F) (p := p) j
  refine ⟨(j % p).toNat, ?_, by omega, ?_⟩
  · rcases Nat.eq_zero_or_pos (j % p).toNat with h0 | h0
    · exfalso
      apply hs
      rw [← h2, hjm, h0]
      simp
    · exact h0
  · rw [← h2, hjm]

theorem eq_of_zpowers_mul_eq [hp : Fact p.Prime] [CharP F p] {s t : F}
    (hst : zpowers (f s * x) = zpowers (f t * x)) : s = t := by
  have hmem : f s * x ∈ zpowers (f t * x) := hst ▸ mem_zpowers _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have hcomm : Commute (f t) x := h.f_comm t
  rw [Commute.mul_zpow hcomm, ← h.f_intCast_mul] at hj
  have h1 : f ((j : F) * t - s) = x ^ (1 - j) := by
    rw [sub_eq_add_neg, h.f_add, h.f_neg]
    have h2 : f ((j : F) * t) = f s * x * (x ^ j)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hj
    rw [h2]
    have h3 : x ^ (1 - j) = x * (x ^ j)⁻¹ := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg, zpow_one]
    rw [h3]
    have h4 : f s * x * (x ^ j)⁻¹ * (f s)⁻¹ = (f s * (x * (x ^ j)⁻¹)) * (f s)⁻¹ := by
      group
    rw [h4]
    have h5 : f s * (x * (x ^ j)⁻¹) = (x * (x ^ j)⁻¹) * f s := by
      rw [← h3]
      exact h.x_zpow_comm s (1 - j)
    rw [h5]
    group
  have h6 : x ^ (1 - j) = 1 := by
    by_contra hne
    exact h.f_ne_zpow_x _ _ hne h1
  rw [h6] at h1
  have h7 : (j : F) * t - s = 0 := h.f_inj (by rw [h1, h.f_zero])
  have h8 : ((1 - j : ℤ) : F) = 0 := by
    rw [CharP.intCast_eq_zero_iff F p]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h6
    rw [h.orderOf_x] at this
    exact_mod_cast this
  have h9 : (j : F) = 1 := by
    push_cast at h8
    linear_combination -h8
  rw [h9, one_mul] at h7
  linear_combination -h7

omit [Finite G] in
theorem conj_torus {k : F} {e : ℕ}
    (hL : ∃ g : G, zpowers (f k * x ^ e) = (zpowers x).map (MulAut.conj g).toMonoidHom)
    {a : F} (ha : a ≠ 0) :
    ∃ g : G, zpowers (f (a ^ 2 * k) * x ^ e) =
      (zpowers x).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g₀, hg₀⟩ := hL
  obtain ⟨g, hgx, hgf⟩ := h.torus (Units.mk0 a ha)
  refine ⟨g * g₀, ?_⟩
  have h1 : zpowers (f (a ^ 2 * k) * x ^ e) =
      (zpowers (f k * x ^ e)).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_zpowers']
    congr 1
    have := hgf k
    simp only [Units.val_mk0] at this
    calc f (a ^ 2 * k) * x ^ e = (g * f k * g⁻¹) * (g * x * g⁻¹) ^ e := by rw [this, hgx]
      _ = g * (f k * x ^ e) * g⁻¹ := by rw [conj_pow]; group
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom =
      (MulAut.conj (g * g₀)).toMonoidHom := MonoidHom.ext fun z => by simp [mul_assoc]
  rw [h1, hg₀, Subgroup.map_map, hcomp]

omit [Finite G] in
theorem card_zpowers_x [hp : Fact p.Prime] : Nat.card (zpowers x) = p := by
  rw [Nat.card_zpowers, h.orderOf_x]

omit [Finite G] in
theorem false_of_lines [hp : Fact p.Prime] {u v : G} (hu : u ∈ W) (hv : v ∈ W)
    (huv : u * v = v * u) (hu1 : u ≠ 1) (hup : u ^ p = 1) (hvp : v ^ p = 1)
    (hvu : v ∉ zpowers u) (y : ℕ → G) (hyD : ∀ i < p, y i ∈ closure ({u, v} : Set G))
    (hy1 : ∀ i < p, y i ≠ 1)
    (hyc : ∀ i < p, ∃ g : G, zpowers (y i) = (zpowers x).map (MulAut.conj g).toMonoidHom)
    (hinj : ∀ i < p, ∀ j < p, zpowers (y i) = zpowers (y j) → i = j) : False := by
  classical
  set D : Subgroup G := closure ({u, v} : Set G) with hD
  have hcomm : ({u, v} : Set G).Pairwise Commute := by
    rw [Set.pairwise_pair]
    intro _
    exact ⟨huv, huv.symm⟩
  have hDcomm : IsMulCommutative D := Subgroup.isMulCommutative_closure hcomm
  have hDW : D ≤ W := by
    rw [hD, closure_le]
    intro a ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv
  have hDexp : ∀ d ∈ D, d ^ p = 1 := by
    intro d hd
    induction hd using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact hup
      · rw [Set.mem_singleton_iff.mp hz]
        exact hvp
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩)
      rw [(Commute.mul_pow hab p), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hDabel : IsElemAbelian p D := ⟨hDcomm, hDexp⟩
  have hDcard : Nat.card D = p ^ 2 := card_closure_pair huv hu1 hup hvp hvu
  refine h.no_plane D hDW hDabel hDcard ⟨(Finset.range p).image fun i => zpowers (y i), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  · intro L hL
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
    have hi' := Finset.mem_range.mp hi
    refine ⟨zpowers_le.mpr (hyD i hi'), ?_, hyc i hi'⟩
    have hyp : y i ^ p = 1 := hDexp _ (hyD i hi')
    rw [Nat.card_zpowers, orderOf_eq_prime hyp (hy1 i hi')]

end FusionData

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
