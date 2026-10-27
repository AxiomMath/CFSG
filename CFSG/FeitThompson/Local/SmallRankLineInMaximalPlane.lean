module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import Mathlib.GroupTheory.NoncommCoprod
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {p a : ℕ} {P : Type*} [Group P] {A B X Z : Subgroup P}

def IsElementaryAbelian (p : ℕ) {P : Type*} [Group P] (A : Subgroup P) : Prop :=
  IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1

theorem isElementaryAbelian_iff :
    IsElementaryAbelian p A ↔ IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1 := Iff.rfl

theorem IsElementaryAbelian.isMulCommutative (hA : IsElementaryAbelian p A) :
    IsMulCommutative A := hA.1

theorem IsElementaryAbelian.pow_eq_one (hA : IsElementaryAbelian p A) {x : P} (hx : x ∈ A) :
    x ^ p = 1 := hA.2 x hx

theorem IsElementaryAbelian.mul_comm (hA : IsElementaryAbelian p A) {x y : P} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem isElementaryAbelian_bot : IsElementaryAbelian p (⊥ : Subgroup P) :=
  ⟨IsMulCommutative.of_comm fun x y => by
      rw [show x = 1 from Subtype.ext (mem_bot.1 x.2), show y = 1 from Subtype.ext (mem_bot.1 y.2),
        one_mul],
    fun x hx => by rw [mem_bot.1 hx, one_pow]⟩

theorem IsElementaryAbelian.mono (hA : IsElementaryAbelian p A) (h : B ≤ A) :
    IsElementaryAbelian p B :=
  ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hA.mul_comm (h x.2) (h y.2)),
    fun x hx => hA.2 x (h hx)⟩

theorem IsElementaryAbelian.isPGroup (hA : IsElementaryAbelian p A) : IsPGroup p A :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA.2 g.1 g.2)⟩

theorem IsElementaryAbelian.exists_natCard_eq_pow [Finite P] (hp : p.Prime)
    (hA : IsElementaryAbelian p A) : ∃ d, Nat.card A = p ^ d := by
  have := Fact.mk hp
  exact hA.isPGroup.exists_card_eq

theorem IsElementaryAbelian.le_centralizer (hA : IsElementaryAbelian p A) (hBA : B ≤ A) :
    A ≤ centralizer (B : Set P) := fun _ hg =>
  mem_centralizer_iff.2 fun _ hh => hA.mul_comm (hBA hh) hg

theorem IsElementaryAbelian.of_natCard_eq_prime (hp : p.Prime) (hA : Nat.card A = p) :
    IsElementaryAbelian p A := by
  have := Fact.mk hp
  have : IsCyclic A := isCyclic_of_prime_card hA
  have : CommGroup A := IsCyclic.commGroup
  refine ⟨inferInstance, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : A) ^ p = 1 := by rw [← hA]; exact pow_card_eq_one'
  simpa using congrArg Subtype.val h

theorem IsElementaryAbelian.mem_elementaryAbelianRanks_of_le {d : ℕ} (hp : p.Prime)
    (hA : IsElementaryAbelian p A) (hd : Nat.card A = p ^ d) (hAB : A ≤ B) :
    d ∈ elementaryAbelianRanks p B := by
  refine (mem_elementaryAbelianRanks_iff_exists_subgroup hp).2 ⟨A.subgroupOf B, ?_, ?_, ?_⟩
  · have : IsMulCommutative A := hA.1
    infer_instance
  · exact fun x hx => Subtype.ext (by simpa using hA.2 x.1 (mem_subgroupOf.1 hx))
  · rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv, hd]

theorem IsElementaryAbelian.le_elementaryAbelianPRank [Finite P] {d : ℕ} (hp : p.Prime)
    (hA : IsElementaryAbelian p A) (hd : Nat.card A = p ^ d) (hAB : A ≤ B) :
    d ≤ elementaryAbelianPRank p B :=
  CFSG.FeitThompson.le_elementaryAbelianPRank hp.one_lt
    (hA.mem_elementaryAbelianRanks_of_le hp hd hAB)

private theorem normal_of_le_center (hZ : Z ≤ center P) : Z.Normal where
  conj_mem n hn x := by
    have := (mem_center_iff.1 (hZ hn)) x
    simpa [this] using hn

theorem exists_mul_eq_of_mem_sup_of_le_center (hZ : Z ≤ center P) {g : P} (hg : g ∈ X ⊔ Z) :
    ∃ x ∈ X, ∃ z ∈ Z, x * z = g := by
  have := normal_of_le_center hZ
  obtain ⟨x, hx, z, hz, rfl⟩ : g ∈ ((X : Set P) * (Z : Set P)) := X.mul_normal Z ▸ hg
  exact ⟨x, hx, z, hz, rfl⟩

theorem IsElementaryAbelian.sup_of_le_center (hX : IsElementaryAbelian p X)
    (hZe : IsElementaryAbelian p Z) (hZ : Z ≤ center P) : IsElementaryAbelian p (X ⊔ Z) := by
  constructor
  · refine IsMulCommutative.of_comm fun g₁ g₂ => Subtype.ext ?_
    obtain ⟨y₁, hy₁, z₁, hz₁, he₁⟩ := exists_mul_eq_of_mem_sup_of_le_center hZ g₁.2
    obtain ⟨y₂, hy₂, z₂, hz₂, he₂⟩ := exists_mul_eq_of_mem_sup_of_le_center hZ g₂.2
    have h1 : ∀ b : P, b * z₁ = z₁ * b := mem_center_iff.1 (hZ hz₁)
    have h2 : ∀ b : P, b * z₂ = z₂ * b := mem_center_iff.1 (hZ hz₂)
    have hy : y₁ * y₂ = y₂ * y₁ := hX.mul_comm hy₁ hy₂
    have hzz : z₁ * z₂ = z₂ * z₁ := hZe.mul_comm hz₁ hz₂
    simp only [Subgroup.coe_mul, ← he₁, ← he₂]
    calc y₁ * z₁ * (y₂ * z₂) = y₁ * (z₁ * y₂) * z₂ := by group
      _ = y₁ * (y₂ * z₁) * z₂ := by rw [← h1 y₂]
      _ = y₁ * y₂ * (z₁ * z₂) := by group
      _ = y₂ * y₁ * (z₂ * z₁) := by rw [hy, hzz]
      _ = y₂ * (y₁ * z₂) * z₁ := by group
      _ = y₂ * (z₂ * y₁) * z₁ := by rw [h2 y₁]
      _ = y₂ * z₂ * (y₁ * z₁) := by group
  · intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_center hZ hg
    have c : Commute y z := mem_center_iff.1 (hZ hz) y
    rw [c.mul_pow, hX.2 y hy, hZe.2 z hz, one_mul]

theorem natCard_sup_of_le_center (hZ : Z ≤ center P) (h : X ⊓ Z = ⊥) :
    Nat.card (X ⊔ Z : Subgroup P) = Nat.card X * Nat.card Z := by
  have hcomm : ∀ (x : X) (z : Z), Commute (X.subtype x) (Z.subtype z) :=
    fun x z => mem_center_iff.1 (hZ z.2) x.1
  have hrange : (X.subtype.noncommCoprod Z.subtype hcomm).range = X ⊔ Z := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hinj : Function.Injective (X.subtype.noncommCoprod Z.subtype hcomm) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, z⟩ hxz
    obtain ⟨hx, hz⟩ := disjoint_iff_mul_eq_one.1 (disjoint_iff.2 h) x.2 z.2 hxz
    simp [Prod.ext_iff, Subtype.ext_iff, hx, hz]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

private theorem zpowers_eq_of_natCard_eq_prime (hp : p.Prime) (hX : Nat.card X = p) {g : P}
    (hg : g ∈ X) (hg1 : g ≠ 1) : zpowers g = X := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact hp.ne_zero)
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg) ?_
  rw [Nat.card_zpowers, hX]
  have hdvd : orderOf g ∣ p := by
    rw [← hX]
    have h : orderOf (⟨g, hg⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hg1
  · omega

theorem inf_eq_bot_or_eq_of_natCard_eq_prime (hp : p.Prime) (hX : Nat.card X = p)
    (hZ : Nat.card Z = p) : X ⊓ Z = ⊥ ∨ X = Z := by
  by_cases h : X ⊓ Z = ⊥
  · exact Or.inl h
  · simp only [eq_bot_iff_forall] at h
    push Not at h
    obtain ⟨g, hg, hg1⟩ := h
    exact Or.inr ((zpowers_eq_of_natCard_eq_prime hp hX (mem_inf.1 hg).1 hg1).symm.trans
      (zpowers_eq_of_natCard_eq_prime hp hZ (mem_inf.1 hg).2 hg1))

theorem exists_le_center_natCard_eq (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    ∃ Z : Subgroup P, Z ≤ center P ∧ Nat.card Z = p := by
  obtain ⟨z, hzc, hz⟩ := exists_mem_center_orderOf_eq hp hP ha
  exact ⟨zpowers z, zpowers_le.2 hzc, by rw [Nat.card_zpowers, hz]⟩

theorem inf_eq_bot_of_elementaryAbelianPRank_centralizer_le [Finite P] (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p P)
    (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2)
    (hX : Nat.card X = p) (hZ : Z ≤ center P) (hZc : Nat.card Z = p) : X ⊓ Z = ⊥ := by
  rcases inf_eq_bot_or_eq_of_natCard_eq_prime hp hX hZc with h | h
  · exact h
  · exfalso
    have htop : centralizer (X : Set P) = ⊤ := centralizer_eq_top_iff_subset.2 (h ▸ hZ)
    have := elementaryAbelianPRank_eq_of_mulEquiv (p := p) hp.one_lt
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
    omega

theorem natCard_sup_eq_sq_of_elementaryAbelianPRank_centralizer_le [Finite P] (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p P)
    (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2)
    (hX : Nat.card X = p) (hZ : Z ≤ center P) (hZc : Nat.card Z = p) :
    Nat.card (X ⊔ Z : Subgroup P) = p ^ 2 := by
  rw [natCard_sup_of_le_center hZ
    (inf_eq_bot_of_elementaryAbelianPRank_centralizer_le hp hrank hCX hX hZ hZc), hX, hZc, sq]

theorem maximal_isElementaryAbelian_sup [Finite P] (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p P)
    (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2)
    (hX : Nat.card X = p) (hZ : Z ≤ center P) (hZc : Nat.card Z = p) :
    Maximal (IsElementaryAbelian p) (X ⊔ Z) := by
  have hcard : Nat.card (X ⊔ Z : Subgroup P) = p ^ 2 :=
    natCard_sup_eq_sq_of_elementaryAbelianPRank_centralizer_le hp hrank hCX hX hZ hZc
  refine ⟨(IsElementaryAbelian.of_natCard_eq_prime hp hX).sup_of_le_center
    (IsElementaryAbelian.of_natCard_eq_prime hp hZc) hZ, fun A hA hle => ?_⟩
  obtain ⟨d, hd⟩ := hA.exists_natCard_eq_pow hp
  have hdle : d ≤ 2 :=
    (hA.le_elementaryAbelianPRank hp hd (hA.le_centralizer (le_sup_left.trans hle))).trans hCX
  refine ge_of_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [hd, hcard]
  exact Nat.pow_le_pow_right hp.pos hdle

theorem exists_central_line_and_maximal_plane (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hrank : 3 ≤ elementaryAbelianPRank p P) (hX : Nat.card X = p)
    (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2) :
    (∃ Z : Subgroup P, Z ≤ center P ∧ Nat.card Z = p) ∧
      ∀ Z : Subgroup P, Z ≤ center P → Nat.card Z = p →
        X ⊓ Z = ⊥ ∧ Nat.card (X ⊔ Z : Subgroup P) = p ^ 2 ∧
          Maximal (IsElementaryAbelian p) (X ⊔ Z) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.ne_zero)
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.1 (by simpa using hP)).1
      rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt] at hrank
      omega
    · exact h
  refine ⟨exists_le_center_natCard_eq hp hP ha, fun Z hZ hZc => ⟨?_, ?_, ?_⟩⟩
  · exact inf_eq_bot_of_elementaryAbelianPRank_centralizer_le hp hrank hCX hX hZ hZc
  · exact natCard_sup_eq_sq_of_elementaryAbelianPRank_centralizer_le hp hrank hCX hX hZ hZc
  · exact maximal_isElementaryAbelian_sup hp hrank hCX hX hZ hZc

end

end CFSG.FeitThompson
