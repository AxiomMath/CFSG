module

public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem natCard_image_eq_relIndex {X : Type*} {A B : Subgroup G} (f : G → X)
    (h : ∀ a ∈ A, ∀ a' ∈ A, f a = f a' ↔ a⁻¹ * a' ∈ B) :
    Nat.card (f '' (A : Set G)) = B.relIndex A := by
  let g : A ⧸ B.subgroupOf A → f '' (A : Set G) :=
    Quotient.lift (fun a : A => ⟨f a, a, a.2, rfl⟩) fun a b hab => by
      refine Subtype.ext ?_
      have h1 : (a : A)⁻¹ * b ∈ B.subgroupOf A := QuotientGroup.leftRel_apply.mp hab
      exact (h a a.2 b b.2).mpr h1
  have hg : Function.Bijective g := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      intro hxy
      rename_i a b
      have h1 : f a = f b := congrArg Subtype.val hxy
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((h a a.2 b b.2).mp h1))
    · rintro ⟨_, a, ha, rfl⟩
      exact ⟨Quotient.mk _ ⟨a, ha⟩, rfl⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem exists_mem_normalizer_not_mem_sq_mem [Finite G] {T U : Subgroup G} (hU : IsPGroup 2 U)
    (hTU : T ≤ U) (hne : T ≠ U) :
    ∃ x ∈ U, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ T ∧ x * x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsU, hsN, hsT⟩ := exists_mem_normalizer_not_mem hU hTU hne
  have hex : ∃ k : ℕ, s ^ (2 ^ k) ∈ T := by
    obtain ⟨k, hk⟩ := hU ⟨s, hsU⟩
    refine ⟨k, ?_⟩
    have h1 : s ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact T.one_mem
  classical
  have hk₀T : s ^ (2 ^ Nat.find hex) ∈ T := Nat.find_spec hex
  have hk₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hk₀T
    exact hsT (by simpa using hk₀T)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk₀pos
  refine ⟨s ^ (2 ^ j), U.pow_mem hsU _, (Subgroup.normalizer (T : Set G)).pow_mem hsN _, ?_, ?_⟩
  · intro hx
    exact Nat.find_min hex (by omega : j < Nat.find hex) hx
  · have h1 : s ^ (2 ^ j) * s ^ (2 ^ j) = s ^ (2 ^ Nat.find hex) := by
      rw [← pow_add, hj, pow_succ]
      congr 1
      ring
    rw [h1]
    exact hk₀T

theorem conjSubgroup_centralizer (g a : G) :
    conjSubgroup g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  have h1 : y ∈ conjSubgroup g (Subgroup.centralizer ({a} : Set G)) ↔
      g⁻¹ * y * g ∈ Subgroup.centralizer ({a} : Set G) := mem_conjSubgroup_iff
  rw [h1, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc (g * a * g⁻¹) * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g) = g⁻¹ * ((g * a * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * y * g) * a := by group

theorem natCard_centralizer_conj (g a : G) :
    Nat.card (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  rw [← conjSubgroup_centralizer, card_conjSubgroup]

theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnc : ¬ ∀ a b : G, a * b = b * a) {c : G}
    (hc : c ≠ 1) : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have hcen : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({c} : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp this c rfl).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hc hcen
  · apply hnc
    intro a b
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem conj_eq_iff_mem_normalizer {S T : Subgroup G} {a a' : G}
    (ha : a ∈ Subgroup.normalizer (T : Set G)) (ha' : a' ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup a S = conjSubgroup a' S ↔
      a⁻¹ * a' ∈ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) := by
  have key : conjSubgroup a S = conjSubgroup a' S ↔ conjSubgroup (a⁻¹ * a') S = S := by
    constructor
    · intro h
      have := congrArg (conjSubgroup a⁻¹) h
      rw [conjSubgroup_inv_conjSubgroup, conjSubgroup_conjSubgroup] at this
      exact this.symm
    · intro h
      have := congrArg (conjSubgroup a) h
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left] at this
      exact this.symm
  rw [key, conjSubgroup_eq_self_iff]
  exact ⟨fun h => ⟨h, (Subgroup.normalizer (T : Set G)).mul_mem
    ((Subgroup.normalizer (T : Set G)).inv_mem ha) ha'⟩, fun h => h.1⟩

theorem conj_eq_iff_mem_centralizer {t a a' : G} :
    a * t * a⁻¹ = a' * t * a'⁻¹ ↔ a⁻¹ * a' ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc t * (a⁻¹ * a') = a⁻¹ * (a * t * a⁻¹) * a' := by group
      _ = a⁻¹ * (a' * t * a'⁻¹) * a' := by rw [h]
      _ = (a⁻¹ * a') * t := by group
  · intro hc
    calc a * t * a⁻¹ = a * (t * (a⁻¹ * a') * (a⁻¹ * a')⁻¹) * a⁻¹ := by group
      _ = a * (((a⁻¹ * a') * t) * (a⁻¹ * a')⁻¹) * a⁻¹ := by rw [hc]
      _ = a' * t * a'⁻¹ := by group

structure Escape (T U : Subgroup G) (x : G) : Prop where
  two : IsPGroup 2 U
  le : T ≤ U
  mem : x ∈ U
  normalizes : x ∈ Subgroup.normalizer (T : Set G)
  not_mem : x ∉ T
  sq_mem : x * x ∈ T

namespace OddByQuat

variable {R S T U : Subgroup G} {t x : G}

section Criterion

variable [Finite G]

theorem T_sylow_H (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    IsSylow2Of T (Subgroup.centralizer ({t} : Set G)) :=
  (d.sylow_of_sylow_M hT).1

theorem S_le_T (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    S ≤ T := (d.sylow_of_sylow_M hT).2.1

omit [Finite G] in
theorem T_le_C (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    T ≤ Subgroup.centralizer ({t} : Set G) := fun _ hx => d.M_le_C (hT.1 hx)

theorem t_central (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    ∀ x ∈ T, t * x = x * t := (d.sylow_of_sylow_M hT).2.2.2

theorem inf_R_eq (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    T ⊓ R = S :=
  d.sylow.2.2 (T ⊓ R) inf_le_right (hT.2.1.to_le inf_le_left) (le_inf (d.S_le_T hT) d.S_le)

theorem normalizer_inf_eq (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (T : Set G) := by
  ext x
  constructor
  · rintro ⟨hm, hn⟩
    exact ⟨d.M_le_C hm, hn⟩
  · rintro ⟨hh, hn⟩
    refine ⟨?_, hn⟩
    show x ∈ Subgroup.normalizer (S : Set G)
    rw [← conjSubgroup_eq_self_iff, ← d.inf_R_eq hT, conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr hn, conjSubgroup_eq_self_iff.mpr (d.normal hh)]

theorem conj_t_eq_iff (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    {a a' : G} (ha : a ∈ Subgroup.normalizer (T : Set G))
    (ha' : a' ∈ Subgroup.normalizer (T : Set G)) :
    a * t * a⁻¹ = a' * t * a'⁻¹ ↔
      a⁻¹ * a' ∈ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) := by
  rw [d.normalizer_inf_eq hT, conj_eq_iff_mem_centralizer]
  have hA : a⁻¹ * a' ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).inv_mem ha) ha'
  exact ⟨fun h => ⟨h, hA⟩, fun h => h.1⟩

omit [Finite G] in
theorem card_orbit_S (S T : Subgroup G) :
    Nat.card ((fun a => conjSubgroup a S) '' (Subgroup.normalizer (T : Set G) : Set G)) =
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)).relIndex
        (Subgroup.normalizer (T : Set G)) :=
  natCard_image_eq_relIndex _ fun _ ha _ ha' => conj_eq_iff_mem_normalizer ha ha'

theorem card_orbit_t (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    Nat.card ((fun a => a * t * a⁻¹) '' (Subgroup.normalizer (T : Set G) : Set G)) =
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)).relIndex
        (Subgroup.normalizer (T : Set G)) :=
  natCard_image_eq_relIndex _ fun _ ha _ ha' => d.conj_t_eq_iff hT ha ha'

theorem conj_eq_iff_conj_t_eq (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) {a a' : G}
    (ha : a ∈ Subgroup.normalizer (T : Set G)) (ha' : a' ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup a S = conjSubgroup a' S ↔ a * t * a⁻¹ = a' * t * a'⁻¹ :=
  (conj_eq_iff_mem_normalizer ha ha').trans (d.conj_t_eq_iff hT ha ha').symm

theorem conj_t_mem (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    {a : G} (ha : a ∈ Subgroup.normalizer (T : Set G)) :
    a * t * a⁻¹ ∈ T ∧ ∀ x ∈ T, (a * t * a⁻¹) * x = x * (a * t * a⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp ha t).mp (d.S_le_T hT d.t_mem), fun x hx => ?_⟩
  have hx' : a⁻¹ * x * a ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem ha) x).mp hx
    simpa using this
  have hc := d.t_central hT (a⁻¹ * x * a) hx'
  calc a * t * a⁻¹ * x = a * (t * (a⁻¹ * x * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * x * a) * t) * a⁻¹ := by rw [hc]
    _ = x * (a * t * a⁻¹) := by group

theorem T_sylow_B (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    IsSylow2Of T (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)) := by
  have hTB : T ≤ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) :=
    le_inf hT.1 Subgroup.le_normalizer
  exact ⟨hTB, hT.2.1, fun P' hP'B hP'2 hle =>
    (d.T_sylow_H hT).2.2 P' (fun x hx => d.M_le_C (hP'B hx).1) hP'2 hle⟩

omit [Finite G] in
theorem card_normalizer_T (S T : Subgroup G) : Nat.card (Subgroup.normalizer (T : Set G)) =
    Nat.card (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) *
      (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)).relIndex
        (Subgroup.normalizer (T : Set G)) := by
  have := Subgroup.card_mul_index ((Subgroup.normalizer (S : Set G) ⊓
    Subgroup.normalizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at this
  exact this.symm

theorem sylow_top_iff_odd (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) : IsSylow2Of T ⊤ ↔ Odd
    ((Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)).relIndex
      (Subgroup.normalizer (T : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := (d.T_sylow_B hT).card_eq
  have hA := card_normalizer_T S T
  set B := Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G) with hBdef
  set A := Subgroup.normalizer (T : Set G) with hAdef
  have hr : B.relIndex A ≠ 0 := by
    intro h
    rw [h, mul_zero] at hA
    exact Nat.card_pos.ne' hA
  have hf : (Nat.card A).factorization 2 =
      (Nat.card B).factorization 2 + (B.relIndex A).factorization 2 := by
    rw [hA, Nat.factorization_mul Nat.card_pos.ne' hr]
    rfl
  constructor
  · intro hTtop
    obtain ⟨P, hP, hTP⟩ := exists_isSylow2Of_ge hT.2.1 (Subgroup.le_normalizer : T ≤ A)
    have h1 : Nat.card P = 2 ^ (Nat.card A).factorization 2 := hP.card_eq
    have h2 : Nat.card P ≤ Nat.card T := by
      have := card_le_of_isPGroup_le hP.2.1 (le_top : P ≤ ⊤)
      rwa [← hTtop.card_eq] at this
    have h3 : Nat.card T ≤ Nat.card P := Subgroup.card_le_of_le hTP
    have h4 : 2 ^ (Nat.card A).factorization 2 = 2 ^ (Nat.card B).factorization 2 := by
      rw [← h1, ← hB]
      exact le_antisymm h2 h3
    have h5 := Nat.pow_right_injective (le_refl 2) h4
    have h6 : (B.relIndex A).factorization 2 = 0 := by omega
    rw [Nat.odd_iff]
    by_contra hcon
    have hdvd : 2 ∣ B.relIndex A := by omega
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hr hdvd
    omega
  · intro hodd
    have hnd : ¬ 2 ∣ B.relIndex A := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have h0 : (B.relIndex A).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    have hAB : (Nat.card A).factorization 2 = (Nat.card B).factorization 2 := by
      rw [hf, h0]
      rfl
    obtain ⟨U, hU, hTU⟩ := exists_isSylow2Of_ge hT.2.1 (le_top : T ≤ ⊤)
    by_cases hTU' : T = U
    · rw [hTU']
      exact hU
    · exfalso
      obtain ⟨s, hsU, hsN, hsT⟩ := exists_mem_normalizer_not_mem (p := 2) hU.2.1 hTU hTU'
      have hzs : Subgroup.zpowers s ≤ A := (Subgroup.zpowers_le).mpr hsN
      have hP2 : IsPGroup 2 (T ⊔ Subgroup.zpowers s : Subgroup G) :=
        IsPGroup.to_sup_of_normal_left' hT.2.1 (hU.2.1.to_le ((Subgroup.zpowers_le).mpr hsU)) hzs
      have hPA : T ⊔ Subgroup.zpowers s ≤ A := sup_le Subgroup.le_normalizer hzs
      have h1 := card_le_of_isPGroup_le hP2 hPA
      rw [hAB, ← hB] at h1
      have h2 : T ⊔ Subgroup.zpowers s = T :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left h1).symm
      exact hsT (h2 ▸ (le_sup_right : Subgroup.zpowers s ≤ T ⊔ Subgroup.zpowers s)
        (Subgroup.mem_zpowers s))

end Criterion

section Escape

variable [Finite G]

omit [Finite G] in
theorem mul_comm_of_comm {a b y : G} (ha : a * y = y * a) (hb : b * y = y * b) :
    (a * b) * y = y * (a * b) := by
  calc (a * b) * y = a * (b * y) := mul_assoc a b y
    _ = a * (y * b) := by rw [hb]
    _ = (a * y) * b := (mul_assoc a y b).symm
    _ = (y * a) * b := by rw [ha]
    _ = y * (a * b) := mul_assoc y a b


theorem x_not_mem_C (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x ∉ Subgroup.centralizer ({t} : Set G) := by
  intro hx
  have h := (d.T_sylow_H hT).2.2 (U ⊓ Subgroup.centralizer ({t} : Set G)) inf_le_right
    (e.two.to_le inf_le_left) (le_inf e.le (d.T_le_C hT))
  have hxU : x ∈ U ⊓ Subgroup.centralizer ({t} : Set G) := ⟨e.mem, hx⟩
  rw [h] at hxU
  exact e.not_mem hxU

theorem t₁_ne (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x * t * x⁻¹ ≠ t := by
  intro h
  apply d.x_not_mem_C hT e
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  calc y * x = (x * y * x⁻¹) * x := by rw [h]
    _ = x * y := by group

omit [Finite G] in
theorem orderOf_t₁ (d : OddByQuat R S t) (x : G) : orderOf (x * t * x⁻¹) = 2 := by
  have := (MulAut.conj x).orderOf_eq t
  rw [MulAut.conj_apply] at this
  rw [this]
  exact d.t_ord

theorem conj_t₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : x * (x * t * x⁻¹) * x⁻¹ = t := by
  have hxxT : (x * x) * t = t * (x * x) := (d.t_central hT (x * x) e.sq_mem).symm
  calc x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by group
    _ = t := by rw [hxxT]; group

omit [Finite G] in
theorem T_le_normalizer_S₁ (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : T ≤ Subgroup.normalizer ((conjSubgroup x S : Subgroup G) : Set G) := by
  intro y hy
  rw [← conjSubgroup_eq_self_iff]
  have hy' : x⁻¹ * y * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem
      e.normalizes) y).mp hy
    simpa using this
  have h1 : conjSubgroup y (conjSubgroup x S) = conjSubgroup x (conjSubgroup (x⁻¹ * y * x) S) := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [h1, conjSubgroup_eq_self_iff.mpr (hT.1 hy')]

theorem S₁_le_T (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : conjSubgroup x S ≤ T := by
  have := conjSubgroup_mono (g := x) (d.S_le_T hT)
  rwa [conjSubgroup_eq_self_iff.mpr e.normalizes] at this

omit [Finite G] in
theorem unique_S₁ (d : OddByQuat R S t) (x : G) :
    ∀ y ∈ conjSubgroup x S, orderOf y = 2 → y = x * t * x⁻¹ := by
  intro y hy hy2
  have hy' : x⁻¹ * y * x ∈ S := mem_conjSubgroup_iff.mp hy
  have h2 : orderOf (x⁻¹ * y * x) = 2 := by
    have := (MulAut.conj x⁻¹).orderOf_eq y
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this]
    exact hy2
  have h3 := d.unique _ hy' h2
  calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    _ = x * t * x⁻¹ := by rw [h3]

theorem inf_S_S₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : S ⊓ conjSubgroup x S = ⊥ := by
  by_contra h
  have ht : t ∈ S ⊓ conjSubgroup x S := d.t_mem_of_ne_bot inf_le_left h
  exact d.t₁_ne hT e (d.unique_S₁ x t ht.2 d.t_ord).symm

theorem commute_S_S₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : ∀ a ∈ S, ∀ b ∈ conjSubgroup x S, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ conjSubgroup x S := by
    have := (Subgroup.mem_normalizer_iff.mp
      (T_le_normalizer_S₁ hT e (d.S_le_T hT ha)) b).mp hb
    exact (conjSubgroup x S).mul_mem this ((conjSubgroup x S).inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ S := by
    have e' : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e']
    have := (Subgroup.mem_normalizer_iff.mp (hT.1 (d.S₁_le_T hT e hb)) a⁻¹).mp (S.inv_mem ha)
    exact S.mul_mem ha this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ S ⊓ conjSubgroup x S := ⟨h2, h1⟩
  rw [d.inf_S_S₁ hT e, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem card_sq_le_card_T (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    Nat.card S * Nat.card S ≤ Nat.card T := by
  have hS₁N : conjSubgroup x S ≤ Subgroup.normalizer (S : Set G) :=
    (d.S₁_le_T hT e).trans hT.1
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left S (conjSubgroup x S) hS₁N
  have hQ : Nat.card (S ⊔ conjSubgroup x S : Subgroup G) =
      Nat.card S * Nat.card (conjSubgroup x S) := by
    refine natCard_eq_mul_of_inf_eq_bot le_sup_left le_sup_right (d.inf_S_S₁ hT e) fun m hm => ?_
    have h1 : m ∈ ((S ⊔ conjSubgroup x S : Subgroup G) : Set G) := hm
    rw [hmul] at h1
    obtain ⟨a, ha, b, hb, rfl⟩ := h1
    exact ⟨a, ha, b, hb, rfl⟩
  have hle : Nat.card (S ⊔ conjSubgroup x S : Subgroup G) ≤ Nat.card T :=
    Subgroup.card_le_of_le (sup_le (d.S_le_T hT) (d.S₁_le_T hT e))
  rw [hQ, card_conjSubgroup] at hle
  exact hle

theorem nonempty_mulEquiv_S_S₁ (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    Nonempty ((S ⊔ conjSubgroup x S : Subgroup G) ≃* S × conjSubgroup x S) := by
  have hS₁N : conjSubgroup x S ≤ Subgroup.normalizer (S : Set G) :=
    (d.S₁_le_T hT e).trans hT.1
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left S (conjSubgroup x S) hS₁N
  refine nonempty_mulEquiv_prod le_sup_left le_sup_right (d.inf_S_S₁ hT e)
    (d.commute_S_S₁ hT e) fun m hm => ?_
  have h1 : m ∈ ((S ⊔ conjSubgroup x S : Subgroup G) : Set G) := hm
  rw [hmul] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite G] in
theorem mem_W (e : Escape T U x) {w : G} (hw : w ∈ T ⊔ Subgroup.zpowers x) :
    w ∈ T ∨ ∃ y ∈ T, w = y * x := by
  have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.zpowers_le).mpr e.normalizes
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers x) hxn
  have h1 : w ∈ ((T ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hw
  rw [hmul] at h1
  obtain ⟨y, hy, z, hz, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have key : ∀ k : ℤ, x ^ k ∈ T ∨ ∃ y' ∈ T, x ^ k = y' * x := by
    intro k
    induction k using Int.induction_on with
    | zero => exact Or.inl (by simp)
    | succ n ih =>
      rcases ih with h | ⟨y', hy', h⟩
      · exact Or.inr ⟨x ^ (n : ℤ), h, zpow_add_one x n⟩
      · left
        rw [zpow_add_one, h, mul_assoc]
        exact T.mul_mem hy' e.sq_mem
    | pred n ih =>
      rcases ih with h | ⟨y', hy', h⟩
      · right
        refine ⟨x ^ (-(n : ℤ)) * (x * x)⁻¹, T.mul_mem h (T.inv_mem e.sq_mem), ?_⟩
        rw [zpow_sub_one]
        group
      · left
        rw [zpow_sub_one, h]
        simpa using hy'
  rcases key k with h | ⟨y', hy', h⟩
  · exact Or.inl (T.mul_mem hy h)
  · exact Or.inr ⟨y * y', T.mul_mem hy hy', by rw [h]; group⟩

omit [Finite G] in
theorem relIndex_W (e : Escape T U x) : T.relIndex (T ⊔ Subgroup.zpowers x) = 2 := by
  have hxW : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    Nat.card_eq_two_iff' (QuotientGroup.mk (1 : (T ⊔ Subgroup.zpowers x : Subgroup G)) :
      (T ⊔ Subgroup.zpowers x : Subgroup G) ⧸ T.subgroupOf (T ⊔ Subgroup.zpowers x))]
  refine ⟨QuotientGroup.mk ⟨x, hxW⟩, ?_, ?_⟩
  · intro h
    rw [QuotientGroup.eq] at h
    have h1 : (x⁻¹ * 1 : G) ∈ T := h
    simp only [mul_one] at h1
    exact e.not_mem (by simpa using T.inv_mem h1)
  · intro z hz
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective z
    rcases mem_W e hw with h | ⟨y, hy, rfl⟩
    · exfalso
      apply hz
      rw [QuotientGroup.eq]
      show ((w⁻¹ * 1 : G)) ∈ T
      simpa using T.inv_mem h
    · rw [QuotientGroup.eq]
      show ((y * x)⁻¹ * x : G) ∈ T
      have h1 : (y * x)⁻¹ * x = x⁻¹ * y⁻¹ * x := by group
      rw [h1]
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem
        e.normalizes) y⁻¹).mp (T.inv_mem hy)
      simpa using this

omit [Finite G] in
theorem card_W (e : Escape T U x) :
    Nat.card (T ⊔ Subgroup.zpowers x : Subgroup G) = 2 * Nat.card T := by
  have h := Subgroup.card_mul_index (T.subgroupOf (T ⊔ Subgroup.zpowers x))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (le_sup_left : T ≤ T ⊔ Subgroup.zpowers x)).toEquiv] at h
  have h2 := relIndex_W e
  rw [Subgroup.relIndex] at h2
  rw [h2] at h
  rw [← h]
  ring

omit [Finite G] in
theorem W_two (e : Escape T U x) : IsPGroup 2 (T ⊔ Subgroup.zpowers x : Subgroup G) :=
  e.two.to_le (sup_le e.le ((Subgroup.zpowers_le).mpr e.mem))

omit [Finite G] in
theorem W_le_normalizer_Q (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    T ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer ((S ⊔ conjSubgroup x S : Subgroup G) : Set G) := by
  have hTS : ∀ y ∈ T, conjSubgroup y S = S := fun y hy => conjSubgroup_eq_self_iff.mpr (hT.1 hy)
  have hTS₁ : ∀ y ∈ T, conjSubgroup y (conjSubgroup x S) = conjSubgroup x S := fun y hy =>
    conjSubgroup_eq_self_iff.mpr (T_le_normalizer_S₁ hT e hy)
  have hxS₁ : conjSubgroup x (conjSubgroup x S) = S := by
    rw [conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_self_iff.mpr (hT.1 e.sq_mem)
  refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).mpr ?_)
  · rw [← conjSubgroup_eq_self_iff, conjSubgroup, Subgroup.map_sup]
    have h1 := hTS y hy
    have h2 := hTS₁ y hy
    unfold conjSubgroup at h1 h2
    rw [h1, h2]
  · rw [← conjSubgroup_eq_self_iff, conjSubgroup, Subgroup.map_sup]
    have h2 : (Subgroup.map (MulAut.conj x).toMonoidHom S) = conjSubgroup x S := rfl
    have h3 : (Subgroup.map (MulAut.conj x).toMonoidHom (conjSubgroup x S)) = S := hxS₁
    rw [h2, h3, sup_comm]

theorem c_central (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    T ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) := by
  have hT₁ := d.conj_t_mem hT e.normalizes
  have hcT : ∀ y ∈ T, y * (t * (x * t * x⁻¹)) = (t * (x * t * x⁻¹)) * y := fun y hy =>
    (mul_comm_of_comm (d.t_central hT y hy) (hT₁.2 y hy)).symm
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) :=
    (d.t_central hT _ hT₁.1).symm
  refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcT y hy).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hx1 := d.conj_t₁ hT e
    have hxc : x * (t * (x * t * x⁻¹)) * x⁻¹ = t * (x * t * x⁻¹) := by
      calc x * (t * (x * t * x⁻¹)) * x⁻¹ = (x * t * x⁻¹) * (x * (x * t * x⁻¹) * x⁻¹) := by group
        _ = (x * t * x⁻¹) * t := by rw [hx1]
        _ = t * (x * t * x⁻¹) := hcomm
    exact (mul_inv_eq_iff_eq_mul.mp hxc).symm

theorem orderOf_c (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : orderOf (t * (x * t * x⁻¹)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁ := d.conj_t_mem hT e.normalizes
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) := (d.t_central hT _ hT₁.1).symm
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [d.t_ord, pow_two] at this
  have ht₁2 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  apply orderOf_eq_prime
  · rw [pow_two]
    calc t * (x * t * x⁻¹) * (t * (x * t * x⁻¹)) = t * ((x * t * x⁻¹) * t) * (x * t * x⁻¹) := by
          group
      _ = t * (t * (x * t * x⁻¹)) * (x * t * x⁻¹) := by rw [hcomm]
      _ = (t * t) * ((x * t * x⁻¹) * (x * t * x⁻¹)) := by group
      _ = 1 := by rw [ht2, ht₁2]; group
  · intro h
    apply d.t₁_ne hT e
    have h1 : x * t * x⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right ht2

theorem inf_C_W_t (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    (T ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({t} : Set G) = T := by
  refine le_antisymm (fun w hw => ?_) (le_inf le_sup_left (d.T_le_C hT))
  rcases mem_W e hw.1 with h | ⟨y, hy, rfl⟩
  · exact h
  · exfalso
    have hc := Subgroup.mem_centralizer_iff.mp hw.2 t rfl
    have h1 : (y * x) * t * (y * x)⁻¹ = t := by
      calc (y * x) * t * (y * x)⁻¹ = (t * (y * x)) * (y * x)⁻¹ := by rw [← hc]
        _ = t := by group
    have h2 : (y * x) * t * (y * x)⁻¹ = x * t * x⁻¹ := by
      have := (d.conj_t_mem hT e.normalizes).2 y⁻¹ (T.inv_mem hy)
      calc (y * x) * t * (y * x)⁻¹ = y * (x * t * x⁻¹) * y⁻¹ := by group
        _ = y * ((x * t * x⁻¹) * y⁻¹) := by rw [mul_assoc]
        _ = y * (y⁻¹ * (x * t * x⁻¹)) := by rw [this]
        _ = x * t * x⁻¹ := by group
    exact d.t₁_ne hT e (h2.symm.trans h1)

theorem inf_C_W_t₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    (T ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G) = T := by
  refine le_antisymm (fun w hw => ?_) (le_inf le_sup_left ?_)
  · rcases mem_W e hw.1 with h | ⟨y, hy, rfl⟩
    · exact h
    · exfalso
      have hc := Subgroup.mem_centralizer_iff.mp hw.2 (x * t * x⁻¹) rfl
      have h1 : (y * x) * (x * t * x⁻¹) * (y * x)⁻¹ = x * t * x⁻¹ := by
        calc (y * x) * (x * t * x⁻¹) * (y * x)⁻¹ = ((x * t * x⁻¹) * (y * x)) * (y * x)⁻¹ := by
              rw [← hc]
          _ = x * t * x⁻¹ := by group
      have h2 : (y * x) * (x * t * x⁻¹) * (y * x)⁻¹ = t := by
        have := d.t_central hT y⁻¹ (T.inv_mem hy)
        calc (y * x) * (x * t * x⁻¹) * (y * x)⁻¹ = y * (x * (x * t * x⁻¹) * x⁻¹) * y⁻¹ := by group
          _ = y * t * y⁻¹ := by rw [d.conj_t₁ hT e]
          _ = y * (t * y⁻¹) := by rw [mul_assoc]
          _ = y * (y⁻¹ * t) := by rw [this]
          _ = t := by group
      exact d.t₁_ne hT e (h1.symm.trans h2)
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact ((d.conj_t_mem hT e.normalizes).2 y hy)

theorem two_part_lt (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    2 ^ (Nat.card (Subgroup.centralizer ({t} : Set G))).factorization 2 <
      2 ^ (Nat.card (Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G))).factorization 2 := by
  have h1 := (d.T_sylow_H hT).card_eq
  rw [← h1]
  have h2 := card_le_of_isPGroup_le (W_two e) (d.c_central hT e)
  rw [card_W e] at h2
  have : 0 < Nat.card T := Nat.card_pos
  omega

theorem not_isConj (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : ¬ IsConj t (t * (x * t * x⁻¹)) := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have h1 := d.two_part_lt hT e
  rw [← hg, natCard_centralizer_conj] at h1
  exact lt_irrefl _ h1

theorem centralizer_c_ne_top [IsSimpleGroup G] (hnc : ¬ ∀ a b : G, a * b = b * a)
    (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) ≠ ⊤ :=
  centralizer_ne_top_of_simple hnc fun h => by
    have := d.orderOf_c hT e
    rw [h, orderOf_one] at this
    omega

theorem sylow_top_of_card_lt (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (hlt : Nat.card T < Nat.card S * Nat.card S) : IsSylow2Of T ⊤ := by
  by_contra hnot
  obtain ⟨U, hU, hTU⟩ := exists_isSylow2Of_ge hT.2.1 (le_top : T ≤ ⊤)
  have hne : T ≠ U := fun h => hnot (by rw [h]; exact hU)
  obtain ⟨x, hxU, hxN, hxT, hxx⟩ := exists_mem_normalizer_not_mem_sq_mem hU.2.1 hTU hne
  exact absurd (d.card_sq_le_card_T hT ⟨hU.2.1, hTU, hxU, hxN, hxT, hxx⟩) (not_le.mpr hlt)

theorem sylow_top_of_characteristic (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (hchar : (S.subgroupOf T).Characteristic) : IsSylow2Of T ⊤ := by
  rw [d.sylow_top_iff_odd hT]
  have hAB : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    refine le_normalizer_of_conj_mem fun a ha s hs => ?_
    let α : MulAut T := Subgroup.normalizerMonoidHom T ⟨a, ha⟩
    have hα := Subgroup.characteristic_iff_map_eq.mp hchar α
    have hsT : s ∈ T := d.S_le_T hT hs
    have : α ⟨s, hsT⟩ ∈ S.subgroupOf T := by
      rw [← hα]
      exact ⟨⟨s, hsT⟩, hs, rfl⟩
    exact this
  have h1 : (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (T : Set G)).relIndex
      (Subgroup.normalizer (T : Set G)) = 1 :=
    Subgroup.relIndex_eq_one.mpr (le_inf hAB le_rfl)
  rw [h1]
  exact odd_one

end Escape

end OddByQuat

end CFSG.ClassicalInvolution
