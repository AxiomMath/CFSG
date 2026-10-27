module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.PU3.Pack

open Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

theorem even_card_of_nonabelian_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Even (Nat.card G) := by
  by_contra hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem subsingleton_of_odd_perfect {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (h : Odd (Nat.card G)) : Subsingleton G := by
  by_contra hns
  have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hns
  exact Group.IsPerfect.not_isSolvable G (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)

theorem map_eq_bot_of_odd_card {Y V : Type*} [Group Y] [Finite Y] [Group V] [IsSimpleGroup V]
    (hV : Even (Nat.card V)) (g : Y →* V) (hg : Function.Surjective g) (K : Subgroup Y)
    [K.Normal] (hK : Odd (Nat.card K)) : K.map g = ⊥ := by
  have : (K.map g).Normal := ‹K.Normal›.map g hg
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.map g) with h | h
  · exact h
  · exfalso
    have h1 : Nat.card (K.map g) = Nat.card V := by rw [h]; exact Subgroup.card_top
    have h2 : Odd (Nat.card (K.map g)) := hK.of_dvd_nat (Subgroup.card_map_dvd K g)
    rw [h1] at h2
    exact (Nat.not_even_iff_odd.2 h2) hV

theorem surj_or_trivial {Y U S : Type*} [Group Y] [Finite Y] [Group U] [Finite U] [Group S]
    [IsSimpleGroup S] [Group.IsPerfect Y] (θ : Y →* S) (hθ : Function.Surjective θ)
    (hodd : Odd (Nat.card θ.ker)) (g : Y →* U) (hcard : Nat.card U ≤ Nat.card S) :
    (g.range = ⊤ ∧ g.ker ≤ θ.ker) ∨ g.range = ⊥ := by
  have hN : (g.ker.map θ).Normal := (MonoidHom.normal_ker g).map θ hθ
  rcases Subgroup.Normal.eq_bot_or_eq_top (g.ker.map θ) with h | h
  · left
    have hle : g.ker ≤ θ.ker := (Subgroup.map_eq_bot_iff _).1 h
    refine ⟨Subgroup.eq_top_of_card_eq _ ?_, hle⟩
    have h1 : Nat.card g.ker * Nat.card g.range = Nat.card Y := by
      have := Subgroup.card_mul_index g.ker
      rwa [Subgroup.index_ker] at this
    have h2 : Nat.card θ.ker * Nat.card S = Nat.card Y := by
      have := Subgroup.card_mul_index θ.ker
      rwa [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective θ hθ,
        Subgroup.card_top] at this
    have h3 : Nat.card g.ker ≤ Nat.card θ.ker := Subgroup.card_le_of_le hle
    have h4 : Nat.card g.range ≤ Nat.card U := Subgroup.card_le_card_group _
    have h5 : Nat.card S ≤ Nat.card g.range := by
      have hpos : 0 < Nat.card g.ker := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : Nat.card g.ker * Nat.card g.range < Nat.card θ.ker * Nat.card S :=
        calc _ < Nat.card g.ker * Nat.card S := Nat.mul_lt_mul_of_pos_left hlt hpos
          _ ≤ _ := Nat.mul_le_mul_right _ h3
      omega
    omega
  · right
    have hrange : g.range = θ.ker.map g := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        have hy : θ y ∈ g.ker.map θ := by rw [h]; trivial
        obtain ⟨k, hk, hky⟩ := hy
        refine ⟨k⁻¹ * y, ?_, ?_⟩
        · show θ (k⁻¹ * y) = 1
          rw [map_mul, map_inv, hky, inv_mul_cancel]
        · have hk' : g k = 1 := hk
          rw [map_mul, map_inv, hk', inv_one, one_mul]
      · rintro ⟨r, -, rfl⟩
        exact ⟨r, rfl⟩
    have hperf : Group.IsPerfect g.range := Group.IsPerfect.range g
    have hodd' : Odd (Nat.card g.range) := by
      rw [hrange]
      exact hodd.of_dvd_nat (Subgroup.card_map_dvd θ.ker g)
    have := subsingleton_of_odd_perfect hodd'
    exact Subgroup.eq_bot_of_subsingleton _

variable {X : Type*} [Group X] [Finite X]

@[expose] def NonabSimple (A : Subgroup X) : Prop :=
  IsSimpleGroup ↥A ∧ ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a

@[expose] def IsDiag (A B Y : Subgroup X) : Prop :=
  (∀ a ∈ A, ∃ y ∈ Y, ∃ b ∈ B, y = a * b) ∧ (∀ b ∈ B, ∃ y ∈ Y, ∃ a ∈ A, y = a * b) ∧
    Y ⊓ A = ⊥ ∧ Y ⊓ B = ⊥

section Product

variable {A B : Subgroup X}

omit [Finite X] in
theorem NonabSimple.eq_one_of_central {A : Subgroup X} (hA : NonabSimple A) {a : X} (ha : a ∈ A)
    (hc : ∀ x ∈ A, a * x = x * a) : a = 1 := by
  have := hA.1
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥A) with h | h
  · have : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · obtain ⟨a', ha', b', hb', hne⟩ := hA.2
    have : (⟨a', ha'⟩ : ↥A) ∈ Subgroup.center ↥A := by rw [h]; trivial
    rw [Subgroup.mem_center_iff] at this
    exact absurd (congrArg Subtype.val (this ⟨b', hb'⟩)).symm hne

theorem NonabSimple.even_card {A : Subgroup X} (hA : NonabSimple A) : Even (Nat.card ↥A) := by
  have := hA.1
  obtain ⟨a, ha, b, hb, h⟩ := hA.2
  exact even_card_of_nonabelian_simple ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => h (congrArg Subtype.val h')⟩

omit [Finite X] in
theorem inf_eq_bot_of_commute (hA : NonabSimple A) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact hA.eq_one_of_central hx.1 fun a ha => (hcomm a ha x hx.2).symm

omit [Finite X] in
theorem exists_mul_of_mem_sup (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {u : X}
    (hu : u ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, u = a * b := by
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype
    (fun (a : ↥A) (b : ↥B) => hcomm a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange] at hu
  obtain ⟨⟨a, b⟩, rfl⟩ := hu
  exact ⟨a, a.2, b, b.2, rfl⟩

omit [Finite X] in
theorem exists_prod_lift (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {Y : Type*} [Group Y] (f : Y →* X) (hf : f.range ≤ A ⊔ B) :
    ∃ F : Y →* ↥A × ↥B, ∀ y, ((F y).1 : X) * ((F y).2 : X) = f y := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  obtain ⟨e, he⟩ : ∃ e : ↥A × ↥B →* X, e = A.subtype.noncommCoprod B.subtype hc := ⟨_, rfl⟩
  have hinj : Function.Injective e := by
    rw [he, MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hAB
  have hrange : e.range = A ⊔ B := by
    rw [he, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have happ : ∀ p : ↥A × ↥B, e p = (p.1 : X) * (p.2 : X) := by
    intro p
    rw [he]
    rfl
  have hmem : ∀ y, f y ∈ e.range := fun y => hrange ▸ hf ⟨y, rfl⟩
  refine ⟨((MonoidHom.ofInjective hinj).symm : e.range ≃* ↥A × ↥B).toMonoidHom.comp
    (f.codRestrict e.range hmem), fun y => ?_⟩
  have h := MonoidHom.apply_ofInjective_symm hinj ⟨f y, hmem y⟩
  rw [happ] at h
  exact h

omit [Finite X] in
theorem IsDiag.cov_right {A B Y : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hY : IsDiag A B Y) : ∀ b ∈ B, ∃ y ∈ Y, ∃ a ∈ A, y = b * a := by
  intro b hb
  obtain ⟨y, hy, a, ha, rfl⟩ := hY.2.1 b hb
  exact ⟨a * b, hy, a, ha, hcomm a ha b hb⟩

end Product

section Perfect

omit [Finite X] in
theorem map_conj_mul_eq (A : Subgroup X) (x y : X) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {A : Subgroup X} {x : X}
    (h : A.map (MulAut.conj x).toMonoidHom = A) : x ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← h]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  · intro ha
    rw [← h] at ha
    obtain ⟨a', ha', h'⟩ := ha
    have : a' = a := by simpa [MulAut.conj_apply] using h'
    rwa [← this]

omit [Finite X] in
theorem exists_parity_hom {A B : Subgroup X} (hAB : A ≠ B)
    (hperm : ∀ x : X,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A)) :
    ∃ ε : X →* Multiplicative (ZMod 2), ∀ x, ε x = 1 →
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) := by
  classical
  let ε : X → Multiplicative (ZMod 2) := fun x =>
    if A.map (MulAut.conj x).toMonoidHom = A then 1 else Multiplicative.ofAdd 1
  have hsw : ∀ x, A.map (MulAut.conj x).toMonoidHom ≠ A →
      A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A := by
    intro x hx
    rcases hperm x with h | h
    · exact absurd h.1 hx
    · exact h
  have hpres : ∀ x, A.map (MulAut.conj x).toMonoidHom = A →
      B.map (MulAut.conj x).toMonoidHom = B := by
    intro x hx
    rcases hperm x with h | h
    · exact h.2
    · exact absurd (hx.symm.trans h.1) hAB
  have hε1 : ∀ x, A.map (MulAut.conj x).toMonoidHom = A → ε x = 1 :=
    fun x hx => ite_eq_left hx
  have hε2 : ∀ x, A.map (MulAut.conj x).toMonoidHom ≠ A → ε x = Multiplicative.ofAdd 1 :=
    fun x hx => ite_eq_right hx
  have hne : B ≠ A := fun h => hAB h.symm
  have hmul : ∀ x y, ε (x * y) = ε x * ε y := by
    intro x y
    by_cases hx : A.map (MulAut.conj x).toMonoidHom = A <;>
      by_cases hy : A.map (MulAut.conj y).toMonoidHom = A
    · have hxy : A.map (MulAut.conj (x * y)).toMonoidHom = A := by
        rw [map_conj_mul_eq, hy, hx]
      rw [hε1 _ hxy, hε1 _ hx, hε1 _ hy, mul_one]
    · obtain ⟨hy1, -⟩ := hsw y hy
      have hxy : A.map (MulAut.conj (x * y)).toMonoidHom ≠ A := by
        rw [map_conj_mul_eq, hy1, hpres x hx]
        exact hne
      rw [hε2 _ hxy, hε1 _ hx, hε2 _ hy, one_mul]
    · obtain ⟨hx1, -⟩ := hsw x hx
      have hxy : A.map (MulAut.conj (x * y)).toMonoidHom ≠ A := by
        rw [map_conj_mul_eq, hy, hx1]
        exact hne
      rw [hε2 _ hxy, hε2 _ hx, hε1 _ hy, mul_one]
    · obtain ⟨-, hx2⟩ := hsw x hx
      obtain ⟨hy1, -⟩ := hsw y hy
      have hxy : A.map (MulAut.conj (x * y)).toMonoidHom = A := by
        rw [map_conj_mul_eq, hy1, hx2]
      rw [hε1 _ hxy, hε2 _ hx, hε2 _ hy]
      decide
  refine ⟨MonoidHom.mk' ε hmul, fun x hx => ?_⟩
  by_cases h : A.map (MulAut.conj x).toMonoidHom = A
  · exact ⟨h, hpres x h⟩
  · exfalso
    have h1 : ε x = 1 := hx
    rw [hε2 x h] at h1
    exact absurd h1 (by decide)

omit [Finite X] in
theorem exists_inner_of_perfect {I Y : Subgroup X} (hY : ⁅Y, Y⁆ = Y)
    (hYN : Y ≤ Subgroup.normalizer (I : Set X)) (hOut : Group.IsSolvable (Outer ↥I)) :
    ∀ y ∈ Y, ∃ i ∈ I, ∀ x ∈ I, y * x * y⁻¹ = i * x * i⁻¹ := by
  classical
  have hZ : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  let ψ : ↥Y →* Outer ↥I :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥I)).comp
      ((I.normalizerMonoidHom).comp (Subgroup.inclusion hYN))
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsolv : Group.IsSolvable ↥ψ.range := inferInstance
  have htriv : ∀ z : ↥Y, ψ z = 1 := by
    intro z
    by_contra hz
    have : Nontrivial ↥ψ.range :=
      ⟨⟨⟨ψ z, z, rfl⟩, 1, fun h => hz (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) hsolv
  intro z hz
  have h1 : ψ ⟨z, hz⟩ = 1 := htriv ⟨z, hz⟩
  have h2 : (I.normalizerMonoidHom ⟨z, hYN hz⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥I :=
    (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨i, hi⟩ := h2
  refine ⟨i, i.2, fun x hx => ?_⟩
  have := congrArg (fun a : MulAut ↥I => ((a ⟨x, hx⟩ : ↥I) : X)) hi
  simpa using this.symm

omit [Finite X] in
theorem perfect_le_sup {A B : Subgroup X} (hA : NonabSimple A) (hB : NonabSimple B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hperm : ∀ x : X,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A))
    (hcent : ∀ x : X, (∀ a ∈ A, x * a = a * x) → (∀ b ∈ B, x * b = b * x) → x = 1)
    (hOA : Group.IsSolvable (Outer ↥A)) (hOB : Group.IsSolvable (Outer ↥B))
    {Y : Subgroup X} (hY : ⁅Y, Y⁆ = Y) : Y ≤ A ⊔ B := by
  have hAB : A ≠ B := by
    rintro rfl
    obtain ⟨a, ha, b, hb, hne⟩ := hA.2
    exact hne (hcomm a ha b hb)
  obtain ⟨ε, hε⟩ := exists_parity_hom hAB hperm
  have hYε : Y ≤ ε.ker := by
    have : ⁅Y, Y⁆ ≤ ε.ker := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    rwa [hY] at this
  have hYA : Y ≤ Subgroup.normalizer (A : Set X) := fun y hy =>
    mem_normalizer_of_map_conj_eq (hε y (hYε hy)).1
  have hYB : Y ≤ Subgroup.normalizer (B : Set X) := fun y hy =>
    mem_normalizer_of_map_conj_eq (hε y (hYε hy)).2
  intro y hy
  obtain ⟨a, ha, haconj⟩ := exists_inner_of_perfect hY hYA hOA y hy
  obtain ⟨b, hb, hbconj⟩ := exists_inner_of_perfect hY hYB hOB y hy
  have hab : Commute a b := hcomm a ha b hb
  have hc : (a * b)⁻¹ * y = 1 := by
    refine hcent _ (fun x hx => ?_) (fun x hx => ?_)
    · have hyx : y * x = a * x * a⁻¹ * y :=
        calc y * x = (y * x * y⁻¹) * y := by group
          _ = a * x * a⁻¹ * y := by rw [haconj x hx]
      have hbx : x * b⁻¹ = b⁻¹ * x := (Commute.inv_right (hcomm x hx b hb : Commute x b)).eq
      calc (a * b)⁻¹ * y * x = b⁻¹ * a⁻¹ * (y * x) := by group
        _ = b⁻¹ * a⁻¹ * (a * x * a⁻¹ * y) := by rw [hyx]
        _ = (b⁻¹ * x) * a⁻¹ * y := by group
        _ = (x * b⁻¹) * a⁻¹ * y := by rw [hbx]
        _ = x * ((a * b)⁻¹ * y) := by group
    · have hyx : y * x = b * x * b⁻¹ * y :=
        calc y * x = (y * x * y⁻¹) * y := by group
          _ = b * x * b⁻¹ * y := by rw [hbconj x hx]
      have hax : a⁻¹ * x = x * a⁻¹ := (Commute.inv_left (hcomm a ha x hx : Commute a x)).eq
      have hab1 : a⁻¹ * b = b * a⁻¹ := hab.inv_left.eq
      have hab2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := hab.inv_inv.eq
      calc (a * b)⁻¹ * y * x = b⁻¹ * a⁻¹ * (y * x) := by group
        _ = b⁻¹ * a⁻¹ * (b * x * b⁻¹ * y) := by rw [hyx]
        _ = b⁻¹ * (a⁻¹ * b) * x * b⁻¹ * y := by group
        _ = b⁻¹ * (b * a⁻¹) * x * b⁻¹ * y := by rw [hab1]
        _ = (a⁻¹ * x) * b⁻¹ * y := by group
        _ = (x * a⁻¹) * b⁻¹ * y := by rw [hax]
        _ = x * (a⁻¹ * b⁻¹) * y := by group
        _ = x * (b⁻¹ * a⁻¹) * y := by rw [hab2]
        _ = x * ((a * b)⁻¹ * y) := by group
  have hy' : y = a * b := (inv_mul_eq_one.1 hc).symm
  rw [hy']
  exact Subgroup.mul_mem_sup ha hb

end Perfect

section Trichotomy

theorem perfect_trichotomy {A B : Subgroup X} (hA : NonabSimple A) (hB : NonabSimple B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {Y : Type*} [Group Y] [Finite Y] (f : Y →* X) (hf : f.range ≤ A ⊔ B)
    (hperf : commutator Y = ⊤)
    {S₀ : Type*} [Group S₀] (hS₀ : IsSimpleGroup S₀) (hS₀n : ∃ a b : S₀, a * b ≠ b * a)
    (θ : Y →* S₀) (hθ : Function.Surjective θ) (hodd : Odd (Nat.card θ.ker))
    (hkfodd : Odd (Nat.card f.ker)) (hcard : Nat.card A ≤ Nat.card S₀)
    (hcardB : Nat.card B ≤ Nat.card S₀) :
    f.range = A ∨ f.range = B ∨ IsDiag A B f.range := by
  have hSA := hA.1
  have hSB := hB.1
  have hfin : Finite S₀ := Finite.of_surjective θ hθ
  have hperfY : Group.IsPerfect Y := Group.isPerfect_def.mpr hperf
  have hAB : A ⊓ B = ⊥ := inf_eq_bot_of_commute hA hcomm
  have hS₀even : Even (Nat.card S₀) := even_card_of_nonabelian_simple hS₀n
  obtain ⟨F, hF⟩ := exists_prod_lift hAB hcomm f hf
  let gA : Y →* ↥A := (MonoidHom.fst ↥A ↥B).comp F
  let gB : Y →* ↥B := (MonoidHom.snd ↥A ↥B).comp F
  have hfy : ∀ y, f y = (gA y : X) * (gB y : X) := fun y => (hF y).symm
  have hker : f.ker ≤ θ.ker :=
    (Subgroup.map_eq_bot_iff _).1 (map_eq_bot_of_odd_card hS₀even θ hθ f.ker hkfodd)
  have hAt' : ∀ y, gA.range = ⊥ → gA y = 1 := fun y h => by
    have : gA y ∈ gA.range := ⟨y, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hBt' : ∀ y, gB.range = ⊥ → gB y = 1 := fun y h => by
    have : gB y ∈ gB.range := ⟨y, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  rcases surj_or_trivial θ hθ hodd gA hcard with ⟨hAs, hAK⟩ | hAt
  · rcases surj_or_trivial θ hθ hodd gB hcardB with ⟨hBs, hBK⟩ | hBt
    ·
      right
      right
      have hAsurj : Function.Surjective gA := MonoidHom.range_eq_top.1 hAs
      have hBsurj : Function.Surjective gB := MonoidHom.range_eq_top.1 hBs
      have hKAodd : Odd (Nat.card gA.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hAK)
      have hKBodd : Odd (Nat.card gB.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hBK)
      have kA : ∀ y, gA y = 1 → gB y = 1 := by
        intro y hy
        have h0 := map_eq_bot_of_odd_card hB.even_card gB hBsurj gA.ker hKAodd
        have : gB y ∈ gA.ker.map gB := ⟨y, hy, rfl⟩
        rw [h0] at this
        exact Subgroup.mem_bot.1 this
      have kB : ∀ y, gB y = 1 → gA y = 1 := by
        intro y hy
        have h0 := map_eq_bot_of_odd_card hA.even_card gA hAsurj gB.ker hKBodd
        have : gA y ∈ gB.ker.map gA := ⟨y, hy, rfl⟩
        rw [h0] at this
        exact Subgroup.mem_bot.1 this
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨y₀, hy₀⟩ := hAsurj ⟨a, ha⟩
        exact ⟨f y₀, ⟨y₀, rfl⟩, (gB y₀ : X), (gB y₀).2, by rw [hfy y₀, hy₀]⟩
      · intro b hb
        obtain ⟨y₀, hy₀⟩ := hBsurj ⟨b, hb⟩
        exact ⟨f y₀, ⟨y₀, rfl⟩, (gA y₀ : X), (gA y₀).2, by rw [hfy y₀, hy₀]⟩
      · rw [Subgroup.eq_bot_iff_forall]
        rintro x ⟨⟨y, rfl⟩, hxA⟩
        have h1 : (gB y : X) ∈ A ⊓ B := by
          refine ⟨?_, (gB y).2⟩
          have : (gB y : X) = ((gA y : X))⁻¹ * f y := by rw [hfy y]; group
          rw [this]
          exact A.mul_mem (A.inv_mem (gA y).2) hxA
        rw [hAB, Subgroup.mem_bot] at h1
        have h2 : gB y = 1 := Subtype.ext h1
        have h3 : gA y = 1 := kB y h2
        rw [hfy y, h2, h3]
        simp
      · rw [Subgroup.eq_bot_iff_forall]
        rintro x ⟨⟨y, rfl⟩, hxB⟩
        have h1 : (gA y : X) ∈ A ⊓ B := by
          refine ⟨(gA y).2, ?_⟩
          have : (gA y : X) = f y * ((gB y : X))⁻¹ := by rw [hfy y]; group
          rw [this]
          exact B.mul_mem hxB (B.inv_mem (gB y).2)
        rw [hAB, Subgroup.mem_bot] at h1
        have h2 : gA y = 1 := Subtype.ext h1
        have h3 : gB y = 1 := kA y h2
        rw [hfy y, h2, h3]
        simp
    ·
      left
      have hAsurj : Function.Surjective gA := MonoidHom.range_eq_top.1 hAs
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rw [hfy y, hBt' y hBt]
        simp
      · intro hx
        obtain ⟨y, hy⟩ := hAsurj ⟨x, hx⟩
        refine ⟨y, ?_⟩
        rw [hfy y, hy, hBt' y hBt]
        simp
  · rcases surj_or_trivial θ hθ hodd gB hcardB with ⟨hBs, hBK⟩ | hBt
    ·
      right
      left
      have hBsurj : Function.Surjective gB := MonoidHom.range_eq_top.1 hBs
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rw [hfy y, hAt' y hAt]
        simp
      · intro hx
        obtain ⟨y, hy⟩ := hBsurj ⟨x, hx⟩
        refine ⟨y, ?_⟩
        rw [hfy y, hy, hAt' y hAt]
        simp
    ·
      exfalso
      have hfone : ∀ y, f y = 1 := fun y => by
        rw [hfy y, hAt' y hAt, hBt' y hBt]
        simp
      have hθone : ∀ y, θ y = 1 := fun y =>
        hker (show y ∈ f.ker from hfone y)
      obtain ⟨a, b, hab⟩ := hS₀n
      obtain ⟨y₁, rfl⟩ := hθ a
      obtain ⟨y₂, rfl⟩ := hθ b
      rw [hθone y₁, hθone y₂] at hab
      exact hab (by simp)

end Trichotomy

section NotSubnormal

omit [Finite X] in
theorem le_of_normal_inf {A J : Subgroup X} (hA : IsSimpleGroup ↥A)
    (hnorm : ∀ g ∈ A, ∀ n ∈ A, n ∈ J → g * n * g⁻¹ ∈ J) {n : X} (hnA : n ∈ A) (hnJ : n ∈ J)
    (hn1 : n ≠ 1) : A ≤ J := by
  have hN : (J.subgroupOf A).Normal :=
    ⟨fun n hn g => hnorm g g.2 n n.2 (Subgroup.mem_subgroupOf.1 hn)⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (J.subgroupOf A) with h | h
  · exfalso
    have : (⟨n, hnA⟩ : ↥A) ∈ J.subgroupOf A := hnJ
    rw [h, Subgroup.mem_bot] at this
    exact hn1 (congrArg Subtype.val this)
  · intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ J.subgroupOf A := by rw [h]; trivial
    exact this

omit [Finite X] in
theorem conj_mem_of_cov {A B Y J : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcov : ∀ a ∈ A, ∃ y ∈ Y, ∃ b ∈ B, y = a * b) (hYJ : Y ≤ J) :
    ∀ g ∈ A, ∀ n ∈ A, n ∈ J → g * n * g⁻¹ ∈ J := by
  intro g hg n hn hnJ
  obtain ⟨y, hy, b, hb, rfl⟩ := hcov g hg
  have hbn : b * n * b⁻¹ = n := by rw [← hcomm n hn b hb]; group
  have : g * b * n * (g * b)⁻¹ = g * n * g⁻¹ :=
    calc g * b * n * (g * b)⁻¹ = g * (b * n * b⁻¹) * g⁻¹ := by group
      _ = g * n * g⁻¹ := by rw [hbn]
  rw [← this]
  exact J.mul_mem (J.mul_mem (hYJ hy) hnJ) (J.inv_mem (hYJ hy))

omit [Finite X] in
theorem le_of_normalizes {A B Y J : Subgroup X} (hA : NonabSimple A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hcov : ∀ a ∈ A, ∃ y ∈ Y, ∃ b ∈ B, y = a * b)
    (hYJ : Y ≤ J) (hJ : ∀ g ∈ A, ∀ j ∈ J, g * j * g⁻¹ ∈ J) : A ≤ J := by
  obtain ⟨a₀, ha₀, x₀, hx₀, hne⟩ := hA.2
  obtain ⟨y, hy, b, hb, rfl⟩ := hcov a₀ ha₀
  have hbx : b * x₀ * b⁻¹ = x₀ := by rw [← hcomm x₀ hx₀ b hb]; group
  have hn : a₀ * x₀ * a₀⁻¹ * x₀⁻¹ = (a₀ * b) * (x₀ * (a₀ * b)⁻¹ * x₀⁻¹) :=
    calc a₀ * x₀ * a₀⁻¹ * x₀⁻¹ = a₀ * (b * x₀ * b⁻¹) * a₀⁻¹ * x₀⁻¹ := by rw [hbx]
      _ = (a₀ * b) * (x₀ * (a₀ * b)⁻¹ * x₀⁻¹) := by group
  have hnJ : a₀ * x₀ * a₀⁻¹ * x₀⁻¹ ∈ J := by
    rw [hn]
    exact J.mul_mem (hYJ hy) (hJ x₀ hx₀ _ (J.inv_mem (hYJ hy)))
  have hnA : a₀ * x₀ * a₀⁻¹ * x₀⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem ha₀ hx₀) (A.inv_mem ha₀)) (A.inv_mem hx₀)
  have hn1 : a₀ * x₀ * a₀⁻¹ * x₀⁻¹ ≠ 1 := by
    intro h
    apply hne
    calc a₀ * x₀ = (a₀ * x₀ * a₀⁻¹ * x₀⁻¹) * (x₀ * a₀) := by group
      _ = x₀ * a₀ := by rw [h, one_mul]
  exact le_of_normal_inf hA.1 (fun g hg n _ hnJ' => hJ g hg n hnJ') hnA hnJ hn1

theorem le_of_isSubnormal {G : Type*} [Group G] {J₀ U : Subgroup G}
    (hN : ∀ J : Subgroup G, J₀ ≤ J → U ≤ Subgroup.normalizer (J : Set G) → U ≤ J)
    {J : Subgroup G} (hJ : J.IsSubnormal) (h : J₀ ≤ J) : U ≤ J := by
  revert h
  induction hJ with
  | top => intro _; exact le_top
  | step J K hJK hK hnorm ih =>
    intro h
    apply hN J h
    exact (ih (h.trans hJK)).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJK).1 hnorm)

omit [Finite X] in
theorem not_subnormal_diag {A B : Subgroup X} (hA : NonabSimple A) (hB : NonabSimple B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {Y : Subgroup X} (hY : IsDiag A B Y) (hYle : Y ≤ A ⊔ B)
    {P : Subgroup X} (hP : IsSylowOf 2 P Y) {z : X} (hz : z ∈ P) (_hzc : ∀ p ∈ P, z * p = p * z)
    {H : Subgroup X} (hYH : Y ≤ H) (hCH : Subgroup.centralizer ({z} : Set X) ≤ H)
    (hsn : (Y.subgroupOf H).IsSubnormal) : False := by
  have hSA := hA.1
  have hSB := hB.1
  have hzY : z ∈ Y := hP.le hz
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hcovB := hY.cov_right hcomm
  obtain ⟨hcovA, -, hYA, hYB⟩ := hY
  have hABH : A ≤ H ∧ B ≤ H := by
    by_cases hz1 : z = 1
    · have hH : H = ⊤ := by
        rw [eq_top_iff]
        intro x _
        apply hCH
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh, hz1, one_mul, mul_one]
      exact ⟨hH ▸ le_top, hH ▸ le_top⟩
    · obtain ⟨az, haz, bz, hbz, hzab⟩ := exists_mul_of_mem_sup hcomm (hYle hzY)
      have haz1 : az ≠ 1 := by
        rintro rfl
        apply hz1
        have : z ∈ Y ⊓ B := ⟨hzY, by rw [hzab, one_mul]; exact hbz⟩
        rw [hYB, Subgroup.mem_bot] at this
        exact this
      have hbz1 : bz ≠ 1 := by
        rintro rfl
        apply hz1
        have : z ∈ Y ⊓ A := ⟨hzY, by rw [hzab, mul_one]; exact haz⟩
        rw [hYA, Subgroup.mem_bot] at this
        exact this
      have hab : Commute az bz := hcomm az haz bz hbz
      have hazc : Commute z az := by
        rw [hzab]
        exact (Commute.refl az).mul_left hab.symm
      have hbzc : Commute z bz := by
        rw [hzab]
        exact hab.mul_left (Commute.refl bz)
      have hazH : az ∈ H := by
        apply hCH
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hazc.eq
      have hbzH : bz ∈ H := by
        apply hCH
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hbzc.eq
      exact ⟨le_of_normal_inf hSA (conj_mem_of_cov hcomm hcovA hYH) haz hazH haz1,
        le_of_normal_inf hSB (conj_mem_of_cov hcomm' hcovB hYH) hbz hbzH hbz1⟩
  obtain ⟨hAH, hBH⟩ := hABH
  have hsupH : A ⊔ B ≤ H := sup_le hAH hBH
  have key : (A ⊔ B).subgroupOf H ≤ Y.subgroupOf H := by
    refine le_of_isSubnormal (J₀ := Y.subgroupOf H) ?_ hsn le_rfl
    intro J hJ0 hUJ
    have hYJ : Y ≤ J.map H.subtype := fun y hy =>
      ⟨⟨y, hYH hy⟩, hJ0 (Subgroup.mem_subgroupOf.2 hy), rfl⟩
    have hnorm : ∀ u ∈ A ⊔ B, ∀ j ∈ J.map H.subtype, u * j * u⁻¹ ∈ J.map H.subtype := by
      rintro u hu _ ⟨j, hj, rfl⟩
      have huU : (⟨u, hsupH hu⟩ : ↥H) ∈ (A ⊔ B).subgroupOf H := hu
      have := (Subgroup.mem_normalizer_iff.1 (hUJ huU) j).1 hj
      exact ⟨_, this, rfl⟩
    have hAJ : A ≤ J.map H.subtype :=
      le_of_normalizes hA hcomm hcovA hYJ (fun g hg => hnorm g (Subgroup.mem_sup_left hg))
    have hBJ : B ≤ J.map H.subtype :=
      le_of_normalizes hB hcomm' hcovB hYJ (fun g hg => hnorm g (Subgroup.mem_sup_right hg))
    intro u hu
    obtain ⟨j, hj, hju⟩ := sup_le hAJ hBJ (show (u : X) ∈ A ⊔ B from hu)
    have : j = u := Subtype.ext hju
    rwa [this] at hj
  have hAY : A ≤ Y := fun a ha =>
    key (show (⟨a, hAH ha⟩ : ↥H) ∈ (A ⊔ B).subgroupOf H from Subgroup.mem_sup_left ha)
  obtain ⟨a, ha, b, hb, hne⟩ := hA.2
  have : a ∈ Y ⊓ A := ⟨hAY ha, ha⟩
  rw [hYA, Subgroup.mem_bot] at this
  subst this
  exact hne (by simp)

end NotSubnormal

end CFSG.GH74.GLS.PU3.Pack
