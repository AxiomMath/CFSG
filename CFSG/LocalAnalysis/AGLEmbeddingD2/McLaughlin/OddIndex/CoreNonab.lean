module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreComb
public import CFSG.RankThree.PartOne.MB3.FixedPoint
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def cj {G : Type} [Group G] (g : G) (S : Subgroup G) : Subgroup G :=
  S.map (MulAut.conj g).toMonoidHom

section Cj

variable {G : Type} [Group G]

theorem mem_cj {g x : G} {S : Subgroup G} : x ∈ cj g S ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_mul (g h : G) (S : Subgroup G) : cj (g * h) S = cj g (cj h S) := by
  ext x
  simp only [mem_cj, mul_inv_rev]
  simp [mul_assoc]

theorem cj_one (S : Subgroup G) : cj 1 S = S := by
  ext x
  simp [mem_cj]

theorem cj_injective (g : G) : Function.Injective (cj g : Subgroup G → Subgroup G) := by
  intro S T h
  have := congrArg (cj g⁻¹) h
  rwa [← cj_mul, ← cj_mul, inv_mul_cancel, cj_one, cj_one] at this

theorem cj_cj_of_pow {g : G} (hg : g ^ 3 = 1) (S : Subgroup G) : cj g (cj g (cj g S)) = S := by
  rw [← cj_mul, ← cj_mul]
  have : g * g * g = 1 := by rw [← hg, pow_succ, pow_two]
  rw [this, cj_one]

theorem mul_mem_cj {g t : G} {S : Subgroup G} (ht : t ∈ S) : g * t * g⁻¹ ∈ cj g S := by
  rw [mem_cj]; simpa [mul_assoc] using ht

@[expose] noncomputable def stab (S : Subgroup G) : Subgroup G where
  carrier := {g | cj g S = S}
  mul_mem' := by
    intro g h hg hh
    change cj g S = S at hg
    change cj h S = S at hh
    change cj (g * h) S = S
    rw [cj_mul, hh, hg]
  one_mem' := cj_one S
  inv_mem' := by
    intro g hg
    change cj g S = S at hg
    change cj g⁻¹ S = S
    conv_lhs => rw [← hg]
    rw [← cj_mul, inv_mul_cancel, cj_one]

theorem mul_mem_of_mem_stab {S : Subgroup G} {g : G} (hg : g ∈ stab S) {x : G} (hx : x ∈ S) :
    g * x * g⁻¹ ∈ S := by
  have := mul_mem_cj (g := g) hx
  rwa [hg] at this

@[expose] noncomputable def stabAut (S : Subgroup G) : ↥(stab S) →* MulAut ↥S where
  toFun g :=
    { toFun := fun x => ⟨g * x * g⁻¹, mul_mem_of_mem_stab g.2 x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, by
        have := mul_mem_of_mem_stab (S := S) ((stab S).inv_mem g.2) x.2
        simpa using this⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g h => by ext x; simp [mul_assoc]

theorem stabAut_apply {S : Subgroup G} (g : ↥(stab S)) (x : ↥S) :
    ((stabAut S g x : ↥S) : G) = g * x * (g : G)⁻¹ := rfl

@[expose] noncomputable def stabSet (T : Finset (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ P, P ∈ T ↔ cj g P ∈ T}
  mul_mem' := by
    intro g h hg hh P
    change ∀ P, P ∈ T ↔ cj g P ∈ T at hg
    change ∀ P, P ∈ T ↔ cj h P ∈ T at hh
    rw [cj_mul, ← hg, ← hh]
  one_mem' := by
    intro P
    rw [cj_one]
  inv_mem' := by
    intro g hg P
    change ∀ P, P ∈ T ↔ cj g P ∈ T at hg
    rw [hg (cj g⁻¹ P), ← cj_mul, mul_inv_cancel, cj_one]

@[expose] noncomputable def permStab (T : Finset (Subgroup G)) :
    ↥(stabSet T) →* Equiv.Perm ↥T where
  toFun g :=
    { toFun := fun P => ⟨cj g P, (g.2 P).1 P.2⟩
      invFun := fun P => ⟨cj (g⁻¹ : G) P, ((stabSet T).inv_mem g.2 P).1 P.2⟩
      left_inv := fun P => by
        apply Subtype.ext
        change cj (g⁻¹ : G) (cj (g : G) P) = P
        rw [← cj_mul, inv_mul_cancel, cj_one]
      right_inv := fun P => by
        apply Subtype.ext
        change cj (g : G) (cj (g⁻¹ : G) P) = P
        rw [← cj_mul, mul_inv_cancel, cj_one] }
  map_one' := Equiv.ext fun P => Subtype.ext (cj_one (P : Subgroup G))
  map_mul' := fun g h => Equiv.ext fun P => Subtype.ext (cj_mul (g : G) (h : G) (P : Subgroup G))

end Cj

section Cfg

variable {G : Type} [Group G]

@[expose] def conjClass (Y : Subgroup G) (a : G) : Set G :=
  {c | ∃ y ∈ Y, c = y * a * y⁻¹ ∨ c = y * a⁻¹ * y⁻¹}

theorem a_mem_conjClass (Y : Subgroup G) (a : G) : a ∈ conjClass Y a :=
  ⟨1, Y.one_mem, Or.inl (by group)⟩

structure NonabCfg (G : Type) [Group G] where
  Y : Subgroup G
  M : Subgroup G
  a : G
  𝒮 : Set (Subgroup G)
  a_mem : a ∈ Y
  a_pow : a ^ 3 = 1
  simple : ∀ S ∈ 𝒮, IsSimpleGroup ↥S
  nonab : ∀ S ∈ 𝒮, ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x
  le_M : ∀ S ∈ 𝒮, S ≤ M
  comm : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → ∀ x ∈ S, ∀ y ∈ S', x * y = y * x
  cj_mem : ∀ y ∈ Y, ∀ S ∈ 𝒮, cj y S ∈ 𝒮
  trans : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, ∃ y ∈ Y, cj y S = S'
  normM : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M
  three : ∀ S ∈ 𝒮, ¬ 3 ∣ Nat.card S
  outer : ∀ S ∈ 𝒮, Group.IsSolvable (Outer ↥S)
  kills : ∀ (Q : Type) [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(Subgroup.closure (conjClass Y a)) →* Q),
    ψ ⟨a, Subgroup.subset_closure (a_mem_conjClass Y a)⟩ = 1

namespace NonabCfg

variable (C : NonabCfg G)

@[expose] def U : Subgroup G :=
  Subgroup.closure {x | x ∈ C.M ∧ ∃ c ∈ conjClass C.Y C.a, x * c = c * x}

theorem mem_U {x c : G} (hx : x ∈ C.M) (hc : c ∈ conjClass C.Y C.a) (hxc : x * c = c * x) :
    x ∈ C.U :=
  Subgroup.subset_closure ⟨hx, c, hc, hxc⟩

variable {C}

theorem class_mem {c : G} (hc : c ∈ conjClass C.Y C.a) : c ∈ C.Y := by
  obtain ⟨y, hy, rfl | rfl⟩ := hc
  · exact C.Y.mul_mem (C.Y.mul_mem hy C.a_mem) (C.Y.inv_mem hy)
  · exact C.Y.mul_mem (C.Y.mul_mem hy (C.Y.inv_mem C.a_mem)) (C.Y.inv_mem hy)

theorem class_pow {c : G} (hc : c ∈ conjClass C.Y C.a) : c ^ 3 = 1 := by
  obtain ⟨y, hy, rfl | rfl⟩ := hc
  · rw [conj_pow, C.a_pow]; group
  · rw [conj_pow, inv_pow, C.a_pow]; group

theorem class_inv {c : G} (hc : c ∈ conjClass C.Y C.a) : c⁻¹ ∈ conjClass C.Y C.a := by
  obtain ⟨y, hy, rfl | rfl⟩ := hc
  · exact ⟨y, hy, Or.inr (by group)⟩
  · exact ⟨y, hy, Or.inl (by group)⟩

theorem class_conj {c y : G} (hc : c ∈ conjClass C.Y C.a) (hy : y ∈ C.Y) :
    y * c * y⁻¹ ∈ conjClass C.Y C.a := by
  obtain ⟨z, hz, rfl | rfl⟩ := hc
  · exact ⟨y * z, C.Y.mul_mem hy hz, Or.inl (by group)⟩
  · exact ⟨y * z, C.Y.mul_mem hy hz, Or.inr (by group)⟩

theorem cj_class_mem {c : G} (hc : c ∈ conjClass C.Y C.a) {S : Subgroup G} (hS : S ∈ C.𝒮) :
    cj c S ∈ C.𝒮 := C.cj_mem c (class_mem hc) S hS

def kap (c t : G) : G := t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)

theorem kap_comm_c {c t : G} (hc3 : c ^ 3 = 1) (h01 : t * (c * t * c⁻¹) = (c * t * c⁻¹) * t)
    (h02 : t * (c * (c * t * c⁻¹) * c⁻¹) = (c * (c * t * c⁻¹) * c⁻¹) * t) :
    c * kap c t = kap c t * c := by
  have h3 : c * c * c = 1 := by rw [← hc3, pow_succ, pow_two]
  have e3 : c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹ = t := by
    calc _ = (c * c * c) * t * (c * c * c)⁻¹ := by group
      _ = t := by rw [h3]; group
  have key : c * kap c t * c⁻¹ = kap c t := by
    have e : c * kap c t * c⁻¹ = (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) *
        (c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹) := by unfold kap; group
    rw [e, e3]
    unfold kap
    calc (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) * t
        = (c * t * c⁻¹) * ((c * (c * t * c⁻¹) * c⁻¹) * t) := by group
      _ = (c * t * c⁻¹) * (t * (c * (c * t * c⁻¹) * c⁻¹)) := by rw [h02]
      _ = ((c * t * c⁻¹) * t) * (c * (c * t * c⁻¹) * c⁻¹) := by group
      _ = (t * (c * t * c⁻¹)) * (c * (c * t * c⁻¹) * c⁻¹) := by rw [h01]
  exact (mul_inv_eq_iff_eq_mul.1 key)

theorem kap_conj {c t x : G} (hx1 : x * (c * t * c⁻¹) = (c * t * c⁻¹) * x)
    (hx2 : x * (c * (c * t * c⁻¹) * c⁻¹) = (c * (c * t * c⁻¹) * c⁻¹) * x) :
    kap c t * x * (kap c t)⁻¹ = t * x * t⁻¹ := by
  have hp : x * ((c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) =
      ((c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) * x := by
    generalize c * (c * t * c⁻¹) * c⁻¹ = t2 at hx2 ⊢
    generalize c * t * c⁻¹ = t1 at hx1 ⊢
    rw [← mul_assoc, hx1, mul_assoc, hx2, ← mul_assoc]
  have e : kap c t = t * ((c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) := by unfold kap; group
  rw [e]
  set p := (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) with hpdef
  calc t * p * x * (t * p)⁻¹ = t * (p * x) * p⁻¹ * t⁻¹ := by group
    _ = t * (x * p) * p⁻¹ * t⁻¹ := by rw [← hp]
    _ = t * x * t⁻¹ := by group

theorem triple_ne {c : G} (hc3 : c ^ 3 = 1) {S : Subgroup G} (hne : cj c S ≠ S) :
    cj c (cj c S) ≠ cj c S ∧ cj c (cj c S) ≠ S := by
  refine ⟨fun h => hne (cj_injective c h), fun h => hne ?_⟩
  have := cj_cj_of_pow hc3 S
  rw [h] at this
  exact this

theorem triple_comm {S : Subgroup G} (hS : S ∈ C.𝒮) {c : G} (hc : c ∈ conjClass C.Y C.a)
    (hne : cj c S ≠ S) {t : G} (ht : t ∈ S) :
    t * (c * t * c⁻¹) = (c * t * c⁻¹) * t ∧
    t * (c * (c * t * c⁻¹) * c⁻¹) = (c * (c * t * c⁻¹) * c⁻¹) * t := by
  obtain ⟨h1, h2⟩ := triple_ne (class_pow hc) hne
  have hS1 := cj_class_mem hc hS
  have hS2 := cj_class_mem hc hS1
  exact ⟨C.comm S hS _ hS1 hne.symm t ht _ (mul_mem_cj ht),
    C.comm S hS _ hS2 h2.symm t ht _ (mul_mem_cj (mul_mem_cj ht))⟩

theorem kap_mem_U {S : Subgroup G} (hS : S ∈ C.𝒮) {c : G} (hc : c ∈ conjClass C.Y C.a)
    (hne : cj c S ≠ S) {t : G} (ht : t ∈ S) : kap c t ∈ C.U := by
  have hS1 := cj_class_mem hc hS
  have hS2 := cj_class_mem hc hS1
  obtain ⟨h01, h02⟩ := triple_comm hS hc hne ht
  refine C.mem_U ?_ hc (kap_comm_c (class_pow hc) h01 h02).symm
  exact C.M.mul_mem (C.M.mul_mem (C.le_M S hS ht) (C.le_M _ hS1 (mul_mem_cj ht)))
    (C.le_M _ hS2 (mul_mem_cj (mul_mem_cj ht)))

theorem le_U_or_inf_eq_one {S : Subgroup G} (hS : S ∈ C.𝒮) {c : G}
    (hc : c ∈ conjClass C.Y C.a) (hne : cj c S ≠ S) :
    S ≤ C.U ∨ ∀ x ∈ S, x ∈ C.U → x = 1 := by
  have hS1 := cj_class_mem hc hS
  have hS2 := cj_class_mem hc hS1
  obtain ⟨h1, h2⟩ := triple_ne (class_pow hc) hne
  let N : Subgroup ↥S := (C.U ⊓ S).subgroupOf S
  have : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnU, hnS⟩ := hn
    refine ⟨?_, (g * n * g⁻¹ : S).2⟩
    obtain ⟨h01, h02⟩ := triple_comm hS hc hne g.2
    have hx1 := C.comm S hS _ hS1 hne.symm n hnS _ (mul_mem_cj g.2)
    have hx2 := C.comm S hS _ hS2 h2.symm n hnS _ (mul_mem_cj (mul_mem_cj g.2))
    have hκ := kap_mem_U hS hc hne g.2
    have := C.U.mul_mem (C.U.mul_mem hκ hnU) (C.U.inv_mem hκ)
    rwa [kap_conj hx1 hx2] at this⟩
  have := C.simple S hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · right
    intro x hxS hxU
    have : (⟨x, hxS⟩ : S) ∈ N := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨hxU, hxS⟩
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · left
    intro x hxS
    have : (⟨x, hxS⟩ : S) ∈ N := by rw [h]; trivial
    exact ((Subgroup.mem_subgroupOf.1 this).1)

theorem false_of_fixed [Finite G] {S : Subgroup G} (hS : S ∈ C.𝒮) {c : G}
    (hc : c ∈ conjClass C.Y C.a) (hfix : cj c S = S) (hU : ∀ x ∈ S, x ∈ C.U → x = 1) : False := by
  have hsimple := C.simple S hS
  obtain ⟨x, hx, y, hy, hxy⟩ := C.nonab S hS
  have hcs : c ∈ stab S := hfix
  set α : MulAut ↥S := stabAut S ⟨c, hcs⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨c, hcs⟩ : ↥(stab S)) ^ 3 = 1 := Subtype.ext (by simpa using class_pow hc)
    rw [this, map_one]
  have hfixpt : ∀ z : ↥S, α z = z → z = 1 := by
    intro z hz
    have hzc : (z : G) * c = c * z := by
      have := congrArg Subtype.val hz
      rw [hα, stabAut_apply] at this
      simp only at this
      calc (z : G) * c = (c * z * c⁻¹) * c := by rw [this]
        _ = c * z := by group
    exact Subtype.ext (hU z z.2 (C.mem_U (C.le_M S hS z.2) hc hzc))
  have hα1 : α ≠ 1 := by
    intro h1
    have hall : ∀ z : ↥S, z = 1 := fun z => hfixpt z (by rw [h1]; rfl)
    exact hxy (by
      have h1 := hall ⟨x, hx⟩
      have h2 := hall ⟨y, hy⟩
      have e1 : x = 1 := congrArg Subtype.val h1
      have e2 : y = 1 := congrArg Subtype.val h2
      rw [e1, e2])
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have := Fact.mk Nat.prime_three
  have hnil : Group.IsNilpotent ↥S :=
    CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime α (by rw [hord]; exact Nat.prime_three)
      hfixpt
  have hnt : Nontrivial ↥S := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : x = y := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥S) ⟨y, hy⟩)
    exact hxy (by rw [this])
  have hct : Subgroup.center ↥S = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left (Group.IsNilpotent.center_ne_bot _)
  have hxc : (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S := by rw [hct]; trivial
  have h := Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩
  exact hxy (congrArg Subtype.val h).symm

theorem le_U_of_all_fix {S : Subgroup G} (hS : S ∈ C.𝒮)
    (hall : ∀ c ∈ conjClass C.Y C.a, cj c S = S) : S ≤ C.U := by
  have hle : Subgroup.closure (conjClass C.Y C.a) ≤ stab S :=
    (Subgroup.closure_le _).2 (fun c hc => hall c hc)
  let ψ₀ : ↥(Subgroup.closure (conjClass C.Y C.a)) →* MulAut ↥S :=
    (stabAut S).comp (Subgroup.inclusion hle)
  have := C.outer S hS
  let ψ := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)).comp ψ₀
  have h1 := C.kills (Outer ↥S) ψ
  set a₀ : ↥(Subgroup.closure (conjClass C.Y C.a)) :=
    ⟨C.a, Subgroup.subset_closure (a_mem_conjClass C.Y C.a)⟩ with ha₀
  have hin : ψ₀ a₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨s, hs⟩ := hin
  have hsx : ∀ x : ↥S, (s : G) * x * (s : G)⁻¹ = C.a * x * C.a⁻¹ := by
    intro x
    have := congrArg (fun φ : MulAut ↥S => ((φ x : ↥S) : G)) hs
    simpa [MulAut.conj_apply, ψ₀, stabAut_apply, ha₀] using this
  have hα3 : ψ₀ a₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : a₀ ^ 3 = 1 := Subtype.ext (by simpa using C.a_pow)
    rw [this, map_one]
  have hs3 : MulAut.conj (s ^ 3) = 1 := by
    rw [map_pow, hs]; exact hα3
  have hsimple := C.simple S hS
  have hcen : s ^ 3 ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut ↥S => φ g) hs3
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  obtain ⟨x, hx, y, hy, hxy⟩ := C.nonab S hS
  have hcen1 : Subgroup.center ↥S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S) with h | h
    · exact h
    · exfalso
      have hxc : (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S := by rw [h]; trivial
      exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩)).symm
  have hs31 : s ^ 3 = 1 := by
    rw [hcen1, Subgroup.mem_bot] at hcen; exact hcen
  have hs1 : s = 1 := by
    have h3 : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one hs31
    have h4 : orderOf s ∣ Nat.card ↥S := orderOf_dvd_natCard s
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h4) (C.three S hS)
  intro x hxS
  have hcomm : x * C.a = C.a * x := by
    have := hsx ⟨x, hxS⟩
    rw [hs1] at this
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at this
    calc x * C.a = (C.a * x * C.a⁻¹) * C.a := by rw [← this]
      _ = C.a * x := by group
  exact C.mem_U (C.le_M S hS hxS) (a_mem_conjClass C.Y C.a) hcomm

theorem comm_aux {s t P P' : G} (h1 : P * t = t * P) (h2 : P' * s = s * P')
    (h3 : P * P' = P' * P) :
    (s * P) * (t * P') * (s * P)⁻¹ * (t * P')⁻¹ = s * t * s⁻¹ * t⁻¹ := by
  have e1 : (s * P) * (t * P') = s * t * (P * P') := by
    calc s * P * (t * P') = s * (P * t) * P' := by group
      _ = s * (t * P) * P' := by rw [h1]
      _ = s * t * (P * P') := by group
  have e2 : (t * P') * (s * P) = t * s * (P * P') := by
    calc t * P' * (s * P) = t * (P' * s) * P := by group
      _ = t * (s * P') * P := by rw [h2]
      _ = t * s * (P' * P) := by group
      _ = t * s * (P * P') := by rw [h3]
  calc (s * P) * (t * P') * (s * P)⁻¹ * (t * P')⁻¹
      = ((s * P) * (t * P')) * ((t * P') * (s * P))⁻¹ := by group
    _ = s * t * s⁻¹ * t⁻¹ := by rw [e1, e2]; group

theorem false_of_orbits {S : Subgroup G} (hS : S ∈ C.𝒮) {b b' : G}
    (hb : b ∈ conjClass C.Y C.a) (hb' : b' ∈ conjClass C.Y C.a)
    (hbne : cj b S ≠ S) (hb'ne : cj b' S ≠ S) (hU : ∀ x ∈ S, x ∈ C.U → x = 1)
    (hdisj : ∀ Q, Q ∈ orb (cj b) S → Q ∈ orb (cj b') S → Q = S) : False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := C.nonab S hS
  have hS1 := cj_class_mem hb hS
  have hS2 := cj_class_mem hb hS1
  have hS1' := cj_class_mem hb' hS
  have hS2' := cj_class_mem hb' hS1'
  obtain ⟨n1, n2⟩ := triple_ne (class_pow hb) hbne
  obtain ⟨n1', n2'⟩ := triple_ne (class_pow hb') hb'ne
  have m1 : cj b S ∈ orb (cj b) S := by simp [orb]
  have m2 : cj b (cj b S) ∈ orb (cj b) S := by simp [orb]
  have m1' : cj b' S ∈ orb (cj b') S := by simp [orb]
  have m2' : cj b' (cj b' S) ∈ orb (cj b') S := by simp [orb]
  have d : ∀ Q ∈ orb (cj b) S, ∀ Q' ∈ orb (cj b') S, Q ≠ S → Q ≠ Q' := by
    intro Q hQ Q' hQ' hQS e
    exact hQS (hdisj Q hQ (e ▸ hQ'))
  have d11 := d _ m1 _ m1' hbne
  have d12 := d _ m1 _ m2' hbne
  have d21 := d _ m2 _ m1' n2
  have d22 := d _ m2 _ m2' n2
  have key : x * y = y * x := by
    have hκ := kap_mem_U hS hb hbne hx
    have hκ' := kap_mem_U hS hb' hb'ne hy
    have hs1 : b * x * b⁻¹ ∈ cj b S := mul_mem_cj hx
    have hs2 : b * (b * x * b⁻¹) * b⁻¹ ∈ cj b (cj b S) := mul_mem_cj hs1
    have ht1 : b' * y * b'⁻¹ ∈ cj b' S := mul_mem_cj hy
    have ht2 : b' * (b' * y * b'⁻¹) * b'⁻¹ ∈ cj b' (cj b' S) := mul_mem_cj ht1
    have c1 : Commute (b * x * b⁻¹) y := C.comm _ hS1 S hS hbne _ hs1 y hy
    have c2 : Commute (b * (b * x * b⁻¹) * b⁻¹) y := C.comm _ hS2 S hS n2 _ hs2 y hy
    have c3 : Commute (b' * y * b'⁻¹) x := C.comm _ hS1' S hS hb'ne _ ht1 x hx
    have c4 : Commute (b' * (b' * y * b'⁻¹) * b'⁻¹) x := C.comm _ hS2' S hS n2' _ ht2 x hx
    have c11 : Commute (b * x * b⁻¹) (b' * y * b'⁻¹) := C.comm _ hS1 _ hS1' d11 _ hs1 _ ht1
    have c12 : Commute (b * x * b⁻¹) (b' * (b' * y * b'⁻¹) * b'⁻¹) :=
      C.comm _ hS1 _ hS2' d12 _ hs1 _ ht2
    have c21 : Commute (b * (b * x * b⁻¹) * b⁻¹) (b' * y * b'⁻¹) :=
      C.comm _ hS2 _ hS1' d21 _ hs2 _ ht1
    have c22 : Commute (b * (b * x * b⁻¹) * b⁻¹) (b' * (b' * y * b'⁻¹) * b'⁻¹) :=
      C.comm _ hS2 _ hS2' d22 _ hs2 _ ht2
    have hPy : ((b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹)) * y =
        y * ((b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹)) := (c1.mul_left c2).eq
    have hP'x : ((b' * y * b'⁻¹) * (b' * (b' * y * b'⁻¹) * b'⁻¹)) * x =
        x * ((b' * y * b'⁻¹) * (b' * (b' * y * b'⁻¹) * b'⁻¹)) := (c3.mul_left c4).eq
    have hPP : ((b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹)) *
        ((b' * y * b'⁻¹) * (b' * (b' * y * b'⁻¹) * b'⁻¹)) =
        ((b' * y * b'⁻¹) * (b' * (b' * y * b'⁻¹) * b'⁻¹)) *
        ((b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹)) :=
      ((c11.mul_right c12).mul_left (c21.mul_right c22)).eq
    have hk1 : kap b x = x * ((b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹)) := by
      unfold kap; group
    have hk2 : kap b' y = y * ((b' * y * b'⁻¹) * (b' * (b' * y * b'⁻¹) * b'⁻¹)) := by
      unfold kap; group
    have hcomm := comm_aux hPy hP'x hPP
    rw [← hk1, ← hk2] at hcomm
    have hmemU : x * y * x⁻¹ * y⁻¹ ∈ C.U := by
      rw [← hcomm]
      exact C.U.mul_mem (C.U.mul_mem (C.U.mul_mem hκ hκ') (C.U.inv_mem hκ)) (C.U.inv_mem hκ')
    have hmemS : x * y * x⁻¹ * y⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
    have h1 := hU _ hmemS hmemU
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  exact hxy key

theorem cj_U_le {y : G} (hy : y ∈ C.Y) : cj y C.U ≤ C.U := by
  unfold cj NonabCfg.U
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, ⟨hxM, c, hc, hxc⟩, rfl⟩
  refine C.mem_U (C.normM y hy x hxM) (class_conj hc hy) ?_
  change (y * x * y⁻¹) * (y * c * y⁻¹) = (y * c * y⁻¹) * (y * x * y⁻¹)
  calc (y * x * y⁻¹) * (y * c * y⁻¹) = y * (x * c) * y⁻¹ := by group
    _ = y * (c * x) * y⁻¹ := by rw [hxc]
    _ = (y * c * y⁻¹) * (y * x * y⁻¹) := by group

theorem all_le_U [Finite G] : ∀ S ∈ C.𝒮, S ≤ C.U := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S₀, hS₀, hS₀U⟩ := hcon
  have h1 : ∀ S ∈ C.𝒮, ¬ S ≤ C.U := by
    intro S hS hle
    obtain ⟨y, hy, hyS⟩ := C.trans S hS S₀ hS₀
    apply hS₀U
    rw [← hyS]
    exact (Subgroup.map_mono hle).trans (cj_U_le hy)
  have h2 : ∀ S ∈ C.𝒮, ∃ c ∈ conjClass C.Y C.a, cj c S ≠ S := by
    intro S hS
    by_contra h
    push Not at h
    exact h1 S hS (le_U_of_all_fix hS h)
  have h3 : ∀ S ∈ C.𝒮, ∀ x ∈ S, x ∈ C.U → x = 1 := by
    intro S hS
    obtain ⟨c, hc, hne⟩ := h2 S hS
    rcases le_U_or_inf_eq_one hS hc hne with h | h
    · exact absurd h (h1 S hS)
    · exact h
  have h4 : ∀ S ∈ C.𝒮, ∀ c ∈ conjClass C.Y C.a, cj c S ≠ S :=
    fun S hS c hc hfix => false_of_fixed hS hc hfix (h3 S hS)
  have h5 : ∀ S ∈ C.𝒮, ∀ b ∈ conjClass C.Y C.a, ∀ b' ∈ conjClass C.Y C.a,
      ∃ Q, Q ≠ S ∧ Q ∈ orb (cj b) S ∧ Q ∈ orb (cj b') S := by
    intro S hS b hb b' hb'
    by_contra h
    push Not at h
    exact false_of_orbits hS hb hb' (h4 S hS b hb) (h4 S hS b' hb') (h3 S hS)
      (fun Q hQ hQ' => by
        by_contra hne
        exact h Q hne hQ hQ')
  have ha := a_mem_conjClass C.Y C.a
  have hf3 : ∀ x : Subgroup G, cj C.a (cj C.a (cj C.a x)) = x := fun x => cj_cj_of_pow C.a_pow x
  have hg : ∀ c ∈ conjClass C.Y C.a, ∀ P ∈ C.𝒮, cj c P ∈ orb (cj C.a) P := by
    intro c hc P hP
    exact g_mem_orb (D := fun x => x ∈ C.𝒮) hf3 (fun x => cj_cj_of_pow (class_pow hc) x)
      (fun x hx => h4 x hx C.a ha) (fun x hx => h4 x hx c hc)
      (fun x hx => cj_class_mem ha hx) (fun x hx => h5 x hx C.a ha c hc) hP
  set T := orb (cj C.a) S₀ with hT
  have hT𝒮 : ∀ P ∈ T, P ∈ C.𝒮 := by
    intro P hP
    simp only [hT, orb, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact hS₀
    · exact cj_class_mem ha hS₀
    · exact cj_class_mem ha (cj_class_mem ha hS₀)
  have horb : ∀ P ∈ T, orb (cj C.a) P = T := fun P hP => orb_eq_of_mem hf3 hP
  have fwd : ∀ c ∈ conjClass C.Y C.a, ∀ P ∈ T, cj c P ∈ T := by
    intro c hc P hP
    rw [← horb P hP]
    exact hg c hc P (hT𝒮 P hP)
  have hstab : ∀ c ∈ conjClass C.Y C.a, c ∈ stabSet T := by
    intro c hc P
    refine ⟨fwd c hc P, fun h => ?_⟩
    have := fwd c⁻¹ (class_inv hc) _ h
    rwa [← cj_mul, inv_mul_cancel, cj_one] at this
  have hle : Subgroup.closure (conjClass C.Y C.a) ≤ stabSet T :=
    (Subgroup.closure_le _).2 hstab
  have hcard : Nat.card ↥T = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact orb_card hf3 (h4 S₀ hS₀ C.a ha)
  have : Group.IsSolvable (Equiv.Perm ↥T) := Equiv.Perm.isSolvable (by rw [hcard]; norm_num)
  let ψ : ↥(Subgroup.closure (conjClass C.Y C.a)) →* Equiv.Perm ↥T :=
    (permStab T).comp (Subgroup.inclusion hle)
  have h1' := C.kills (Equiv.Perm ↥T) ψ
  have hS₀T : S₀ ∈ T := mem_orb_self _ _
  have := congrArg (fun σ : Equiv.Perm ↥T => ((σ ⟨S₀, hS₀T⟩ : ↥T) : Subgroup G)) h1'
  exact h4 S₀ hS₀ C.a ha this

end NonabCfg

end Cfg

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
