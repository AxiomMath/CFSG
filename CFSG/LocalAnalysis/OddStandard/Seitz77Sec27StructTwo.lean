module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructBase

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.LocalCores

theorem lieModel_of_alt {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : LieModel Y .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

variable {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}

theorem four_dvd_card_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) : 4 ∣ Nat.card K := by
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have h2 := CFSG.Walter.two_le_twoRank K hnonab heven
  obtain ⟨E, hE, h4⟩ := exists_elemAbelian_of_two_le_twoRank h2
  have hE2 : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 g g.2⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> omega
  have : 4 ∣ Nat.card E := by
    rw [hk]
    exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  exact this.trans (Subgroup.card_subgroup_dvd_card E)

namespace Local27

theorem le_zpowers_of_centralizer_X (c : Local27 N X t)
    {T : Subgroup N} (hT2 : IsPGroup 2 T) (hTC : T ≤ centralizer (X : Set N)) (htT : t ∈ T) :
    T ≤ zpowers t := by
  have htt := c.t_mul_t
  have ht1 : t ≠ 1 := by
    intro h1
    have := c.t_order
    rw [h1, orderOf_one] at this
    omega
  have hM : T ⊓ centralizer ({t} : Set N) ≤ zpowers t := by
    intro m hm
    exact c.mem_zpowers_of_isPGroup ⟨hm.2, hTC hm.1⟩ (hT2.to_le (zpowers_le.2 hm.1))
  by_cases hTbot : T = ⊥
  · rw [hTbot]; exact bot_le
  · have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hTbot
    have : Group.IsNilpotent ↥T := hT2.isNilpotent
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.center_ne_bot ↥T)
    have hwc := mem_center_iff.1 w.2
    have hwt : (w.1 : N) * t = t * (w.1 : N) := (congrArg Subtype.val (hwc ⟨t, htT⟩)).symm
    have hwM : (w.1 : N) ∈ T ⊓ centralizer ({t} : Set N) :=
      ⟨w.1.2, mem_centralizer_singleton_iff.2 hwt⟩
    have hw1' : (w.1 : N) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
    have hwt' : (w.1 : N) = t := by
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt (hM hwM) with h | h
      · exact absurd h hw1'
      · exact h
    intro g hg
    apply hM
    refine ⟨hg, mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : g * (w.1 : N) = (w.1 : N) * g := congrArg Subtype.val (hwc ⟨g, hg⟩)
    rw [hwt'] at h2
    exact h2

theorem not_four_dvd_card_centralizer_X (c : Local27 N X t) :
    ¬ 4 ∣ Nat.card ↥(centralizer (X : Set N)) := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (X : Set N) with hC
  let t' : ↥C := ⟨t, c.t_mem_centralizer_X⟩
  have hzt' : IsPGroup 2 (zpowers t') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : orderOf t' = orderOf t := (Subgroup.orderOf_coe t').symm
    rw [this, c.t_order]
  obtain ⟨S, hS⟩ := hzt'.exists_le_sylow
  have hcard : Nat.card S = 2 ^ (Nat.card ↥C).factorization 2 := Sylow.card_eq_multiplicity S
  have hv : 2 ≤ (Nat.card ↥C).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (by simpa using h4)
  set T : Subgroup N := (S : Subgroup ↥C).map C.subtype with hT
  have hT2 : IsPGroup 2 T := S.isPGroup'.map C.subtype
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have htT : t ∈ T := ⟨t', hS (mem_zpowers t'), rfl⟩
  have hle := c.le_zpowers_of_centralizer_X hT2 hTC htT
  have hcardT : Nat.card T = Nat.card S := Subgroup.card_map_of_injective C.subtype_injective
  have h1 : Nat.card T ≤ Nat.card (zpowers t) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  rw [Nat.card_zpowers, c.t_order, hcardT, hcard] at h1
  have : 2 ^ 2 ≤ 2 ^ (Nat.card ↥C).factorization 2 := Nat.pow_le_pow_right (by norm_num) hv
  omega

theorem not_four_dvd_card_R (c : Local27 N X t) :
    ¬ 4 ∣ Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4' : 2 ^ 2 ∣ Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) := by
    norm_num
    exact h4
  have h := (padicValNat_dvd_iff_le (p := 2) (n := 2) Nat.card_pos.ne').1 h4'
  rw [c.cent_two] at h
  omega

theorem inf_centralizer_le_R (c : Local27 N X t) {S : Subgroup N} (hXS : X ⊓ S = ⊥)
    (hnorm : ∀ x ∈ X, ∀ y ∈ S, x * y * x⁻¹ ∈ S) :
    S ⊓ centralizer ({t} : Set N) ≤ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) := by
  intro k ⟨hkS, hkD⟩
  refine ⟨hkD, mem_centralizer_iff.2 fun x hx => ?_⟩
  have h1 : (k * x * k⁻¹) * x⁻¹ ∈ X := X.mul_mem (c.X_normal k hkD x hx) (X.inv_mem hx)
  have h2 : k * (x * k⁻¹ * x⁻¹) ∈ S := S.mul_mem hkS (hnorm x hx k⁻¹ (S.inv_mem hkS))
  have heq : (k * x * k⁻¹) * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
  have h3 : (k * x * k⁻¹) * x⁻¹ ∈ X ⊓ S := ⟨h1, heq ▸ h2⟩
  rw [hXS, mem_bot] at h3
  calc x * k = (k * x * k⁻¹ * x⁻¹)⁻¹ * (k * x) := by group
    _ = k * x := by rw [h3]; simp

end Local27

omit [Finite N] in
theorem simple_inf_or_le {T S : Subgroup N} (hTs : IsSimpleGroup ↥T)
    (hSnorm : ∀ x ∈ T, ∀ y ∈ S, x * y * x⁻¹ ∈ S) : T ⊓ S = ⊥ ∨ T ≤ S := by
  have hn : ((T ⊓ S).subgroupOf T).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    exact ⟨T.mul_mem (T.mul_mem x.2 hy.1) (T.inv_mem x.2), hSnorm x x.2 y hy.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ S).subgroupOf T) with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy.1⟩ : T) ∈ (T ⊓ S).subgroupOf T := hy
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · right
    intro x hx
    have : (⟨x, hx⟩ : T) ∈ (T ⊓ S).subgroupOf T := by rw [h]; trivial
    exact this.2

omit [Finite N] in
theorem eq_of_le_of_simple {T S : Subgroup N} (hSs : IsSimpleGroup ↥S) (hTS : T ≤ S)
    (hTne : T ≠ ⊥) (hTnorm : ∀ e ∈ S, ∀ x ∈ T, e * x * e⁻¹ ∈ T) : T = S := by
  have hn : (T.subgroupOf S).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    exact hTnorm x x.2 y hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf S) with h | h
  · exfalso
    apply hTne
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hTS hy⟩ : S) ∈ T.subgroupOf S := hy
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · refine le_antisymm hTS fun x hx => ?_
    have : (⟨x, hx⟩ : S) ∈ T.subgroupOf S := by rw [h]; trivial
    exact this

omit [Finite N] in
theorem mem_normalizer_iff_map_eq {S : Subgroup N} (n : N) :
    n ∈ normalizer (S : Set N) ↔ S.map (MulAut.conj n).toMonoidHom = S := by
  have hfx : ∀ x : N, (MulAut.conj n).toMonoidHom x = n * x * n⁻¹ := fun x => rfl
  rw [mem_normalizer_iff]
  constructor
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hfx]
      exact (h x).1 hx
    · intro hy
      refine ⟨n⁻¹ * y * n, (h _).2 (by simpa [mul_assoc] using hy), ?_⟩
      rw [hfx]
      group
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, hfx x⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      rw [hfx] at hzx
      have : z = x := by simpa using hzx
      exact this ▸ hz

omit [Finite N] in
theorem even_card_inf_centralizer {S : Subgroup N} [Finite S] (hS : Even (Nat.card S))
    (htt : t * t = 1) (hn : ∀ x ∈ S, t * x * t⁻¹ ∈ S) :
    Even (Nat.card ↥(S ⊓ centralizer ({t} : Set N))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let f : Function.End ↥S := fun x => ⟨t * x * t⁻¹, hn x x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    change f (f x) = x
    apply Subtype.ext
    change t * (t * (x : N) * t⁻¹) * t⁻¹ = x
    rw [hti]
    calc t * (t * (x : N) * t) * t = (t * t) * (x : N) * (t * t) := by group
      _ = x := by rw [htt]; simp
  let _ : Fintype ↥S := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hcard : Nat.card ↥(S ⊓ centralizer ({t} : Set N)) = Nat.card f.fixedPoints := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        invFun := fun y => ⟨y.1.1, ⟨y.1.2, ?_⟩⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · apply Subtype.ext
      change t * (x.1 : N) * t⁻¹ = x.1
      have := mem_centralizer_singleton_iff.1 x.2.2
      calc t * (x.1 : N) * t⁻¹ = (x.1 : N) * t * t⁻¹ := by rw [← this]
        _ = x.1 := by group
    · have h := congrArg Subtype.val y.2
      change t * (y.1.1 : N) * t⁻¹ = y.1.1 at h
      refine mem_centralizer_singleton_iff.2 ?_
      calc (y.1.1 : N) * t = t * (y.1.1 : N) * t⁻¹ * t := by rw [h]
        _ = t * y.1.1 := by group
  rw [hcard]
  rw [Nat.card_eq_fintype_card] at hS ⊢
  have h1 : Fintype.card ↥S % 2 = Fintype.card f.fixedPoints % 2 := hmod
  exact Nat.even_iff.2 (by rw [← h1]; exact Nat.even_iff.1 hS)

structure TwoComp (N : Type) [Group N] (S₁ S₂ : Subgroup N) : Prop where
  simple₁ : IsSimpleGroup ↥S₁
  simple₂ : IsSimpleGroup ↥S₂
  nonab₁ : ∃ a b : ↥S₁, a * b ≠ b * a
  nonab₂ : ∃ a b : ↥S₂, a * b ≠ b * a
  sup_eq : S₁ ⊔ S₂ = layer N
  disj : Disjoint S₁ S₂
  comm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x
  cent_bot : centralizer ((layer N : Subgroup N) : Set N) = ⊥

namespace TwoComp

omit [Finite N]

variable {S₁ S₂ : Subgroup N} (hT : TwoComp N S₁ S₂)
include hT

theorem norm₁ : ∀ e ∈ layer N, ∀ x ∈ S₁, e * x * e⁻¹ ∈ S₁ := by
  intro e he x hx
  rw [← hT.sup_eq] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hT.comm e).1 he
  have hbx : b * x = x * b := (hT.comm x hx b hb).symm
  have : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = a * x * a⁻¹ := by group
  rw [this]
  exact S₁.mul_mem (S₁.mul_mem ha hx) (S₁.inv_mem ha)

theorem norm₂ : ∀ e ∈ layer N, ∀ x ∈ S₂, e * x * e⁻¹ ∈ S₂ := by
  intro e he x hx
  rw [← hT.sup_eq] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hT.comm e).1 he
  have hbxb : b * x * b⁻¹ ∈ S₂ := S₂.mul_mem (S₂.mul_mem hb hx) (S₂.inv_mem hb)
  have hax : a * (b * x * b⁻¹) = (b * x * b⁻¹) * a := hT.comm a ha _ hbxb
  have : a * b * x * (a * b)⁻¹ = b * x * b⁻¹ := by
    calc a * b * x * (a * b)⁻¹ = (a * (b * x * b⁻¹)) * a⁻¹ := by group
      _ = ((b * x * b⁻¹) * a) * a⁻¹ := by rw [hax]
      _ = b * x * b⁻¹ := by group
  rw [this]
  exact hbxb

theorem symm : TwoComp N S₂ S₁ where
  simple₁ := hT.simple₂
  simple₂ := hT.simple₁
  nonab₁ := hT.nonab₂
  nonab₂ := hT.nonab₁
  sup_eq := by rw [sup_comm]; exact hT.sup_eq
  disj := hT.disj.symm
  comm := fun x hx y hy => (hT.comm y hy x hx).symm
  cent_bot := hT.cent_bot

theorem le_layer₁ : S₁ ≤ layer N := hT.sup_eq ▸ le_sup_left

theorem le_layer₂ : S₂ ≤ layer N := hT.sup_eq ▸ le_sup_right

theorem eq_of_simple_normal {T : Subgroup N} (hTs : IsSimpleGroup ↥T)
    (hTn : ∃ a b : ↥T, a * b ≠ b * a) (hTE : T ≤ layer N)
    (hTnorm : ∀ e ∈ layer N, ∀ x ∈ T, e * x * e⁻¹ ∈ T) : T = S₁ ∨ T = S₂ := by
  have hS₁ := hT.simple₁
  have hS₂ := hT.simple₂
  have hTne : T ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hTn
    exact hab (Subsingleton.elim a b ▸ rfl)
  rcases simple_inf_or_le hTs (fun x hx y hy => hT.norm₁ x (hTE hx) y hy) with h1 | h1
  · rcases simple_inf_or_le hTs (fun x hx y hy => hT.norm₂ x (hTE hx) y hy) with h2 | h2
    · exfalso
      have hc : ∀ x ∈ T, ∀ y ∈ layer N, x * y = y * x := by
        have hc1 : ∀ x ∈ T, ∀ y ∈ S₁, x * y = y * x := by
          intro x hx y hy
          have ha : x * y * x⁻¹ * y⁻¹ ∈ S₁ :=
            S₁.mul_mem (hT.norm₁ x (hTE hx) y hy) (S₁.inv_mem hy)
          have hb : x * (y * x⁻¹ * y⁻¹) ∈ T :=
            T.mul_mem hx (hTnorm y (hT.le_layer₁ hy) x⁻¹ (T.inv_mem hx))
          have heq : x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by group
          have : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ S₁ := ⟨heq ▸ hb, ha⟩
          rw [h1, mem_bot] at this
          calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
            _ = y * x := by rw [this, one_mul]
        have hc2 : ∀ x ∈ T, ∀ y ∈ S₂, x * y = y * x := by
          intro x hx y hy
          have ha : x * y * x⁻¹ * y⁻¹ ∈ S₂ :=
            S₂.mul_mem (hT.norm₂ x (hTE hx) y hy) (S₂.inv_mem hy)
          have hb : x * (y * x⁻¹ * y⁻¹) ∈ T :=
            T.mul_mem hx (hTnorm y (hT.le_layer₂ hy) x⁻¹ (T.inv_mem hx))
          have heq : x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by group
          have : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ S₂ := ⟨heq ▸ hb, ha⟩
          rw [h2, mem_bot] at this
          calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
            _ = y * x := by rw [this, one_mul]
        intro x hx y hy
        rw [← hT.sup_eq] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hT.comm y).1 hy
        calc x * (a * b) = (x * a) * b := (mul_assoc _ _ _).symm
          _ = (a * x) * b := by rw [hc1 x hx a ha]
          _ = a * (x * b) := mul_assoc _ _ _
          _ = a * (b * x) := by rw [hc2 x hx b hb]
          _ = (a * b) * x := (mul_assoc _ _ _).symm
      apply hTne
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ centralizer ((layer N : Subgroup N) : Set N) :=
        mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm
      rw [hT.cent_bot, mem_bot] at this
      exact mem_bot.2 this
    · right
      exact eq_of_le_of_simple hS₂ h2 hTne fun e he x hx => hTnorm e (hT.le_layer₂ he) x hx
  · left
    exact eq_of_le_of_simple hS₁ h1 hTne fun e he x hx => hTnorm e (hT.le_layer₁ he) x hx


end TwoComp


namespace TwoComp

omit [Finite N]

variable {S₁ S₂ : Subgroup N} (hT : TwoComp N S₁ S₂)
include hT

theorem conj_eq_or (n : N) :
    S₁.map (MulAut.conj n).toMonoidHom = S₁ ∨ S₁.map (MulAut.conj n).toMonoidHom = S₂ := by
  have hS₁ := hT.simple₁
  have hchar : (layer N).Characteristic := layer_characteristic
  set f : N →* N := (MulAut.conj n).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj n).injective
  have hfx : ∀ x : N, f x = n * x * n⁻¹ := fun x => rfl
  let e : ↥S₁ ≃* ↥(S₁.map f) := S₁.equivMapOfInjective f hfinj
  have hTs : IsSimpleGroup ↥(S₁.map f) := e.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hT.nonab₁
  have hTn : ∃ a b : ↥(S₁.map f), a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  have hTE : S₁.map f ≤ layer N := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hfx]
    exact Normal.conj_mem inferInstance x (hT.le_layer₁ hx) n
  have hTnorm : ∀ e ∈ layer N, ∀ x ∈ S₁.map f, e * x * e⁻¹ ∈ S₁.map f := by
    rintro e he _ ⟨x, hx, rfl⟩
    have hu : n⁻¹ * e * n ∈ layer N := by
      simpa using Normal.conj_mem inferInstance e he n⁻¹
    refine ⟨(n⁻¹ * e * n) * x * (n⁻¹ * e * n)⁻¹, hT.norm₁ _ hu x hx, ?_⟩
    simp only [hfx]
    group
  exact hT.eq_of_simple_normal hTs hTn hTE hTnorm

theorem ne : S₁ ≠ S₂ := by
  intro h
  have hd := hT.disj
  rw [← h] at hd
  have hbot : S₁ = ⊥ := disjoint_self.1 hd
  obtain ⟨a, b, hab⟩ := hT.nonab₁
  have ha : (a : N) = 1 := (Subgroup.eq_bot_iff_forall _).1 hbot a a.2
  have hb : (b : N) = 1 := (Subgroup.eq_bot_iff_forall _).1 hbot b b.2
  exact hab (Subtype.ext (by simp [ha, hb]))

theorem normalizes_or_swaps (n : N) :
    (S₁.map (MulAut.conj n).toMonoidHom = S₁ ∧ S₂.map (MulAut.conj n).toMonoidHom = S₂) ∨
    (S₁.map (MulAut.conj n).toMonoidHom = S₂ ∧ S₂.map (MulAut.conj n).toMonoidHom = S₁) := by
  have h1 := hT.conj_eq_or n
  have h2 := hT.symm.conj_eq_or n
  have hinj : S₁.map (MulAut.conj n).toMonoidHom ≠ S₂.map (MulAut.conj n).toMonoidHom := fun h =>
    hT.ne (Subgroup.map_injective (MulAut.conj n).injective h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hinj
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inr ⟨h1, h2⟩

theorem simple_le_normalizer {Y : Subgroup N} (hY : IsSimpleGroup ↥Y) (hY2 : Nat.card Y ≠ 2) :
    ∀ y ∈ Y, S₁.map (MulAut.conj y).toMonoidHom = S₁ := by
  by_contra hne
  push Not at hne
  obtain ⟨y₀, hy₀, hy₀ne⟩ := hne
  have hy₀swap : S₁.map (MulAut.conj y₀).toMonoidHom = S₂ :=
    (hT.conj_eq_or y₀).resolve_left hy₀ne
  have hmapmul : ∀ a b : N, S₁.map (MulAut.conj (a * b)).toMonoidHom =
      (S₁.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  let H : Subgroup ↥Y := (Y ⊓ normalizer (S₁ : Set N)).subgroupOf Y
  have hmem : ∀ b : ↥Y, b ∈ H ↔ S₁.map (MulAut.conj (b : N)).toMonoidHom = S₁ := by
    intro b
    rw [← mem_normalizer_iff_map_eq]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  have hH2 : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y₀, hy₀⟩, fun b => ?_⟩
    have hba : b * ⟨y₀, hy₀⟩ ∈ H ↔
        (S₂.map (MulAut.conj (b : N)).toMonoidHom = S₁) := by
      rw [hmem]
      change S₁.map (MulAut.conj ((b : N) * y₀)).toMonoidHom = S₁ ↔ _
      rw [hmapmul, hy₀swap]
    rw [hba, hmem]
    rcases hT.normalizes_or_swaps (b : N) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      exact ⟨h1, fun h => hT.ne (h.symm.trans h2)⟩
    · left
      exact ⟨h2, fun h => hT.ne (h.symm.trans h1)⟩
  have : H.Normal := Subgroup.normal_of_index_eq_two hH2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · rw [h, Subgroup.index_bot] at hH2
    exact hY2 hH2
  · rw [h, Subgroup.index_top] at hH2
    omega


end TwoComp

namespace TwoComp

variable {S₁ S₂ : Subgroup N} (hT : TwoComp N S₁ S₂)
include hT

theorem X_normalizes (c : Local27 N X t) :
    (∀ x ∈ X, ∀ y ∈ S₁, x * y * x⁻¹ ∈ S₁) ∧ (∀ x ∈ X, ∀ y ∈ S₂, x * y * x⁻¹ ∈ S₂) := by
  have hX1 := hT.simple_le_normalizer c.isSimpleGroup_X (by rw [c.card_eq_sixty]; norm_num)
  have hX2 := hT.symm.simple_le_normalizer c.isSimpleGroup_X (by rw [c.card_eq_sixty]; norm_num)
  exact ⟨fun x hx y hy => by
      have : x * y * x⁻¹ ∈ S₁.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
      rwa [hX1 x hx] at this,
    fun x hx y hy => by
      have : x * y * x⁻¹ ∈ S₂.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
      rwa [hX2 x hx] at this⟩

theorem X_inf_eq_bot (c : Local27 N X t) : X ⊓ S₁ = ⊥ := by
  have hS₂ := hT.simple₂
  have := c.isSimpleGroup_X
  rcases simple_inf_or_le c.isSimpleGroup_X (hT.X_normalizes c).1 with h | h
  · exact h
  · exfalso
    have hC : S₂ ≤ centralizer (X : Set N) := fun y hy =>
      mem_centralizer_iff.2 fun x hx => hT.comm x (h hx) y hy
    have h4 := four_dvd_card_of_simple (K := ↥S₂) hT.nonab₂
    exact c.not_four_dvd_card_centralizer_X (h4.trans (Subgroup.card_dvd_of_le hC))

theorem not_normalizes (c : Local27 N X t)
    (hn₁ : ∀ x ∈ S₁, t * x * t⁻¹ ∈ S₁) (hn₂ : ∀ x ∈ S₂, t * x * t⁻¹ ∈ S₂) : False := by
  have htt := c.t_mul_t
  have h₁ := hT.simple₁
  have h₂ := hT.simple₂
  have h41 := four_dvd_card_of_simple (K := ↥S₁) hT.nonab₁
  have h42 := four_dvd_card_of_simple (K := ↥S₂) hT.nonab₂
  have hev₁ : Even (Nat.card ↥S₁) := even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h41)
  have hev₂ : Even (Nat.card ↥S₂) := even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h42)
  have hK₁ := even_card_inf_centralizer hev₁ htt hn₁
  have hK₂ := even_card_inf_centralizer hev₂ htt hn₂
  have hR₁ := c.inf_centralizer_le_R (hT.X_inf_eq_bot c) (hT.X_normalizes c).1
  have hR₂ := c.inf_centralizer_le_R (hT.symm.X_inf_eq_bot c) (hT.X_normalizes c).2
  have hcomm : ∀ a ∈ S₁ ⊓ centralizer ({t} : Set N), ∀ b ∈ S₂ ⊓ centralizer ({t} : Set N),
      a * b = b * a := fun a ha b hb => hT.comm a ha.1 b hb.1
  have hdisj : (S₁ ⊓ centralizer ({t} : Set N)) ⊓ (S₂ ⊓ centralizer ({t} : Set N)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := hT.disj.le_bot ⟨hx.1.1, hx.2.1⟩
    exact this
  have hcard := card_sup_of_commute hcomm hdisj
  have hle : (S₁ ⊓ centralizer ({t} : Set N)) ⊔ (S₂ ⊓ centralizer ({t} : Set N)) ≤
      centralizer ({t} : Set N) ⊓ centralizer (X : Set N) := sup_le hR₁ hR₂
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  have h4 : 4 ∣ Nat.card ↥(S₁ ⊓ centralizer ({t} : Set N)) *
      Nat.card ↥(S₂ ⊓ centralizer ({t} : Set N)) := by
    obtain ⟨a, ha⟩ := hK₁
    obtain ⟨b, hb⟩ := hK₂
    rw [ha, hb]
    exact ⟨a * b, by ring⟩
  exact c.not_four_dvd_card_R (h4.trans hdvd)

theorem swap_case (c : Local27 N X t)
    (hs₁ : ∀ x ∈ S₁, t * x * t⁻¹ ∈ S₂) (hs₂ : ∀ x ∈ S₂, t * x * t⁻¹ ∈ S₁) :
    X = centralizer ({t} : Set N) ⊓ layer N ∧ Nonempty (↥S₁ ≃* ↥X) := by
  have htt := c.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h₁ := hT.simple₁
  have hchar : (layer N).Characteristic := layer_characteristic
  let φ : ↥S₁ →* N := MonoidHom.mk' (fun s => (s : N) * (t * (s : N) * t⁻¹)) (by
    intro a b
    have hcomm : (t * (a : N) * t⁻¹) * (b : N) = (b : N) * (t * (a : N) * t⁻¹) :=
      (hT.comm b b.2 _ (hs₁ a a.2)).symm
    change (a : N) * b * (t * ((a : N) * b) * t⁻¹) =
      ((a : N) * (t * a * t⁻¹)) * ((b : N) * (t * b * t⁻¹))
    calc (a : N) * b * (t * ((a : N) * b) * t⁻¹)
        = (a : N) * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = (a : N) * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hcomm]
      _ = ((a : N) * (t * a * t⁻¹)) * ((b : N) * (t * b * t⁻¹)) := by group)
  have hφ : ∀ s : ↥S₁, φ s = (s : N) * (t * (s : N) * t⁻¹) := fun s => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, hφ] at hs
    have hu : t * (s : N) * t⁻¹ ∈ S₂ := hs₁ s s.2
    have hs2 : (s : N) ∈ S₂ := by
      have : (s : N) = (t * (s : N) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hs
      rw [this]
      exact S₂.inv_mem hu
    have := hT.disj.le_bot ⟨s.2, hs2⟩
    exact mem_bot.2 (Subtype.ext (mem_bot.1 this))
  have hrange : φ.range = centralizer ({t} : Set N) ⊓ layer N := by
    ext e
    constructor
    · rintro ⟨s, rfl⟩
      have hu : t * (s : N) * t⁻¹ ∈ S₂ := hs₁ s s.2
      have hE : (s : N) * (t * (s : N) * t⁻¹) ∈ layer N := by
        rw [← hT.sup_eq]
        exact Subgroup.mul_mem _ (mem_sup_left s.2) (mem_sup_right hu)
      refine ⟨mem_centralizer_singleton_iff.2 ?_, hE⟩
      have hcomm : (s : N) * (t * s * t⁻¹) = (t * s * t⁻¹) * s := hT.comm s s.2 _ hu
      have h3 : t * (t * (s : N) * t⁻¹) = s * t := by
        calc t * (t * (s : N) * t⁻¹) = (t * t) * s * t⁻¹ := by group
          _ = s * t := by rw [htt, one_mul, hti]
      change (s : N) * (t * s * t⁻¹) * t = t * ((s : N) * (t * s * t⁻¹))
      calc (s : N) * (t * s * t⁻¹) * t = (t * s * t⁻¹) * s * t := by rw [hcomm]
        _ = (t * s * t⁻¹) * (s * t) := by group
        _ = (t * s * t⁻¹) * (t * (t * s * t⁻¹)) := by rw [h3]
        _ = t * s * (t⁻¹ * t) * (t * s * t⁻¹) := by group
        _ = t * (s * (t * s * t⁻¹)) := by group
    · rintro ⟨hD, hE⟩
      have hee : (e : N) * t = t * e := mem_centralizer_singleton_iff.1 hD
      rw [← hT.sup_eq] at hE
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hT.comm e).1 hE
      have ha'' : t * a * t⁻¹ ∈ S₂ := hs₁ a ha
      have hb'' : t * b * t⁻¹ ∈ S₁ := hs₂ b hb
      have hcomm : (t * b * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * b * t⁻¹) :=
        hT.comm _ hb'' _ ha''
      have hconj : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
        calc (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
          _ = a * b := by
            have : t * (a * b) = (a * b) * t := hee.symm
            rw [this]; group
      have key : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
        calc a⁻¹ * (t * b * t⁻¹) = a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by
              group
          _ = a⁻¹ * ((t * a * t⁻¹) * (t * b * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [hcomm]
          _ = a⁻¹ * (a * b) * (t * a * t⁻¹)⁻¹ := by rw [hconj]
          _ = b * (t * a * t⁻¹)⁻¹ := by group
      have hL : a⁻¹ * (t * b * t⁻¹) ∈ S₁ := S₁.mul_mem (S₁.inv_mem ha) hb''
      have hR : b * (t * a * t⁻¹)⁻¹ ∈ S₂ := S₂.mul_mem hb (S₂.inv_mem ha'')
      have h1 : a⁻¹ * (t * b * t⁻¹) = 1 := mem_bot.1 (hT.disj.le_bot ⟨hL, key ▸ hR⟩)
      have hba : b = t * a * t⁻¹ := by
        have h2 : b * (t * a * t⁻¹)⁻¹ = 1 := key ▸ h1
        exact mul_inv_eq_one.1 h2
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [hφ]
      change a * (t * a * t⁻¹) = a * b
      rw [hba]
  set C : Subgroup N := centralizer ({t} : Set N) ⊓ layer N with hC
  let eS : ↥S₁ ≃* ↥C := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hCs : IsSimpleGroup ↥C := eS.symm.isSimpleGroup
  have h4C : 4 ∣ Nat.card ↥C := by
    rw [← Nat.card_congr eS.toEquiv]
    exact four_dvd_card_of_simple hT.nonab₁
  have hCD : C ≤ centralizer ({t} : Set N) := inf_le_left
  have hXnormC : ∀ x ∈ X, ∀ y ∈ C, x * y * x⁻¹ ∈ C := by
    intro x hx y hy
    have hxD := c.X_le_centralizer_t hx
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hxD hy.1) (Subgroup.inv_mem _ hxD),
      Normal.conj_mem inferInstance y hy.2 x⟩
  have hXC : X ≤ C := by
    have := c.isSimpleGroup_X
    rcases simple_inf_or_le c.isSimpleGroup_X hXnormC with h | h
    · exfalso
      have hle : C ⊓ centralizer ({t} : Set N) ≤
          centralizer ({t} : Set N) ⊓ centralizer (X : Set N) := c.inf_centralizer_le_R h hXnormC
      have hle' : C ≤ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) :=
        (le_inf le_rfl hCD).trans hle
      exact c.not_four_dvd_card_R (h4C.trans (Subgroup.card_dvd_of_le hle'))
    · exact h
  have hXne : X ≠ ⊥ := by
    intro h
    have := c.card_eq_sixty
    rw [h, Subgroup.card_bot] at this
    omega
  have hXeq : X = C :=
    eq_of_le_of_simple hCs hXC hXne fun e he x hx => c.X_normal e (hCD he) x hx
  exact ⟨hXeq, ⟨eS.trans (MulEquiv.subgroupCongr hXeq.symm)⟩⟩

end TwoComp

theorem twoComp27 (c : Local27 N X t) (S₁ S₂ : Subgroup N)
    (h₁ : IsSimpleGroup ↥S₁) (h₂ : IsSimpleGroup ↥S₂) (hS : S₁ ⊔ S₂ = layer N)
    (hd : Disjoint S₁ S₂) (hc : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hn₁ : ∃ a b : ↥S₁, a * b ≠ b * a) (hn₂ : ∃ a b : ↥S₂, a * b ≠ b * a)
    (hcent : centralizer ((layer N : Subgroup N) : Set N) = ⊥) : Out27B N X t := by
  have hT : TwoComp N S₁ S₂ := ⟨h₁, h₂, hn₁, hn₂, hS, hd, hc, hcent⟩
  rcases hT.normalizes_or_swaps t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    refine hT.not_normalizes c (fun x hx => ?_) (fun x hx => ?_)
    · have : t * x * t⁻¹ ∈ S₁.map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h1] at this
    · have : t * x * t⁻¹ ∈ S₂.map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h2] at this
  · have hs₁ : ∀ x ∈ S₁, t * x * t⁻¹ ∈ S₂ := fun x hx => by
      have : t * x * t⁻¹ ∈ S₁.map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h1] at this
    have hs₂ : ∀ x ∈ S₂, t * x * t⁻¹ ∈ S₁ := fun x hx => by
      have : t * x * t⁻¹ ∈ S₂.map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h2] at this
    obtain ⟨hXeq, ⟨e₁⟩⟩ := hT.swap_case c hs₁ hs₂
    obtain ⟨eA⟩ := c.exists_equiv_alt
    have e₂ : ↥S₂ ≃* ↥S₁ := (S₂.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).trans (MulEquiv.subgroupCongr h2)
    exact ⟨S₁, S₂, lieModel_of_alt (e₁.trans eA), lieModel_of_alt ((e₂.trans e₁).trans eA), hS, hd,
      hc, hs₁, hXeq⟩

end CFSG.OddStandard.Seitz77
