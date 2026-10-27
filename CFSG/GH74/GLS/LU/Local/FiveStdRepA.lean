module

public import CFSG.GH74.GLS.LU.Local.FiveModelLeaf

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

namespace FiveStdRep

section Z4

variable {G : Type} [Group G]

@[expose] def z4Hom (a b : G) (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a) : Z4Z4 →* G where
  toFun x := a ^ x.1.toAdd.val * b ^ x.2.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    have h1 : ∀ (c : G), c ^ 4 = 1 → ∀ i k : ZMod 4, c ^ (i + k).val = c ^ i.val * c ^ k.val := by
      intro c hc i k
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hc, pow_add]
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, h1 a ha, h1 b hb]
    have hc : b ^ x.2.toAdd.val * a ^ y.1.toAdd.val = a ^ y.1.toAdd.val * b ^ x.2.toAdd.val :=
      (Commute.pow_pow (Commute.symm (show Commute a b from hab)) _ _).eq
    calc a ^ x.1.toAdd.val * a ^ y.1.toAdd.val * (b ^ x.2.toAdd.val * b ^ y.2.toAdd.val)
        = a ^ x.1.toAdd.val * (a ^ y.1.toAdd.val * b ^ x.2.toAdd.val) * b ^ y.2.toAdd.val := by
          simp only [mul_assoc]
      _ = a ^ x.1.toAdd.val * (b ^ x.2.toAdd.val * a ^ y.1.toAdd.val) * b ^ y.2.toAdd.val := by rw [hc]
      _ = a ^ x.1.toAdd.val * b ^ x.2.toAdd.val * (a ^ y.1.toAdd.val * b ^ y.2.toAdd.val) := by
          simp only [mul_assoc]

theorem z4Hom_apply {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} (x : Z4Z4) :
    z4Hom a b ha hb hab x = a ^ x.1.toAdd.val * b ^ x.2.toAdd.val := rfl

theorem card_z4z4 : Nat.card Z4Z4 = 16 := by
  rw [Nat.card_prod]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem mem_range_z4Hom {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} {g : G} :
    g ∈ (z4Hom a b ha hb hab).range ↔ ∃ i < 4, ∃ j < 4, g = a ^ i * b ^ j := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ZMod.val_lt _, _, ZMod.val_lt _, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    refine ⟨(Multiplicative.ofAdd (i : ZMod 4), Multiplicative.ofAdd (j : ZMod 4)), ?_⟩
    rw [z4Hom_apply]
    simp only [toAdd_ofAdd, ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj]

theorem z4Hom_injective_iff {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} :
    Function.Injective (z4Hom a b ha hb hab) ↔
      Set.ncard {g : G | ∃ i < 4, ∃ j < 4, g = a ^ i * b ^ j} = 16 := by
  have hset : {g : G | ∃ i < 4, ∃ j < 4, g = a ^ i * b ^ j} = z4Hom a b ha hb hab '' Set.univ := by
    ext g
    rw [Set.image_univ]
    exact (mem_range_z4Hom (ha := ha) (hb := hb) (hab := hab)).symm
  have h16 : (Set.univ : Set Z4Z4).ncard = 16 := by
    rw [Set.ncard_univ]; exact card_z4z4
  rw [hset]
  conv_rhs => rw [← h16]
  rw [Set.ncard_image_iff, Set.injOn_univ]

@[expose] def z4Sub (a b : G) (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a) : Subgroup G :=
  (z4Hom a b ha hb hab).range

theorem mem_z4Sub {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} {g : G} :
    g ∈ z4Sub a b ha hb hab ↔ ∃ i < 4, ∃ j < 4, g = a ^ i * b ^ j := mem_range_z4Hom

theorem left_mem_z4Sub {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} :
    a ∈ z4Sub a b ha hb hab :=
  mem_z4Sub.2 ⟨1, by norm_num, 0, by norm_num, by simp⟩

theorem right_mem_z4Sub {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} :
    b ∈ z4Sub a b ha hb hab :=
  mem_z4Sub.2 ⟨0, by norm_num, 1, by norm_num, by simp⟩

theorem z4Sub_le {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a} {H : Subgroup G}
    (h1 : a ∈ H) (h2 : b ∈ H) : z4Sub a b ha hb hab ≤ H := by
  intro g hg
  obtain ⟨i, -, j, -, rfl⟩ := mem_z4Sub.1 hg
  exact H.mul_mem (H.pow_mem h1 i) (H.pow_mem h2 j)

theorem z4Sub_equiv {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a}
    (h : Function.Injective (z4Hom a b ha hb hab)) : Nonempty (↥(z4Sub a b ha hb hab) ≃* Z4Z4) :=
  ⟨(MonoidHom.ofInjective h).symm⟩

theorem z4_decomp : ∀ x : Z4Z4,
    x = ((Multiplicative.ofAdd (1 : ZMod 4), 1) : Z4Z4) ^ x.1.toAdd.val *
      ((1, Multiplicative.ofAdd (1 : ZMod 4)) : Z4Z4) ^ x.2.toAdd.val := by decide

theorem orderOf_z4_gen : orderOf (((Multiplicative.ofAdd (1 : ZMod 4), 1) : Z4Z4)) = 4 ∧
    orderOf (((1, Multiplicative.ofAdd (1 : ZMod 4)) : Z4Z4)) = 4 := by
  constructor <;> rw [orderOf_eq_iff (by norm_num)] <;> refine ⟨by decide, fun m hm hm0 => ?_⟩ <;>
    interval_cases m <;> decide

theorem exists_z4_of_equiv {A : Subgroup G} (f : ↥A ≃* Z4Z4) :
    ∃ (a b : G) (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a),
      Function.Injective (z4Hom a b ha hb hab) ∧ z4Sub a b ha hb hab = A := by
  let ψ : Z4Z4 →* G := A.subtype.comp f.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp f.symm.injective
  let g1 : Z4Z4 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
  let g2 : Z4Z4 := (1, Multiplicative.ofAdd (1 : ZMod 4))
  have hg1 : g1 ^ 4 = 1 := by decide
  have hg2 : g2 ^ 4 = 1 := by decide
  have ha : ψ g1 ^ 4 = 1 := by rw [← map_pow, hg1, map_one]
  have hb : ψ g2 ^ 4 = 1 := by rw [← map_pow, hg2, map_one]
  have hab : ψ g1 * ψ g2 = ψ g2 * ψ g1 := by rw [← map_mul, ← map_mul, mul_comm]
  have hz : z4Hom (ψ g1) (ψ g2) ha hb hab = ψ := by
    ext x
    rw [z4Hom_apply, ← map_pow, ← map_pow, ← map_mul, ← z4_decomp x]
  refine ⟨ψ g1, ψ g2, ha, hb, hab, by rw [hz]; exact hψ, ?_⟩
  unfold z4Sub
  rw [hz]
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (f.symm x).2
  · intro hg
    exact ⟨f ⟨g, hg⟩, by simp [ψ]⟩

theorem orderOf_eq_four_of_inj {a b : G} {ha : a ^ 4 = 1} {hb : b ^ 4 = 1} {hab : a * b = b * a}
    (h : Function.Injective (z4Hom a b ha hb hab)) : orderOf a = 4 ∧ orderOf b = 4 := by
  have h1 : z4Hom a b ha hb hab (Multiplicative.ofAdd (1 : ZMod 4), 1) = a := by
    rw [z4Hom_apply]
    have : (1 : ZMod 4).val = 1 := by decide
    simp [this]
  have h2 : z4Hom a b ha hb hab (1, Multiplicative.ofAdd (1 : ZMod 4)) = b := by
    rw [z4Hom_apply]
    have : (1 : ZMod 4).val = 1 := by decide
    simp [this]
  have h3 := orderOf_injective _ h (Multiplicative.ofAdd (1 : ZMod 4), 1)
  have h4 := orderOf_injective _ h (1, Multiplicative.ofAdd (1 : ZMod 4))
  rw [h1] at h3
  rw [h2] at h4
  exact ⟨h3.trans orderOf_z4_gen.1, h4.trans orderOf_z4_gen.2⟩

end Z4

section Cj

variable {G : Type} [Group G]

theorem repCj_mem {g : G} {A : Subgroup G} {x : G} : x ∈ cjL g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    simpa [MulAut.conj_apply, this] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply]; group⟩

theorem repCj_mem_self {g x : G} {A : Subgroup G} (hx : x ∈ A) : g * x * g⁻¹ ∈ cjL g A :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem repCj_card (g : G) (A : Subgroup G) : Nat.card ↥(cjL g A) = Nat.card ↥A :=
  (Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv).symm

theorem repCj_eq_of_le [Finite G] {g : G} {A : Subgroup G} (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) :
    cjL g A = A := by
  have hle : cjL g A ≤ A := by
    rintro y ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using h a ha
  exact Subgroup.eq_of_le_of_card_ge hle (repCj_card g A).ge

theorem repCj_eq_iff {g : G} {K : Subgroup G} : cjL g K = K ↔ g ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := SetLike.ext_iff.1 h (g * y * g⁻¹)
    rwa [repCj_mem, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
  · intro h
    ext x
    rw [repCj_mem]
    have := h (g⁻¹ * x * g)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

theorem mem_inf_normalizer {g : G} {K₁ K₂ : Subgroup G} :
    g ∈ normalizer (K₁ : Set G) ⊓ normalizer (K₂ : Set G) ↔ cjL g K₁ = K₁ ∧ cjL g K₂ = K₂ := by
  rw [Subgroup.mem_inf, ← repCj_eq_iff, ← repCj_eq_iff]

theorem mem_P_iff {z u g : G} :
    g ∈ centralizer ((UU z u : Subgroup G) : Set G) ↔ g * z = z * g ∧ g * u = u * g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))).symm,
      (h u (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))).symm⟩
  · rintro ⟨h1, h2⟩
    have hz : z ∈ centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro k hk; rw [Set.mem_singleton_iff.1 hk]; exact h1
    have hu : u ∈ centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro k hk; rw [Set.mem_singleton_iff.1 hk]; exact h2
    have hle : UU z u ≤ centralizer ({g} : Set G) :=
      sup_le ((Subgroup.zpowers_le).2 hz) ((Subgroup.zpowers_le).2 hu)
    intro h hh
    have := hle hh
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this g rfl).symm

end Cj

end FiveStdRep

end CFSG.GH74.GLS.LU.Local.Five
