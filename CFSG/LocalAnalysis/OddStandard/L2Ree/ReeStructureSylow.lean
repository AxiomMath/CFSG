module

public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Blueprint CFSG.LieType.Ree

structure IsReeSylow {Y : Type*} [Group Y] (E : Subgroup Y) : Prop where
  card_eq : Nat.card E = 8
  sq_eq_one : ∀ x ∈ E, x * x = 1
  sylow : ∀ P : Subgroup Y, IsPGroup 2 P → ∃ g : Y, P ≤ E.map (MulAut.conj g).toMonoidHom
  centralizer_eq : centralizer (E : Set Y) = E
  card_normalizer : Nat.card (normalizer (E : Set Y)) = 168

section Transport

variable {Y W : Type*} [Group Y] [Group W]

theorem IsReeSylow.comm {E : Subgroup Y} (hE : IsReeSylow E) {a b : Y} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a :=
  mem_centralizer_iff.1 (by rw [hE.centralizer_eq]; exact hb) a ha

theorem IsReeSylow.map {E : Subgroup Y} (hE : IsReeSylow E) (e : Y ≃* W) :
    IsReeSylow (E.map e.toMonoidHom) where
  card_eq := by rw [Subgroup.card_map_of_injective e.injective, hE.card_eq]
  sq_eq_one := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE.sq_eq_one x hx, map_one]
  sylow P hP := by
    obtain ⟨g, hg⟩ := hE.sylow (P.comap e.toMonoidHom) (hP.comap_of_injective _ e.injective)
    refine ⟨e g, fun x hx => ?_⟩
    obtain ⟨a, ha, hax⟩ := hg (show e.symm x ∈ P.comap e.toMonoidHom by simpa using hx)
    refine ⟨e a, ⟨a, ha, rfl⟩, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hax ⊢
    rw [← map_inv, ← map_mul, ← map_mul, hax, e.apply_symm_apply]
  centralizer_eq := by
    ext y
    constructor
    · intro hy
      rw [mem_centralizer_iff] at hy
      have hmem : e.symm y ∈ E := by
        rw [← hE.centralizer_eq, mem_centralizer_iff]
        intro a ha
        apply e.injective
        simpa using hy (e a) ⟨a, ha, rfl⟩
      exact ⟨e.symm y, hmem, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hE.comm hb ha]
  card_normalizer := by
    rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective e.injective,
      hE.card_normalizer]

end Transport

section Embedding

variable {G : Type*} [Group G] {L : Subgroup G}

theorem IsReeSylow.exists_map_subtype {E₀ : Subgroup L} (h : IsReeSylow E₀) :
    ∃ E : Subgroup G, E ≤ L ∧ Nat.card E = 8 ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
        ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom) ∧
      centralizer (E : Set G) ⊓ L = E ∧
      Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168 := by
  have hmem : ∀ a : L, (a : G) ∈ E₀.map L.subtype ↔ a ∈ E₀ := fun a =>
    ⟨fun ⟨b, hb, hba⟩ => by rwa [← Subtype.ext hba], fun ha => ⟨a, ha, rfl⟩⟩
  refine ⟨E₀.map L.subtype, Subgroup.map_subtype_le E₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, h.card_eq]
  · rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (h.sq_eq_one x hx)
    simpa using this
  · intro P hPL hP
    obtain ⟨g, hg⟩ := h.sylow (P.comap L.subtype) hP.comap_subtype
    refine ⟨g, g.2, fun x hx => ?_⟩
    obtain ⟨a, ha, hax⟩ := hg (show (⟨x, hPL hx⟩ : L) ∈ P.comap L.subtype from hx)
    refine ⟨a, ⟨a, ha, rfl⟩, ?_⟩
    have := congrArg Subtype.val hax
    simpa [MulAut.conj_apply] using this
  · ext x
    constructor
    · rintro ⟨hxC, hxL⟩
      have hy : (⟨x, hxL⟩ : L) ∈ E₀ := by
        rw [← h.centralizer_eq, mem_centralizer_iff]
        intro a ha
        apply Subtype.ext
        exact mem_centralizer_iff.1 hxC a ((hmem a).2 ha)
      exact ⟨⟨x, hxL⟩, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mem_centralizer_iff.2 ?_, y.2⟩
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (h.comm ha hy)
  · have hN : normalizer ((E₀.map L.subtype : Subgroup G) : Set G) ⊓ L =
        (normalizer (E₀ : Set L)).map L.subtype := by
      ext x
      constructor
      · rintro ⟨hxN, hxL⟩
        refine ⟨⟨x, hxL⟩, mem_normalizer_iff.2 fun a => ?_, rfl⟩
        have h1 := mem_normalizer_iff.1 hxN (a : G)
        exact (hmem a).symm.trans (h1.trans (hmem (⟨x, hxL⟩ * a * ⟨x, hxL⟩⁻¹)))
      · rintro ⟨y, hy, rfl⟩
        refine ⟨mem_normalizer_iff.2 fun g => ⟨?_, ?_⟩, y.2⟩
        · rintro ⟨a, ha, rfl⟩
          exact ⟨y * a * y⁻¹, (mem_normalizer_iff.1 hy a).1 ha, rfl⟩
        · rintro ⟨b, hb, hbg⟩
          have hb' := (mem_normalizer_iff.1 (inv_mem hy) b).1 hb
          rw [inv_inv] at hb'
          refine ⟨y⁻¹ * b * y, hb', ?_⟩
          have hbg' : (b : G) = y * g * (y : G)⁻¹ := hbg
          change (y : G)⁻¹ * b * y = g
          rw [hbg']
          group
    rw [hN, Subgroup.card_map_of_injective L.subtype_injective, h.card_normalizer]

end Embedding

theorem exists_le_map_conj_of_sylow {W : Type*} [Group W] [Finite W] (S : Sylow 2 W)
    {P : Subgroup W} (hP : IsPGroup 2 P) :
    ∃ g : W, P ≤ (S : Subgroup W).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W S Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ ((g • S : Sylow 2 W) : Subgroup W) := by rw [hg]; exact hQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hxQ
  obtain ⟨s, hs, rfl⟩ := hxQ
  exact ⟨s, hs, rfl⟩


section Ree


theorem exists_isReeSylow_reeGamma (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ E : Subgroup (ReeTag.G2.reeGamma K a), IsReeSylow E := by
  obtain ⟨h, hp3, -, -⟩ := CFSG.Walter.Ree.Model.small_Ree_jtHyp a ha K hK
  have hp : h.p ≠ 2 := by rw [hp3]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, h.orderOf_t, pow_one]) : IsPGroup 2 (zpowers h.t)).exists_le_sylow
  have htS : h.t ∈ (S : Subgroup (ReeTag.G2.reeGamma K a)) := hS (mem_zpowers _)
  refine ⟨S, h.card_sylow hp S htS, fun x hx => h.mul_self_of_mem_sylow hp S htS hx,
    fun P hP => exists_le_map_conj_of_sylow S hP, h.centralizer_sylow hp S htS, ?_⟩
  have h1 := h.index_sylow_normalizer hp S htS
  have h2 := Subgroup.card_mul_index
    ((S : Subgroup (ReeTag.G2.reeGamma K a)).subgroupOf
      (normalizer ((S : Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a))))
  have h3 : Nat.card ↥((S : Subgroup (ReeTag.G2.reeGamma K a)).subgroupOf
      (normalizer ((S : Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a)))) =
        8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact h.card_sylow hp S htS
  rw [h1, h3] at h2
  omega

theorem exists_isReeSylow_of_lieModel {Y : Type} [Group Y] {f : ℕ}
    (hm : LieModel Y .twistedG2 0 3 f) : ∃ E : Subgroup Y, IsReeSylow E := by
  have hm' : ReeTitsModel Y .twistedG2 3 f := (LieModel.reeTitsModel hm (by decide)).2
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier Y 3 f hm'
  obtain ⟨-, a', hfa', K', _, _, hK', hw⟩ := hm'
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K' ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK'
  obtain ⟨E⟩ := hiso a' K' hfa hK' hw
  have hK'' : Nat.card K' = 3 ^ (2 * a' + 1) := by rw [hK', hfa]
  obtain ⟨E₀, hE₀⟩ := exists_isReeSylow_reeGamma a' ha K' hK''
  exact ⟨E₀.map E.symm.toMonoidHom, hE₀.map E.symm⟩

theorem exists_sylow_of_ree {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    (hm : LieModel (L ⧸ center L) .twistedG2 0 3 f) (hZ : center L = ⊥) :
    ∃ E : Subgroup G, E ≤ L ∧ Nat.card E = 8 ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
        ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom) ∧
      centralizer (E : Set G) ⊓ L = E ∧
      Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168 := by
  let e : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨E₀, hE₀⟩ := exists_isReeSylow_of_lieModel (hm.of_mulEquiv e)
  exact hE₀.exists_map_subtype

end Ree

end CFSG.OddStandard.L2Ree
