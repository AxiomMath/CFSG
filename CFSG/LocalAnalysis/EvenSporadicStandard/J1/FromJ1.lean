module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Setting
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Walter.J1.Local
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

structure IsJ1Sylow {Y : Type*} [Group Y] (E : Subgroup Y) : Prop where
  card_eq : Nat.card E = 8
  sq_eq_one : ∀ x ∈ E, x * x = 1
  sylow : ∀ P : Subgroup Y, IsPGroup 2 P → ∃ g : Y, P ≤ E.map (MulAut.conj g).toMonoidHom
  centralizer_eq : centralizer (E : Set Y) = E
  card_normalizer : Nat.card (normalizer (E : Set Y)) = 168

section Transport

variable {Y W : Type*} [Group Y] [Group W]

theorem IsJ1Sylow.comm {E : Subgroup Y} (hE : IsJ1Sylow E) {a b : Y} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a :=
  mem_centralizer_iff.1 (by rw [hE.centralizer_eq]; exact hb) a ha

theorem IsJ1Sylow.map {E : Subgroup Y} (hE : IsJ1Sylow E) (e : Y ≃* W) :
    IsJ1Sylow (E.map e.toMonoidHom) where
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

section Sylow

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

theorem isJ1Sylow_of_jankoHyp {W : Type} [Group W] [Finite W] (h : CFSG.Walter.J1.JankoHyp W)
    (S : Sylow 2 W) : IsJ1Sylow (S : Subgroup W) where
  card_eq := (h.sylow_structure S).1
  sq_eq_one := (h.sylow_structure S).2.1
  sylow _ hP := exists_le_map_conj_of_sylow S hP
  centralizer_eq := (h.sylow_structure S).2.2.2
  card_normalizer := h.card_normalizer_sylow'' S

theorem exists_isJ1Sylow_walterJ1 :
    ∃ E : Subgroup CFSG.Open.walterJ1, IsJ1Sylow E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 CFSG.Open.walterJ1) := inferInstance
  exact ⟨S, isJ1Sylow_of_jankoHyp CFSG.Walter.J1Props.jankoHyp S⟩

theorem exists_isJ1Sylow_of_mulEquiv {Y : Type*} [Group Y]
    (e : Y ≃* NativeSporadic.J1) : ∃ E : Subgroup Y, IsJ1Sylow E := by
  obtain ⟨E, hE⟩ := exists_isJ1Sylow_walterJ1
  exact ⟨E.map (CFSG.Walter.walterJ1EquivNative.trans e.symm).toMonoidHom,
    hE.map (CFSG.Walter.walterJ1EquivNative.trans e.symm)⟩

end Sylow

section Embedding

variable {G : Type*} [Group G] {L : Subgroup G}

theorem IsJ1Sylow.exists_map_subtype {E₀ : Subgroup L} (h : IsJ1Sylow E₀) :
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

theorem exists_sylow_of_isSporadic_J1 {G : Type} [Group G]
    {L : Subgroup G} (hL : IsSporadic L .J1) :
    ∃ E : Subgroup G, E ≤ L ∧ Nat.card E = 8 ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
        ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom) ∧
      centralizer (E : Set G) ⊓ L = E ∧
      Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168 := by
  obtain ⟨e⟩ := hL
  obtain ⟨E₀, hE₀⟩ := exists_isJ1Sylow_of_mulEquiv (e : ↥L ≃* NativeSporadic.J1)
  exact hE₀.exists_map_subtype

theorem center_eq_bot_of_isSporadic_J1 {Y : Type} [Group Y]
    (hY : IsSporadic Y .J1) : center Y = ⊥ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.J1 := e
  have hcard : Nat.card Y = 175560 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsSimpleGroup NativeSporadic.J1 := CFSG.Sporadic.J1.isSimpleGroup_J1
  have : IsSimpleGroup Y := e'.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h0 | h0
  · exact h0
  · exfalso
    let : CommGroup Y := { ‹Group Y› with
      mul_comm := fun a b => (mem_center_iff.mp (h0 ▸ mem_top a) b).symm }
    have hp := IsSimpleGroup.prime_card (α := Y)
    rw [hcard] at hp
    norm_num at hp

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

theorem forall_mulAut_inner_of_isSporadic_J1
    {Y : Type} [Group Y] (hY : IsSporadic Y .J1) :
    ∀ α : MulAut (Y ⧸ center Y), ∃ q, α = MulAut.conj q := by
  obtain ⟨φ⟩ := isSporadic_quotient_of_center_eq_bot (center_eq_bot_of_isSporadic_J1 hY) hY
  let ψ : (Y ⧸ center Y) ≃* NativeSporadic.J1 := φ
  intro α
  obtain ⟨g, hg⟩ := (CFSG.Sporadic.Schreier.at_j1_schreier).2.1 (ψ.symm.trans (α.trans ψ))
  refine ⟨ψ.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut NativeSporadic.J1 => β (ψ x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  apply ψ.injective
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem hypothesisOne_quotient_of_isSporadic_J1 {Y : Type}
    [Group Y] (hY : IsSporadic Y .J1) (hI : HypothesisOne NativeSporadic.J1) :
    HypothesisOne (Y ⧸ center Y) := by
  obtain ⟨φ⟩ := isSporadic_quotient_of_center_eq_bot (center_eq_bot_of_isSporadic_J1 hY) hY
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv φ.symm hI

theorem Setting.exists_of_stdHyp
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hL : IsSporadic L .J1) (hI : HypothesisOne (L ⧸ Subgroup.center L)) :
    ∃ H : Setting G, H.L = L := by
  have hZ := center_eq_bot_of_isSporadic_J1 hL
  have hinn := forall_mulAut_inner_of_isSporadic_J1 hL
  have hS := h.card_sylow_eq_two_of_inner hI hinn
  obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
  obtain ⟨hC, hd, -⟩ := h.centralizer_eq_prod_of_center_eq_bot hS ht ht2
    (h.centralizer_le_sup_centralizer_of_inner ht ht2 hinn) hZ
  obtain ⟨E, hEL, hE8, hEsq, hEsyl, hEC, hEN⟩ := exists_sylow_of_isSporadic_J1 hL
  exact ⟨{
    z := t
    L := L
    E := E
    simple := h.simple
    nonabelian := h.nonabelian
    order_z := ht2
    centralizer_eq := hC
    disjoint := hd
    E_le := hEL
    card_E := hE8
    sq_E := hEsq
    sylow_E := hEsyl
    centralizer_E := hEC
    card_normalizer_E := hEN }, rfl⟩

end CFSG.EvenSporadicStandard.J1Std
