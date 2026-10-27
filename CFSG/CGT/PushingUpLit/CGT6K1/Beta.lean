module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.CGT.PushingUpLit.CGT6

section Datum

variable {G : Type} [Group G] {D : Subgroup G} [D.Normal] {t : G}

theorem kb_fixedRootDatum {A : Subgroup G} (hAD : A ≤ D) (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G)) (hCt : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d)
    (hodd : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) ⊓ D → IsPGroup 2 P → P = ⊥)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    FixedRootDatum D n K (MulAut.conjNormal t) (A.subgroupOf D) := by
  set F := (MulAut.conjNormal t : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D) with hF
  have hle : A.subgroupOf D ≤ F := fun s hs => by
    rw [hF, mem_eqLocus_conjNormal_iff]
    have hc := mem_centralizer_iff.1 htA s (mem_subgroupOf.1 hs)
    calc t * (s : G) * t⁻¹ = s * t * t⁻¹ := by rw [hc]
      _ = s := by group
  refine ⟨hn, hK, orderOf_conjNormal ht hnt, hle, ⟨fun x hx g => ?_⟩,
    ⟨(subgroupOfEquivOfLe hAD).trans φ⟩, fun P hP hP2 => ?_⟩
  ·
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgN := hCt (mem_centralizer_of_mem_eqLocus g.2)
    exact (mem_normalizer_iff.1 hgN _).1 hx
  ·
    have hPA : P.map D.subtype ≤ centralizer (A : Set G) ⊓ D := by
      rintro _ ⟨p, hp, rfl⟩
      refine ⟨mem_centralizer_iff.2 fun a ha => ?_, p.2⟩
      exact congrArg Subtype.val
        (mem_centralizer_iff.1 (hP hp).2 ⟨a, hAD ha⟩ (mem_subgroupOf.2 ha))
    have hbot : P = ⊥ :=
      (map_eq_bot_iff_of_injective P D.subtype_injective).1 (hodd _ hPA (hP2.map D.subtype))
    exact ⟨by rw [hbot, card_bot]; omega, fun _ => hbot⟩

end Datum

theorem kb_inf_eq_bot_of_pGroup {Q : Type} [Group Q] [Finite Q] {C D T₀ : Subgroup Q} [D.Normal]
    (hT : ABGLocalTools.IsSylowOf 2 T₀ C) (hβ : T₀ ⊓ D = ⊥) {P : Subgroup Q} (hP : P ≤ C ⊓ D)
    (hP2 : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : C ≤ normalizer ((C ⊓ D : Subgroup Q) : Set Q) := fun c hc =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hc, by rw [normalizer_eq_top D]; exact mem_top c⟩
  have hcard := (hT.inf_of_le_normalizer inf_le_left hCN).card_eq
  have hbot : T₀ ⊓ (C ⊓ D) = ⊥ := le_bot_iff.1 ((inf_le_inf_left T₀ inf_le_right).trans hβ.le)
  rw [hbot, card_bot] at hcard
  rcases hP2.card_eq_or_dvd with h1 | h2
  · exact card_eq_one.1 h1
  · have h3 := (Nat.prime_two.dvd_iff_one_le_factorization Nat.card_pos.ne').1
      (h2.trans (card_dvd_of_le hP))
    have h4 : 2 ^ 1 ≤ 2 ^ (Nat.card (C ⊓ D : Subgroup Q)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) h3
    omega

theorem beta_survivors (hSel : CatSelector) {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    {A T₀ : Subgroup Q} (h : AlmostSimple Q n A T₀) (hβ : T₀ ⊓ CFSG.layer Q = ⊥) :
    FixedRootSurvivors ↥(CFSG.layer Q) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.LocalCores.layer_characteristic (G := Q)
  have := h.simple
  obtain ⟨t, ht⟩ : ∃ t : T₀, orderOf t = 2 := by
    rcases h.sylow.isPGroup.card_eq_or_dvd with h1 | h2
    · exact absurd (card_eq_one.1 h1) h.ne
    · exact exists_prime_orderOf_dvd_card' 2 h2
  rw [← Subgroup.orderOf_coe] at ht
  have htA : (t : Q) ∈ centralizer (A : Set Q) := h.sylow.le t.2
  obtain ⟨hCt, -⟩ := CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    (h.std.2.1 : CFSG.Assembly.ComponentType.IsStandardSubgroup A) htA ht
  have hnt : ∃ d ∈ CFSG.layer Q, (t : Q)⁻¹ * d * t ≠ d := by
    by_contra hcon
    push Not at hcon
    have hmem : (t : Q) ∈ centralizer (CFSG.layer Q : Set Q) :=
      mem_centralizer_iff.2 fun d hd => by
        calc d * t = t * ((t : Q)⁻¹ * d * t) := by group
          _ = t * d := by rw [hcon d hd]
    rw [h.cen, mem_bot] at hmem
    rw [hmem, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨hn, -, -, K, _, _, hK, ⟨φ⟩⟩ := h.std
  have hcat : Catalog ↥(CFSG.layer Q) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup (CFSG.layer Q)
      (MonoidHom.id _) Function.surjective_id
  exact hSel.survivors_of_datum h.simple hcat (kb_fixedRootDatum h.le ht htA hCt hnt
    (fun P hP hP2 => kb_inf_eq_bot_of_pGroup h.sylow hβ hP hP2) hn hK φ)

end CFSG.CGT.PushingUpLit.CGT6K1
