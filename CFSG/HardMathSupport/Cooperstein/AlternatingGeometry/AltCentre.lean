module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

theorem odd_card_center_barM_sup (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    Odd (Nat.card (Subgroup.center ↥(barM (L ⊔ S) L))) := by
  set Y := L ⊔ S with hY
  set Q := ↥Y ⧸ CFSG.pCore 2 ↥Y with hQ
  set C : Subgroup Q := barM Y L with hC
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hSL
  have hCn : C.Normal := by
    refine ⟨fun c hc q => ?_⟩
    obtain ⟨⟨l, hl'⟩, hl, rfl⟩ := (mem_barM c).1 hc
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
    refine (mem_barM _).2 ⟨⟨y * l * y⁻¹, ?_⟩, ?_, ?_⟩
    · exact Y.mul_mem (Y.mul_mem hy hl') (Y.inv_mem hy)
    · exact (Subgroup.mem_normalizer_iff.1 (hYN hy) l).1 hl
    · rfl
  have h2 : ∀ q : Q, ∃ e : ℕ, q ^ 2 ^ e ∈ C := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := Coordinator.exists_pow_mem_sup_subgroupOf hA.twoRadical.isPGroup hSL y
    refine ⟨e, (mem_barM _).2 ⟨y ^ 2 ^ e, Subgroup.mem_subgroupOf.1 he, ?_⟩⟩
    rfl
  have hO : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hodd := Coordinator.StarAux.odd_card_centralizer C h2 hO
  have hle : (Subgroup.center ↥C).map C.subtype ≤ Subgroup.centralizer (C : Set Q) := by
    rintro _ ⟨z, hz, rfl⟩ c hc
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨c, hc⟩)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective C.subtype_injective] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

theorem card_center_barM_sup_eq_one (hA : Asc81bHyp (L ⊔ S) S)
    (hL : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {m : ℕ}
    (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) :
    Nat.card (Subgroup.center ↥(barM (L ⊔ S) L)) = 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  set C := barM (L ⊔ S) L with hC
  have hq : CFSG.Open.IsQuasisimple ↥C := hL.component.2.2
  have : Group.IsPerfect ↥C := ⟨hq.1⟩
  let η : ↥C →* alternatingGroup (Fin (m' + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥C))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center ↥C := by
    ext x
    simp only [η, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    rw [show (e.toMonoidHom (QuotientGroup.mk x) = 1) ↔ (QuotientGroup.mk x = 1) from
      ⟨fun h => e.injective (by simpa using h), fun h => by simp [h]⟩]
    exact QuotientGroup.eq_one_iff x
  have hodd := odd_card_center_barM_sup hA hSL
  have := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hηs hker.le
    (by rw [hker]; exact hodd)
  rwa [hker] at this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
