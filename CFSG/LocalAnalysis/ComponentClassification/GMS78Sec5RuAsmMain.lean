module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmEnd
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmGlueP
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7

theorem injective_of_ruHom {P G : Type} [Group P] [Group G]
    (eP : P ≃* Blueprint.NativeSporadic.Ru) (Φ : P →* G) {z : G} (hz : z ∈ Φ.range)
    (hz1 : z ≠ 1) : Function.Injective Φ := by
  have hsRu : IsSimpleGroup Blueprint.NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hsP : IsSimpleGroup P := @MulEquiv.isSimpleGroup P _ Blueprint.NativeSporadic.Ru _ hsRu eP
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hsP.eq_bot_or_eq_top_of_normal Φ.ker with h | h
  · exact h
  · exfalso
    obtain ⟨y, rfl⟩ := hz
    exact hz1 (MonoidHom.mem_ker.mp (h ▸ mem_top y))

theorem nonempty_mulEquiv_ru_of_edgeAgree
    {R : List (List (Fin 7 × Bool))} (eP : PG 7 R ≃* Blueprint.NativeSporadic.Ru)
    (hR : ∀ r ∈ R, ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) ∧ pi7Word r = 1) ∨
      ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))) ∧ pi7Word r = 1) ∨ r = ruW7Word)
    {G : Type} [Group G] [Finite G] {z e : G} {A : Subgroup G}
    (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))) (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hag : RuEdgeAgree f₁ f₂ (MonoidHom.id _))
    (hw : (ruLetterImg f₁ f₂ 5 * ruLetterImg f₁ f₂ 0 * ruLetterImg f₁ f₂ 2 *
      ruLetterImg f₁ f₂ 6) ^ 7 = 1)
    (hz2 : orderOf z = 2) (hzc : 2 ^ 9 ∣ Nat.card (centralizer ({z} : Set G)))
    (he : e ∈ normalizer (A : Set G)) (he2 : orderOf e = 2)
    (hec : Nat.card (centralizer ({e} : Set G)) = 116480) :
    Nonempty (G ≃* Blueprint.NativeSporadic.Ru) := by
  obtain ⟨Φ, -, hC, hN⟩ := exists_hom_of_edgeAgree hR f₁ f₂ hag hw
  have hz : z ∈ Φ.range := hC (mem_centralizer_singleton_iff.mpr rfl)
  have htop := range_eq_top_of_ruHom eP Φ hz hz2 hC hzc (hN he) he2 hec
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hbij : Function.Bijective Φ :=
    ⟨injective_of_ruHom eP Φ hz hz1, MonoidHom.range_eq_top.mp htop⟩
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm.trans eP⟩

end CFSG.ComponentClassification.GMS78.RuAsm

namespace CFSG.ComponentClassification.GMS78.SzMinCounter

open Subgroup CFSG.ComponentClassification.RankTwoStandard

theorem false_of_mulEquiv_ru {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hM : SzMinCounter G L 1) (eG : G ≃* Blueprint.NativeSporadic.Ru) : False := by
  have hsRu : IsSimpleGroup Blueprint.NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hsG : IsSimpleGroup G :=
    @MulEquiv.isSimpleGroup G _ Blueprint.NativeSporadic.Ru _ hsRu eG
  have hX : rankTwoX L = ⊤ := by
    rcases hsG.eq_bot_or_eq_top_of_normal (rankTwoX L) with h | h
    · exfalso
      apply hM.hyp.not_normal
      have hL : L = ⊥ := eq_bot_iff.mpr (le_normalClosure.trans h.le)
      rw [hL]
      infer_instance
    · exact h
  exact hM.not_concl ⟨rfl, ⟨((MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv).trans eG⟩⟩

end CFSG.ComponentClassification.GMS78.SzMinCounter
