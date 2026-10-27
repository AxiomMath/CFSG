module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Cls
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonTriv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Psp4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem nonswap_nontriv_psp4 (hp : Stage1PSp4 G z S q L₁ L₂) (hz2 : orderOf z = 2) {u : G}
    (huS : u ∈ S) (hu : u ∈ Cen z) (hu2 : u * u = 1) (hu1 : u ∉ zpowers z)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))) :
    Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
      Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1 :=
  actOnK_ne_one_of_mem_LBar (PairShape.of_pair hp.pair) hz2 hu hu2 hu1
    (toBar_mem_LBar (mem_RC_of_nonswap hp huS hu hn₁).2) hn₁ hn₂

theorem lemma29FirstAt_of_psp4 (hND : NonCentralDihedral) {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) (hk : k = Kind.psp4) : Lemma29FirstAt z k := by
  subst hk
  cases ctx.data with
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hq⟩ := h
    obtain ⟨x, htc⟩ := hq.two
    have hz2 : orderOf z = 2 := ctx.central.1
    have hcl : IsClassicalKind Kind.psp4 := Or.inl rfl
    refine lemma29FirstAt_of_pair ctx (PairShape.of_pair hq.pair)
      (fun U hU hno => lemma29Alt_of_no_conj ctx hcl hND hU hno) ?_ ?_
    · intro u huS hu hu2 hu1 hsw U hU hzU huU
      exact lemma29Alt_of_swap_twoClass ctx hcl hND hq.pair.ne hq.pair.comps htc hU hzU huU huS
        hu1 hsw
    · intro u huS hu hu2 hu1 hn₁ hn₂
      exact nonswap_nontriv_psp4 hq hz2 huS hu hu2 hu1 hn₁ hn₂

end Psp4

section L4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool}

theorem lemma29FirstAt_of_l4 (hND : NonCentralDihedral) (ctx : Stage2Ctx G z (Kind.l4 ε) S)
    (hS1 : ∀ {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}, Stage1L4 G z S ε q L₁ L₂ →
      (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ u ∈ S, u ∈ Cen z → u * u = 1 → u ∉ zpowers z → Swaps z u L₁ L₂ →
        ∀ U : Subgroup G, IVK.IsFourSubgroup U → z ∈ U → u ∈ U →
          Lemma29Alt z (Kind.l4 ε) U) :
    Lemma29FirstAt z (Kind.l4 ε) := by
  cases ctx.data with
  | l4 _ h =>
    obtain ⟨q, L₁, L₂, hq⟩ := h
    have hz2 : orderOf z = 2 := ctx.central.1
    have hcl : IsClassicalKind (Kind.l4 ε) := Or.inr ⟨ε, rfl⟩
    refine lemma29FirstAt_of_pair ctx (PairShape.of_pair hq.pair)
      (fun U hU hno => lemma29Alt_of_no_conj ctx hcl hND hU hno) ?_ ?_
    · intro u huS hu hu2 hu1 hsw U hU hzU huU
      rcases hq.fusion with ⟨-, hone⟩ | ⟨-, x, htc, -⟩
      · exact hS1 hq hone u huS hu hu2 hu1 hsw U hU hzU huU
      · exact lemma29Alt_of_swap_twoClass ctx hcl hND hq.pair.ne hq.pair.comps htc hU hzU huU huS
          hu1 hsw
    · intro u huS hu hu2 hu1 hn₁ hn₂
      exact nonswap_nontriv_l4 hq hz2 huS hu hu2 hu1 hn₁ hn₂

end L4

section NonSwap

variable {G : Type} [Group G] [Finite G] {z : G}

theorem hasNormal2Compl_of_nonswap {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hk : IsClassicalKind k) {U : Subgroup G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U)
    (hUS : U ≤ S) (hns : ∀ u ∈ U, ¬ SwapsComps z u) :
    HasNormal2Compl (centralizer (U : Set G)) := by
  have hz2 : orderOf z = 2 := ctx.central.1
  obtain ⟨u, huU, hu1⟩ := exists_mem_not_zpowers hU hzU
  have hu : u ∈ Cen z := by
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU huU hzU
  rcases hk with rfl | ⟨ε, rfl⟩
  · cases ctx.data with
    | psp4 h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      exact (hasNormal2Compl_iff_twoNilp _).mpr
        (twoNilp_centralizer_of_nonswap ctx (PairShape.of_pair hq.pair)
          (fun u huS hu hu2 hu1 hn₁ hn₂ => nonswap_nontriv_psp4 hq hz2 huS hu hu2 hu1 hn₁ hn₂)
          hU hzU huU (hUS huU) hu1 hu
          (fun hsw => hns u huU ⟨L₁, L₂, hq.pair.ne, hq.pair.comps, hsw⟩))
  · cases ctx.data with
    | l4 _ h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      exact (hasNormal2Compl_iff_twoNilp _).mpr
        (twoNilp_centralizer_of_nonswap ctx (PairShape.of_pair hq.pair)
          (fun u huS hu hu2 hu1 hn₁ hn₂ => nonswap_nontriv_l4 hq hz2 huS hu hu2 hu1 hn₁ hn₂)
          hU hzU huU (hUS huU) hu1 hu
          (fun hsw => hns u huU ⟨L₁, L₂, hq.pair.ne, hq.pair.comps, hsw⟩))

end NonSwap

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
