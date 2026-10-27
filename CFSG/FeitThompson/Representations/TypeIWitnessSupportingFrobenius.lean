module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.TypeISmallerPrimeFrobenius

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {p d : ℕ} {X Y : Type*} [Group X] [Group Y]

theorem mem_elementaryAbelianRanks_of_injective {f : X →* Y} (hf : Function.Injective f)
    (h : d ∈ elementaryAbelianRanks p X) : d ∈ elementaryAbelianRanks p Y := by
  obtain ⟨A, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1 h
  exact mem_elementaryAbelianRanks.2 ⟨A.map f, ⟨(A.equivMapOfInjective f hf).symm.trans e⟩⟩

section

variable {G : Type*} [Group G]

open CFSG.FeitThompson.Prep05

theorem not_isTIWithNormalizer_hallCoreSharp_of_centralizer_not_le {L : Subgroup G} {x : G}
    (hx : x ∈ hallCoreOf L) (hx1 : x ≠ 1) (hC : ¬ centralizer ({x} : Set G) ≤ L) :
    ¬ IsTIWithNormalizer (hallCoreSharp L) L := by
  intro hTI
  obtain ⟨g, hgC, hgL⟩ := Set.not_subset.1 hC
  have hxD : x ∈ hallCoreSharp L := mem_hallCoreSharp.2 ⟨hx, hx1⟩
  refine Set.disjoint_left.1 (hTI.disjoint_conj_image g hgL) hxD ⟨x, hxD, ?_⟩
  have hgx : g * x = x * g := (Subgroup.mem_centralizer_singleton_iff).1 hgC
  simp only [MulAut.conj_apply]
  rw [hgx]
  group

theorem subgroupOf_le_hallCore_of_le_hallCoreOf {L P : Subgroup G} (hP : P ≤ hallCoreOf L) :
    P.subgroupOf L ≤ hallCore ↥L := by
  have h := Subgroup.comap_mono (f := L.subtype) hP
  rwa [hallCoreOf_eq, Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h

theorem mem_elementaryAbelianRanks_hallCore_of_le_hallCoreOf {L P : Subgroup G}
    (hP : P ≤ hallCoreOf L) (h : d ∈ elementaryAbelianRanks p ↥P) :
    d ∈ elementaryAbelianRanks p ↥(hallCore ↥L) := by
  have hPL : P ≤ L := hP.trans (hallCoreOf_le L)
  have hsub : P.subgroupOf L ≤ hallCore ↥L := subgroupOf_le_hallCore_of_le_hallCoreOf hP
  refine mem_elementaryAbelianRanks_of_injective
    (f := (Subgroup.inclusion hsub).comp (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom) ?_ h
  exact (Subgroup.inclusion_injective hsub).comp
    (Subgroup.subgroupOfEquivOfLe hPL).symm.injective

theorem natCard_hallCoreOf_eq (L : Subgroup G) :
    Nat.card ↥(hallCoreOf L) = Nat.card ↥(hallCore ↥L) := by
  rw [hallCoreOf_eq]
  exact (Nat.card_eq_of_bijective _ (Subgroup.equivMapOfInjective _ _
    L.subtype_injective).bijective).symm

theorem map_subtype_ne_bot_of_ne_bot {L : Subgroup G} {U : Subgroup ↥L} (hU : U ≠ ⊥) :
    U.map L.subtype ≠ ⊥ := by
  intro hbot
  refine hU ?_
  rw [← Subgroup.comap_map_eq_self_of_injective L.subtype_injective (H := U), hbot]
  simp

theorem isInternalSemidirectProduct_hallCoreOf_map {L : Subgroup G} {U : Subgroup ↥L}
    (hU : (hallCore ↥L).IsComplement' U) :
    FreeCore.IsInternalSemidirectProduct L (hallCoreOf L) (U.map L.subtype) where
  sup_eq := by
    rw [hallCoreOf_eq, ← Subgroup.map_sup, hU.sup_eq_top]
    exact le_antisymm (Subgroup.map_subtype_le _) fun x hx => ⟨⟨x, hx⟩, trivial, rfl⟩
  le_normalizer := le_normalizer_map_subtype_hallCore L
  disjoint := by
    rw [disjoint_iff, hallCoreOf_eq, ← Subgroup.map_inf_eq _ _ _ L.subtype_injective,
      hU.disjoint.eq_bot]
    simp

theorem isFixedPointFreeOn_map_subtype {L : Subgroup G} {U : Subgroup ↥L}
    (hfree : ∀ u ∈ U, u ≠ 1 → hallCore ↥L ⊓ centralizer {u} = ⊥) :
    IsFixedPointFreeOn (hallCoreOf L) (U.map L.subtype) := by
  intro b hb hb1
  obtain ⟨u, hu, rfl⟩ := hb
  have hu1 : u ≠ 1 := fun h => hb1 (by rw [h]; rfl)
  rw [centralizerIn_eq, centralizer_coe_zpowers]
  refine le_antisymm (fun z hz => ?_) bot_le
  have hzH : z ∈ hallCoreOf L := hz.1
  have hzC : z ∈ centralizer ({(L.subtype u : G)} : Set G) := hz.2
  have hzL : z ∈ L := hallCoreOf_le L hzH
  have hzmem : (⟨z, hzL⟩ : ↥L) ∈ hallCore ↥L ⊓ centralizer {u} :=
    ⟨subgroupOf_le_hallCore_of_le_hallCoreOf (le_refl (hallCoreOf L)) hzH,
      (Subgroup.mem_centralizer_singleton_iff (G := ↥L)).2
        (Subtype.ext ((Subgroup.mem_centralizer_singleton_iff).1 hzC))⟩
  rw [hfree u hu hu1] at hzmem
  have h1 : (⟨z, hzL⟩ : ↥L) = 1 := hzmem
  simpa [Subtype.ext_iff] using h1

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_i_witness_supporting_frobenius
    (hdade : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_i_witness_supporting_frobenius.{u} := by
  intro G _ _ hG p hp hsmall M L hM hL hMI hLI P hPM hPcomm hPp hrank hPsig x hxP hxord hnorm hnotle
  have hG' : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hSL, -, -, -, -, -, -, -, hiv⟩ := hdade G hG' L hL hLI
  have hPH : P ≤ hallCoreOf L := hPsig.trans (le_of_eq hSL)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hp.one_lt.ne' hxord.symm
  have hxH : x ∈ hallCoreOf L := hPH hxP
  have hnotTI : ¬ IsTIWithNormalizer (hallCoreSharp L) L :=
    not_isTIWithNormalizer_hallCoreSharp_of_centralizer_not_le hxH hx1 hnotle
  have hplaneP : 2 ∈ elementaryAbelianRanks p ↥P := by
    rw [← hrank]
    exact elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt
  have hplane : 2 ∈ elementaryAbelianRanks p ↥(hallCore ↥L) :=
    mem_elementaryAbelianRanks_hallCore_of_le_hallCoreOf hPH hplaneP
  have hsmall' : ∀ q : ℕ, q.Prime → q < p → 2 ∈ elementaryAbelianRanks q ↥L →
      q ∣ Nat.card ↥(hallCore ↥L) := by
    intro q hq hqp hplaneq
    rw [← natCard_hallCoreOf_eq L]
    exact hsmall q hq hqp L hL hLI (le_elementaryAbelianPRank hq.one_lt hplaneq)
  obtain ⟨U, hUbot, hUcompl, hUfree⟩ :=
    exists_isComplement'_hallCore_of_isTypeI hG.odd_natCard hLI hnotTI hp hplane hsmall'
  have hxA : x ∈ CFSG.FeitThompson.Prep09.coreFixedSet
      (CFSG.FeitThompson.Prep09.hallCoreIn L) L := by
    refine ⟨hallCoreOf_le L hxH, hx1, fun hbot => ?_⟩
    have hmem : x ∈ CFSG.FeitThompson.Prep09.centIn
        (CFSG.FeitThompson.Prep09.hallCoreIn L) {x} :=
      ⟨hxH, (Subgroup.mem_centralizer_singleton_iff).2 rfl⟩
    rw [hbot] at hmem
    exact hx1 hmem
  obtain ⟨-, T, hTu, -, -, hTsd, -, -, -, -⟩ := hiv x hxA hnotle
  have hCM : centralizer ({x} : Set G) ≤ M := by
    refine le_trans ?_ hnorm
    rw [← centralizer_coe_zpowers x]
    exact Subgroup.centralizer_le_normalizer _
  have hTM : T = M := (hTu.eq_of_isCoatom hM hCM).symm
  subst hTM
  refine ⟨hPH, ⟨U.map L.subtype, Subgroup.map_subtype_le _, map_subtype_ne_bot_of_ne_bot hUbot,
    isInternalSemidirectProduct_hallCoreOf_map hUcompl,
    isFixedPointFreeOn_map_subtype hUfree⟩, ?_, hTu⟩
  rw [inf_comm]
  exact hTsd

end CFSG.FeitThompson.Proofs
