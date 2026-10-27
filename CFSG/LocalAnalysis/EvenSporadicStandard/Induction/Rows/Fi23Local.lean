module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverAut

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem card_autCentralizer_le_of_allInner {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    {u : H} (hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l) (huK : u ∈ K)
    (hK : K = L ⊓ centralizer ({u} : Set H)) :
    Nat.card (autCentralizer L K) ≤ Nat.card (center ↥K) := by
  classical
  have hKL : K ≤ L := hK ▸ inf_le_left
  have key : ∀ α : autCentralizer L K, ∃ (l : ↥L) (hlK : (l : H) ∈ K),
      (α : MulAut ↥L) = MulAut.conj l ∧ (⟨(l : H), hlK⟩ : ↥K) ∈ center ↥K := by
    intro α
    obtain ⟨l, hl⟩ := hinn α
    have hcomm : ∀ k : H, k ∈ K → (l : H) * k = k * l := by
      intro k hkK
      have hkL : k ∈ L := hKL hkK
      have h1 : (α : MulAut ↥L) ⟨k, hkL⟩ = ⟨k, hkL⟩ := α.2 ⟨k, hkL⟩ hkK
      rw [hl, MulAut.conj_apply] at h1
      have h2 : (l : H) * k * (l : H)⁻¹ = k := congrArg Subtype.val h1
      calc (l : H) * k = ((l : H) * k * (l : H)⁻¹) * l := by group
        _ = k * l := by rw [h2]
    have hlK : (l : H) ∈ K := by
      rw [hK]
      exact ⟨l.2, mem_centralizer_singleton_iff.2 (hcomm u huK)⟩
    refine ⟨l, hlK, hl, ?_⟩
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hcomm k k.2).symm
  choose l hlK hl hcen using key
  refine Nat.card_le_card_of_injective
    (fun α => (⟨⟨(l α : H), hlK α⟩, hcen α⟩ : center ↥K)) ?_
  intro α β hab
  have h1 : l α = l β :=
    Subtype.ext (congrArg (fun z : center ↥K => ((z : ↥K) : H)) hab)
  apply Subtype.ext
  rw [hl α, hl β, h1]

theorem card_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) := by
  have hZ : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
  rw [← hZ, Subgroup.card_map_of_injective e.injective]

theorem nonempty_inf_centralizer_mulEquiv {H Y : Type} [Group H] [Group Y] {L : Subgroup H}
    (ψ : ↥L ≃* Y) {u : H} (hu : u ∈ L) :
    Nonempty (↥(L ⊓ centralizer ({u} : Set H)) ≃* ↥(centralizer ({ψ ⟨u, hu⟩} : Set Y))) := by
  have h1 : (L ⊓ centralizer ({u} : Set H)).subgroupOf L =
      centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  exact ⟨(Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    ((MulEquiv.subgroupCongr h1).trans (CFSG.Fischer.centralizerEquiv ψ ⟨u, hu⟩))⟩

theorem card_center_inf_centralizer_of_isConj {H Y : Type} [Group H] [Group Y] {L : Subgroup H}
    (ψ : ↥L ≃* Y) {u : H} (hu : u ∈ L) {d : Y} (hconj : IsConj d (ψ ⟨u, hu⟩)) :
    Nat.card (center ↥(L ⊓ centralizer ({u} : Set H))) =
      Nat.card (center ↥(centralizer ({d} : Set Y))) := by
  obtain ⟨e1⟩ := nonempty_inf_centralizer_mulEquiv ψ hu
  obtain ⟨c, hcx⟩ := isConj_iff.1 hconj
  have e2 : ↥(centralizer ({d} : Set Y)) ≃* ↥(centralizer ({ψ ⟨u, hu⟩} : Set Y)) :=
    (CFSG.Fischer.centralizerEquiv (MulAut.conj c) d).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hcx]))
  exact card_center_congr (e1.trans e2.symm)

section Certificates


theorem fi23_card_center_inf_centralizer {H : Type} [Group H] {L : Subgroup H}
    (hL : IsSporadic ↥L .Fi23) {u : H} (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hc : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = 129123503308800) :
    Nat.card (center ↥(L ⊓ centralizer ({u} : Set H))) = 2 := by
  obtain ⟨e⟩ := hL
  let ψ : ↥L ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hx2 : orderOf (ψ ⟨u, hu⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  have hcard : Nat.card ↥(centralizer ({ψ ⟨u, hu⟩} : Set CFSG.Sporadic.Fi23.J)) =
      129123503308800 := by
    rw [← @fi23_card_inf_centralizer_eq H CFSG.Sporadic.Fi23.J _ (inferInstance) L ψ u hu]
    exact hc
  rw [@card_center_inf_centralizer_of_isConj H CFSG.Sporadic.Fi23.J _ (inferInstance) L ψ u hu
    CFSG.Sporadic.Fi23.d (fi23J_isConj_d_of_card hx2 hcard)]
  exact CFSG.Sporadic.Fi23.card_center_C

@[expose] def Fi23FixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .Fi23 L →
    fiLoc (2 * 64561751654400) H L K u → InvolutionFixesElem ↥K 16

theorem lemma36DataQ_fi23 (hmult : OddMultTrivial .Fi23) (hfix : Fi23FixesElem) :
    Lemma36DataQ .Fi23 (fiLoc (2 * 64561751654400)) 2 16 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hQ
  have hL : IsSporadic ↥L .Fi23 := hcov.isSporadic_of_mult hmult
  obtain ⟨e⟩ := hL
  obtain ⟨huL, hu2, hKL, hKu, hKq, hsz⟩ := id hQ
  have hX : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hle := fi23_card_inf_centralizer_le ⟨e⟩ huL hu2
  have hKcard : 129123503308800 ≤ Nat.card ↥K := by
    have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    omega
  have hKX : K = L ⊓ centralizer ({u} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hX (hle.trans hKcard)
  have hcard : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = 129123503308800 :=
    le_antisymm hle (hKcard.trans (Subgroup.card_le_of_le hX))
  have hZ := fi23_card_center_inf_centralizer ⟨e⟩ huL hu2 hcard
  have hZK : Nat.card (center ↥K) = 2 := by rw [hKX]; exact hZ
  have huK : u ∈ K := by
    rw [hKX]
    exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩
  have hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have hC : Nat.card (autCentralizer L K) ≤ 4 :=
    (card_autCentralizer_le_of_allInner hinn huK hKX).trans (by rw [hZK]; norm_num)
  have hchar : (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic := by
    have : K.subgroupOf (L ⊓ centralizer ({u} : Set H)) = ⊤ :=
      Subgroup.subgroupOf_eq_top.2 hKX.ge
    rw [this]
    infer_instance
  exact ⟨hu2, huK, hX, hchar, hKq, isSolvable_autCentralizer_of_card_le hC,
    twoAdic_le_two_of_card_le_four _ hC, hfix H L K u hcov hQ⟩

end Certificates

end CFSG.EvenSporadicStandard.Induction
