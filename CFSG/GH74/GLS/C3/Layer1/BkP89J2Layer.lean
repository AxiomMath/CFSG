module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1P14Rank
public import CFSG.Walter.AStar.Basic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalCores CFSG.GH74.GLS.Stage1.Thm6.Sec13
  CFSG.GH74.GLS.C3.Layer1.P14
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B810

variable {X : Type} [Group X] [Finite X]

theorem two_dvd_card_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : 2 ∣ Nat.card Q := by
  obtain ⟨-, hs, hnab⟩ := hQ
  have := hs
  exact (CFSG.Walter.even_card_of_isSimpleGroup hnab).two_dvd.trans
    (Subgroup.card_quotient_dvd_card _)

theorem exists_component_center_ne_bot {z : X} (hz2 : orderOf z = 2) (hzc : z ∈ center X)
    (hpc : pCore 2 X = zpowers z) (hpp : pPrimeCore 2 X = ⊥) {S : Subgroup X}
    (hS : IsSylowOf 2 S ⊤) (hScent : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s = 1 ∨ s = z)
    {P : Subgroup X} (hP3 : 3 ∣ Nat.card P) :
    ∃ K : Subgroup X, IsComponent K ∧ center ↥K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlayer : layer X ≠ ⊥ := by
    intro hl
    have hchar := isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 2 hpp hl
    have hall : ∀ g : X, g ∈ zpowers z := by
      intro g
      have hg : g ∈ Subgroup.centralizer (pCore 2 X : Set X) := by
        rw [hpc, Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hzc n) g).symm
      have := (show Subgroup.centralizer (pCore 2 X : Set X) ≤ pCore 2 X from hchar) hg
      rwa [hpc] at this
    have hcardX : Nat.card X = 2 := by
      have htop : zpowers z = ⊤ := eq_top_iff.2 fun g _ => hall g
      rw [← Subgroup.card_top (G := X), ← htop, Nat.card_zpowers, hz2]
    have := dvd_trans hP3 (Subgroup.card_subgroup_dvd_card P)
    rw [hcardX] at this
    omega
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subgroup X, IsComponent K₀ := by
    by_contra hno
    exact hlayer (layer_eq_bot_of_forall fun K hK => hno ⟨K, hK⟩)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₀) 2
    (two_dvd_card_of_quasisimple hK₀.1)
  have hu' : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have huL : (u : X) ∈ layer X := component_le_layer hK₀ u.2
  have hS2 : Sylow2In S ⊤ := isSylowOf_iff.1 hS
  have hpg : IsPGroup 2 ↥(zpowers (u : X)) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hu']; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow2In hS2 hpg
  have hwS : g * (u : X) * g⁻¹ ∈ S :=
    hg (Subgroup.mem_map.2 ⟨(u : X), Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩)
  have hchar : (layer X).Characteristic := layer_characteristic (G := X)
  have : (layer X).Normal := inferInstance
  have hwL : g * (u : X) * g⁻¹ ∈ layer X := Subgroup.Normal.conj_mem inferInstance _ huL g
  have hw1 : g * (u : X) * g⁻¹ ≠ 1 := by
    intro h
    have h1 : (u : X) = 1 := by
      have : (u : X) = g⁻¹ * (g * (u : X) * g⁻¹) * g := by group
      rw [this, h]
      group
    rw [h1, orderOf_one] at hu'
    omega
  have : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
  have hH : (layer X).subgroupOf S ≠ ⊥ := by
    intro hbot
    have : (⟨g * (u : X) * g⁻¹, hwS⟩ : ↥S) ∈ (layer X).subgroupOf S := hwL
    rw [hbot, Subgroup.mem_bot] at this
    exact hw1 (congrArg Subtype.val this)
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  obtain ⟨hcH, hcZ⟩ := Subgroup.mem_inf.1 hc
  have hcc : ∀ t ∈ S, (c : X) * t = t * (c : X) := fun t ht =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcZ ⟨t, ht⟩)).symm
  have hzL : z ∈ layer X := by
    rcases hScent (c : X) c.2 hcc with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hc1
    · rw [← h]
      exact hcH
  have hzcenter : z ∈ (center (layer X)).map (layer X).subtype :=
    (mem_map_center_iff (layer X)).2 ⟨hzL, Subgroup.mem_centralizer_iff.2 fun h _ =>
      Subgroup.mem_center_iff.1 hzc h⟩
  rw [(layer_center (G := X)).1] at hzcenter
  by_contra hcon
  have hno : ∀ K : Subgroup X, IsComponent K → center ↥K = ⊥ := fun K hK => by
    by_contra h
    exact hcon ⟨K, hK, h⟩
  have hbot : (⨆ K : ComponentIndex X, (center K.1).map K.1.subtype) = ⊥ := by
    refine iSup_eq_bot.2 fun K => ?_
    rw [hno K.1 K.2]
    exact Subgroup.map_bot _
  rw [hbot, Subgroup.mem_bot] at hzcenter
  rw [hzcenter, orderOf_one] at hz2
  omega

theorem exists_conj_sylow_le {S : Subgroup X} (hS : IsSylowOf 2 S ⊤) (hScard : Nat.card S = 2 ^ 7)
    {K : Subgroup X} (hK : (Nat.card K).factorization 2 = 7) :
    ∃ g : X, S ≤ K.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  have hQp : IsPGroup 2 ↥((Q : Subgroup ↥K).map K.subtype) := Q.isPGroup'.map K.subtype
  have hQcard : Nat.card ↥((Q : Subgroup ↥K).map K.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity, hK]
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow2In (isSylowOf_iff.1 hS) hQp
  have hmapcard : Nat.card ↥(((Q : Subgroup ↥K).map K.subtype).map
      (MulAut.conj g).toMonoidHom) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQcard]
  have heq := Subgroup.eq_of_le_of_card_ge hg (by rw [hScard, hmapcard])
  refine ⟨g, ?_⟩
  rw [← heq]
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

theorem eq_of_isComponent_of_sylow_le {z : X} (hz2 : orderOf z = 2) {S : Subgroup X}
    (hS : IsSylowOf 2 S ⊤) (hScent : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s = 1 ∨ s = z)
    {K : Subgroup X} (hK : IsComponent K) (hSK : S ≤ K) {J : Subgroup X} (hJ : IsComponent J) :
    J = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases distinct_components_commute hJ hK with h | h
  · exact h
  exfalso
  have hJc : J ≤ centralizer (K : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hJS : J ≤ centralizer (S : Set X) := hJc.trans (Subgroup.centralizer_le hSK)
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 ↥J))
  have hR'p : IsPGroup 2 ↥((R : Subgroup ↥J).map J.subtype) := R.isPGroup'.map J.subtype
  have hR'J : (R : Subgroup ↥J).map J.subtype ≤ J := Subgroup.map_subtype_le _
  have hSR' : S ≤ centralizer (((R : Subgroup ↥J).map J.subtype : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.2 (hR'J.trans hJS)
  have hSnorm : S ≤ normalizer (((R : Subgroup ↥J).map J.subtype : Subgroup X) : Set X) :=
    hSR'.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(S ⊔ (R : Subgroup ↥J).map J.subtype) :=
    hS.isPGroup.to_sup_of_normal_right' hR'p hSnorm
  have hSR : S ⊔ (R : Subgroup ↥J).map J.subtype = S := hS.eq_of_le le_sup_left le_top hsup
  have hR'S : (R : Subgroup ↥J).map J.subtype ≤ S := hSR ▸ le_sup_right
  have hR'z : (R : Subgroup ↥J).map J.subtype ≤ zpowers z := by
    intro r hr
    have hrS : r ∈ S := hR'S hr
    have hrc : ∀ t ∈ S, r * t = t * r := fun t ht =>
      ((Subgroup.mem_centralizer_iff.1 (hJS (hR'J hr)) t ht)).symm
    rcases hScent r hrS hrc with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers z
  have hRcard : Nat.card ↥(R : Subgroup ↥J) ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hR'z
    rw [Nat.card_zpowers, hz2, Subgroup.card_map_of_injective J.subtype_injective] at h1
    exact h1
  have : Group.IsPerfect ↥J := hJ.1.1
  have hRne : (R : Subgroup ↥J) ≠ ⊥ := by
    intro hbot
    have hidx := R.not_dvd_index
    rw [hbot, Subgroup.index_bot] at hidx
    exact hidx (two_dvd_card_of_quasisimple hJ.1)
  have h4 := CFSG.GroupTheory.four_le_index_center_subgroupOf_sylow_two R hRne
  have hdvd := Subgroup.index_dvd_card ((center ↥J).subgroupOf (R : Subgroup ↥J))
  have := Nat.le_of_dvd Nat.card_pos hdvd
  omega

omit [Finite X] in
theorem perfect_le_of_solvable_quotient (K : Subgroup X) [K.Normal]
    (hsolv : Group.IsSolvable (X ⧸ K)) {P : Subgroup X} (hP : ⁅P, P⁆ = P) : P ≤ K := by
  have key : ∀ n : ℕ, P.map (QuotientGroup.mk' K) ≤ derivedSeries (X ⧸ K) n := by
    intro n
    induction n with
    | zero => simp [derivedSeries_zero]
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P.map (QuotientGroup.mk' K) = (⁅P, P⁆).map (QuotientGroup.mk' K) := by rw [hP]
        _ = ⁅P.map (QuotientGroup.mk' K), P.map (QuotientGroup.mk' K)⁆ :=
          Subgroup.map_commutator _ _ _
        _ ≤ ⁅derivedSeries (X ⧸ K) n, derivedSeries (X ⧸ K) n⁆ := Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := hsolv.solvable
  have := key n
  rwa [hn, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this

end CFSG.GH74.GLS.C3.Layer1.Bk.B810
