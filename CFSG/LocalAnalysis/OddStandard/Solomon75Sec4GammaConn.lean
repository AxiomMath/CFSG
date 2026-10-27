module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Subgroup CFSG.Open
open scoped commutatorElement

@[expose] def RankThreeVertex {K : Type*} [Group K] (S E : Subgroup K) : Prop :=
  E ≤ S ∧ IsElemAbelian 2 E ∧ 8 ≤ Nat.card E

@[expose] def RankThreeAdj {K : Type*} [Group K] (S E E' : Subgroup K) : Prop :=
  RankThreeVertex S E ∧ RankThreeVertex S E' ∧ 4 ≤ Nat.card ↥(E ⊓ E')

theorem rankThreeAdj_symm {K : Type*} [Group K] {S E E' : Subgroup K}
    (h : RankThreeAdj S E E') : RankThreeAdj S E' E :=
  ⟨h.2.1, h.1, by rw [inf_comm]; exact h.2.2⟩

namespace RankThreeHub

theorem isElemAbelian_closure_of_comm {K : Type*} [Group K] (G : Set K)
    (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a) (hsq : ∀ a ∈ G, a * a = 1) :
    IsElemAbelian 2 (Subgroup.closure G) := by
  have hC : IsMulCommutative (Subgroup.closure G) :=
    Subgroup.isMulCommutative_closure fun a ha b hb _ => hcomm a ha b hb
  refine ⟨hC, fun x hx => ?_⟩
  rw [pow_two]
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := congrArg Subtype.val (hC.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, mul_one]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

theorem commutator_mul_of_central {K : Type*} [Group K] {y a b : K}
    (ha : ⁅a, y⁆ ∈ center K) (hb : ⁅b, y⁆ ∈ center K) :
    ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆ := by
  have h1 : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
    rw [mem_center_iff.1 hb a]; group
  rw [h1, h2]
  exact mem_center_iff.1 ha ⁅b, y⁆

theorem card_le_two_mul_card_inf_centralizer {K : Type*} [Group K] [Finite K] {y : K}
    (hZ : Nat.card (center K) = 2) {E : Subgroup K} (hcomm : ∀ e ∈ E, ⁅e, y⁆ ∈ center K) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ centralizer {y}) := by
  let ψ : E →* center K :=
    MonoidHom.mk' (fun e => ⟨⁅(e : K), y⁆, hcomm e e.2⟩) fun a b =>
      Subtype.ext (commutator_mul_of_central (hcomm a a.2) (hcomm b b.2))
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card ψ.range ≤ 2 := hZ ▸ Subgroup.card_le_card_group ψ.range
  have h3 : Nat.card ψ.ker ≤ Nat.card ↥(E ⊓ centralizer {y}) := by
    refine Nat.card_le_card_of_injective
      (fun e => ⟨(e.1 : K), Subgroup.mem_inf.2 ⟨e.1.2, ?_⟩⟩) ?_
    · have he : ψ e.1 = 1 := MonoidHom.mem_ker.1 e.2
      have he' : ⁅(e.1 : K), y⁆ = 1 := congrArg Subtype.val he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_commute.1 he'
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
    _ ≤ Nat.card ψ.ker * 2 := Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card ↥(E ⊓ centralizer {y}) * 2 := Nat.mul_le_mul_right _ h3
    _ = 2 * Nat.card ↥(E ⊓ centralizer {y}) := Nat.mul_comm _ _

theorem isElemAbelian_closure_hub {K : Type*} [Group K] {A : Set K} {y : K}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAs : ∀ a ∈ A, a * a = 1)
    (hy2 : y * y = 1) (hAy : ∀ a ∈ A, a * y = y * a)
    (hZ : ∀ a ∈ center K, a * a = 1) :
    IsElemAbelian 2 (Subgroup.closure (A ∪ {y} ∪ (center K : Set K))) := by
  refine isElemAbelian_closure_of_comm _ ?_ ?_
  · rintro a ((ha | rfl) | ha) b ((hb | rfl) | hb)
    · exact hAc a ha b hb
    · exact hAy a ha
    · exact mem_center_iff.1 hb a
    · exact (hAy b hb).symm
    · rfl
    · exact mem_center_iff.1 hb a
    · exact (mem_center_iff.1 ha b).symm
    · exact (mem_center_iff.1 ha b).symm
    · exact (mem_center_iff.1 ha b).symm
  · rintro a ((ha | rfl) | ha)
    · exact hAs a ha
    · exact hy2
    · exact hZ a ha

theorem two_mul_card_le_of_not_mem {K : Type*} [Group K] [Finite K] {A B : Subgroup K}
    (hAB : A ≤ B) {x : K} (hxB : x ∈ B) (hxA : x ∉ A) : 2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hAB
  have hlt : Nat.card A < Nat.card B :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hAB fun h => hxA (h ▸ hxB))
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c <;> omega
    · exact h
  calc 2 * Nat.card A ≤ c * Nat.card A := Nat.mul_le_mul_right _ hc2
    _ = Nat.card B := by rw [hc, Nat.mul_comm]

theorem sq_eq_one_of_mem_center {K : Type*} [Group K] (hZ : Nat.card (center K) = 2) :
    ∀ a ∈ center K, a * a = 1 := by
  intro a ha
  have h := pow_card_eq_one' (G := ↥(center K)) (x := ⟨a, ha⟩)
  rw [hZ, pow_two] at h
  exact congrArg Subtype.val h

theorem exists_hub_vertex {K : Type*} [Group K] [Finite K] {S : Subgroup K} {y : K}
    (hZ : Nat.card (center K) = 2) (hZS : center K ≤ S) (hyS : y ∈ S) (hy2 : y * y = 1)
    (hcomm : ∀ s ∈ S, ⁅s, y⁆ ∈ center K) {E : Subgroup K} (hE : RankThreeVertex S E) :
    ∃ F : Subgroup K, RankThreeVertex S F ∧ y ∈ F ∧ center K ≤ F ∧ RankThreeAdj S E F := by
  obtain ⟨hES, hEab, hE8⟩ := hE
  have hcard : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ centralizer {y}) :=
    card_le_two_mul_card_inf_centralizer hZ fun e he => hcomm e (hES he)
  obtain ⟨F, hF⟩ : ∃ F : Subgroup K, F = Subgroup.closure
      (((E ⊓ centralizer {y} : Subgroup K) : Set K) ∪ {y} ∪ (center K : Set K)) := ⟨_, rfl⟩
  have hE₁F : E ⊓ centralizer {y} ≤ F := by
    rw [hF]; exact fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hyF : y ∈ F := by
    rw [hF]; exact Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hZF : center K ≤ F := by
    rw [hF]; exact fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hFS : F ≤ S := by
    rw [hF, Subgroup.closure_le]
    rintro x ((hx | hx) | hx)
    · exact hES (Subgroup.mem_inf.1 hx).1
    · rw [Set.mem_singleton_iff.1 hx]; exact hyS
    · exact hZS hx
  have hFab : IsElemAbelian 2 F := by
    rw [hF]
    refine isElemAbelian_closure_hub (fun a ha b hb => ?_) (fun a ha => ?_) hy2
      (fun a ha => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2)
      (sq_eq_one_of_mem_center hZ)
    · exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, (Subgroup.mem_inf.1 ha).1⟩
        ⟨b, (Subgroup.mem_inf.1 hb).1⟩)
    · exact (pow_two a).symm.trans (hEab.2 a (Subgroup.mem_inf.1 ha).1)
  have hEF : Nat.card E ≤ Nat.card F := by
    by_cases hyE : y ∈ E
    · refine Subgroup.card_le_of_le fun x hx => hE₁F (Subgroup.mem_inf.2 ⟨hx, ?_⟩)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hyE⟩)
    · exact hcard.trans
        (two_mul_card_le_of_not_mem hE₁F hyF fun h => hyE (Subgroup.mem_inf.1 h).1)
  have hinf : Nat.card ↥(E ⊓ centralizer {y}) ≤ Nat.card ↥(E ⊓ F) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hE₁F)
  have hF8 : 8 ≤ Nat.card F := hE8.trans hEF
  exact ⟨F, ⟨hFS, hFab, hF8⟩, hyF, hZF, ⟨hES, hEab, hE8⟩, ⟨hFS, hFab, hF8⟩, by omega⟩

theorem adj_of_hub {K : Type*} [Group K] [Finite K] {S F F' : Subgroup K} {y : K}
    (hZ : Nat.card (center K) = 2) (hyc : y ∉ center K)
    (hF : RankThreeVertex S F) (hF' : RankThreeVertex S F')
    (hyF : y ∈ F) (hyF' : y ∈ F') (hZF : center K ≤ F) (hZF' : center K ≤ F') :
    RankThreeAdj S F F' := by
  refine ⟨hF, hF', ?_⟩
  have h := two_mul_card_le_of_not_mem (le_inf hZF hZF') (Subgroup.mem_inf.2 ⟨hyF, hyF'⟩) hyc
  omega

end RankThreeHub

theorem rankThree_connected_of_hub {K : Type*} [Group K] [Finite K] {S : Subgroup K} {y : K}
    (hz2 : Nat.card (center K) = 2) (hzS : center K ≤ S)
    (hyS : y ∈ S) (hy2 : y * y = 1) (hyc : y ∉ center K)
    (hcomm : ∀ s ∈ S, ⁅s, y⁆ ∈ center K) {E E' : Subgroup K}
    (hE : RankThreeVertex S E) (hE' : RankThreeVertex S E') :
    Relation.ReflTransGen (RankThreeAdj S) E E' := by
  obtain ⟨F, hF, hyF, hZF, hEF⟩ := RankThreeHub.exists_hub_vertex hz2 hzS hyS hy2 hcomm hE
  obtain ⟨F', hF', hyF', hZF', hEF'⟩ := RankThreeHub.exists_hub_vertex hz2 hzS hyS hy2 hcomm hE'
  have hFF' : RankThreeAdj S F F' := RankThreeHub.adj_of_hub hz2 hyc hF hF' hyF hyF' hZF hZF'
  exact ((Relation.ReflTransGen.single hEF).tail hFF').tail (rankThreeAdj_symm hEF')

end CFSG.OddStandard.Solomon75.AhatData
