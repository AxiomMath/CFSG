module

import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Joins

variable {G : Type} [Group G]

theorem mem_Q_of_mem_sup {X A : Subgroup G} (hAX : A ≤ X) {w : G} (hwX : w ∈ X)
    (hw : w ∈ A ⊔ centralizer (A : Set G)) : w ∈ A ⊔ (X ⊓ centralizer (A : Set G)) := by
  obtain ⟨j, hj, c, hc, rfl⟩ := exists_mul_of_mem_sup (A := A) (B := centralizer (A : Set G))
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hw
  have hcX : c ∈ X := by
    have : c = j⁻¹ * (j * c) := by group
    rw [this]
    exact X.mul_mem (X.inv_mem (hAX hj)) hwX
  exact Subgroup.mul_mem_sup hj ⟨hcX, hc⟩

theorem mem_sup_centralizer_two {J J' : Subgroup G} (hcomm : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a)
    {w : G} (h1 : w ∈ J ⊔ centralizer (J : Set G)) (h2 : w ∈ J' ⊔ centralizer (J' : Set G)) :
    w ∈ (J ⊔ J') ⊔ centralizer ((J ⊔ J' : Subgroup G) : Set G) := by
  obtain ⟨j, hj, c, hc, hjc⟩ := exists_mul_of_mem_sup (A := J) (B := centralizer (J : Set G))
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) h1
  obtain ⟨j', hj', c', hc', hjc'⟩ := exists_mul_of_mem_sup (A := J')
    (B := centralizer (J' : Set G)) (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) h2
  have hjj' : j * j' = j' * j := hcomm j hj j' hj'
  have e1 : (j * j')⁻¹ * w = j'⁻¹ * c := by rw [← hjc]; group
  have e2 : (j * j')⁻¹ * w = j⁻¹ * c' := by rw [hjj', ← hjc']; group
  have hc₀J : ∀ a ∈ J, a * ((j * j')⁻¹ * w) = ((j * j')⁻¹ * w) * a := by
    intro a ha
    rw [e1]
    have h1 : a * j'⁻¹ = j'⁻¹ * a := by
      have := hcomm a ha j' hj'
      calc a * j'⁻¹ = j'⁻¹ * (j' * a) * j'⁻¹ := by group
        _ = j'⁻¹ * (a * j') * j'⁻¹ := by rw [this]
        _ = j'⁻¹ * a := by group
    have h2 : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a ha
    calc a * (j'⁻¹ * c) = (a * j'⁻¹) * c := by group
      _ = j'⁻¹ * (a * c) := by rw [h1]; group
      _ = j'⁻¹ * (c * a) := by rw [h2]
      _ = (j'⁻¹ * c) * a := by group
  have hc₀J' : ∀ a ∈ J', a * ((j * j')⁻¹ * w) = ((j * j')⁻¹ * w) * a := by
    intro a ha
    rw [e2]
    have h1 : a * j⁻¹ = j⁻¹ * a := by
      have := hcomm j hj a ha
      calc a * j⁻¹ = j⁻¹ * (j * a) * j⁻¹ := by group
        _ = j⁻¹ * (a * j) * j⁻¹ := by rw [← this]
        _ = j⁻¹ * a := by group
    have h2 : a * c' = c' * a := Subgroup.mem_centralizer_iff.mp hc' a ha
    calc a * (j⁻¹ * c') = (a * j⁻¹) * c' := by group
      _ = j⁻¹ * (a * c') := by rw [h1]; group
      _ = j⁻¹ * (c' * a) := by rw [h2]
      _ = (j⁻¹ * c') * a := by group
  have hsup : (J ⊔ J' : Subgroup G) ≤ centralizer ({(j * j')⁻¹ * w} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc₀J a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc₀J' a ha)
  have hc₀ : (j * j')⁻¹ * w ∈ centralizer ((J ⊔ J' : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hsup hh)
  have hw : w = (j * j') * ((j * j')⁻¹ * w) := by group
  rw [hw]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
    (Subgroup.mem_sup_right hj')) hc₀

theorem mem_normalizer_inf3 [Finite G] {A B C : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G))
    (hC : g ∈ normalizer (C : Set G)) : g ∈ normalizer ((A ⊓ B ⊓ C : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hA, hB⟩, hC⟩

end Joins

section Norm

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_commutator_eq {J : Subgroup G} {z : G} (h : ⁅J, zpowers z⁆ = J) :
    z ∈ normalizer (J : Set G) := by
  refine mem_normalizer_of_forall_conj fun j hj => ?_
  have h1 : ⁅j⁻¹, z⁆ ∈ ⁅J, zpowers z⁆ :=
    Subgroup.commutator_mem_commutator (J.inv_mem hj) (Subgroup.mem_zpowers z)
  rw [h] at h1
  have h2 : z * j * z⁻¹ = j * ⁅j⁻¹, z⁆ := by simp only [commutatorElement_def]; group
  rw [h2]
  exact J.mul_mem hj h1

end Norm

section Cyclic

theorem isCyclic_of_le {K : Type} [Group K] {A B : Subgroup K} [IsCyclic ↥B] (h : A ≤ B) :
    IsCyclic ↥A := by
  have : IsCyclic ↥(A.subgroupOf B) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    fun a => ⟨(Subgroup.subgroupOfEquivOfLe h).symm a,
      (Subgroup.subgroupOfEquivOfLe h).apply_symm_apply a⟩

variable {G : Type} [Group G]

theorem isCyclic_Pbar_of_le_sup {J P : Subgroup G} [Group.IsPerfect ↥J] {y : G}
    (hy : y ∈ normalizer (J : Set G)) (hP : P ≤ zpowers y ⊔ centralizer (J : Set G)) :
    IsCyclic ↥(K0.Pbar J P) := by
  have hC : centralizer (J : Set G) ≤ normalizer (J : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have key : ∀ u ∈ zpowers y ⊔ centralizer (J : Set G), ∃ hu : u ∈ normalizer (J : Set G),
      YCfg.yAct J ⟨u, hu⟩ ∈ zpowers (YCfg.yAct J ⟨y, hy⟩) := by
    intro u hu
    rw [Subgroup.sup_eq_closure] at hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with hu | hu
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        refine ⟨Subgroup.zpow_mem _ hy m, ?_⟩
        have : (⟨y ^ m, Subgroup.zpow_mem _ hy m⟩ : ↥(normalizer (J : Set G))) = ⟨y, hy⟩ ^ m :=
          rfl
        rw [this, map_zpow]
        exact Subgroup.zpow_mem_zpowers _ m
      · have hCu : u ∈ normalizer (J : Set G) := hC hu
        refine ⟨hCu, ?_⟩
        rw [(YCfg.yAct_eq_one_iff J ⟨u, hCu⟩).mpr hu]
        exact Subgroup.one_mem _
    | one =>
      refine ⟨(normalizer (J : Set G)).one_mem, ?_⟩
      have : (⟨1, (normalizer (J : Set G)).one_mem⟩ : ↥(normalizer (J : Set G))) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul u v _ _ ihu ihv =>
      obtain ⟨hu', hu''⟩ := ihu
      obtain ⟨hv', hv''⟩ := ihv
      refine ⟨(normalizer (J : Set G)).mul_mem hu' hv', ?_⟩
      have : (⟨u * v, (normalizer (J : Set G)).mul_mem hu' hv'⟩ : ↥(normalizer (J : Set G))) =
          ⟨u, hu'⟩ * ⟨v, hv'⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ hu'' hv''
    | inv u _ ih =>
      obtain ⟨hu', hu''⟩ := ih
      refine ⟨(normalizer (J : Set G)).inv_mem hu', ?_⟩
      have : (⟨u⁻¹, (normalizer (J : Set G)).inv_mem hu'⟩ : ↥(normalizer (J : Set G))) =
          ⟨u, hu'⟩⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ hu''
  have hle : K0.Pbar J P ≤ zpowers (YCfg.yAct J ⟨y, hy⟩) := by
    rintro e he
    obtain ⟨x, hx, hxP, rfl⟩ := K0.mem_Pbar.mp he
    obtain ⟨hu, hmem⟩ := key x (hP hxP)
    exact hmem
  have : IsCyclic ↥(zpowers (YCfg.yAct J ⟨y, hy⟩)) := inferInstance
  exact isCyclic_of_le hle

theorem card_dvd_of_cyclic_pow_eq_one {K : Type} [Group K] [Finite K] {R : Subgroup K}
    [IsCyclic ↥R] {p : ℕ} (h : ∀ e ∈ R, e ^ p = 1) : Nat.card ↥R ∣ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥R)
  have h1 : g ^ p = 1 := Subtype.ext (h g g.2)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one h1

theorem pow_eq_one_of_mem_sup {A B : Subgroup G} {p : ℕ}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : ∀ a ∈ A, a ^ p = 1)
    (hB : ∀ b ∈ B, b ^ p = 1) {x : G} (hx : x ∈ A ⊔ B) : x ^ p = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  have hc : Commute a b := hcomm a ha b hb
  rw [hc.mul_pow, hA a ha, hB b hb, one_mul]

end Cyclic

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4
