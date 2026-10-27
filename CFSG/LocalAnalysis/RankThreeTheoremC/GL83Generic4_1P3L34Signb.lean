module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem l34Sign_sign_eq_neg_one {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h2 : σ ^ 2 = 1) (h6 : σ.support.card = 6) : Equiv.Perm.sign σ = -1 := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    simp at h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn, ho, Multiset.sum_replicate, h6, smul_eq_mul] at hsum
  rw [Equiv.Perm.sign_of_cycleType, hn, ho, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul]
  obtain rfl : n = 2 := by omega
  decide

theorem l34Sign_le_commutator [Finite G] {S : Subgroup G} {x : G}
    (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hfix : ∀ s ∈ S, s * x = x * s → s = 1) :
    S ≤ ⁅S, zpowers x⁆ := by
  let f : ↥S → ↥S := fun s => ⟨(s : G)⁻¹ * (x * s * x⁻¹), S.mul_mem (S.inv_mem s.2) (hxS s s.2)⟩
  have hf : Function.Injective f := by
    intro s t hst
    have h : (s : G)⁻¹ * (x * s * x⁻¹) = (t : G)⁻¹ * (x * t * x⁻¹) := congrArg Subtype.val hst
    have h' : (s : G)⁻¹ * x * s = (t : G)⁻¹ * x * t := by
      calc (s : G)⁻¹ * x * s = (s : G)⁻¹ * (x * s * x⁻¹) * x := by group
        _ = (t : G)⁻¹ * (x * t * x⁻¹) * x := by rw [h]
        _ = (t : G)⁻¹ * x * t := by group
    have hc : (t : G) * (s : G)⁻¹ * x = x * ((t : G) * (s : G)⁻¹) := by
      calc (t : G) * (s : G)⁻¹ * x = (t : G) * ((s : G)⁻¹ * x * s) * (s : G)⁻¹ := by group
        _ = (t : G) * ((t : G)⁻¹ * x * t) * (s : G)⁻¹ := by rw [h']
        _ = x * ((t : G) * (s : G)⁻¹) := by group
    exact (Subtype.ext (mul_inv_eq_one.mp (hfix _ (S.mul_mem t.2 (S.inv_mem s.2)) hc))).symm
  intro g hg
  obtain ⟨s, hs⟩ := Finite.injective_iff_surjective.mp hf ⟨g, hg⟩
  have hg' : g = ⁅(s : G)⁻¹, x⁆ := by
    have h := congrArg Subtype.val hs
    simp only [f] at h
    rw [commutatorElement_def, ← h]
    group
  rw [hg']
  exact commutator_mem_commutator (S.inv_mem s.2) (mem_zpowers x)

theorem l34Sign_ker_facts {M : Subgroup G} (χ : ↥M →* ℤˣ) :
    χ.ker.map M.subtype ≤ M ∧ ((χ.ker.map M.subtype).subgroupOf M).Normal ∧
      (χ.ker.map M.subtype).relIndex M ≤ 2 ∧
      (∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ χ.ker.map M.subtype) ∧
      ∀ g (hg : g ∈ M), g ∈ χ.ker.map M.subtype ↔ χ ⟨g, hg⟩ = 1 := by
  have hsub : (χ.ker.map M.subtype).subgroupOf M = χ.ker :=
    comap_map_eq_self_of_injective M.subtype_injective _
  have hmem : ∀ g (hg : g ∈ M), g ∈ χ.ker.map M.subtype ↔ χ ⟨g, hg⟩ = 1 := by
    intro g hg
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  refine ⟨map_subtype_le _, ?_, ?_, ?_, hmem⟩
  · rw [hsub]
    infer_instance
  · rw [relIndex, hsub, index_ker]
    calc Nat.card χ.range ≤ Nat.card ℤˣ := card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  · intro a ha b hb
    refine (hmem _ (M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb))).mpr ?_
    have h : (⟨a * b * a⁻¹ * b⁻¹, M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha))
        (M.inv_mem hb)⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [h, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (χ ⟨a, ha⟩)]
    group

private def l34SignConj {B M : Subgroup G} (hMB : M ≤ normalizer (B : Set G)) (m : ↥M) :
    ↥B →* ↥B where
  toFun b := ⟨(m : G) * b * (m : G)⁻¹, (mem_normalizer_iff.mp (hMB m.2) b).mp b.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [MulMemClass.coe_mul]; group)

private theorem l34SignConj_apply {B M : Subgroup G} (hMB : M ≤ normalizer (B : Set G)) (m : ↥M)
    (b : ↥B) : (l34SignConj hMB m b : G) = (m : G) * b * (m : G)⁻¹ :=
  rfl

private def l34SignAct {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G)) (m : ↥M) :
    ↥B ⧸ N.subgroupOf B →* ↥B ⧸ N.subgroupOf B :=
  QuotientGroup.map _ _ (l34SignConj hMB m) fun b hb => by
    rw [mem_comap, mem_subgroupOf, l34SignConj_apply]
    exact (mem_normalizer_iff.mp (hMN m.2) b).mp (mem_subgroupOf.mp hb)

private theorem l34SignAct_mk {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G)) (m : ↥M) (b : ↥B) :
    l34SignAct hMB hMN m (b : ↥B ⧸ N.subgroupOf B) =
      ((l34SignConj hMB m b : ↥B) : ↥B ⧸ N.subgroupOf B) :=
  QuotientGroup.map_mk _ _ _ _ _

private theorem l34SignAct_mul {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G)) (m₁ m₂ : ↥M)
    (v : ↥B ⧸ N.subgroupOf B) :
    l34SignAct hMB hMN (m₁ * m₂) v = l34SignAct hMB hMN m₁ (l34SignAct hMB hMN m₂ v) := by
  induction v using QuotientGroup.induction_on with
  | H b =>
    rw [l34SignAct_mk, l34SignAct_mk, l34SignAct_mk]
    congr 1
    apply Subtype.ext
    simp only [l34SignConj_apply, MulMemClass.coe_mul]
    group

private theorem l34SignAct_one {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G))
    (v : ↥B ⧸ N.subgroupOf B) : l34SignAct hMB hMN 1 v = v := by
  induction v using QuotientGroup.induction_on with
  | H b =>
    rw [l34SignAct_mk]
    congr 1
    apply Subtype.ext
    simp [l34SignConj_apply]

private def l34SignRho {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G)) :
    ↥M →* Equiv.Perm (↥B ⧸ N.subgroupOf B) where
  toFun m :=
    { toFun := l34SignAct hMB hMN m
      invFun := l34SignAct hMB hMN m⁻¹
      left_inv := fun v => by rw [← l34SignAct_mul, inv_mul_cancel, l34SignAct_one]
      right_inv := fun v => by rw [← l34SignAct_mul, mul_inv_cancel, l34SignAct_one] }
  map_one' := Equiv.ext fun v => l34SignAct_one hMB hMN v
  map_mul' m₁ m₂ := Equiv.ext fun v => l34SignAct_mul hMB hMN m₁ m₂ v

private theorem l34SignRho_mk {B N M : Subgroup G} [(N.subgroupOf B).Normal]
    (hMB : M ≤ normalizer (B : Set G)) (hMN : M ≤ normalizer (N : Set G)) (m : ↥M) (b : ↥B) :
    l34SignRho hMB hMN m (b : ↥B ⧸ N.subgroupOf B) =
      ((l34SignConj hMB m b : ↥B) : ↥B ⧸ N.subgroupOf B) :=
  l34SignAct_mk hMB hMN m b

theorem l34Sign_exists_sign [Finite G] {A N M : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hMB : M ≤ normalizer ((A ⊔ N : Subgroup G) : Set G)) (hMN : M ≤ normalizer (N : Set G))
    (hA : Nat.card A = 3 ^ 2) (hAN1 : ∀ a ∈ A, a ∈ N → a = 1) :
    ∃ χ : ↥M →* ℤˣ, (∀ n : ↥M, (n : G) ∈ N → χ n = 1) ∧
      ∀ w : ↥M, (w : G) ^ 2 = 1 → (∃ u ∈ A, u ≠ 1 ∧ (w : G) * u = u * w) →
        (∃ a ∈ A, ((w : G) * a * (w : G)⁻¹)⁻¹ * a ∉ N) → χ w = -1 := by
  classical
  set B : Subgroup G := A ⊔ N with hB
  have hNB : N ≤ B := le_sup_right
  have hAB : A ≤ B := le_sup_left
  have hBN : B ≤ normalizer (N : Set G) := sup_le hAN le_normalizer
  have : (N.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hNB).mpr hBN
  have : Fintype (↥B ⧸ N.subgroupOf B) := Fintype.ofFinite _
  have hfix : ∀ (m : ↥M) (b : ↥B), l34SignRho hMB hMN m (b : ↥B ⧸ N.subgroupOf B) = b ↔
      ((m : G) * b * (m : G)⁻¹)⁻¹ * b ∈ N := by
    intro m b
    rw [l34SignRho_mk, QuotientGroup.eq, mem_subgroupOf]
    rfl
  refine ⟨Equiv.Perm.sign.comp (l34SignRho hMB hMN), ?_, ?_⟩
  · intro n hn
    have h1 : l34SignRho hMB hMN n = 1 := by
      ext v
      induction v using QuotientGroup.induction_on with
      | H b =>
        rw [Equiv.Perm.one_apply, hfix]
        have h := (mem_normalizer_iff.mp (hBN (B.inv_mem b.2)) (n : G)⁻¹).mp (N.inv_mem hn)
        have h' := N.mul_mem hn h
        convert h' using 1
        group
    rw [MonoidHom.comp_apply, h1, map_one]
  · rintro w hw2 ⟨u, huA, hu1, hwu⟩ ⟨a, haA, ha⟩
    set σ := l34SignRho hMB hMN w with hσ
    have hσ2 : σ ^ 2 = 1 := by
      have hw : w ^ 2 = 1 := Subtype.ext (by simpa using hw2)
      rw [hσ, ← map_pow, hw, map_one]
    let f : ↥A → ↥B ⧸ N.subgroupOf B := fun a => ((⟨a, hAB a.2⟩ : ↥B) : ↥B ⧸ N.subgroupOf B)
    have hf : Function.Bijective f := by
      constructor
      · intro a₁ a₂ h
        have h' := QuotientGroup.eq.mp h
        rw [mem_subgroupOf] at h'
        have h1 := hAN1 _ (A.mul_mem (A.inv_mem a₁.2) a₂.2) h'
        exact Subtype.ext (inv_mul_eq_one.mp h1)
      · intro v
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
        have hb : (b : G) ∈ ((A ⊔ N : Subgroup G) : Set G) := b.2
        rw [coe_mul_of_left_le_normalizer_right A N hAN] at hb
        obtain ⟨a, ha, n, hn, hanb⟩ := hb
        refine ⟨⟨a, ha⟩, QuotientGroup.eq.mpr ?_⟩
        rw [mem_subgroupOf]
        have : (a : G)⁻¹ * b = n := by rw [← hanb]; group
        change (a : G)⁻¹ * b ∈ N
        rw [this]
        exact hn
    have hV : Nat.card (↥B ⧸ N.subgroupOf B) = 3 ^ 2 :=
      (Nat.card_eq_of_bijective f hf).symm.trans hA
    let F : Subgroup (↥B ⧸ N.subgroupOf B) :=
      MonoidHom.eqLocus (l34SignAct hMB hMN w) (MonoidHom.id _)
    have hFmem : ∀ v, v ∈ F ↔ σ v = v := fun v => Iff.rfl
    have hF3 : Nat.card F = 3 := by
      have hdvd : Nat.card F ∣ 3 ^ 2 := hV ▸ card_subgroup_dvd_card F
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases k
      · exfalso
        have hbot : F = ⊥ := eq_bot_of_card_eq F (by simpa using hk')
        have huF : f ⟨u, huA⟩ ∈ F := by
          rw [hFmem, hσ, hfix]
          have : (w : G) * u * (w : G)⁻¹ = u := by rw [hwu]; group
          change ((w : G) * u * (w : G)⁻¹)⁻¹ * u ∈ N
          rw [this, inv_mul_cancel]
          exact N.one_mem
        rw [hbot, mem_bot] at huF
        have h' := (QuotientGroup.eq_one_iff _).mp huF
        rw [mem_subgroupOf] at h'
        exact hu1 (hAN1 u huA h')
      · simpa using hk'
      · exfalso
        have htop : F = ⊤ := eq_top_of_card_eq F (by rw [hk', hV])
        have haF : f ⟨a, haA⟩ ∈ F := by
          rw [htop]
          exact mem_top _
        rw [hFmem, hσ, hfix] at haF
        exact ha haF
    have hsupp : σ.support.card = 6 := by
      have h1 : σ.support = Finset.univ.filter (fun v => ¬ σ v = v) := by
        ext v
        simp [Equiv.Perm.mem_support]
      have h2 : (Finset.univ.filter (fun v => σ v = v)).card = 3 := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← hF3]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun v => (hFmem v).symm)
      have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => σ v = v)
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hV, h2] at h3
      rw [h1]
      omega
    rw [MonoidHom.comp_apply]
    exact l34Sign_sign_eq_neg_one hσ2 hsupp

end CFSG.LocalAnalysis.RankThreeTheoremC
