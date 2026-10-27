module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Equiv Equiv.Perm Finset

theorem mem_centralizer_zpowers {G : Type*} [Group G] {a b : G} (h : Commute a b) :
    a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((h.symm).zpow_left m).eq

variable {K : Type*} [Group K] [Finite K] {n p : ℕ}

theorem exists_disjoint_cycles_mem_sylow (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p + 1 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) :
    ∃ c₁ ∈ (T : Subgroup K), ∃ c₂ ∈ (T : Subgroup K), orderOf c₁ = p ∧ orderOf c₂ = p ∧
      _root_.Disjoint (e c₁ : Perm (Fin n)).support (e c₂ : Perm (Fin n)).support ∧
      #(e c₁ : Perm (Fin n)).support = p ∧ #(e c₂ : Perm (Fin n)).support = p ∧
      ∃ x, x ∉ (e c₁ : Perm (Fin n)).support ∧ x ∉ (e c₂ : Perm (Fin n)).support := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d₁, d₂, hc₁, hc₂, hs₁, hs₂, hd, x, hx₁, hx₂⟩ :=
    exists_two_disjoint_cycles (α := Fin n) hp.two_le (by simpa using hn)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set k₁ := e.symm ⟨d₁, mem_alternatingGroup_of_isCycle hc₁ (hs₁ ▸ hodd)⟩ with hk₁
  set k₂ := e.symm ⟨d₂, mem_alternatingGroup_of_isCycle hc₂ (hs₂ ▸ hodd)⟩ with hk₂
  have hek₁ : (e k₁ : Perm (Fin n)) = d₁ := by simp [hk₁]
  have hek₂ : (e k₂ : Perm (Fin n)) = d₂ := by simp [hk₂]
  have hord : ∀ k : K, orderOf k = orderOf (e k : Perm (Fin n)) := fun k => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have ho₁ : orderOf k₁ = p := by rw [hord, hek₁, hc₁.orderOf, hs₁]
  have ho₂ : orderOf k₂ = p := by rw [hord, hek₂, hc₂.orderOf, hs₂]
  have hcomm : Commute k₁ k₂ := by
    have h := (disjoint_iff_disjoint_support.mpr hd).commute
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hek₁, hek₂]
    exact h.eq
  have hP1 : IsPGroup p (Subgroup.zpowers k₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho₁, pow_one])
  have hP2 : IsPGroup p (Subgroup.zpowers k₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho₂, pow_one])
  have hle : Subgroup.zpowers k₁ ≤ Subgroup.normalizer (Subgroup.zpowers k₂ : Set K) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hcomm)
  obtain ⟨Q, hQ⟩ := (hP1.to_sup_of_normal_right' hP2 hle).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q T
  have hmem : ∀ k ∈ (Q : Subgroup K), g * k * g⁻¹ ∈ (T : Subgroup K) := by
    intro k hk
    rw [← hg, Sylow.coe_subgroup_smul, ← MulAut.conj_apply]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj g) _ hk
  have hconj : ∀ k : K, (e (g * k * g⁻¹) : Perm (Fin n)) =
      (e g : Perm (Fin n)) * (e k : Perm (Fin n)) * (e g : Perm (Fin n))⁻¹ := fun k => by
    simp only [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
  have hordc : ∀ k : K, orderOf (g * k * g⁻¹) = orderOf k := fun k => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  refine ⟨g * k₁ * g⁻¹, hmem k₁ (hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers k₁))),
    g * k₂ * g⁻¹, hmem k₂ (hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers k₂))),
    by rw [hordc, ho₁], by rw [hordc, ho₂], ?_, ?_, ?_, (e g : Perm (Fin n)) x, ?_, ?_⟩
  · rw [hconj, hconj, support_conj, support_conj, Finset.disjoint_map, hek₁, hek₂]
    exact hd
  · rw [hconj, support_conj, Finset.card_map, hek₁, hs₁]
  · rw [hconj, support_conj, Finset.card_map, hek₂, hs₂]
  · rw [hconj, support_conj, Finset.mem_map_equiv, hek₁]
    simpa using hx₁
  · rw [hconj, support_conj, Finset.mem_map_equiv, hek₂]
    simpa using hx₂

theorem not_isCyclic_sylow (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p + 1 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) : ¬ IsCyclic (T : Subgroup K) := by
  intro hcyc
  obtain ⟨c₁, hc₁T, c₂, hc₂T, ho₁, ho₂, hd, -, hs₂, -⟩ :=
    exists_disjoint_cycles_mem_sylow hp hp2 hn e T
  have hle : Subgroup.zpowers (⟨c₂, hc₂T⟩ : (T : Subgroup K)) ≤ Subgroup.zpowers ⟨c₁, hc₁T⟩ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, ho₁, ho₂]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  have hm' : c₁ ^ m = c₂ := by simpa using congrArg Subtype.val hm
  have hsub : (e c₂ : Perm (Fin n)).support ⊆ (e c₁ : Perm (Fin n)).support := by
    rw [← hm', map_zpow, SubgroupClass.coe_zpow]
    exact support_zpow_le _ m
  have hempty := Disjoint.mono_left hsub hd
  rw [disjoint_self, Finset.bot_eq_empty] at hempty
  rw [hempty, Finset.card_empty] at hs₂
  exact hp.ne_zero hs₂.symm

theorem normalizer_zpowers_le_glbCore (hp : p.Prime) {T : Subgroup K} {c : K} (hcT : c ∈ T)
    (hoc : orderOf c = p) :
    Subgroup.normalizer (Subgroup.zpowers c : Set K) ≤ GLBCore p 1 T := by
  apply le_sSup
  refine ⟨Subgroup.zpowers c, Subgroup.zpowers_le.mpr hcT, ?_, rfl⟩
  refine SectionRank.le_pRank hp.one_lt le_rfl ⟨inferInstance, fun y hy => ?_⟩
    (by rw [Nat.card_zpowers, hoc, pow_one])
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hoc, pow_orderOf_eq_one,
    one_zpow]

theorem glbCore_one_eq_top (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p + 1 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) : GLBCore p 1 (T : Subgroup K) = ⊤ := by
  obtain ⟨c₁, hc₁T, c₂, hc₂T, ho₁, ho₂, hd, hs₁, hs₂, x, hx₁, hx₂⟩ :=
    exists_disjoint_cycles_mem_sylow hp hp2 hn e T
  set φ : K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (Subgroup.subtype_injective _).comp e.injective
  have hφe : ∀ k : K, φ k = (e k : Perm (Fin n)) := fun _ => rfl
  have hC : ∀ c ∈ (T : Subgroup K), orderOf c = p → ∀ g : Perm (Fin n), g.IsThreeCycle →
      _root_.Disjoint g.support (e c : Perm (Fin n)).support →
      g ∈ (GLBCore p 1 (T : Subgroup K)).map φ := by
    intro c hcT hoc g hg hdis
    have hgA : g ∈ alternatingGroup (Fin n) := hg.mem_alternatingGroup
    have hφg : φ (e.symm ⟨g, hgA⟩) = g := by simp [hφe]
    refine ⟨e.symm ⟨g, hgA⟩, normalizer_zpowers_le_glbCore hp hcT hoc ?_, hφg⟩
    apply Subgroup.centralizer_le_normalizer
    apply mem_centralizer_zpowers
    apply hφinj
    rw [map_mul, map_mul, hφg, hφe c]
    exact (disjoint_iff_disjoint_support.mpr hdis).commute.eq
  have hAle := alternatingGroup_le_of_disjoint (hC c₁ hc₁T ho₁) (hC c₂ hc₂T ho₂) hd
    (by rw [hs₁]; exact hp.one_lt) (by rw [hs₂]; exact hp.one_lt) hx₁ hx₂
  rw [eq_top_iff]
  intro k _
  obtain ⟨h, hh, hhk⟩ := hAle (show φ k ∈ alternatingGroup (Fin n) from (e k).2)
  rwa [hφinj hhk] at hh

theorem kFactBetaAlt : KFactBetaAlt := by
  intro K _ _ n hn5 hn6 ⟨e⟩ p hp hp2 T _ hT
  left
  by_cases hsmall : n ≤ 2 * p
  · exact (pRank_top_mulAut_le hn5 hn6 e hp).trans (Nat.div_le_of_le_mul (by omega))
  · exfalso
    rcases hT with h | h
    · exact not_isCyclic_sylow hp hp2 (by omega) e T h
    · exact h (glbCore_one_eq_top hp hp2 (by omega) e T)

end CFSG.AGLEmbedding
