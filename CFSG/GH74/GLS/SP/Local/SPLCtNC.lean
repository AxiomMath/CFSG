module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtNC

variable {G : Type} [Group G]

private theorem gw_quasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.GorensteinWalter.IsQuasisimple Q := by
  have hs : IsSimpleGroup (Q ⧸ center Q) := h.2.1
  exact ⟨(QuotientGroup.mk_surjective (s := center Q)).nontrivial, h.1.commutator_eq_top, hs⟩

private theorem conj_diag_aux {g g' n : G} (h : n * g' = g' * n) :
    g * n * g⁻¹ = (g * g') * n * (g * g')⁻¹ := by
  have h2 : g' * n * g'⁻¹ = n := by rw [← h]; group
  calc g * n * g⁻¹ = g * (g' * n * g'⁻¹) * g⁻¹ := by rw [h2]
    _ = (g * g') * n * (g * g')⁻¹ := by group

end CtNC

section CtNCD

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

omit [Finite G] in
private theorem t_conj_conj (hs : SPLSetup D.toSPLNot0) (b : G) :
    D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ = b := by
  have htt := t_mul_t' D hs
  calc D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * b * (D.t * D.t)⁻¹ := by group
    _ = b := by rw [htt]; group

omit [Finite G] in
private theorem C_Ct_le_normalizer (hA : SPLCtA D) {A₀ : Subgroup G} (hA₀ : A₀ ≤ D.Act) :
    D.C ⊓ D.Ct ≤ normalizer (A₀ : Set G) ⊓ D.C := by
  have : IsCyclic ↥D.Act := hA.A_cyc
  rintro c ⟨hcC, hcCt⟩
  exact ⟨normalizer_le_of_cyclic hA₀ (CFSG.GH74.GLS.LU.Local.mem_normalizer_pPrimeCoreOf hcCt), hcC⟩

private theorem N1_normal (hs : SPLSetup D.toSPLNot0) {X : Subgroup G} (hIX : D.Ict ≤ X) :
    ((X ⊓ D.K₁).subgroupOf D.K₁).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨hnX, hnK⟩ := hn
  have hg' : D.t * (g : G) * D.t⁻¹ ∈ D.K₂ := t_conj_K₁' D hs g g.2
  have hdg : D.dg hs g ∈ X := hIX (by rw [Ict_eq D hs]; exact ⟨g, rfl⟩)
  have hcomm : (n : G) * (D.t * g * D.t⁻¹) = (D.t * g * D.t⁻¹) * n :=
    hs.comps.comm n hnK _ hg'
  have key : (g : G) * n * (g : G)⁻¹ = D.dg hs g * n * (D.dg hs g)⁻¹ := conj_diag_aux hcomm
  show (g : G) * n * (g : G)⁻¹ ∈ X ⊓ D.K₁
  refine ⟨?_, D.K₁.mul_mem (D.K₁.mul_mem g.2 hnK) (D.K₁.inv_mem g.2)⟩
  rw [key]
  exact X.mul_mem (X.mul_mem hdg hnX) (X.inv_mem hdg)

private theorem X_inf_K_le_Ct (hs : SPLSetup D.toSPLNot0) {X : Subgroup G} (hIX : D.Ict ≤ X)
    (hz : ∀ n ∈ X ⊓ D.K₁, n ∈ zpowers D.z) : X ⊓ D.K ≤ D.Ct := by
  rintro κ ⟨hκX, hκK⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hκK
  have hb' : D.t * b * D.t⁻¹ ∈ D.K₁ := t_conj_K₂' D hs b hb
  have hdg : D.dg hs ⟨D.t * b * D.t⁻¹, hb'⟩ = (D.t * b * D.t⁻¹) * b := by
    rw [dg_apply]
    show (D.t * b * D.t⁻¹) * (D.t * (D.t * b * D.t⁻¹) * D.t⁻¹) = _
    rw [t_conj_conj D hs b]
  have hdgI : D.dg hs ⟨D.t * b * D.t⁻¹, hb'⟩ ∈ D.Ict := by
    rw [Ict_eq D hs]; exact ⟨_, rfl⟩
  have hw : a * (D.t * b * D.t⁻¹)⁻¹ ∈ X ⊓ D.K₁ := by
    refine ⟨?_, D.K₁.mul_mem ha (D.K₁.inv_mem hb')⟩
    have e : a * (D.t * b * D.t⁻¹)⁻¹ = (a * b) * (D.dg hs ⟨D.t * b * D.t⁻¹, hb'⟩)⁻¹ := by
      rw [hdg]; group
    rw [e]
    exact X.mul_mem hκX (X.inv_mem (hIX hdgI))
  have hwz := hz _ hw
  have hwCt : a * (D.t * b * D.t⁻¹)⁻¹ ∈ D.Ct := by
    have hzCt : zpowers D.z ≤ D.Ct := by
      rw [zpowers_le]; exact mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)
    exact hzCt hwz
  have e : a * b = (a * (D.t * b * D.t⁻¹)⁻¹) * D.dg hs ⟨D.t * b * D.t⁻¹, hb'⟩ := by
    rw [hdg]; group
  rw [e]
  exact D.Ct.mul_mem hwCt (Ict_le_Ct D hs hdgI)

private theorem K₁_not_le_normalizer (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ D.Act) (hne : A₀ ≠ ⊥) (hK : D.K₁ ≤ normalizer (A₀ : Set G)) : False := by
  have hcyc : IsCyclic ↥D.Act := hA.A_cyc
  have hcyc₀ : IsCyclic ↥A₀ := Subgroup.isCyclic_of_le hA₀
  have hcen : D.K₁ ≤ centralizer (A₀ : Set G) := perfect_le_centralizer_of_cyclic (K₁_perfect D hs) hK
  apply hne
  rw [eq_bot_iff]
  intro a ha
  rw [mem_bot]
  have h0 : a * D.z = D.z * a := mem_centralizer_iff.mp (hcen (z_mem_K₁' D hs)) a ha
  have h1 : D.z * a * D.z⁻¹ = a := by rw [← h0]; group
  have h2 : D.z * a * D.z⁻¹ = a⁻¹ := Act_inv D hs a (hA₀ ha)
  have h3 : a * a = 1 := by
    rw [h1] at h2
    exact mul_eq_one_iff_eq_inv.mpr h2
  have hodd : Odd (orderOf a) := by
    have h4 : orderOf (⟨a, hA₀ ha⟩ : ↥D.Act) ∣ Nat.card ↥D.Act := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h4
    exact Odd.of_dvd_nat (Act_odd D) h4
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hodd
    exact absurd hodd (by decide)

private theorem X_le_CCt (hs : SPLSetup D.toSPLNot0) (hF : D.F ≤ D.Ct) {X : Subgroup G}
    (hXC : D.C ⊓ D.Ct ≤ X) (hXC' : X ≤ D.C) (hK₁ : ¬ D.K₁ ≤ X) : X ≤ D.C ⊓ D.Ct := by
  have hIX : D.Ict ≤ X := (Ict_le_CCt D hs).trans hXC
  have hN := N1_normal D hs hIX
  have hq : CFSG.GorensteinWalter.IsQuasisimple ↥D.K₁ := gw_quasisimple hs.comps.quasi₁
  have hz : ∀ n ∈ X ⊓ D.K₁, n ∈ zpowers D.z := by
    rcases CFSG.GorensteinWalter.normal_subgroup_le_center_or_eq_top hq _ hN with hcen | htop
    · intro n hn
      have hn' : (⟨n, hn.2⟩ : ↥D.K₁) ∈ (X ⊓ D.K₁).subgroupOf D.K₁ := hn
      exact (mem_center_K₁_iff D.ext3 hs _).mp (hcen hn')
    · exfalso
      apply hK₁
      intro k hk
      have h : (⟨k, hk⟩ : ↥D.K₁) ∈ (X ⊓ D.K₁).subgroupOf D.K₁ := by
        rw [htop]; exact mem_top _
      exact (mem_subgroupOf.mp h).1
  have hKCt := X_inf_K_le_Ct D hs hIX hz
  have hzt : zpowers D.t ≤ D.C ⊓ D.Ct := by
    rw [zpowers_le]
    exact ⟨t_mem_Cz hs, mem_centralizer_singleton_iff.mpr rfl⟩
  intro c hc
  have hcC : c ∈ D.C := hXC' hc
  obtain ⟨k, hk, s, hsS, y, hyF, rfl⟩ := hs.gen c hcC
  have hsKt : s ∈ D.K ⊔ zpowers D.t := S_le_Kt D.ext3 hs hsS
  obtain ⟨κ', hκ', τ, hτ, rfl⟩ := mem_sup_of_le_normalizer (t_le_normalizer_K D.ext3 hs) hsKt
  have hτX : τ ∈ X := hXC (hzt hτ)
  have hyX : y ∈ X := hXC ⟨F_le_C hs hyF, hF hyF⟩
  have hkκ : k * κ' ∈ X ⊓ D.K := by
    refine ⟨?_, D.K.mul_mem hk hκ'⟩
    have e : k * κ' = (k * (κ' * τ) * y) * y⁻¹ * τ⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem hc (X.inv_mem hyX)) (X.inv_mem hτX)
  have hkκCt : k * κ' ∈ D.Ct := hKCt hkκ
  refine ⟨hcC, ?_⟩
  have e : k * (κ' * τ) * y = (k * κ') * τ * y := by group
  rw [e]
  exact D.Ct.mul_mem (D.Ct.mul_mem hkκCt (hzt hτ).2) (hF hyF)

end CtNCD

theorem ct_NC {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    (hA : SPLCtA D) (hF : D.F ≤ D.Ct) :
    ∀ A₀ : Subgroup G, A₀ ≤ D.Act → A₀ ≠ ⊥ →
      normalizer (A₀ : Set G) ⊓ D.C = D.C ⊓ D.Ct := by
  intro A₀ hA₀ hne
  refine le_antisymm ?_ (C_Ct_le_normalizer D hA hA₀)
  refine X_le_CCt D hs hF (C_Ct_le_normalizer D hA hA₀) inf_le_right ?_
  intro hK
  exact K₁_not_le_normalizer D hs hA hA₀ hne (hK.trans inf_le_left)

end CFSG.GH74.GLS.SP.Local
