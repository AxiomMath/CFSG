module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI

public section

namespace CFSG.GH74.GLS.Th2.P85

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem mem_of_two_elt_of_cover {Γ : Type*} [Group Γ] {N : Subgroup Γ}
    (hNodd : Odd (Nat.card ↥N)) :
    ∀ {J : Subgroup Γ}, J.IsSubnormal → (∀ g : Γ, ∃ j ∈ J, ∃ n ∈ N, g = j * n) →
      ∀ s : Γ, (∃ k : ℕ, s ^ (2 ^ k) = 1) → s ∈ J := by
  intro J hJ
  induction hJ with
  | top => intro _ s _; exact Subgroup.mem_top s
  | step H K hHK hKsub hnorm ih =>
    intro hcov s hs
    have hcovK : ∀ g : Γ, ∃ j ∈ K, ∃ n ∈ N, g = j * n := fun g => by
      obtain ⟨j, hj, n, hn, rfl⟩ := hcov g
      exact ⟨j, hHK hj, n, hn, rfl⟩
    have hsK : s ∈ K := ih hcovK s hs
    obtain ⟨h, hh, n, hn, hsn⟩ := hcov s
    have hnK : n ∈ K := by
      have : n = h⁻¹ * s := by rw [hsn]; group
      rw [this]
      exact K.mul_mem (K.inv_mem (hHK hh)) hsK
    obtain ⟨k, hk⟩ := hs
    have hmk : (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) =
        QuotientGroup.mk (⟨n, hnK⟩ : ↥K) := by
      have e : (⟨s, hsK⟩ : ↥K) = ⟨h, hHK hh⟩ * ⟨n, hnK⟩ := Subtype.ext hsn
      rw [e, QuotientGroup.mk_mul]
      have : (QuotientGroup.mk (⟨h, hHK hh⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hh)
      rw [this, one_mul]
    have h1 : orderOf (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow]
      have : (⟨s, hsK⟩ : ↥K) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this]
      exact QuotientGroup.mk_one _
    have h2 : orderOf (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) ∣
        Nat.card ↥N := by
      rw [hmk]
      refine (orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf K)) ⟨n, hnK⟩).trans ?_
      have h3 : orderOf (⟨n, hnK⟩ : ↥K) = orderOf n := by
        rw [← Subgroup.orderOf_coe]
      rw [h3]
      exact Subgroup.orderOf_dvd_natCard N hn
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥N) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hNodd)
    have h4 : orderOf (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 :=
      Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
    have h5 := orderOf_eq_one_iff.1 h4
    have := (QuotientGroup.eq_one_iff (⟨s, hsK⟩ : ↥K)).1 h5
    exact Subgroup.mem_subgroupOf.1 this


theorem mem_of_two_elt_of_cover' {H : Type*} [Group H] {L J N : Subgroup H} (hJL : J ≤ L)
    (hJ : (J.subgroupOf L).IsSubnormal) (hNL : N ≤ L) (hNodd : Odd (Nat.card ↥N))
    (hcov : ∀ l ∈ L, ∃ j ∈ J, ∃ n ∈ N, l = j * n) :
    ∀ s ∈ L, (∃ k : ℕ, s ^ (2 ^ k) = 1) → s ∈ J := by
  have hN' : Odd (Nat.card ↥(N.subgroupOf L)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
  have hcov' : ∀ g : ↥L, ∃ j ∈ J.subgroupOf L, ∃ n ∈ N.subgroupOf L, g = j * n := by
    intro g
    obtain ⟨j, hj, n, hn, hg⟩ := hcov g g.2
    have hjL : j ∈ L := hJL hj
    have hnL : n ∈ L := hNL hn
    exact ⟨⟨j, hjL⟩, Subgroup.mem_subgroupOf.2 hj, ⟨n, hnL⟩, Subgroup.mem_subgroupOf.2 hn,
      Subtype.ext hg⟩
  intro s hsL ⟨k, hk⟩
  have := mem_of_two_elt_of_cover hN' hJ hcov' ⟨s, hsL⟩ ⟨k, Subtype.ext (by simpa using hk)⟩
  exact Subgroup.mem_subgroupOf.1 this


section Main

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_of_eq_sup {K M L : Subgroup G} (hKM : K ≤ M) (hKperf : ⁅K, K⁆ = K)
    (hKq : CFSG.IsQuasisimple (kBar K)) (hL : IsMinSubnormalIn K M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : IsPCompIn 2 M L := by
  have hKL : K ≤ L := hL.1
  have hsub : IsSubnormalIn L M := hL.2.1
  have hLM : L ≤ M := hsub.1
  refine ⟨hLM, ?_⟩
  obtain ⟨eL⟩ := imgM_equiv_kBar hKL hsub hLeq
  refine ⟨imgM M L, ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hKq,
    hsub.2.map barMk_surjective⟩, hsub.2, rfl, ?_⟩
  intro J hJlt hJsub hJmap
  have hJL : J ≤ L.subgroupOf M := hJlt.le
  have hLmap : (L.subgroupOf M).map M.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLM
  have hJGL : J.map M.subtype ≤ L := hLmap ▸ Subgroup.map_mono hJL
  have hJGsub : IsSubnormalIn (J.map M.subtype) M := by
    refine ⟨Subgroup.map_subtype_le J, ?_⟩
    have : (J.map M.subtype).subgroupOf M = J :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective J
    rwa [this]
  have hcov : ∀ l ∈ L.subgroupOf M, ∃ j ∈ J, ∃ n ∈ (pPrimeCoreOf 2 L).subgroupOf M, l = j * n := by
    intro l hl
    have hπ : barMk ↥M l ∈ J.map (barMk ↥M) := by
      have : barMk ↥M l ∈ imgM M L := ⟨l, hl, rfl⟩
      rw [← hJmap] at this
      exact this
    obtain ⟨j, hj, hjl⟩ := hπ
    refine ⟨j, hj, j⁻¹ * l, ?_, by group⟩
    have hker : j⁻¹ * l ∈ (barMk ↥M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjl, inv_mul_cancel]
    rw [TwoThin.ker_barMk] at hker
    have h1 : ((j⁻¹ * l : ↥M) : G) ∈ pPrimeCoreOf 2 M :=
      C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨(j⁻¹ * l).2, hker⟩
    have h2 : ((j⁻¹ * l : ↥M) : G) ∈ L := by
      have hjl' : (j : G) ∈ L := by
        have := hJL hj
        exact Subgroup.mem_subgroupOf.1 this
      have hll : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
      simpa using L.mul_mem (L.inv_mem hjl') hll
    exact Subgroup.mem_subgroupOf.2 (Th2.inf_le_pPrimeCoreOf hLM ⟨h1, h2⟩)
  have hNL : (pPrimeCoreOf 2 L).subgroupOf M ≤ L.subgroupOf M :=
    fun n hn => Subgroup.mem_subgroupOf.2 (TwoThin.pPrimeCoreOf_le L (Subgroup.mem_subgroupOf.1 hn))
  have hNodd : Odd (Nat.card ↥((pPrimeCoreOf 2 L).subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (TwoThin.pPrimeCoreOf_le L |>.trans hLM)).toEquiv]
    exact TwoThin.card_pPrimeCoreOf_odd L
  have h2elt := mem_of_two_elt_of_cover' hJL (hJsub.subgroupOf) hNL hNodd hcov
  have hKJ : K ≤ J.map M.subtype := by
    have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
    refine (Th2.CaseI.le_closure_two_elements hperf).trans ((Subgroup.closure_le _).2 ?_)
    rintro g ⟨hgK, n, hn⟩
    have hgM : g ∈ M := hKM hgK
    have hmem : (⟨g, hgM⟩ : ↥M) ∈ J :=
      h2elt ⟨g, hgM⟩ (Subgroup.mem_subgroupOf.2 (hKL hgK))
        ⟨n, Subtype.ext (by simpa using hn)⟩
    exact ⟨⟨g, hgM⟩, hmem, rfl⟩
  have hJGeq : J.map M.subtype = L := hL.2.2 _ hKJ hJGL hJGsub
  apply hJlt.ne
  have : J.map M.subtype = (L.subgroupOf M).map M.subtype := by rw [hJGeq, hLmap]
  exact Subgroup.map_injective M.subtype_injective this

end Main

end CFSG.GH74.GLS.Th2.P85
