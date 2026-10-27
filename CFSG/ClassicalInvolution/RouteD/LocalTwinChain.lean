module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub InClass IsClassicalMember LocalOddCentral
  LieSystemData)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem commutes_partner_of_perfect_conj [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G}
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {S : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hSt : S ≤ Subgroup.centralizer ({t} : Set G))
    (hSK : S ≤ Subgroup.centralizer (K : Set G)) : Commutes β S := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨g, hg⟩ := hsingle β hβ
  have hzg : IsClassicalMember p f β (g * z * g⁻¹) := by
    rw [hg]
    exact hz.conj g
  have htg : t = g * z * g⁻¹ := hzg.eq_of_isCentralInvolution hp2 hf ht.isCentralInvolution
  subst htg
  have hP1t := Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
  obtain ⟨D, hcard⟩ := hD4
  obtain ⟨Dt, hc, -⟩ := Gaps.exists_lieSystemData_conj hΩ.conjInvariant g z D
  obtain ⟨W, hW⟩ := hKβ
  have := Gaps.perfect_le_centralizer_of_partner hMFZ hS3 hΩ hP1t Dt (hc ▸ hcard) hβ ht hW hS hSt
    hSK
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (this hy) x hx

@[expose] def twinChain {m : ℕ} (K β : Subgroup G) (j : Fin m → Subgroup G) :
    Fin (m + 2) → Subgroup G :=
  fun k => if _ : k.val = 0 then K else if _ : k.val = 1 then β else
    j ⟨k.val - 2, by have := k.isLt; omega⟩

theorem twinChain_zero {m : ℕ} (K β : Subgroup G) (j : Fin m → Subgroup G) {k : Fin (m + 2)}
    (hk : k.val = 0) : twinChain K β j k = K := by
  simp [twinChain, hk]

theorem twinChain_one {m : ℕ} (K β : Subgroup G) (j : Fin m → Subgroup G) {k : Fin (m + 2)}
    (hk : k.val = 1) : twinChain K β j k = β := by
  simp [twinChain, hk]

theorem twinChain_node {m : ℕ} (K β : Subgroup G) (j : Fin m → Subgroup G) {k : Fin (m + 2)}
    {a : Fin m} (hk : k.val = a.val + 2) : twinChain K β j k = j a := by
  have h0 : ¬ k.val = 0 := by omega
  have h1 : ¬ k.val = 1 := by omega
  simp only [twinChain, h0, h1, dite_false]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem partner_involution_commutes (hp2 : p ≠ 2) {K β : Subgroup G} {z t : G}
    (hz : IsClassicalMember p f K z) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) : t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hKβ
  have := Gaps.standardPair_involutions_commute (two_ne_zero_galoisField hp2) hW hz.mem ht.mem
    hz.orderOf_eq_two ht.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem conjSub_eq_of_mem_normalizer {K : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) : conjSub y K = K := by
  ext x
  rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hy) x
  rw [inv_inv] at this
  exact this.symm

theorem commutes_conjSub_of_mem_normalizer {K L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (h : Commutes K L) : Commutes K (conjSub y L) := by
  have := h.conjSub y
  rwa [conjSub_eq_of_mem_normalizer hy] at this

theorem locAut_fixed_iff_of_perfect [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {t z : G}
    (hP1 : LocalOddCentral Ω {z}) (ht : t * z * t⁻¹ = z) {N : Subgroup G} (hN : N ≤ locLayer Ω z)
    (hNp : N ≤ ⁅N, N⁆) :
    N ≤ Subgroup.centralizer ({t} : Set G) ↔
      ∀ a ∈ locImg Ω z N, Gaps.locAut hΩ.conjInvariant ht a = a := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    show Gaps.locMk Ω z (Gaps.layerAut hΩ.conjInvariant ht b) = Gaps.locMk Ω z b
    congr 1
    apply Subtype.ext
    show t * (b : G) * t⁻¹ = b
    have := Subgroup.mem_centralizer_singleton_iff.mp (h (Subgroup.mem_subgroupOf.mp hb))
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro h n hn
    have hperf := isPerfect_subgroupOf hN hNp
    set Y := locLayer Ω z
    set O := classicalInvolutionOddCore ↥Y
    have hOc : ∀ b ∈ N.subgroupOf Y, b⁻¹ * Gaps.layerAut hΩ.conjInvariant ht b ∈ O := by
      intro b hb
      have := h _ ⟨b, hb, rfl⟩
      have h2 : Gaps.locMk Ω z (Gaps.layerAut hΩ.conjInvariant ht b) = Gaps.locMk Ω z b := this
      exact QuotientGroup.eq.mp h2.symm
    have key := Gaps.fixed_of_perfect_of_central (Gaps.layerAut hΩ.conjInvariant ht).toMonoidHom
      (N := N.subgroupOf Y) hperf hP1 hOc
    have := key ⟨n, hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 := congrArg Subtype.val this
    have h5 : t * n * t⁻¹ = n := h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm

end CFSG.ClassicalInvolution.RouteD
