module

public import CFSG.GH74.GLS.SP.Local.SPLCtC3
public import CFSG.GH74.GLS.SP.Local.SPLFitK2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section K2

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem pPrimeCoreOf_CcI_le (hA : SPLCtA D) : pPrimeCoreOf 2 D.CcI ≤ D.Act := by
  have hCcI_le : D.CcI ≤ D.Ct := fun x hx => ((mem_CcI D).mp hx).1
  have hnormM : ∀ c ∈ D.Ct, c ∈ normalizer (D.CcI : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact fun hm => CcI_normal D hA c hc m hm
    · intro hm
      have := CcI_normal D hA c⁻¹ (D.Ct.inv_mem hc) _ hm
      simpa [mul_assoc] using this
  exact fitK2_le_pPrimeCoreOf (X := D.Ct) (W := pPrimeCoreOf 2 D.CcI)
    ((TwoThin.pPrimeCoreOf_le D.CcI).trans hCcI_le)
    (fun c hc w hw => TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (hnormM c hc) hw)
    (TwoThin.card_pPrimeCoreOf_odd D.CcI)

theorem hasDihedralSylowTwo_CcI (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D)
    {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo ↥D.CcI := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup G := D.CcI
  let T₀' : Subgroup ↥M := T₀.subgroupOf M
  have hT₀'p : IsPGroup 2 T₀' := IsPGroup.comap_subtype (IsPGroup.to_le hT.T_p (T₀_le_T D hT))
  have hT₀'max : ∀ P : Subgroup ↥M, IsPGroup 2 P → T₀' ≤ P → P = T₀' := by
    intro P hP hle
    have hPp : IsPGroup 2 (P.map M.subtype) := hP.map _
    have hle' : T₀ ≤ P.map M.subtype := fun x hx =>
      ⟨⟨x, T₀_le_CcI D hT hx⟩, hle hx, rfl⟩
    have hPeq := T₀_max_CcI D hA hT (P.map M.subtype) (Subgroup.map_subtype_le P) hPp hle'
    apply le_antisymm
    · intro x hx
      have hx' : (x : G) ∈ P.map M.subtype := ⟨x, hx, rfl⟩
      rw [hPeq] at hx'
      exact hx'
    · exact hle
  obtain ⟨S₀, hS₀⟩ := SylowL2.exists_sylow_eq T₀' hT₀'p hT₀'max
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hT.T₀_dih
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.n = m + 3 := ⟨D.n - 3, by omega⟩
  have hkm : k = 2 ^ (m + 1) := by
    have h1 : 2 ^ (D.n - 1) = 2 * 2 ^ (m + 1) := by
      rw [hm, show m + 3 - 1 = (m + 1) + 1 by omega, pow_succ]; ring
    omega
  intro S
  refine ⟨m + 1, by omega, ⟨(Sylow.equiv S₀ S).symm.trans ?_⟩⟩
  rw [hkm] at φ
  exact (MulEquiv.subgroupCongr hS₀).trans
    ((Subgroup.subgroupOfEquivOfLe (T₀_le_CcI D hT)).trans φ)

theorem splCenIAt_of_GW
    (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {T T₀ T₁ : Subgroup G} {y : G}
    (hT : SPLCtT D T T₀ T₁ y) : SPLCenIAt D := by
  intro c hc hcomm
  have hcM : c ∈ D.CcI := by
    rw [mem_CcI]
    refine ⟨hc, fun i hi => ?_⟩
    have h1 : ⁅i, c⁆ ∈ D.Act := hcomm i hi
    have h2 : ⁅i, c⁆ ∈ D.Ict := by
      have : ⁅i, c⁆ = i * (c * i⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact D.Ict.mul_mem hi (hA.I_normal c hc i⁻¹ (D.Ict.inv_mem hi))
    have h3 : ⁅i, c⁆ ∈ D.Act ⊓ D.Ict := ⟨h1, h2⟩
    rw [Act_inf_Ict D hs, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hD := CFSG.GorensteinWalter.gorensteinWalter ↥D.CcI (hasDihedralSylowTwo_CcI D hs hA hT)
  have htM : D.t ∈ D.CcI := by
    rw [mem_CcI]
    exact ⟨mem_centralizer_singleton_iff.mpr rfl, fun i hi =>
      mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hi)⟩
  let τ : ↥D.CcI := ⟨D.t, htM⟩
  have hτc : τ ∈ Subgroup.center ↥D.CcI := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (mem_centralizer_singleton_iff.mp ((mem_CcI D).mp m.2).1)
  have hτ2 : τ ^ 2 = 1 := Subtype.ext (by
    show D.t ^ 2 = 1
    rw [pow_two]; exact t_mul_t' D hs)
  have hτ1 : τ ≠ 1 := fun h => t_ne_one D.ext3 hs (congrArg Subtype.val h)
  have hq := CFSG.GorensteinWalter.preambleCentralInvolution_quotient_two_of_dgroup hD hτc hτ2 hτ1
  obtain ⟨k, hk⟩ := hq (QuotientGroup.mk ⟨c, hcM⟩)
  refine ⟨k, ?_⟩
  have h1 : (⟨c, hcM⟩ : ↥D.CcI) ^ (2 ^ k) ∈ pPrimeCore 2 ↥D.CcI := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  exact pPrimeCoreOf_CcI_le D hA ⟨_, h1, rfl⟩

end K2

end CFSG.GH74.GLS.SP.Local
