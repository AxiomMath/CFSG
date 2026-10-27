module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.Adapters.GeneralizedFitting
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]


omit [Group G] in
theorem open_isComponentOf_top_of_gw {Q : Type*} [Group Q] {E : Subgroup Q}
    (h : CFSG.GorensteinWalter.IsComponentOf E ⊤) : CFSG.Open.IsComponentOf E ⊤ := by
  obtain ⟨_, hsn, hqs⟩ := h
  have hsn' : E.IsSubnormal := Subgroup.IsSubnormal.trans le_top hsn Subgroup.IsSubnormal.top
  have key : ∀ H : Subgroup Q, H.IsSubnormal → IsSubnormal H ⊤ := fun _ h =>
    CFSG.Open.IsSubnormal.of_mathlib h
  exact ⟨le_top, key E hsn', hqs.2⟩

omit [Group G] in
theorem fittingSubgroup_le_pCore_quotient {p : ℕ} (hp : p.Prime) (H : Type*) [Group H]
    [Finite H] : CFSG.fittingSubgroup (H ⧸ GLAPPrimeCore p H) ≤
      CFSG.pCore p (H ⧸ GLAPPrimeCore p H) := by
  have := Fact.mk hp
  have hbot : GLAPPrimeCore p (H ⧸ GLAPPrimeCore p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hq
  by_cases hqp : (q : ℕ) = p
  · rw [hqp]
  · have hcop : Nat.Coprime p (Nat.card (CFSG.pCore (q : ℕ) (H ⧸ GLAPPrimeCore p H))) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := (q : ℕ))
        (G := H ⧸ GLAPPrimeCore p H))
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
    have := (CFSG.pPrimeCore_eq_bot_iff.1 hbot) _ CFSG.pCore_normal hcop
    rw [this]
    exact bot_le

theorem le_gLAPPrimeCoreOf_of_centralizes_layer [Finite G] {p : ℕ} (hp : p.Prime)
    {C W : Subgroup G} (hW : W ≤ C) (hWcop : Nat.Coprime p (Nat.card W))
    (hO : ⁅oPrimePOf p C, W⁆ ≤ GLAPPrimeCoreOf p C)
    (hL : ∀ L : Subgroup G, GLAPComponent p C L → ⁅L, W⁆ ≤ GLAPPrimeCoreOf p C) :
    W ≤ GLAPPrimeCoreOf p C := by
  classical
  have := Fact.mk hp
  set Q := ↥C ⧸ GLAPPrimeCore p ↥C with hQ
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set Wb : Subgroup Q := barX p C W with hWb
  have hcomm : ∀ T : Subgroup G, ⁅T, W⁆ ≤ GLAPPrimeCoreOf p C →
      Wb ≤ Subgroup.centralizer (barX p C T : Set Q) := by
    intro T hT
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have h1 : s * t * s⁻¹ * t⁻¹ ∈ ⁅W, T⁆ := Subgroup.commutator_mem_commutator hs ht
    rw [Subgroup.commutator_comm] at h1
    exact hT h1
  have hpc : CFSG.pCore p Q ≤ Subgroup.centralizer (Wb : Set Q) := by
    refine fun z hz => (Subgroup.le_centralizer_iff.1 (hcomm _ hO)) ?_
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
    have hc : c ∈ oPrimeP p ↥C := hz
    exact ⟨c, Subgroup.mem_subgroupOf.2 ⟨c, hc, rfl⟩, rfl⟩
  have hF : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer (Wb : Set Q) :=
    (fittingSubgroup_le_pCore_quotient hp ↥C).trans hpc
  have hE : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup Q) ≤
      Subgroup.centralizer (Wb : Set Q) := by
    refine sSup_le fun E hE => ?_
    obtain ⟨L, hL', hbar⟩ := exists_glaPComponent_barX_eq (p := p) C
      (open_isComponentOf_top_of_gw hE)
    rw [← hbar]
    exact Subgroup.le_centralizer_iff.1 (hcomm L (hL L hL'))
  set Fs := CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup Q) with hFs
  have hFs_le : Fs ≤ Subgroup.centralizer (Wb : Set Q) :=
    sup_le ((CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top).trans hF) hE
  have hWbF : Wb ≤ Fs := fun w hw =>
    CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (Subgroup.le_centralizer_iff.2 hFs_le hw)
  have hnorm := (CFSG.GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup Q)).2
  let Z : Subgroup Q := Fs ⊓ Subgroup.centralizer (Fs : Set Q)
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ⟨hnorm g trivial z hz.1, ?_⟩⟩
    show g * z * g⁻¹ ∈ Subgroup.centralizer (Fs : Set Q)
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 := Subgroup.mem_centralizer_iff.1 hz.2 (g⁻¹ * f * g)
      (by have := hnorm g⁻¹ trivial f hf; rwa [inv_inv] at this)
    calc f * (g * z * g⁻¹) = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * f := by group
  have hZc : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.1 b.2.2 a a.2.1)⟩⟩
  have hZnil : Group.IsNilpotent Z := CommGroup.isNilpotent
  have hZF : Z ≤ CFSG.fittingSubgroup Q := (CFSG.LocalCores.fitting_characteristic.2.2) Z hZn hZnil
  have hWbp : Wb ≤ CFSG.pCore p Q := fun w hw =>
    fittingSubgroup_le_pCore_quotient hp ↥C (hZF ⟨hWbF hw, Subgroup.le_centralizer_iff.2 hFs_le hw⟩)
  intro x hx
  have hxC : x ∈ C := hW hx
  have hmem : π ⟨x, hxC⟩ ∈ Wb := ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := Q) ⟨_, hWbp hmem⟩
  have h1 : π ⟨x, hxC⟩ ^ Nat.card W = 1 := by
    have : (⟨x, hxC⟩ : ↥C) ^ Nat.card W = 1 := by
      refine Subtype.ext ?_
      have := congrArg Subtype.val (pow_card_eq_one' (G := W) (x := (⟨x, hx⟩ : W)))
      exact this
    rw [← map_pow, this, map_one]
  have h2 : π ⟨x, hxC⟩ ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h3 : π ⟨x, hxC⟩ = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hWcop) (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨⟨x, hxC⟩, (QuotientGroup.eq_one_iff _).1 h3, rfl⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
