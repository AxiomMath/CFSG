module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.SL23

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

theorem oddCore_sl2f3 : oddCore SL2F3 = ⊥ := by
  refine le_antisymm (sSup_le ?_) bot_le
  rintro N ⟨hN, hodd⟩
  haveI := hN
  exact (CFSG.SignalizerFunctorTheorem.Glauberman.eq_bot_of_normal_of_odd_card_sl_two_three
    N hodd).le

theorem isSL23Mod_sl2f3 : IsSL23Mod SL2F3 :=
  ⟨(QuotientGroup.quotientMulEquivOfEq oddCore_sl2f3).trans QuotientGroup.quotientBot⟩

theorem isSubnormal_subgroupOf_of_two_step {A : Type*} [Group A] {H L C : Subgroup A}
    (hHL : H ≤ L) (hH : ∀ h ∈ H, ∀ l ∈ L, l * h * l⁻¹ ∈ H)
    (hL : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ ∈ L) : (H.subgroupOf C).IsSubnormal := by
  have hLn : (L.subgroupOf C).Normal := by
    constructor
    intro l hl c
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hL _ hl _ c.2
  refine Subgroup.IsSubnormal.step _ (L.subgroupOf C) ?_ hLn.isSubnormal ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHL hx
  · constructor
    intro h hh g
    have hh' : ((h : ↥C) : A) ∈ H := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
    have hg : ((g : ↥C) : A) ∈ L := Subgroup.mem_subgroupOf.mp g.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hH _ hh' _ hg

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sl23PocketIn_of_block (hQ : Q.Nondegenerate) (z : omegaGroup hQ)
    (hs : (z : OGroup Q) * z = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (z : OGroup Q)))
    {K₁ : Subgroup (OGroup (Q.restrict (commSp (z : OGroup Q))))}
    (hπ : piOrth (Q.restrict (commSp (z : OGroup Q))) ∈ K₁)
    (hK₁Ω : K₁ ≤ omegaGroup (nondegenerate_restrict_commSp hQ hs))
    (hK₁n : (K₁.subgroupOf (omegaGroup (nondegenerate_restrict_commSp hQ hs))).Normal)
    (hK₁ : Nonempty (K₁ ≃* SL2F3)) :
    ∃ K : Subgroup (omegaGroup hQ), Sl23PocketIn (⊤ : Subgroup (omegaGroup hQ)) z K := by
  obtain ⟨f⟩ := hK₁
  have hle : K₁.map (blockInr hs) ≤ omegaGroup hQ := by
    rintro _ ⟨b, hb, rfl⟩
    exact blockInr_mem_omegaGroup hQ hs hU (hK₁Ω hb)
  refine ⟨(K₁.map (blockInr hs)).subgroupOf (omegaGroup hQ), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨_, hπ, blockInr_piOrth hs⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨b, -, hbx⟩ := hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hs b)
    simp only [Subgroup.coe_mul]
    rw [← hbx]
    exact hc
  · have hR := nondegenerate_restrict_commSp hQ hs
    refine isSubnormal_subgroupOf_of_two_step
      (L := ((omegaGroup hR).map (blockInr hs)).subgroupOf (omegaGroup hQ)) ?_ ?_ ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨b, hb, hbx⟩ := hx
      exact ⟨b, hK₁Ω hb, hbx⟩
    · intro h hh l hl
      rw [Subgroup.mem_subgroupOf] at hh hl ⊢
      obtain ⟨b₁, hb₁, hb₁h⟩ := hh
      obtain ⟨b₂, hb₂, hb₂l⟩ := hl
      have hmem : b₂ * b₁ * b₂⁻¹ ∈ K₁ := by
        have hc := hK₁n.conj_mem ⟨b₁, hK₁Ω hb₁⟩ (Subgroup.mem_subgroupOf.mpr hb₁) ⟨b₂, hb₂⟩
        exact Subgroup.mem_subgroupOf.mp hc
      refine ⟨b₂ * b₁ * b₂⁻¹, hmem, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hb₁h, hb₂l]
    · intro l hl c hc
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      obtain ⟨b₂, hb₂, hb₂l⟩ := hl
      have hcc : (c : OGroup Q) ∈ Subgroup.centralizer ({(z : OGroup Q)} : Set (OGroup Q)) := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h1
      obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hs hcc b₂
      refine ⟨c₂ * b₂ * c₂⁻¹, (omegaGroup_normal hR).conj_mem b₂ hb₂ c₂, ?_⟩
      rw [← hc₂, hb₂l]
      rfl
  · refine isSL23Mod_of_mulEquiv ?_ isSL23Mod_sl2f3
    exact f.symm.trans ((Subgroup.equivMapOfInjective K₁ (blockInr hs)
      (blockInr_injective hs)).trans (Subgroup.subgroupOfEquivOfLe hle).symm)

theorem asc82PocketCover_holds : Asc82PocketCover := by
  intro V _ _ _ Q hQ z hzz htype
  have hs : (z : OGroup Q) * z = 1 := by
    simpa using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hzz
  have hdim : Module.finrank (ZMod 3) (commSp (z : OGroup Q)) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst htype
  have hsign : quadSign (Q.restrict (commSp (z : OGroup Q))) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd htype
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, Subgroup.coe_one, invType_one] at htype
    exact absurd (congrArg Prod.fst htype) (by decide)
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1, ?_⟩
  obtain ⟨K₁, hπ, hK₁Ω, hK₁n, hK₁⟩ :=
    exists_pocket_plus4 (nondegenerate_restrict_commSp hQ hs) hdim hsign
  exact sl23PocketIn_of_block hQ z hs (by omega) hπ hK₁Ω hK₁n hK₁

end CFSG.OddStandard.SmallF3.Omega
